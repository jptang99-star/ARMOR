package armor

import firrtl._
import firrtl.ir._
import firrtl.options.Dependency
import firrtl.passes.Pass
import logger.LazyLogging

import scala.collection.mutable

/** Promotes repeated bit projections from the same UInt source into one shared
  * ArmorBitGather plus smaller projections from that promoted value.
  *
  * The pass treats bit(), bits(), and ArmorBitGather uniformly as
  * Projection(source, mask).  A group such as:
  *
  *   a = ArmorBitGather(x, 0x000c)
  *   b = ArmorBitGather(x, 0x4050)
  *   c = ArmorBitGather(x, 0x0030)
  *
  * becomes:
  *
  *   p = ArmorBitGather(x, 0x407c)
  *   a = ArmorBitGather(p, 0x03)
  *   b = ArmorBitGather(p, 0x34)
  *   c = ArmorBitGather(p, 0x0c)
  *
  * This deliberately runs before SLP discovery.  The inserted promoted nodes
  * and rewritten users are ordinary IR nodes, so the packer can discover both
  * continuous and non-continuous projection packs without emitter-only
  * peepholes.
  */
object BitProjectionPromotionPass extends Pass with LazyLogging {
  override def prerequisites = Seq(Dependency(BitOpNormalizePass))
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform): Boolean = false

  private val ProjectionNamePrefix = "_armor_bit_projection"
  private val LegacySliceNamePrefix = "_armor_bit_slice"

  final case class Stats(groups: Int, projections: Int, promotedNodes: Int) {
    def +(other: Stats): Stats =
      Stats(groups + other.groups, projections + other.projections, promotedNodes + other.promotedNodes)
  }

  private object Stats {
    val Empty: Stats = Stats(0, 0, 0)
  }

  private final case class SourceKey(serialized: String, tpe: Type)

  private final case class ProjectionCandidate(
    statementIndex: Int,
    node:           DefNode,
    source:         Expression,
    sourceWidth:    Int,
    mask:           BigInt,
    resultWidth:    Int
  )

  private final case class PromotionGroup(
    source:            Expression,
    sourceWidth:       Int,
    unionMask:         BigInt,
    gatherSource:      Expression,
    gatherSourceWidth: Int,
    localUnionMask:    BigInt,
    windowNode:        Option[DefNode],
    name:              String,
    nodeMasks:         Map[String, BigInt]
  ) {
    val width: Int = bitCount(localUnionMask, gatherSourceWidth)
    val tpe: Type = UIntType(IntWidth(width))
  }

  private final case class ProjectionClusterMetrics(
    groupSize:         Int,
    distinctMaskCount: Int,
    sourceWidth:       Int,
    unionWidth:        Int,
    spanWidth:         Int
  )

  private def minProjectionGroupLength: Int =
    Option(java.lang.Integer.getInteger("armor.bitProjectionPromotion.minGroup"))
      .map(_.toInt).getOrElse(3).max(2)

  private def targetPackDegree: Int =
    Option(java.lang.Integer.getInteger("armor.bitProjectionPromotion.targetDegree"))
      .map(_.toInt).getOrElse(4).max(1).min(64)

  private def maxPromotedWidth: Int =
    Option(java.lang.Integer.getInteger("armor.bitProjectionPromotion.maxWidth"))
      .map(_.toInt)
      .filter(_ > 0)
      .getOrElse((64 / targetPackDegree).max(1))
      .max(1)
      .min(64)

  private def disabled: Boolean =
    java.lang.Boolean.getBoolean("armor.disableBitProjectionPromotion")

  private def knownUIntWidth(tpe: Type): Option[Int] = tpe match {
    case UIntType(IntWidth(width)) if width > 0 && width.isValidInt => Some(width.toInt)
    case _                                                          => None
  }

  private def smallUIntWidth(tpe: Type): Option[Int] = tpe match {
    case UIntType(IntWidth(width)) if width > 0 && width <= 64 && width.isValidInt => Some(width.toInt)
    case _                                                                         => None
  }

  private def bitCount(value: BigInt, width: Int): Int =
    (0 until math.min(width, value.bitLength)).count(bit => ((value >> bit) & 1) == 1)

  private def lowestSetBit(value: BigInt): Int = {
    require(value > 0)
    var shifted = value
    var bit = 0
    while ((shifted & BigInt(1)) == 0) {
      shifted = shifted >> 1
      bit += 1
    }
    bit
  }

  private def highestSetBit(value: BigInt): Int = {
    require(value > 0)
    value.bitLength - 1
  }

  private def spanWidth(value: BigInt): Int =
    if (value == 0) 0 else highestSetBit(value) - lowestSetBit(value) + 1

  private def bitsOf(mask: BigInt, width: Int): Vector[Int] =
    (0 until math.min(width, mask.bitLength)).filter(bit => ((mask >> bit) & 1) == 1).toVector

  private def maskFromRange(hi: BigInt, lo: BigInt): Option[BigInt] =
    if (lo >= 0 && hi >= lo && hi.isValidInt && lo.isValidInt) {
      val width = hi.toInt - lo.toInt + 1
      if (width > 0 && width <= 64) Some(((BigInt(1) << width) - 1) << lo.toInt)
      else None
    } else None

  private def defName(statement: Statement): Option[String] = statement match {
    case node: DefNode          => Some(node.name)
    case wire: DefWire          => Some(wire.name)
    case register: DefRegister  => Some(register.name)
    case memory: DefMemory      => Some(memory.name)
    case instance: WDefInstance => Some(instance.name)
    case _                      => None
  }

  private def collectStatementNames(statement: Statement, names: mutable.Set[String]): Unit = {
    defName(statement).foreach(names += _)
    statement match {
      case Block(statements) =>
        statements.foreach(collectStatementNames(_, names))
      case conditional: Conditionally =>
        collectStatementNames(conditional.conseq, names)
        collectStatementNames(conditional.alt, names)
      case _ =>
    }
  }

  private final class ModulePromoter(initialNames: Set[String]) {
    private val usedNames = mutable.HashSet.empty[String] ++ initialNames
    private var nextId = 0

    private final class PromotionBucket(first: ProjectionCandidate) {
      val candidates: mutable.ArrayBuffer[ProjectionCandidate] =
        mutable.ArrayBuffer(first)
      var unionMask: BigInt = first.mask
      val firstStatementIndex: Int = first.statementIndex

      def width: Int =
        bitCount(unionMask, first.sourceWidth)

      def add(candidate: ProjectionCandidate): Unit = {
        candidates += candidate
        unionMask |= candidate.mask
      }
    }

    private def freshName(): String = {
      var candidate = ""
      do {
        candidate = s"${ProjectionNamePrefix}_${nextId}"
        nextId += 1
      } while (usedNames(candidate))
      usedNames += candidate
      candidate
    }

    private def sourceKey(source: Expression): SourceKey =
      SourceKey(source.serialize, source.tpe)

    private def isPromotionSource(source: Expression): Boolean = source match {
      case Reference(name, _, _, _) =>
        name.startsWith(s"${ProjectionNamePrefix}_") || name.startsWith(s"${LegacySliceNamePrefix}_")
      case _ => false
    }

    private def validMask(mask: BigInt, sourceWidth: Int, resultWidth: Int): Boolean =
      mask > 0 &&
        sourceWidth > 0 &&
        resultWidth > 0 && resultWidth <= 64 &&
        (mask & ~((BigInt(1) << sourceWidth) - 1)) == 0 &&
        bitCount(mask, sourceWidth) == resultWidth

    private def projectionCandidate(
      statement: Statement,
      index:     Int
    ): Option[ProjectionCandidate] = statement match {
      case node @ DefNode(_, _, DoPrim(ArmorBitSelect, Seq(source), Seq(bit), resultType))
          if bit >= 0 && bit.isValidInt && smallUIntWidth(resultType).contains(1) &&
            !isPromotionSource(source) =>
        knownUIntWidth(source.tpe).filter(width => bit.toInt < width).map { sourceWidth =>
          ProjectionCandidate(index, node, source, sourceWidth, BigInt(1) << bit.toInt, 1)
        }

      case node @ DefNode(_, _, DoPrim(ArmorBitExtract, Seq(source), Seq(hi, lo), resultType))
          if !isPromotionSource(source) =>
        (knownUIntWidth(source.tpe), smallUIntWidth(resultType), maskFromRange(hi, lo)) match {
          case (Some(sourceWidth), Some(resultWidth), Some(mask))
              if hi < sourceWidth && validMask(mask, sourceWidth, resultWidth) =>
            Some(ProjectionCandidate(index, node, source, sourceWidth, mask, resultWidth))
          case _ => None
        }

      case node @ DefNode(_, _, DoPrim(ArmorBitGather, Seq(source), Seq(mask), resultType))
          if !isPromotionSource(source) =>
        (smallUIntWidth(source.tpe), smallUIntWidth(resultType)) match {
          case (Some(sourceWidth), Some(resultWidth))
              if validMask(mask, sourceWidth, resultWidth) =>
            Some(ProjectionCandidate(index, node, source, sourceWidth, mask, resultWidth))
          case _ => None
        }

      case _ => None
    }

    private def remapMask(mask: BigInt, unionMask: BigInt, sourceWidth: Int): BigInt = {
      val unionBits = bitsOf(unionMask, sourceWidth)
      val indexBySourceBit = unionBits.zipWithIndex.toMap
      bitsOf(mask, sourceWidth).foldLeft(BigInt(0)) { case (result, sourceBit) =>
        result | (BigInt(1) << indexBySourceBit(sourceBit))
      }
    }

    private def projectionClusterMetrics(
      group:     Vector[ProjectionCandidate],
      unionMask: BigInt
    ): ProjectionClusterMetrics = {
      val sourceWidth = group.head.sourceWidth
      ProjectionClusterMetrics(
        groupSize = group.size,
        distinctMaskCount = group.iterator.map(_.mask).toSet.size,
        sourceWidth = sourceWidth,
        unionWidth = bitCount(unionMask, sourceWidth),
        spanWidth = spanWidth(unionMask)
      )
    }

    private def shouldPromote(
      group:       Vector[ProjectionCandidate],
      unionMask:   BigInt,
      widthBudget: Int
    ): Boolean = {
      val metrics = projectionClusterMetrics(group, unionMask)
      metrics.groupSize >= minProjectionGroupLength &&
        metrics.distinctMaskCount >= 2 &&
        metrics.unionWidth > 1 &&
        metrics.unionWidth < metrics.sourceWidth &&
        metrics.unionWidth <= widthBudget &&
        metrics.spanWidth <= 64
    }

    private def splitProjectionGroup(
      group:        Vector[ProjectionCandidate],
      sourceWidth:  Int,
      widthBudget:  Int
    ): Vector[Vector[ProjectionCandidate]] = {
      val buckets = mutable.ArrayBuffer.empty[PromotionBucket]
      val ordered = group.sortBy(candidate =>
        (-candidate.resultWidth, candidate.mask, candidate.statementIndex, candidate.node.name)
      )

      ordered.foreach { candidate =>
        val maskWidth = bitCount(candidate.mask, sourceWidth)
        if (maskWidth <= widthBudget && spanWidth(candidate.mask) <= 64) {
          val choice = buckets
            .flatMap { bucket =>
              val widenedMask = bucket.unionMask | candidate.mask
              val widenedWidth = bitCount(widenedMask, sourceWidth)
              if (widenedWidth <= widthBudget && spanWidth(widenedMask) <= 64) {
                val oldWidth = bucket.width
                val addedWidth = widenedWidth - oldWidth
                val overlapWidth = bitCount(bucket.unionMask & candidate.mask, sourceWidth)
                Some((bucket, addedWidth, -overlapWidth, oldWidth, bucket.firstStatementIndex))
              } else None
            }
            .sortBy { case (_, addedWidth, negativeOverlap, oldWidth, firstIndex) =>
              (addedWidth, negativeOverlap, oldWidth, firstIndex)
            }
            .headOption
            .map(_._1)

          choice match {
            case Some(bucket) => bucket.add(candidate)
            case None         => buckets += new PromotionBucket(candidate)
          }
        }
      }

      buckets.toVector.map(_.candidates.toVector)
    }

    private def buildPromotionGroup(
      source:      Expression,
      sourceWidth: Int,
      bucket:      Vector[ProjectionCandidate],
      unionMask:   BigInt
    ): PromotionGroup = {
      if (sourceWidth <= 64) {
        PromotionGroup(
          source = source,
          sourceWidth = sourceWidth,
          unionMask = unionMask,
          gatherSource = source,
          gatherSourceWidth = sourceWidth,
          localUnionMask = unionMask,
          windowNode = None,
          name = freshName(),
          nodeMasks = bucket.map(candidate => candidate.node.name -> candidate.mask).toMap
        )
      } else {
        val lo = lowestSetBit(unionMask)
        val hi = highestSetBit(unionMask)
        val windowWidth = hi - lo + 1
        require(windowWidth > 0 && windowWidth <= 64)
        val windowType = UIntType(IntWidth(windowWidth))
        val windowName = freshName()
        val windowNode = DefNode(
          NoInfo,
          windowName,
          DoPrim(ArmorBitExtract, Seq(source), Seq(BigInt(hi), BigInt(lo)), windowType)
        )
        val windowRef = Reference(windowName, windowType, NodeKind, SourceFlow)
        PromotionGroup(
          source = source,
          sourceWidth = sourceWidth,
          unionMask = unionMask,
          gatherSource = windowRef,
          gatherSourceWidth = windowWidth,
          localUnionMask = unionMask >> lo,
          windowNode = Some(windowNode),
          name = freshName(),
          nodeMasks = bucket.map(candidate => candidate.node.name -> candidate.mask).toMap
        )
      }
    }

    private def promotionGroups(candidates: Vector[ProjectionCandidate]): Vector[PromotionGroup] = {
      val widthBudget = maxPromotedWidth
      candidates
        .groupBy(candidate => sourceKey(candidate.source))
        .toVector
        .sortBy { case (key, _) => key.serialized }
        .flatMap { case (_, group) =>
          val source = group.head.source
          val sourceWidth = group.head.sourceWidth
          if (group.forall(_.sourceWidth == sourceWidth)) {
            splitProjectionGroup(group, sourceWidth, widthBudget).flatMap { bucket =>
              val unionMask = bucket.iterator.map(_.mask).foldLeft(BigInt(0))(_ | _)
              if (shouldPromote(bucket, unionMask, widthBudget)) {
                Some(buildPromotionGroup(source, sourceWidth, bucket, unionMask))
              } else None
            }
          } else None
        }
    }

    private def promotedNode(group: PromotionGroup): DefNode =
      DefNode(
        NoInfo,
        group.name,
        DoPrim(ArmorBitGather, Seq(group.gatherSource), Seq(group.localUnionMask), group.tpe)
      )

    private def rewriteProjection(node: DefNode, group: PromotionGroup, mask: BigInt): DefNode = {
      val promotedRef = Reference(group.name, group.tpe, NodeKind, SourceFlow)
      val localMask = group.windowNode match {
        case Some(window) =>
          val DoPrim(_, _, Seq(_, lo), _) = window.value
          mask >> lo.toInt
        case None => mask
      }
      val remapped = remapMask(localMask, group.localUnionMask, group.gatherSourceWidth)
      node.copy(value = DoPrim(
        ArmorBitGather,
        Seq(promotedRef),
        Seq(remapped),
        node.value.tpe
      ))
    }

    private def promoteBlock(block: Block): (Block, Stats) = {
      val rewrittenChildren = block.stmts.map(rewriteStatement)
      val statements = rewrittenChildren.map(_._1).toVector
      val childStats = rewrittenChildren.foldLeft(Stats.Empty)(_ + _._2)
      val candidates = statements.zipWithIndex.flatMap { case (statement, index) =>
        projectionCandidate(statement, index)
      }
      val groups = promotionGroups(candidates)
      if (groups.isEmpty) (Block(statements), childStats)
      else {
        val groupByNodeName = groups.flatMap(group => group.nodeMasks.keys.map(_ -> group)).toMap
        val insertionsByIndex = groups
          .map(group => candidates.filter(candidate => group.nodeMasks.contains(candidate.node.name))
            .map(_.statementIndex).min -> group)
          .groupBy(_._1)
          .view.mapValues(_.map(_._2).sortBy(_.name))
          .toMap

        val promotedStatements = Vector.newBuilder[Statement]
        statements.zipWithIndex.foreach { case (statement, index) =>
          insertionsByIndex.getOrElse(index, Vector.empty).foreach { group =>
            group.windowNode.foreach(promotedStatements += _)
            promotedStatements += promotedNode(group)
          }
          statement match {
            case node: DefNode =>
              groupByNodeName.get(node.name).flatMap(group => group.nodeMasks.get(node.name).map(group -> _)) match {
                case Some((group, mask)) => promotedStatements += rewriteProjection(node, group, mask)
                case None                => promotedStatements += statement
              }
            case _ => promotedStatements += statement
          }
        }

        val stats = Stats(
          groups = groups.size,
          projections = groups.iterator.map(_.nodeMasks.size).sum,
          promotedNodes = groups.size + groups.count(_.windowNode.nonEmpty)
        )
        (Block(promotedStatements.result()), childStats + stats)
      }
    }

    private def rewriteStatement(statement: Statement): (Statement, Stats) = statement match {
      case block: Block =>
        promoteBlock(block)
      case conditional: Conditionally =>
        val (conseq, conseqStats) = rewriteStatement(conditional.conseq)
        val (alt, altStats) = rewriteStatement(conditional.alt)
        (conditional.copy(conseq = conseq, alt = alt), conseqStats + altStats)
      case other =>
        (other, Stats.Empty)
    }

    def run(statement: Statement): (Statement, Stats) =
      rewriteStatement(statement)
  }

  override def run(circuit: Circuit): Circuit = {
    if (disabled) {
      logger.info("Armor bit-projection promotion disabled")
      circuit
    } else {
      var total = Stats.Empty
      val modules = circuit.modules.map {
        case module: Module =>
          val names = mutable.HashSet.empty[String] ++ module.ports.map(_.name)
          collectStatementNames(module.body, names)
          val promoter = new ModulePromoter(names.toSet)
          val (body, stats) = promoter.run(module.body)
          total += stats
          module.copy(body = body)
        case extModule: ExtModule => extModule
      }
      logger.info(
        s"Armor bit-projection promotion created ${total.promotedNodes} promoted nodes " +
          s"for ${total.projections} projections in ${total.groups} groups"
      )
      circuit.copy(modules = modules)
    }
  }
}
