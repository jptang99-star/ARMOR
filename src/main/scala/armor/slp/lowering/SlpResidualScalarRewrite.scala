package armor.slp

import essent.ir.{MemWrite, RegUpdate}
import firrtl.PrimOps.{Eq, Or, Shr}
import firrtl.ir._

import scala.collection.mutable

/** Post-SLP scalar cleanup.  These rewrites deliberately run after ordinary
  * pack discovery has had first refusal: they only claim scalar fallback nodes
  * that were not packed and were not already handled by another residual
  * lowering.
  */
sealed trait SlpResidualScalarRewrite {
  def rootNodeId: Int
  def absorbedNodeIds: Set[Int]
  def inputNodeIds: Set[Int]
  def originalNodeIds: Vector[Int]

  final def scalarUses: Set[(Int, Int)] =
    inputNodeIds.iterator.filter(_ != rootNodeId).map(_ -> rootNodeId).toSet
}

/** Rewrites an OR of equality predicates over the same small UInt source into
  * a single bitset-membership test:
  *
  *   (x == a) | (x == b) | ((x >> k) == c)  ==>
  *   ((mask >> x) & 1) != 0
  *
  * Shifted equality expands to the corresponding source-value interval. */
final case class SlpResidualMembershipRewrite(
  rootNodeId:     Int,
  source:         Expression,
  sourceWidth:    Int,
  mask:           BigInt,
  absorbedNodeIds: Set[Int],
  inputNodeIds:   Set[Int],
  originalNodeIds: Vector[Int]
) extends SlpResidualScalarRewrite {
  require(rootNodeId >= 0)
  require(sourceWidth > 0 && sourceWidth <= 6)
  require(mask > 0 && mask < (BigInt(1) << (1 << sourceWidth)))
  require(absorbedNodeIds.forall(_ >= 0))
  require(!absorbedNodeIds(rootNodeId))
  require(inputNodeIds.forall(_ >= 0))
  require(originalNodeIds == originalNodeIds.distinct.sorted)
  require(originalNodeIds.contains(rootNodeId))
}

final case class SlpResidualScalarRewritePlan(
  rewrites: Vector[SlpResidualScalarRewrite]
) {
  require(rewrites.map(_.rootNodeId) == rewrites.map(_.rootNodeId).distinct.sorted)

  val byRootNodeId: Map[Int, SlpResidualScalarRewrite] =
    rewrites.iterator.map(rewrite => rewrite.rootNodeId -> rewrite).toMap
  val absorbedNodeIds: Set[Int] =
    rewrites.iterator.flatMap(_.absorbedNodeIds).toSet
  val scalarUses: Set[(Int, Int)] =
    rewrites.iterator.flatMap(_.scalarUses).toSet
}

object SlpResidualScalarRewritePlan {
  val Empty: SlpResidualScalarRewritePlan = SlpResidualScalarRewritePlan(Vector.empty)
}

object SlpResidualScalarRewritePlanner {
  def build(
    context:               SlpAnalysisContext,
    unavailableNodeIds:    Set[Int],
    scalarFallbackNodeIds: Vector[Int]
  ): SlpResidualScalarRewritePlan = {
    val membership = SlpResidualMembershipPlanner.build(
      context = context,
      unavailableNodeIds = unavailableNodeIds,
      scalarFallbackNodeIds = scalarFallbackNodeIds
    )
    SlpResidualScalarRewritePlan(membership.sortBy(_.rootNodeId))
  }
}

private object SlpResidualMembershipPlanner {
  private final case class Definition(nodeId: Int, node: DefNode)

  private final case class Predicate(
    source:      Expression,
    sourceWidth: Int,
    values:      Set[BigInt],
    nodeIds:     Set[Int],
    inputNodeIds: Set[Int]
  )

  private final case class OrTree(
    leaves:          Vector[Int],
    internalNodeIds: Set[Int]
  )

  private final case class Candidate(
    rootNodeId:     Int,
    source:         Expression,
    sourceWidth:    Int,
    mask:           BigInt,
    absorbedNodeIds: Set[Int],
    inputNodeIds:   Set[Int],
    originalNodeIds: Vector[Int],
    benefit:        Int
  )

  private def uintWidth(tpe: Type): Option[Int] = tpe match {
    case UIntType(IntWidth(width)) if width > 0 && width.isValidInt => Some(width.toInt)
    case _                                                          => None
  }

  private def uintWidth(expression: Expression): Option[Int] =
    uintWidth(expression.tpe)

  private def expressionName(expression: Expression): Option[String] = expression match {
    case Reference(name, _, _, _)     => Some(name)
    case SubField(base, name, _, _)   => expressionName(base).map(prefix => s"$prefix.$name")
    case SubIndex(base, value, _, _)  => expressionName(base).map(prefix => s"$prefix[$value]")
    case SubAccess(base, index, _, _) =>
      expressionName(base).flatMap(prefix => expressionName(index).map(idx => s"$prefix[$idx]"))
    case _ => None
  }

  private def expressionReferences(expression: Expression): Set[String] = {
    val result = mutable.HashSet.empty[String]
    def visit(current: Expression): Unit = {
      expressionName(current).foreach(result += _)
      current.foreachExpr(visit)
    }
    visit(expression)
    result.toSet
  }

  private def statementReferences(statement: Statement): Set[String] = statement match {
    case Block(statements) => statements.iterator.flatMap(statementReferences).toSet
    case conditional: Conditionally =>
      expressionReferences(conditional.pred) ++ statementReferences(conditional.conseq) ++
        statementReferences(conditional.alt)
    case node: DefNode => expressionReferences(node.value)
    case update: RegUpdate => expressionReferences(update.regRef) ++ expressionReferences(update.expr)
    case write: MemWrite => expressionReferences(write.wrEn) ++ expressionReferences(write.wrMask) ++
      expressionReferences(write.wrAddr) ++ expressionReferences(write.wrData)
    case connect: Connect => expressionReferences(connect.loc) ++ expressionReferences(connect.expr)
    case print: Print => expressionReferences(print.en) ++ print.args.flatMap(expressionReferences)
    case stop: Stop => expressionReferences(stop.en)
    case other =>
      val result = mutable.HashSet.empty[String]
      other.foreachExpr(expression => result ++= expressionReferences(expression))
      result.toSet
  }

  private def sameExpression(left: Expression, right: Expression): Boolean =
    left.serialize == right.serialize && left.tpe == right.tpe

  private def definitionFor(
    nodeId: Int,
    definitionsById: Map[Int, DefNode]
  ): Option[DefNode] = definitionsById.get(nodeId)

  private def referencedDefinition(
    expression: Expression,
    definitionsByName: Map[String, Definition]
  ): Option[Definition] = expression match {
    case Reference(name, _, _, _) => definitionsByName.get(name)
    case _                        => None
  }

  private def referencedNodeId(
    expression: Expression,
    definitionsByName: Map[String, Definition]
  ): Option[Int] =
    referencedDefinition(expression, definitionsByName).map(_.nodeId)

  private def decodeOrOperands(
    nodeId: Int,
    definitionsById: Map[Int, DefNode],
    operations: Map[Int, SlpOperation]
  ): Option[(Expression, Expression)] = {
    operations.get(nodeId) match {
      case Some(SlpOperation(SlpOr, 1, _, Vector(_, _), _, _)) =>
        definitionFor(nodeId, definitionsById).collect {
          case DefNode(_, _, DoPrim(Or, Seq(left, right), Seq(), _)) => left -> right
        }
      case _ => None
    }
  }

  private def flattenOrTree(
    nodeId: Int,
    definitionsByName: Map[String, Definition],
    definitionsById:   Map[Int, DefNode],
    operations:        Map[Int, SlpOperation],
    scalarFallbackSet: Set[Int],
    unavailable:       Set[Int],
    visiting:          Set[Int],
    cache:             mutable.HashMap[Int, Option[OrTree]]
  ): Option[OrTree] = {
    if (visiting(nodeId) || unavailable(nodeId) || !scalarFallbackSet(nodeId)) None
    else cache.getOrElseUpdate(nodeId, {
      decodeOrOperands(nodeId, definitionsById, operations) match {
        case Some((left, right)) =>
          val children = Vector(left, right).map { operand =>
            referencedNodeId(operand, definitionsByName) match {
              case Some(childId)
                  if scalarFallbackSet(childId) && !unavailable(childId) =>
                flattenOrTree(
                  childId,
                  definitionsByName,
                  definitionsById,
                  operations,
                  scalarFallbackSet,
                  unavailable,
                  visiting + nodeId,
                  cache
                ).orElse(Some(OrTree(Vector(childId), Set.empty)))
              case _ => None
            }
          }
          if (children.exists(_.isEmpty)) None
          else {
            val merged = children.flatten.foldLeft(OrTree(Vector.empty, Set.empty)) {
              case (acc, tree) =>
                OrTree(
                  leaves = acc.leaves ++ tree.leaves,
                  internalNodeIds = acc.internalNodeIds ++ tree.internalNodeIds
                )
            }
            Some(merged.copy(internalNodeIds = merged.internalNodeIds + nodeId))
          }
        case None => Some(OrTree(Vector(nodeId), Set.empty))
      }
    })
  }

  private def literalAndSignal(left: Expression, right: Expression): Option[(Expression, BigInt)] =
    (left, right) match {
      case (UIntLiteral(value, _), signal) if value >= 0 => Some(signal -> value)
      case (signal, UIntLiteral(value, _)) if value >= 0 => Some(signal -> value)
      case _                                             => None
    }

  private def decodeShift(
    expression: Expression,
    definitionsByName: Map[String, Definition]
  ): Option[(Expression, Int, Option[Int])] = {
    val candidate = referencedDefinition(expression, definitionsByName) match {
      case Some(definition) => Some((definition.node.value, Some(definition.nodeId)))
      case None             => Some((expression, None))
    }
    candidate.flatMap {
      case (DoPrim(Shr, Seq(source), Seq(amount), _), nodeId)
          if amount >= 0 && amount.isValidInt =>
        Some((source, amount.toInt, nodeId))
      case _ => None
    }
  }

  private def decodePredicate(
    nodeId: Int,
    definitionsByName: Map[String, Definition],
    definitionsById:   Map[Int, DefNode],
    operations:        Map[Int, SlpOperation],
    view:              SlpGraphView
  ): Option[Predicate] = {
    operations.get(nodeId) match {
      case Some(SlpOperation(SlpEqConst, 1, _, _, _, _)) =>
        definitionFor(nodeId, definitionsById).flatMap {
          case DefNode(_, _, DoPrim(Eq, Seq(left, right), Seq(), _)) =>
            literalAndSignal(left, right).flatMap { case (signalOrShift, value) =>
              val shifted = for {
                decoded <- decodeShift(signalOrShift, definitionsByName)
                (source, amount, shiftNodeId) = decoded
                sourceWidth <- uintWidth(source)
                shiftedWidth <- uintWidth(signalOrShift)
                if sourceWidth <= 6
                if amount >= 0 && amount < sourceWidth
                if shiftedWidth == sourceWidth - amount
                if value < (BigInt(1) << shiftedWidth)
                first = value << amount
                last = ((value + 1) << amount) - 1
                maxValue = (BigInt(1) << sourceWidth) - 1
                if first <= maxValue
              } yield Predicate(
                source = source,
                sourceWidth = sourceWidth,
                values = (first to (last min maxValue)).toSet,
                nodeIds = Set(nodeId) ++ shiftNodeId,
                inputNodeIds = expressionReferences(source).flatMap(view.graph.nameToID.get)
              )

              shifted.orElse {
                for {
                width <- uintWidth(signalOrShift)
                if width <= 6
                if value < (BigInt(1) << width)
              } yield Predicate(
                source = signalOrShift,
                sourceWidth = width,
                values = Set(value),
                nodeIds = Set(nodeId),
                inputNodeIds = expressionReferences(signalOrShift).flatMap(view.graph.nameToID.get)
              )
              }
            }
          case _ => None
        }
      case _ => None
    }
  }

  private def retainedAbsorbedNodes(
    context: SlpAnalysisContext,
    candidates: Vector[Candidate]
  ): Set[Int] = {
    val view = context.graph
    val chosenRoots = candidates.iterator.map(_.rootNodeId).toSet
    val absorbed = candidates.iterator.flatMap(_.absorbedNodeIds).toSet
    val retained = mutable.HashSet.empty[Int]

    view.validNodeIds.foreach { nodeId =>
      if (!chosenRoots(nodeId) && !absorbed(nodeId)) {
        statementReferences(view.node(nodeId).statement).foreach { name =>
          view.graph.nameToID.get(name).filter(absorbed).foreach(retained += _)
        }
      }
    }

    var changed = true
    while (changed) {
      changed = false
      retained.toVector.foreach { nodeId =>
        statementReferences(view.node(nodeId).statement).foreach { name =>
          view.graph.nameToID.get(name).filter(absorbed).foreach { dependency =>
            val before = retained.size
            retained += dependency
            changed = changed || retained.size != before
          }
        }
      }
    }
    retained.toSet
  }

  def build(
    context:               SlpAnalysisContext,
    unavailableNodeIds:    Set[Int],
    scalarFallbackNodeIds: Vector[Int]
  ): Vector[SlpResidualScalarRewrite] = {
    val view = context.graph
    val scalarFallbackSet = scalarFallbackNodeIds.toSet
    val operations = context.classifications.collect {
      case (nodeId, SlpSupported(operation)) => nodeId -> operation
    }.toMap
    val definitions = view.validNodeIds.flatMap { nodeId =>
      view.node(nodeId).statement match {
        case node: DefNode => Some(node.name -> Definition(nodeId, node))
        case _             => None
      }
    }.toMap
    val definitionsById = definitions.valuesIterator.map(definition =>
      definition.nodeId -> definition.node
    ).toMap

    val orCache = mutable.HashMap.empty[Int, Option[OrTree]]
    val rawCandidates = scalarFallbackNodeIds
      .filterNot(unavailableNodeIds)
      .flatMap { rootNodeId =>
        flattenOrTree(
          rootNodeId,
          definitions,
          definitionsById,
          operations,
          scalarFallbackSet,
          unavailableNodeIds,
          Set.empty,
          orCache
        ).toVector.flatMap { tree =>
          val treeNodeIds = tree.internalNodeIds + rootNodeId
          val leafPredicates = tree.leaves.map { leafNodeId =>
            decodePredicate(leafNodeId, definitions, definitionsById, operations, view)
          }
          if (tree.leaves.size < 4 || leafPredicates.exists(_.isEmpty)) Vector.empty
          else {
            val predicates = leafPredicates.flatten
            val source = predicates.head.source
            val width = predicates.head.sourceWidth
            if (!predicates.forall(predicate =>
                predicate.sourceWidth == width && sameExpression(predicate.source, source)
              )) Vector.empty
            else if ((tree.internalNodeIds - rootNodeId).exists(nodeId =>
                !view.validFanoutIds(nodeId).toSet.subsetOf(treeNodeIds)
              )) Vector.empty
            else {
              val values = predicates.iterator.flatMap(_.values).toSet
              val mask = values.foldLeft(BigInt(0))((acc, value) => acc | (BigInt(1) << value.toInt))
              val predicateNodeIds = predicates.iterator.flatMap(_.nodeIds).toSet
              val absorbed = (tree.internalNodeIds - rootNodeId) ++ predicateNodeIds
              val inputNodeIds = predicates.iterator.flatMap(_.inputNodeIds).toSet
              Vector(Candidate(
                rootNodeId = rootNodeId,
                source = source,
                sourceWidth = width,
                mask = mask,
                absorbedNodeIds = absorbed,
                inputNodeIds = inputNodeIds,
                originalNodeIds = (absorbed + rootNodeId).toVector.sorted,
                benefit = absorbed.size
              ))
            }
          }
        }
      }

    val chosen = {
      val used = mutable.HashSet.empty[Int]
      val builder = Vector.newBuilder[Candidate]
      rawCandidates.sortBy(candidate => (-candidate.benefit, candidate.rootNodeId)).foreach { candidate =>
        val claimed = candidate.absorbedNodeIds + candidate.rootNodeId
        if (candidate.benefit > 0 && claimed.intersect(used).isEmpty) {
          builder += candidate
          used ++= claimed
        }
      }
      builder.result().sortBy(_.rootNodeId)
    }

    val retained = retainedAbsorbedNodes(context, chosen)
    chosen.map { candidate =>
      SlpResidualMembershipRewrite(
        rootNodeId = candidate.rootNodeId,
        source = candidate.source,
        sourceWidth = candidate.sourceWidth,
        mask = candidate.mask,
        absorbedNodeIds = candidate.absorbedNodeIds -- retained,
        inputNodeIds = candidate.inputNodeIds,
        originalNodeIds = candidate.originalNodeIds
      )
    }.filter(_.absorbedNodeIds.nonEmpty)
  }
}
