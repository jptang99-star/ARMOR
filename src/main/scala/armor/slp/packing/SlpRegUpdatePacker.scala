package armor.slp

import essent.ir.RegUpdate
import firrtl.ir.{Connect, DefNode, Expression, IntWidth, Mux, Reference, SubField, SubIndex, UIntLiteral, UIntType}

import scala.collection.mutable

object SlpRegStorageNames {
  def state(regPackId: Int): String = s"_armor_slp_reg_$regPackId"
  def next(regPackId: Int): String = s"_armor_slp_reg_next_$regPackId"
  def view(regPackId: Int, laneIndex: Int): String =
    s"_armor_slp_reg_view_${regPackId}_$laneIndex"
}

final case class SlpRegLane(
  updateNodeId: Int,
  registerName: String,
  width:        Int,
  offset:       Int,
  location:     SlpModuleLocation
) {
  require(updateNodeId >= 0)
  require(registerName.nonEmpty)
  require(width > 0)
  require(offset >= 0)
}

/** One ordered state-commit point for a subset of a packed register's lanes.
  *
  * A RegUpdate is a state boundary, not an ordinary combinational operation:
  * preserving its original StatementGraph level is necessary when a later
  * statement observes a value written earlier in the same eval().  A pack may
  * therefore share storage while committing disjoint lane masks at several
  * original levels.
  */
final case class SlpRegCommitFragment(
  id:          Int,
  level:       Int,
  laneIndices: Vector[Int]
) {
  require(id >= 0)
  require(level >= 0)
  require(laneIndices.nonEmpty)
  require(laneIndices == laneIndices.distinct.sorted)
}

final case class SlpRegPack(
  id:        Int,
  lanes:     Vector[SlpRegLane],
  level:     Int,
  moduleNet: SlpModuleNet,
  discoveryPhase: String = "ict",
  commitFragments: Vector[SlpRegCommitFragment] = Vector.empty
) {
  require(id >= 0)
  require(lanes.size >= 2)
  require(lanes.map(_.updateNodeId).distinct.size == lanes.size)
  require(lanes.map(_.registerName).distinct.size == lanes.size)
  require(lanes.map(_.offset) == lanes.map(_.width).scanLeft(0)(_ + _).dropRight(1))
  require(level >= 0)
  require(commitFragments.nonEmpty)
  require(commitFragments.map(_.id) == commitFragments.indices.toVector)
  require(commitFragments.flatMap(_.laneIndices).sorted == lanes.indices.toVector)

  val totalWidth: Int = lanes.map(_.width).sum
  val validMask: BigInt = (BigInt(1) << totalWidth) - 1
  def nodeIds: Vector[Int] = lanes.map(_.updateNodeId)
  def registerNames: Vector[String] = lanes.map(_.registerName)
  def laneWidths: Vector[Int] = lanes.map(_.width)
  def laneOffsets: Vector[Int] = lanes.map(_.offset)
  def fragment(fragmentId: Int): SlpRegCommitFragment =
    commitFragments.find(_.id == fragmentId).getOrElse(
      throw new IllegalArgumentException(s"unknown commit fragment $fragmentId for register pack $id")
    )
  def fragmentMask(fragmentId: Int): BigInt = fragment(fragmentId).laneIndices.foldLeft(BigInt(0)) {
    case (mask, laneIndex) =>
      val lane = lanes(laneIndex)
      mask | (((BigInt(1) << lane.width) - 1) << lane.offset)
  }
}

/** A current-cycle combinational pack reads the previous-cycle value of a
  * packed register with exactly the same lane layout. This edge deliberately
  * does not participate in the acyclic current-cycle PackGraph.
  */
final case class SlpRegStateRead(
  regPackId:         Int,
  destinationPackId: Int,
  argumentIndex:     Int
) {
  require(regPackId >= 0)
  require(destinationPackId >= 0)
  require(argumentIndex >= 0)
}

/** A combinational pack supplies every next-register lane without an unpack
  * or lane permutation.
  */
final case class SlpRegDirectWrite(sourcePackId: Int, regPackId: Int) {
  require(sourcePackId >= 0)
  require(regPackId >= 0)
}

/** A read-driven register pack whose next state is a common reset-style Mux.
  *
  * The Mux nodes are intentionally kept outside the combinational PackGraph:
  * they are terminal next-state expressions.  Once their branch layout is
  * proved to match a packed producer, the emitter can write the packed state
  * directly without first materializing scalar next-state lanes.
  */
final case class SlpRegMuxWrite(
  regPackId:       Int,
  nextNodeIds:     Vector[Int],
  conditionName:   String,
  falseSourcePackId: Int,
  absorbNextNodes: Boolean = false
) {
  require(regPackId >= 0)
  require(nextNodeIds.distinct.size == nextNodeIds.size)
  require(conditionName.nonEmpty)
  require(falseSourcePackId >= 0)
}

final case class SlpRegPackStats(
  candidates:        Int,
  seedGroups:        Int,
  acceptedPacks:     Int,
  packedRegisters:   Int,
  directStateReads:  Int,
  directStateWrites: Int,
  rejectedSingleton: Int,
  rejectedWidth:     Int,
  rejectedDependency: Int
) {
  require(candidates >= 0)
  require(seedGroups >= 0)
  require(acceptedPacks >= 0)
  require(packedRegisters >= 0)
  require(directStateReads >= 0)
  require(directStateWrites >= 0)
  require(rejectedSingleton >= 0)
  require(rejectedWidth >= 0)
  require(rejectedDependency >= 0)
}

final case class SlpRegPackingResult(
  packs:        Vector[SlpRegPack],
  stateReads:   Vector[SlpRegStateRead],
  directWrites: Vector[SlpRegDirectWrite],
  stats:        SlpRegPackStats,
  muxWrites:    Vector[SlpRegMuxWrite] = Vector.empty
) {
  require(packs.map(_.id) == packs.indices.toVector)
  require(stateReads == stateReads.distinct.sortBy(read =>
    (read.regPackId, read.destinationPackId, read.argumentIndex)
  ))
  require(directWrites == directWrites.distinct.sortBy(write =>
    (write.regPackId, write.sourcePackId)
  ))
  require(muxWrites == muxWrites.distinct.sortBy(write =>
    (write.regPackId, write.falseSourcePackId, write.conditionName)
  ))
}

private final case class RegCandidate(
  nodeId:       Int,
  registerName: String,
  width:        Int,
  level:        Int,
  location:     SlpModuleLocation,
  moduleNet:    SlpModuleNet,
  update:       RegUpdate
)

private final case class RegSeedKey(
  level:     Int,
  moduleNet: SlpModuleNet,
  width:     Int
) {
  def sortKey: (Int, String, String, Int) =
    (level, moduleNet.moduleName, moduleNet.localNetName, width)
}

private final case class ReadDrivenRegCandidate(
  destinationPackId: Int,
  argumentIndex:     Int,
  lanes:             Vector[RegCandidate],
  nextNodeIds:       Vector[Int],
  conditionName:     Option[String],
  sourcePackId:      Int,
  absorbNextNodes:   Boolean
) {
  require(lanes.nonEmpty)
  require(nextNodeIds.distinct.size == nextNodeIds.size)
}

/** A state layout selected from a retained combinational read.  Unlike
  * ReadDrivenRegCandidate, this form deliberately makes no claim about the
  * shape of the next-state logic: its write is materialized from the original
  * scalar RegUpdate expressions at their original commit point. */
private final case class ReadDrivenScalarStorageCandidate(
  destinationPackId: Int,
  argumentIndex:     Int,
  lanes:             Vector[RegCandidate]
) {
  require(destinationPackId >= 0)
  require(argumentIndex >= 0)
  require(lanes.nonEmpty)
}

/** One proposed packed register layout, independent of how it was discovered.
  *
  * Discovery remains source-specific because each source proves a different
  * property.  Selection is intentionally centralized: every candidate competes
  * for the same resources (RegUpdate nodes and destination registers), so
  * duplicate/conflicting layouts must be arbitrated in one place.
  */
private final case class RegLayoutCandidate(
  lanes:         Vector[RegCandidate],
  discoveryPhase: String,
  priority:      Int,
  readDriven:    Option[ReadDrivenRegCandidate] = None,
  scalarStorage: Option[ReadDrivenScalarStorageCandidate] = None
) {
  require(lanes.nonEmpty)
  require(discoveryPhase.nonEmpty)
  require(priority >= 0)
  require(readDriven.isEmpty || readDriven.exists(_.lanes == lanes))
  require(scalarStorage.isEmpty || scalarStorage.exists(_.lanes == lanes))

  val updateNodeIds: Vector[Int] = lanes.map(_.nodeId)
  val registerNames: Vector[String] = lanes.map(_.registerName)
  val totalWidth: Int = lanes.map(_.width).sum
  val exactKey: Vector[(Int, String, Int)] =
    lanes.map(lane => (lane.nodeId, lane.registerName, lane.width))
}

/** Register pack materialization for layouts discovered by ICTPacker.
  *
  * ICT discovery follows combinational def-use correspondence into RegUpdate,
  * then records RegUpdate as a terminal state-boundary layout. RegUpdate still
  * does not enter the current-cycle PackGraph: previous-state reads and the
  * end-of-cycle commit remain explicit state edges below.
  */
final class SlpRegUpdatePacker(
  context:       SlpAnalysisContext,
  combinational: SlpPackingResult
) {
  private val view = context.graph
  private val levels = view.levels.toOption.getOrElse(
    throw new IllegalArgumentException("SlpRegUpdatePacker requires an acyclic graph")
  )

  private def referenceName(expression: Expression): Option[String] = expression match {
    case Reference(name, _, _, _)       => Some(name)
    case SubField(base, name, _, _)     => referenceName(base).map(prefix => s"$prefix.$name")
    case SubIndex(base, index, _, _)    => referenceName(base).map(prefix => s"${prefix}_$index")
    case _                              => None
  }

  private def uintWidth(expression: Expression): Option[Int] = expression.tpe match {
    case UIntType(IntWidth(width)) if width > 0 && width.isValidInt => Some(width.toInt)
    case _                                                         => None
  }

  private def localName(name: String): String = name.split("\\.").last

  private val rejectedWideUpdates: Int = view.validNodeIds.count { nodeId =>
    view.node(nodeId).statement match {
      case update: RegUpdate => uintWidth(update.regRef).exists(_ > context.config.machineWidth)
      case _                 => false
    }
  }

  private val candidates: Vector[RegCandidate] = view.validNodeIds.flatMap { nodeId =>
    view.node(nodeId).statement match {
      case update: RegUpdate =>
        for {
          registerName <- referenceName(update.regRef)
          width <- uintWidth(update.regRef)
          location <- view.node(nodeId).module
          level <- levels.levelOf(nodeId)
          if width <= context.config.machineWidth
        } yield RegCandidate(
          nodeId,
          registerName,
          width,
          level,
          location,
          SlpModuleNet(location.moduleName, localName(registerName)),
          update
        )
      case _ => None
    }
  }

  private def splitByMachineWidth(group: Vector[RegCandidate]): Vector[Vector[RegCandidate]] = {
    val result = Vector.newBuilder[Vector[RegCandidate]]
    var current = Vector.empty[RegCandidate]
    var currentWidth = 0
    def flush(): Unit = {
      if (current.nonEmpty) result += current
      current = Vector.empty
      currentWidth = 0
    }
    group.foreach { candidate =>
      if (current.nonEmpty && currentWidth + candidate.width > context.config.machineWidth) flush()
      current :+= candidate
      currentWidth += candidate.width
    }
    flush()
    result.result()
  }

  private def hasInternalDependency(group: Vector[RegCandidate]): Boolean = {
    val members = group.map(_.nodeId).toSet
    group.exists(candidate => view.fanoutIds(candidate.nodeId).exists(members))
  }

  private def seedKey(candidate: RegCandidate): RegSeedKey =
    RegSeedKey(candidate.level, candidate.moduleNet, candidate.width)

  private val candidateByNodeId: Map[Int, RegCandidate] =
    candidates.map(candidate => candidate.nodeId -> candidate).toMap

  /** A register may have at most one update before it can become canonical
    * packed state.  Ambiguous updates remain scalar. */
  private val candidateByRegisterName: Map[String, RegCandidate] = candidates
    .groupBy(_.registerName)
    .collect { case (name, Vector(candidate)) => name -> candidate }

  private val classifiedOperations = context.classifications.collect {
    case (nodeId, SlpSupported(operation)) => nodeId -> operation
  }.toMap
  private val operations = classifiedOperations ++ combinational.operationOverrides

  private val combinationalPackByNode: Map[Int, SlpPack] =
    combinational.packs.flatMap(pack => pack.nodeIds.map(_ -> pack)).toMap

  /** Resolve state-boundary layouts in the exact order established by ICT.
    * No second discovery or regrouping is allowed here: doing so would change
    * the pack boundaries selected by ICTPacker.
    */
  private val ictDiscoveredLayouts: Vector[(Vector[RegCandidate], String)] =
    combinational.regUpdateLayouts.flatMap { layout =>
      val resolved = layout.updateNodeIds.map(candidateByNodeId.get)
      if (resolved.forall(_.nonEmpty)) {
        val group = resolved.flatten
        val valid =
          group.size >= context.config.minParallelDegree &&
          group.map(_.nodeId).distinct.size == group.size &&
          group.map(_.registerName).distinct.size == group.size &&
          group.map(_.width).sum <= context.config.machineWidth &&
          !hasInternalDependency(group)
        if (valid) Some(group -> layout.discoveryPhase) else None
      } else None
    }

  /** Bridge a retained combinational `$next` pack directly into a packed
    * RegUpdate layout.
    *
    * This is intentionally narrower than the read-driven storage discovery
    * below: it does not infer a register family from state reads and it does
    * not inspect Mux structure.  It only accepts the exact dataflow shape
    *
    *   retained pack lane output  ->  RegUpdate.expr
    *
    * for every lane of the retained pack.  Because the source pack already
    * fixes lane order, width, and offsets, cross-module local-instance packs
    * can safely become packed state commits without requiring all registers to
    * live in one concrete module location.
    */
  private def discoverPackedOutputDirectLayouts(): Vector[(Vector[RegCandidate], String)] = {
    val updatesBySourceNodeId: Map[Int, Vector[RegCandidate]] = candidates.flatMap { candidate =>
      Option.when(candidateByRegisterName.get(candidate.registerName).exists(_.nodeId == candidate.nodeId)) {
        referenceName(candidate.update.expr)
          .flatMap(view.graph.nameToID.get)
          .map(sourceNodeId => sourceNodeId -> candidate)
      }.flatten
    }.groupBy(_._1).view.mapValues(values => values.map(_._2).toVector).toMap

    combinational.packs.flatMap { sourcePack =>
      val laneUpdates = sourcePack.lanes.zip(sourcePack.nodeIds).map {
        case (lane, sourceNodeId) =>
          updatesBySourceNodeId.getOrElse(sourceNodeId, Vector.empty)
            .filter(_.width == lane.resultWidth)
      }
      val targetLocalNames = laneUpdates.flatten.map(candidate =>
        localName(candidate.registerName)
      ).distinct.sorted

      targetLocalNames.flatMap { targetLocalName =>
        val matched = laneUpdates.map(updates =>
          updates.filter(candidate => localName(candidate.registerName) == targetLocalName)
        )
        if (matched.forall(_.size == 1)) {
          val lanes = matched.map(_.head)
          val valid =
            lanes.size >= context.config.minParallelDegree &&
              lanes.map(_.nodeId).distinct.size == lanes.size &&
              lanes.map(_.registerName).distinct.size == lanes.size &&
              lanes.map(_.width) == sourcePack.lanes.map(_.resultWidth) &&
              lanes.map(_.width).sum <= context.config.machineWidth &&
              !hasInternalDependency(lanes)
          Option.when(valid)(lanes -> "packed_next_direct_update")
        } else None
      }
    }.distinct.sortBy { case (lanes, phase) =>
      (-lanes.size, -lanes.map(_.width).sum, phase, lanes.map(_.nodeId).mkString(":"))
    }
  }

  private val packedOutputDirectLayouts: Vector[(Vector[RegCandidate], String)] =
    discoverPackedOutputDirectLayouts()

  private val discoveredLayouts: Vector[(Vector[RegCandidate], String)] =
    ictDiscoveredLayouts ++ packedOutputDirectLayouts

  /** Discover a state layout from an already-retained combinational pack
    * operand, then prove the terminal reset Mux writes the same lane layout.
    * This deliberately does not consult AlignPlanner: state discovery must
    * precede alignment planning. */
  private def discoverReadDrivenCandidates(): Vector[ReadDrivenRegCandidate] = {
    val debugReadDriven: Option[String] =
      Option(System.getProperty("armor.slp.debugReadDriven")).filter(_.nonEmpty)

    def debug(message: => String): Unit =
      debugReadDriven.foreach { needle =>
        if (message.contains(needle)) Console.err.println(s"[slp-read-driven] $message")
      }
    final case class TerminalMux(
      nextNodeId:   Option[Int],
      condition:    String,
      falseSignal:  SlpSignal
    )

    def inlineMux(expression: Expression): Option[TerminalMux] = expression match {
      case Mux(condition, UIntLiteral(value, _), falseValue, _) if value == 0 =>
        for {
          conditionName <- referenceName(condition)
          falseName <- referenceName(falseValue)
          falseWidth <- uintWidth(falseValue)
        } yield TerminalMux(None, conditionName, SlpSignal(falseName, falseWidth))
      case _ => None
    }

    def namedMux(expression: Expression): Option[TerminalMux] = for {
      nextName <- referenceName(expression)
      nextNodeId <- view.graph.nameToID.get(nextName)
      resolved <- {
        val classified = for {
          mux <- operations.get(nextNodeId).filter(_.opcode == SlpMux)
          condition <- mux.operands.headOption.collect { case SlpSignal(name, 1) => name }
          _ <- mux.operands.lift(1).collect { case SlpUIntConstant(value, _) if value == 0 => () }
          falseSignal <- mux.operands.lift(2).collect { case signal: SlpSignal => signal }
        } yield TerminalMux(Some(nextNodeId), condition, falseSignal)

        // SplitRegUpdates introduces `$next` DefNodes for register commits.
        // Those nodes are intentionally not normal combinational SLP nodes,
        // so they may not occur in `operations`.  They still have an ordinary
        // FIRRTL Mux RHS; inspect it directly instead of treating the `$next`
        // name as a scalar boundary.
        val unclassified = view.node(nextNodeId).statement match {
          case DefNode(_, _, value) => inlineMux(value).map(_.copy(nextNodeId = Some(nextNodeId)))
          case Connect(_, _, value) => inlineMux(value).map(_.copy(nextNodeId = Some(nextNodeId)))
          case _                    => None
        }
        classified.orElse(unclassified)
      }
    } yield resolved

    def terminalMux(expression: Expression): Option[TerminalMux] =
      inlineMux(expression).orElse(namedMux(expression))

    def exactSourcePackNames(sourceNames: Vector[String], lanes: Vector[RegCandidate]): Option[Int] = {
      val sourceNodeIds = sourceNames.flatMap(view.graph.nameToID.get)
      val sourcePacks = sourceNodeIds.flatMap(combinationalPackByNode.get).distinct
      if (sourceNames.size == lanes.size &&
          sourceNodeIds.size == sourceNames.size &&
          sourcePacks.size == 1) {
        val sourcePack = sourcePacks.head
        val exactLayout = sourceNodeIds == sourcePack.nodeIds &&
          sourcePack.lanes.map(_.resultWidth) == lanes.map(_.width) &&
          sourcePack.outputOffsets == lanes.map(_.width).scanLeft(0)(_ + _).dropRight(1)
        Option.when(exactLayout)(sourcePack.id)
      } else None
    }

    def exactSourcePack(expressions: Vector[Expression], lanes: Vector[RegCandidate]): Option[Int] =
      exactSourcePackNames(expressions.flatMap(referenceName), lanes)

    def directClosure(
      destinationPackId: Int,
      argumentIndex:     Int,
      lanes:             Vector[RegCandidate]
    ): Option[ReadDrivenRegCandidate] =
      exactSourcePack(lanes.map(_.update.expr), lanes).map { sourcePackId =>
        ReadDrivenRegCandidate(destinationPackId, argumentIndex, lanes, Vector.empty,
          None, sourcePackId, absorbNextNodes = false)
      }

    def muxClosure(
      destinationPackId: Int,
      argumentIndex:     Int,
      lanes:             Vector[RegCandidate]
    ): Option[ReadDrivenRegCandidate] = {
      val matched = lanes.map { lane =>
        for {
          mux <- terminalMux(lane.update.expr)
          if mux.falseSignal.width == lane.width
        } yield mux
      }
      if (matched.exists(_.isEmpty)) None
      else {
        val resolved = matched.flatten
        val conditionNames = resolved.map(_.condition).distinct
        val namedNextNodes = resolved.flatMap(_.nextNodeId)
        val nextNodes = if (namedNextNodes.size == resolved.size) namedNextNodes else Vector.empty
        val exclusiveNextNodes = nextNodes.nonEmpty && nextNodes.zip(lanes).forall { case (nextNodeId, lane) =>
          view.validFanoutIds(nextNodeId).toSet == Set(lane.nodeId)
        }
        exactSourcePackNames(resolved.map(_.falseSignal.name), lanes).flatMap { sourcePackId =>
          if (conditionNames.size == 1) Some(ReadDrivenRegCandidate(
            destinationPackId,
            argumentIndex,
            lanes,
            nextNodes,
            Some(conditionNames.head),
            sourcePackId,
            exclusiveNextNodes
          )) else None
        }
      }
    }

    val result = Vector.newBuilder[ReadDrivenRegCandidate]
    combinational.packs.sortBy(_.id).foreach { destinationPack =>
      val laneOperations = destinationPack.nodeIds.map(operations)
      laneOperations.head.operands.indices.foreach { argumentIndex =>
        val operands = laneOperations.map(_.operands(argumentIndex))
        val signals = operands.collect { case signal: SlpSignal => signal }
        val lanes = signals.flatMap(signal => candidateByRegisterName.get(signal.name))
        val sameLocation = lanes.headOption.forall(first => lanes.forall(_.location == first.location))
        val valid = signals.size == operands.size &&
          lanes.size == signals.size &&
          lanes.size >= context.config.minParallelDegree &&
          lanes.map(_.registerName).distinct.size == lanes.size &&
          lanes.map(_.width) == signals.map(_.width) &&
          lanes.map(_.width).sum <= context.config.machineWidth &&
          sameLocation
        if (debugReadDriven.nonEmpty && signals.exists(signal => signal.name.contains(debugReadDriven.get))) {
          val rhs = lanes.map { lane =>
            val expression = lane.update.expr
            val name = referenceName(expression)
            val nodeId = name.flatMap(view.graph.nameToID.get)
            val packId = nodeId.flatMap(combinationalPackByNode.get).map(_.id)
            val opcode = nodeId.flatMap(operations.get).map(_.opcode.name)
            s"${lane.registerName}<-${expression.serialize}[name=${name.getOrElse("<none>")},node=${nodeId.getOrElse(-1)},pack=${packId.getOrElse(-1)},op=${opcode.getOrElse("<none>")}]"
          }.mkString(";")
          debug(
            s"destination=${destinationPack.id} argument=$argumentIndex " +
              s"signals=${signals.map(_.name).mkString(";")} " +
              s"lanes=${lanes.map(_.registerName).mkString(";")} valid=$valid " +
              s"rhs=$rhs " +
              s"direct=${if (valid) directClosure(destinationPack.id, argumentIndex, lanes).map(_.sourcePackId) else None} " +
              s"mux=${if (valid) muxClosure(destinationPack.id, argumentIndex, lanes).map(_.sourcePackId) else None}"
          )
        }
        if (valid) directClosure(destinationPack.id, argumentIndex, lanes)
          .orElse(muxClosure(destinationPack.id, argumentIndex, lanes))
          .foreach(result += _)
      }
    }
    result.result().sortBy(candidate =>
      (-candidate.lanes.size, -candidate.lanes.map(_.width).sum,
        candidate.destinationPackId, candidate.argumentIndex)
    )
  }

  private val readDrivenCandidates: Vector[ReadDrivenRegCandidate] =
    discoverReadDrivenCandidates()

  /** Discover storage from a complete register operand after write-driven
    * layouts have had first claim on the registers.  The candidate is kept
    * intentionally conservative: all lanes commit at one original graph
    * level, so replacing their scalar writes with one packed write cannot
    * change same-cycle observation order. */
  private def discoverReadDrivenScalarStorageCandidates(): Vector[ReadDrivenScalarStorageCandidate] = {
    def supportsScalarWrite(candidate: RegCandidate): Boolean = candidate.update.expr match {
      case UIntLiteral(_, _) => true
      case expression        => referenceName(expression).nonEmpty
    }

    combinational.packs.flatMap { destinationPack =>
      val laneOperations = destinationPack.nodeIds.map(operations)
      laneOperations.head.operands.indices.flatMap { argumentIndex =>
        val operands = laneOperations.map(_.operands(argumentIndex))
        val signals = operands.collect { case signal: SlpSignal => signal }
        val lanes = signals.flatMap(signal => candidateByRegisterName.get(signal.name))
        val sameLocation = lanes.headOption.forall(first => lanes.forall(_.location == first.location))
        val oneCommit = lanes.headOption.forall(first => lanes.forall(_.level == first.level))
        val valid = signals.size == operands.size &&
          lanes.size == signals.size &&
          lanes.size >= context.config.minParallelDegree &&
          lanes.map(_.registerName).distinct.size == lanes.size &&
          lanes.map(_.width) == signals.map(_.width) &&
          lanes.map(_.width).sum <= context.config.machineWidth &&
          sameLocation && oneCommit && lanes.forall(supportsScalarWrite)
        Option.when(valid)(ReadDrivenScalarStorageCandidate(
          destinationPack.id,
          argumentIndex,
          lanes
        ))
      }
    }.sortBy(candidate =>
      (-candidate.lanes.size, -candidate.lanes.map(_.width).sum,
        candidate.destinationPackId, candidate.argumentIndex)
    )
  }

  private val readDrivenScalarStorageCandidates: Vector[ReadDrivenScalarStorageCandidate] =
    discoverReadDrivenScalarStorageCandidates()

  private def hasExactPackedWrite(lanes: Vector[RegCandidate]): Boolean = {
    val sourceNames = lanes.flatMap(lane => referenceName(lane.update.expr))
    val sourceNodeIds = sourceNames.flatMap(view.graph.nameToID.get)
    val sourcePacks = sourceNodeIds.flatMap(combinationalPackByNode.get).distinct
    sourceNames.size == lanes.size &&
      sourceNodeIds.size == sourceNames.size &&
      sourcePacks.size == 1 && {
        val sourcePack = sourcePacks.head
        sourceNodeIds == sourcePack.nodeIds &&
          sourcePack.lanes.map(_.resultWidth) == lanes.map(_.width) &&
          sourcePack.outputOffsets == lanes.map(_.width).scanLeft(0)(_ + _).dropRight(1)
      }
  }

  private def layoutCandidateSortKey(candidate: RegLayoutCandidate, ordinal: Int):
      (Int, Int, Int, Int, Int, String, String) = (
    -candidate.priority,
    -candidate.lanes.size,
    -candidate.totalWidth,
    candidate.lanes.headOption.map(_.level).getOrElse(Int.MaxValue),
    ordinal,
    candidate.discoveryPhase,
    candidate.updateNodeIds.mkString(":")
  )

  private def selectRegLayoutCandidates(raw: Vector[RegLayoutCandidate]): Vector[RegLayoutCandidate] = {
    val usedUpdateNodeIds = mutable.HashSet.empty[Int]
    val usedRegisterNames = mutable.HashSet.empty[String]
    val seenExactKeys = mutable.HashSet.empty[Vector[(Int, String, Int)]]

    raw.zipWithIndex.sortBy { case (candidate, ordinal) =>
      layoutCandidateSortKey(candidate, ordinal)
    }.flatMap { case (candidate, _) =>
      val exactDuplicate = seenExactKeys(candidate.exactKey)
      val updateOverlap = candidate.updateNodeIds.exists(usedUpdateNodeIds)
      val registerOverlap = candidate.registerNames.exists(usedRegisterNames)
      if (exactDuplicate || updateOverlap || registerOverlap) None
      else {
        seenExactKeys += candidate.exactKey
        usedUpdateNodeIds ++= candidate.updateNodeIds
        usedRegisterNames ++= candidate.registerNames
        Some(candidate)
      }
    }
  }

  private val rawLayoutCandidates: Vector[RegLayoutCandidate] = {
    val discovered = discoveredLayouts.map { case (lanes, phase) =>
      // Existing ICT state layouts with an exact packed producer are already
      // the preferred closed form.  Non-closed discovered layouts are still
      // useful, but they yield to read-driven closures that prove a packed
      // previous-state/new-state relationship.
      val priority = if (hasExactPackedWrite(lanes)) 400 else 100
      RegLayoutCandidate(lanes, phase, priority)
    }
    val readDriven = readDrivenCandidates.map { candidate =>
      RegLayoutCandidate(
        candidate.lanes,
        candidate.conditionName.fold("read_driven_direct_closure")(_ => "read_driven_mux_closure"),
        300,
        readDriven = Some(candidate)
      )
    }
    val scalarStorage = readDrivenScalarStorageCandidates.map { candidate =>
      RegLayoutCandidate(
        candidate.lanes,
        "read_driven_scalar_write",
        200,
        scalarStorage = Some(candidate)
      )
    }
    discovered ++ readDriven ++ scalarStorage
  }

  private val selectedLayoutCandidates: Vector[RegLayoutCandidate] =
    selectRegLayoutCandidates(rawLayoutCandidates)

  private val acceptedReadDrivenCandidates: Vector[ReadDrivenRegCandidate] =
    selectedLayoutCandidates.flatMap(_.readDriven)

  private val acceptedReadDrivenScalarStorageCandidates: Vector[ReadDrivenScalarStorageCandidate] =
    selectedLayoutCandidates.flatMap(_.scalarStorage)

  private val allDiscoveredLayouts: Vector[(Vector[RegCandidate], String)] =
    selectedLayoutCandidates.map(candidate => candidate.lanes -> candidate.discoveryPhase)

  private val readDrivenByUpdateNodeIds: Map[Vector[Int], ReadDrivenRegCandidate] =
    acceptedReadDrivenCandidates.map(candidate =>
      candidate.lanes.map(_.nodeId) -> candidate
    ).toMap

  private def discoverPacks(): (Vector[SlpRegPack], Int, Int, Int, Int) = {
    val seedGroups = allDiscoveredLayouts.size
    var rejectedSingleton = 0
    var rejectedDependency = 0
    var nextPackId = 0
    val packs = Vector.newBuilder[SlpRegPack]
    val packedNodeIds = allDiscoveredLayouts.flatMap(_._1).map(_.nodeId).toSet

    allDiscoveredLayouts.foreach { case (part, discoveryPhase) =>
      val widths = part.map(_.width)
      val offsets = widths.scanLeft(0)(_ + _).dropRight(1)
      val fragments = part.zipWithIndex.groupBy(_._1.level).toVector.sortBy(_._1).zipWithIndex.map {
        case ((level, lanesAtLevel), fragmentId) =>
          SlpRegCommitFragment(fragmentId, level, lanesAtLevel.map(_._2).sorted)
      }
      packs += SlpRegPack(
        nextPackId,
        part.zip(offsets).map { case (candidate, offset) =>
          SlpRegLane(
            candidate.nodeId,
            candidate.registerName,
            candidate.width,
            offset,
            candidate.location
          )
        },
        part.head.level,
        part.head.moduleNet,
        discoveryPhase,
        fragments
      )
      nextPackId += 1
    }

    // Keep rejection accounting for undiscovered state nodes, but never turn
    // them into packs here. ICTPacker is the sole owner of pack discovery.
    candidates.filterNot(candidate => packedNodeIds(candidate.nodeId))
      .groupBy(seedKey).values.foreach { rawCandidates =>
        val ordered = rawCandidates.sortBy(candidate =>
          (candidate.location.instancePath, candidate.registerName, candidate.nodeId)
        ).toVector
        splitByMachineWidth(ordered).foreach { part =>
          if (part.size < context.config.minParallelDegree) rejectedSingleton += 1
          else if (hasInternalDependency(part)) rejectedDependency += 1
        }
      }
    val result = packs.result().zipWithIndex.map { case (pack, id) => pack.copy(id = id) }
    (result, seedGroups, rejectedSingleton, rejectedWideUpdates, rejectedDependency)
  }

  private def exactStateReads(regPacks: Vector[SlpRegPack]): Vector[SlpRegStateRead] = {
    regPacks.flatMap { regPack =>
      combinational.packs.flatMap { destinationPack =>
        val laneOperations = destinationPack.nodeIds.map(operations)
        laneOperations.head.operands.indices.flatMap { argumentIndex =>
          val operands = laneOperations.map(_.operands(argumentIndex))
          val names = operands.collect { case signal: SlpSignal => signal.name }
          val widths = operands.map(_.width)
          val offsets = widths.scanLeft(0)(_ + _).dropRight(1)
          if (names.size == operands.size &&
              names == regPack.registerNames &&
              widths == regPack.laneWidths &&
              offsets == regPack.laneOffsets) {
            Some(SlpRegStateRead(regPack.id, destinationPack.id, argumentIndex))
          } else None
        }
      }
    }.distinct.sortBy(read => (read.regPackId, read.destinationPackId, read.argumentIndex))
  }

  private def exactDirectWrites(regPacks: Vector[SlpRegPack]): Vector[SlpRegDirectWrite] = {
    regPacks.flatMap { regPack =>
      val expressions = regPack.nodeIds.map(nodeId =>
        view.node(nodeId).statement.asInstanceOf[RegUpdate].expr
      )
      val sourceNames = expressions.flatMap(referenceName)
      if (sourceNames.size != expressions.size) None
      else {
        val sourceNodes = sourceNames.flatMap(view.graph.nameToID.get)
        val sourcePacks = sourceNodes.flatMap(combinationalPackByNode.get).distinct
        if (sourceNodes.size == sourceNames.size && sourcePacks.size == 1) {
          val sourcePack = sourcePacks.head
          val exactLayout =
            sourceNames == sourcePack.nodeIds.map(nodeId => view.node(nodeId).name) &&
            sourceNodes == sourcePack.nodeIds &&
            sourcePack.lanes.map(_.resultWidth) == regPack.laneWidths &&
            sourcePack.outputOffsets == regPack.laneOffsets
          if (exactLayout) Some(SlpRegDirectWrite(sourcePack.id, regPack.id)) else None
        } else None
      }
    }.distinct.sortBy(write => (write.regPackId, write.sourcePackId))
  }

  private def muxWrites(regPacks: Vector[SlpRegPack]): Vector[SlpRegMuxWrite] =
    regPacks.flatMap { pack =>
      readDrivenByUpdateNodeIds.get(pack.nodeIds).flatMap { candidate => candidate.conditionName.map { conditionName =>
        SlpRegMuxWrite(
          pack.id,
          candidate.nextNodeIds,
          conditionName,
          candidate.sourcePackId,
          candidate.absorbNextNodes
        )
      }}
    }.sortBy(write => (write.regPackId, write.falseSourcePackId, write.conditionName))

  def run(): SlpRegPackingResult = {
    val (discoveredPacks, seedGroups, rejectedSingleton, rejectedWidth, rejectedDependency) = discoverPacks()
    // A cross-level group can only be materialized when one already-packed
    // combinational producer supplies all of its next-state lanes.  Otherwise
    // reconstructing several partial next values would add work and is harder
    // to reason about than the original scalar updates.
    val initialClosedWrites =
      exactDirectWrites(discoveredPacks).map(_.regPackId).toSet ++
        muxWrites(discoveredPacks).map(_.regPackId)
    val packs = discoveredPacks.filter { pack =>
      pack.commitFragments.size == 1 || initialClosedWrites(pack.id)
    }.zipWithIndex.map { case (pack, denseId) => pack.copy(id = denseId) }
    val reads = exactStateReads(packs)
    val writes = exactDirectWrites(packs)
    val mux = muxWrites(packs)
    SlpRegPackingResult(
      packs,
      reads,
      writes,
      SlpRegPackStats(
        candidates.size,
        seedGroups,
        packs.size,
        packs.map(_.lanes.size).sum,
        reads.size,
        writes.size,
        rejectedSingleton,
        rejectedWidth,
        rejectedDependency
      ),
      mux
    )
  }
}
