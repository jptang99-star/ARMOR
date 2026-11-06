package armor.slp

import armor.{ArmorIndexedMux, CppBitUtils}
import essent.Emitter.{emitExpr, emitExprWrap, emitStmt, emitStmtWithRhs, genCppType}
import essent.Renamer
import essent.ir.{MemWrite, RegUpdate}
import firrtl._
import firrtl.ir._
import firrtl.Utils._

import scala.collection.mutable

final case class SlpEmissionStats(
  scalarNodes:       Int,
  packNodes:         Int,
  fastBitwisePacks:  Int,
  laneWisePacks:     Int,
  scalarToPackNodes: Int,
  packToScalarNodes: Int,
  packSegmentNodes:  Int,
  regUpdatePacks:    Int,
  scalarRegViews:    Int,
  broadcastMuxPacks: Int,
  oneBitMuxPacks:    Int,
  laneMaskMuxPacks:  Int,
  elidedMuxResultMasks: Int
) {
  require(packNodes == fastBitwisePacks + laneWisePacks)
  require(regUpdatePacks >= 0)
  require(scalarRegViews >= 0)
  require(broadcastMuxPacks >= 0)
  require(oneBitMuxPacks >= 0)
  require(laneMaskMuxPacks >= 0)
  require(elidedMuxResultMasks >= 0)
}

private final case class SlpEqPackedSource(
  sourceName:        String,
  sourceOffsets:     Vector[Int],
  bypassAlignmentId: Int,
  segmentIds:        Set[Int]
)

private final case class SlpSparseGatherTerm(
  source:            SlpSegmentSource,
  sourceMask:        BigInt,
  destinationOffset: Int,
  width:             Int
)

private final case class SlpSparseGatherSignature(
  terms:      Vector[SlpSparseGatherTerm],
  totalWidth: Int
)

private final case class SlpSparseGather(
  alignmentId: Int,
  signature:   SlpSparseGatherSignature,
  segmentIds:  Set[Int]
)

private sealed trait SlpAlignmentLaneSignature {
  def width: Int
}
private final case class SlpScalarSignalSignature(
  signalName:     String,
  width:          Int,
  producerNodeId: Option[Int]
) extends SlpAlignmentLaneSignature
private final case class SlpScalarConstantSignature(
  value: BigInt,
  width: Int
) extends SlpAlignmentLaneSignature
private final case class SlpUnpackedLaneSignature(
  signalName:         String,
  width:              Int,
  sourcePackId:       Int,
  sourceLaneIndex:    Int,
  sourceNodeId:       Int,
  segmentAlignmentId: Option[Int]
) extends SlpAlignmentLaneSignature
private final case class SlpPackedRegLaneSignature(
  registerName:       String,
  width:              Int,
  regPackId:          Int,
  sourceLaneIndex:    Int,
  segmentAlignmentId: Option[Int]
) extends SlpAlignmentLaneSignature
private final case class SlpMaterializedAlignmentSignature(
  lanes:       Vector[SlpAlignmentLaneSignature],
  laneOffsets: Vector[Int]
) {
  require(lanes.nonEmpty)
  require(lanes.size == laneOffsets.size)
}

private final case class SlpAlignmentSegmentReuse(
  sourceAlignmentId:      Int,
  destinationAlignmentId: Int,
  destinationLaneBegin:   Int,
  destinationLaneEnd:     Int,
  sourceBitOffset:        Int,
  destinationBitOffset:   Int,
  width:                  Int,
  sourceScheduleIndex:    Int
) {
  require(sourceAlignmentId >= 0)
  require(destinationAlignmentId >= 0)
  require(destinationLaneBegin >= 0)
  require(destinationLaneEnd > destinationLaneBegin)
  require(sourceBitOffset >= 0)
  require(destinationBitOffset >= 0)
  require(sourceBitOffset + width <= 64)
  require(width > 0 && destinationBitOffset + width <= 64)
  require(sourceScheduleIndex >= 0)

  val coveredLanes: Int = destinationLaneEnd - destinationLaneBegin
  val benefit: Int = coveredLanes - 1
}

private final case class SlpAlignmentSegmentSelection(
  benefit:     Int,
  coveredBits: Int,
  segments:    Vector[SlpAlignmentSegmentReuse]
)

private final case class SlpAlignmentSegmentKey(
  lanes:   Vector[SlpAlignmentLaneSignature],
  offsets: Vector[Int]
) {
  require(lanes.nonEmpty)
  require(lanes.size == offsets.size)
}

private final case class SlpMaterializedAlignmentEntry(
  alignmentId:   Int,
  signature:     SlpMaterializedAlignmentSignature,
  scheduleIndex: Int,
  epoch:         Int,
  laneCount:     Int,
  width:         Int
) {
  require(alignmentId >= 0)
  require(scheduleIndex >= 0)
  require(laneCount == signature.lanes.size)
  require(width > 0 && width <= 64)
}

private final case class SlpMaterializedAlignmentSegmentEntry(
  source:          SlpMaterializedAlignmentEntry,
  sourceLaneBegin: Int,
  sourceLaneEnd:   Int,
  sourceBitOffset: Int,
  width:           Int
) {
  require(sourceLaneBegin >= 0)
  require(sourceLaneEnd > sourceLaneBegin)
  require(sourceLaneEnd <= source.laneCount)
  require(sourceBitOffset >= 0)
  require(width > 0 && sourceBitOffset + width <= source.width)
}

private final case class SlpPackWordWrite(
  valueExpr: String,
  width:     Int,
  offset:    Int
) {
  require(valueExpr.nonEmpty)
  require(width > 0 && width <= 64, s"invalid pack write width $width")
  require(offset >= 0 && offset + width <= 64,
    s"invalid pack write range offset=$offset width=$width")
}

private final case class SlpPackWordConstruction(
  terms:  Vector[String],
  writes: Vector[SlpPackWordWrite]
)

/** A scalar side-effect condition which can be read directly from a packed
  * result.  The corresponding pack-to-scalar lane is deliberately not
  * materialized as an `unpack_bits` view.
  */
private final case class SlpPackedSideEffectMember(
  nodeId:        Int,
  sourceNodeId:  Int,
  sourcePackId:  Int,
  sourceOffset:  Int,
  statement:     Statement
)

private sealed trait SlpPackedSideEffectGroup {
  def members: Vector[SlpPackedSideEffectMember]
  final def sourcePackId: Int = members.head.sourcePackId
  final def activeMask: BigInt = members.foldLeft(BigInt(0)) { (mask, member) =>
    mask | (BigInt(1) << member.sourceOffset)
  }
}
private final case class SlpPackedPrintGroup(
  members: Vector[SlpPackedSideEffectMember]
) extends SlpPackedSideEffectGroup
private final case class SlpPackedStopGroup(
  members: Vector[SlpPackedSideEffectMember]
) extends SlpPackedSideEffectGroup
/** A source-order-preserving sequence of Print and Stop statements fed from
  * the same packed UInt<1> result.  Unlike the homogeneous groups above,
  * this preserves interleaved `Print(lane) -> Stop(lane)` pairs exactly.
  */
private final case class SlpPackedInterleavedSideEffectGroup(
  members: Vector[SlpPackedSideEffectMember]
) extends SlpPackedSideEffectGroup

private final case class SlpPackToScalarLaneRef(
  alignmentId:  Int,
  sourcePackId: Int,
  lane:         SlpMaterializedLane
) {
  require(alignmentId >= 0)
  require(sourcePackId >= 0)
}

private final case class SlpPackedMemWriteMember(
  nodeId:       Int,
  enLane:       SlpPackToScalarLaneRef,
  enOffset:     Int,
  suppressEn:   Boolean,
  dataLane:     Option[SlpPackToScalarLaneRef],
  dataOffset:   Option[Int],
  statement:    MemWrite
) {
  require(nodeId >= 0)
  require(enLane.lane.width == 1)
  require(enOffset >= 0)
  require(dataLane.isDefined == dataOffset.isDefined)
}

private final case class SlpPackedMemWriteGroup(
  members: Vector[SlpPackedMemWriteMember]
) {
  require(members.nonEmpty)
  final def enPackId: Int = members.head.enLane.sourcePackId
  final def activeMask: BigInt = members.foldLeft(BigInt(0)) { (mask, member) =>
    mask | (BigInt(1) << member.enOffset)
  }
}

/** Portable C++ lowering of an immutable SlpPlan.
  *
  * Packed and alignment temporaries are plain uint64_t values. Original
  * scalar names continue to be owned by Renamer; this emitter never installs
  * aliases or mutates its declaration metadata.
  */
final class SlpEmitter(
  context: SlpAnalysisContext,
  plan:    SlpPlan,
  rn:      Renamer
) {
  private implicit val implicitRenamer: Renamer = rn
  private val packedAddMode =
    Option(System.getProperty("armor.slp.packedAddMode")).getOrElse("pdep").toLowerCase
  require(Set("swar", "pdep")(packedAddMode),
    s"armor.slp.packedAddMode must be swar or pdep, got $packedAddMode")
  private val classifiedOperations = context.classifications.collect {
    case (nodeId, SlpSupported(operation)) => nodeId -> operation
  }.toMap
  private val operations = classifiedOperations ++ plan.packGraph.operationOverrides
  private val projectionsByPackId = plan.projectionPlan.byDestinationPackId
  private val scalarProjectionByRootNodeId = plan.scalarProjectionPlan.byRootNodeId
  private val suppressedScalarProjectionInternalNodeIds = plan.scalarProjectionPlan.internalCatNodeIds
  private val suppressedScalarProjectionLeafNodeIds = plan.scalarProjectionPlan.elidedLeafNodeIds
  private val scalarReductionProjectionByRootNodeId =
    plan.scalarReductionProjectionPlan.byRootNodeId
  private val suppressedScalarReductionInternalNodeIds =
    plan.scalarReductionProjectionPlan.internalReductionNodeIds
  private val suppressedScalarReductionLeafNodeIds =
    plan.scalarReductionProjectionPlan.elidedPackedLeafNodeIds
  private val laneBitwiseReductionProjectionByRootNodeId =
    plan.laneBitwiseReductionProjectionPlan.byRootNodeId
  private val suppressedLaneBitwiseReductionInternalNodeIds =
    plan.laneBitwiseReductionProjectionPlan.internalNodeIds
  private val suppressedLaneBitwiseReductionLeafNodeIds =
    plan.laneBitwiseReductionProjectionPlan.elidedLeafNodeIds
  private val regionsByRootNodeId = plan.packGraph.regions.iterator.map(region =>
    region.rootNodeId -> region
  ).toMap
  private val directInputs = plan.alignPlan.directPackInputs.map { input =>
    (input.destinationPackId, input.argumentIndex) -> input
  }.toMap
  private val directRegInputs = plan.alignPlan.directRegInputs.map { input =>
    (input.destinationPackId, input.argumentIndex) -> input
  }.toMap
  private val broadcastInputs = plan.alignPlan.broadcastInputs.map { input =>
    (input.destinationPackId, input.argumentIndex) -> input
  }.toMap
  private val scalarInputs = plan.alignPlan.scalarToPack.map { alignment =>
    (alignment.destinationPackId, alignment.argumentIndex) -> alignment
  }.toMap
  private val scalarToPackByAlignmentId: Map[Int, SlpScalarToPackAlignment] =
    plan.alignPlan.scalarToPack.map(alignment => alignment.id -> alignment).toMap
  private val alignmentProjectionsById = plan.alignPlan.alignmentProjections.byAlignmentId

  private final case class SlpBitMoveRun(
    sourceLo:      Int,
    destinationLo: Int,
    width:         Int
  ) {
    require(sourceLo >= 0)
    require(destinationLo >= 0)
    require(width > 0)
    require(sourceLo + width <= 64)
    require(destinationLo + width <= 64)
  }

  private def bitMoveMask(lo: Int, width: Int): BigInt = {
    require(lo >= 0)
    require(width > 0)
    require(lo + width <= 64)
    ((BigInt(1) << width) - 1) << lo
  }

  private def buildBitMoveRuns(moves: Vector[(Int, Int)]): Vector[SlpBitMoveRun] = {
    require(moves.nonEmpty)
    require(moves.map(_._1).distinct.size == moves.size)
    require(moves.map(_._2).distinct.size == moves.size)
    val sorted = moves.sortBy { case (_, destinationBit) => destinationBit }
    sorted.tail.foldLeft(Vector(SlpBitMoveRun(sorted.head._1, sorted.head._2, 1))) {
      case (runs, (sourceBit, destinationBit)) =>
        val last = runs.last
        if (sourceBit == last.sourceLo + last.width &&
            destinationBit == last.destinationLo + last.width) {
          runs.dropRight(1) :+ last.copy(width = last.width + 1)
        } else {
          runs :+ SlpBitMoveRun(sourceBit, destinationBit, 1)
        }
    }
  }

  private def emitBitMoveRun(source: String, run: SlpBitMoveRun): String = {
    val masked = s"($source & ${uint64Constant(bitMoveMask(run.sourceLo, run.width))})"
    if (run.sourceLo == run.destinationLo) masked
    else if (run.sourceLo > run.destinationLo) s"($masked >> ${run.sourceLo - run.destinationLo})"
    else s"($masked << ${run.destinationLo - run.sourceLo})"
  }

  private def emitBitMoveComposition(source: String, moves: Vector[(Int, Int)]): String = {
    val runs = buildBitMoveRuns(moves)
    runs.map(run => emitBitMoveRun(source, run)).mkString(" | ")
  }

  /** A packed bit-select can read its common scalar source once.  The normal
    * scalar alignment would otherwise replicate the full source word once
    * per lane.  The source-bit to destination-bit mapping may be non-monotonic
    * because pack lane order can differ from source bit order; lower it as
    * explicit bit-move runs instead of requiring PEXT-compatible ordering.
    */
  private final case class SlpDirectBitSelectInput(
    sourceName: String,
    sourceWidth: Int,
    bitMoves: Vector[(Int, Int)]
  ) {
    require(sourceName.nonEmpty)
    require(sourceWidth > 0 && sourceWidth <= 64)
    require(bitMoves.nonEmpty)
    require(bitMoves.map(_._1).distinct.size == bitMoves.size)
    require(bitMoves.map(_._2).distinct.size == bitMoves.size)
    require(bitMoves.forall { case (sourceBit, destinationBit) =>
      sourceBit >= 0 && sourceBit < sourceWidth && destinationBit >= 0 && destinationBit < 64
    })
  }

  private def directBitSelectInput(
    pack: SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Option[SlpDirectBitSelectInput] = {
    if (pack.shape.opcode != SlpBitSelect || pack.lanes.exists(_.resultWidth != 1) ||
        pack.totalResultWidth > 64) None
    else {
      val selected = laneOperations.zip(pack.outputOffsets).map {
        case (
              SlpOperation(
                SlpBitSelect, 1, _, Vector(SlpSignal(sourceName, sourceWidth)),
                Vector(bitPosition), _
              ),
              destinationOffset
            ) if sourceWidth <= 64 && bitPosition >= 0 && bitPosition < sourceWidth &&
              destinationOffset >= 0 && destinationOffset < 64 =>
          Some((sourceName, sourceWidth, bitPosition.toInt, destinationOffset))
        case _ => None
      }
      if (selected.exists(_.isEmpty)) None
      else {
        val values = selected.flatten
        val sourceNames = values.map(_._1).distinct
        val sourceWidths = values.map(_._2).distinct
        val bitMoves = values.map { case (_, _, bitPosition, destinationOffset) =>
          bitPosition -> destinationOffset
        }
        if (sourceNames.size != 1 || sourceWidths.size != 1 ||
            bitMoves.map(_._1).distinct.size != bitMoves.size ||
            bitMoves.map(_._2).distinct.size != bitMoves.size) None
        else Some(SlpDirectBitSelectInput(sourceNames.head, sourceWidths.head, bitMoves))
      }
    }
  }

  private val directBitSelectInputsByPackId: Map[Int, SlpDirectBitSelectInput] =
    plan.packGraph.packs.flatMap { pack =>
      directBitSelectInput(pack, pack.nodeIds.map(operations)).map(pack.id -> _)
    }.toMap
  private val bypassedDirectBitSelectAlignmentIds: Set[Int] =
    directBitSelectInputsByPackId.keySet.flatMap(packId => scalarInputs.get((packId, 0)).map(_.id))
  private val fusedMaskedAndByPackId: Map[Int, SlpScalarToPackAlignment] =
    plan.packGraph.packs.flatMap { pack =>
      val laneOperations = pack.nodeIds.map(operations)
      val isLowTruncation = pack.shape.opcode == SlpMaskedAnd && laneOperations.forall { operation =>
        operation.operands match {
          case Vector(source: SlpSignal, mask: SlpUIntConstant) =>
            source.width >= operation.resultWidth &&
              mask.width == operation.resultWidth &&
              mask.value == (BigInt(1) << operation.resultWidth) - 1
          case _ => false
        }
      }
      scalarInputs.get((pack.id, 0)).filter { alignment =>
        isLowTruncation && alignment.lanes.forall {
          case _: SlpScalarInputLane   => true
          case _: SlpConstantInputLane => true
          case _                       => false
        }
      }.map(pack.id -> _)
    }.toMap
  private val fusedMaskedAndByAlignmentId: Map[Int, SlpPack] =
    fusedMaskedAndByPackId.iterator.map { case (packId, alignment) =>
      alignment.id -> plan.packGraph.pack(packId)
    }.toMap
  private val unpackAlignments = plan.alignPlan.packToScalar.map(_.id).toSet
  private val indexedPackReadsByRootNodeId = plan.indexedPackReadPlan.byRootNodeId
  private val residualIndexedMuxByRootNodeId = plan.residualIndexedMuxPlan.byRootNodeId
  private val residualScalarRewriteByRootNodeId = plan.residualScalarRewritePlan.byRootNodeId
  private val suppressedResidualScalarRewriteNodeIds = plan.residualScalarRewritePlan.absorbedNodeIds
  private val segmentAlignments = plan.alignPlan.packSegments.map(alignment => alignment.id -> alignment).toMap
  private val regWriteInputs = plan.alignPlan.regWriteInputs.map(input => input.regPackId -> input).toMap
  private val regPacking = plan.regPacking

  private def directReferenceName(expression: Expression): Option[String] = expression match {
    case Reference(name, _, _, _) => Some(name)
    case _                        => None
  }

  private def isUIntOne(expression: Expression): Boolean = expression match {
    case UIntLiteral(value, _) => value == 1
    case _                     => false
  }

  private def referencesName(expression: Expression, name: String): Boolean =
    directReferenceName(expression).contains(name) || {
      var found = false
      expression.foreachExpr(child => if (referencesName(child, name)) found = true)
      found
    }

  private def sideEffectConsumesOnlyCondition(
    statement: Statement,
    outputName: String
  ): Boolean = statement match {
    case print: Print =>
      directReferenceName(print.en).contains(outputName) &&
        !print.args.exists(referencesName(_, outputName))
    case stop: Stop => directReferenceName(stop.en).contains(outputName)
    case _          => false
  }

  /** Build maximal runs of side-effect-only packed UInt<1> conditions.  This
    * is intentionally an emitter-local lowering decision: ICTPacker remains
    * unaware of Print/Stop, while the emitter has both lane offsets and final
    * statement order.
    */
  private val packedSideEffectMembersByScheduleNode: Map[Int, SlpPackedSideEffectMember] = {
    plan.alignPlan.packToScalar.flatMap { alignment =>
      val sourcePack = plan.packGraph.pack(alignment.sourcePackId)
      alignment.lanes.flatMap { lane =>
        val sideEffectConsumers = lane.consumers.collect {
          case SlpScalarConsumer(nodeId) => nodeId
        }.distinct.sorted
        val consumersAreExclusive = sideEffectConsumers.nonEmpty &&
          sideEffectConsumers.size == lane.consumers.size
        if (!consumersAreExclusive || lane.width != 1) Vector.empty
        else {
          sideEffectConsumers.flatMap { consumerNodeId =>
            val statement = context.graph.node(consumerNodeId).statement
            if (sideEffectConsumesOnlyCondition(statement, lane.outputName)) {
              Vector(consumerNodeId -> SlpPackedSideEffectMember(
                consumerNodeId,
                lane.sourceNodeId,
                alignment.sourcePackId,
                sourcePack.outputOffsets(lane.sourceLaneIndex),
                statement
              ))
            } else Vector.empty
          }
        }
      }
    }.toMap
  }

  private val packedSideEffectGroups: Vector[SlpPackedSideEffectGroup] = {
    val groups = Vector.newBuilder[SlpPackedSideEffectGroup]
    var run = Vector.empty[SlpPackedSideEffectMember]

    def samePack(left: SlpPackedSideEffectMember, right: SlpPackedSideEffectMember): Boolean =
      left.sourcePackId == right.sourcePackId

    def flush(): Unit = {
      val distinctLanes = run.map(_.sourceOffset).distinct.size
      if (run.size >= 2 && distinctLanes >= 2) {
        val homogeneous = run.map(_.statement.getClass).distinct.size == 1
        if (homogeneous) {
          run.head.statement match {
            case _: Print => groups += SlpPackedPrintGroup(run)
            case _: Stop  => groups += SlpPackedStopGroup(run)
            case _        =>
          }
        } else {
          groups += SlpPackedInterleavedSideEffectGroup(run)
        }
      }
      run = Vector.empty
    }

    // Only immediately consecutive scalar *schedule* nodes are grouped.  The
    // StatementGraph's node ids are not a source-order sequence, so node-id
    // adjacency would miss otherwise contiguous Print/Stop statements.
    plan.topologicalSchedule.foreach { node =>
      node match {
        case SlpScalarScheduleNode(nodeId) if packedSideEffectMembersByScheduleNode.contains(nodeId) =>
          val member = packedSideEffectMembersByScheduleNode(nodeId)
          // Keep an interleaved Print/Stop run together so that one packed
          // condition can serve both side effects without materializing an
          // unpacked scalar condition.  Homogeneous runs retain the more
          // specialized Print/Stop lowering above.
          if (run.nonEmpty && !samePack(run.last, member)) flush()
          run :+= member
        case _ =>
          flush()
      }
    }
    flush()
    groups.result()
  }

  private val packedSideEffectGroupByLeaderNodeId: Map[Int, SlpPackedSideEffectGroup] =
    packedSideEffectGroups.map(group => group.members.head.nodeId -> group).toMap
  private val suppressedPackedSideEffectNodeIds: Set[Int] =
    packedSideEffectGroups.flatMap(_.members.drop(1).map(_.nodeId)).toSet
  private val suppressedPackedSideEffectSourceNodeIds: Set[Int] =
    packedSideEffectGroups.flatMap(_.members.map(_.sourceNodeId)).toSet

  private val packToScalarLaneByOutputName: Map[String, SlpPackToScalarLaneRef] =
    plan.alignPlan.packToScalar.flatMap { alignment =>
      alignment.lanes.map { lane =>
        lane.outputName -> SlpPackToScalarLaneRef(alignment.id, alignment.sourcePackId, lane)
      }
    }.toMap

  private def exclusiveScalarConsumer(lane: SlpMaterializedLane, nodeId: Int): Boolean =
    lane.consumers == Vector(SlpScalarConsumer(nodeId))

  /** Packed MemWrite side-effect lowering emits _armor_slp_mem_write_active_*
    * guards and suppresses the scalar pack-to-scalar views for write enables.
    * Keep it behind one local switch so it can be disabled independently from
    * ordinary SLP discovery and from MemWrite guard normalization.
    */
  private val enablePackedMemWriteLowering: Boolean = false

  private def packedMemWriteMember(nodeId: Int): Option[SlpPackedMemWriteMember] = {
    context.graph.node(nodeId).statement match {
      case write: MemWrite if isUIntOne(write.wrMask) =>
        val enLane = directReferenceName(write.wrEn)
          .flatMap(packToScalarLaneByOutputName.get)
          .filter(_.lane.width == 1)
        enLane.map { enRef =>
          val enPack = plan.packGraph.pack(enRef.sourcePackId)
          val dataRef = directReferenceName(write.wrData)
            .flatMap(packToScalarLaneByOutputName.get)
            .filter(ref => exclusiveScalarConsumer(ref.lane, nodeId))
          val dataOffset = dataRef.map { ref =>
            val dataPack = plan.packGraph.pack(ref.sourcePackId)
            dataPack.outputOffsets(ref.lane.sourceLaneIndex)
          }
          SlpPackedMemWriteMember(
            nodeId = nodeId,
            enLane = enRef,
            enOffset = enPack.outputOffsets(enRef.lane.sourceLaneIndex),
            suppressEn = exclusiveScalarConsumer(enRef.lane, nodeId),
            dataLane = dataRef,
            dataOffset = dataOffset,
            statement = write
          )
        }
      case _ => None
    }
  }

  private val packedMemWriteCandidatesByScheduleNode: Map[Int, SlpPackedMemWriteMember] =
    if (!enablePackedMemWriteLowering) Map.empty
    else plan.topologicalSchedule.collect {
        case SlpScalarScheduleNode(nodeId) => packedMemWriteMember(nodeId).map(nodeId -> _)
      }.flatten.toMap

  private val packedMemWriteGroups: Vector[SlpPackedMemWriteGroup] = {
    val groups = Vector.newBuilder[SlpPackedMemWriteGroup]
    var run = Vector.empty[SlpPackedMemWriteMember]

    def sameEnablePack(left: SlpPackedMemWriteMember, right: SlpPackedMemWriteMember): Boolean =
      left.enLane.sourcePackId == right.enLane.sourcePackId

    def flush(): Unit = {
      val distinctLanes = run.map(_.enOffset).distinct.size
      if (run.size >= 2 && distinctLanes >= 2) {
        groups += SlpPackedMemWriteGroup(run)
      }
      run = Vector.empty
    }

    if (enablePackedMemWriteLowering) {
      plan.topologicalSchedule.foreach {
        case SlpScalarScheduleNode(nodeId) if packedMemWriteCandidatesByScheduleNode.contains(nodeId) =>
          val member = packedMemWriteCandidatesByScheduleNode(nodeId)
          if (run.nonEmpty && !sameEnablePack(run.last, member)) flush()
          run :+= member
        case _ =>
          flush()
      }
    }
    flush()
    groups.result()
  }

  private val packedMemWriteGroupByLeaderNodeId: Map[Int, SlpPackedMemWriteGroup] =
    packedMemWriteGroups.map(group => group.members.head.nodeId -> group).toMap
  private val suppressedPackedMemWriteNodeIds: Set[Int] =
    packedMemWriteGroups.flatMap(_.members.drop(1).map(_.nodeId)).toSet
  private val suppressedPackedMemWriteSourceNodeIds: Set[Int] =
    packedMemWriteGroups.flatMap { group =>
      group.members.flatMap(member =>
        Option.when(member.suppressEn)(member.enLane.lane.sourceNodeId).toVector ++
          member.dataLane.map(_.lane.sourceNodeId)
      )
    }.toSet
  private val regPacksById = regPacking.toVector.flatMap(_.packs).map(pack => pack.id -> pack).toMap
  /** A scalar register name can be read directly from packed state when its
    * write-side register pack owns the corresponding lane. */
  private val packedRegisterLaneByName: Map[String, (Int, SlpRegLane)] =
    regPacking.toVector.flatMap(_.packs).flatMap { pack =>
      pack.lanes.map(lane => lane.registerName -> (pack.id -> lane))
    }.toMap
  private var elidedMuxResultMasks = 0

  private def sparseGatherFor(alignment: SlpScalarToPackAlignment): Option[SlpSparseGather] = {
    final case class Entry(
      source:            SlpSegmentSource,
      sourceOffset:      Int,
      destinationOffset: Int,
      width:             Int,
      destinationLane:   Int,
      segmentId:         Option[Int]
    )

    val entries = alignment.lanes.map {
      case lane: SlpUnpackedInputLane =>
        val sourcePack = plan.packGraph.pack(lane.sourcePackId)
        Some(Entry(
          SlpCombSegmentSource(lane.sourcePackId),
          sourcePack.outputOffsets(lane.sourceLaneIndex),
          alignment.laneOffsets(lane.destinationLane),
          lane.width,
          lane.destinationLane,
          lane.segmentAlignmentId
        ))
      case lane: SlpRegInputLane =>
        regPacksById.get(lane.regPackId).map { sourcePack =>
          Entry(
            SlpRegSegmentSource(lane.regPackId),
            sourcePack.lanes(lane.sourceLaneIndex).offset,
            alignment.laneOffsets(lane.destinationLane),
            lane.width,
            lane.destinationLane,
            lane.segmentAlignmentId
          )
        }
      case _ => None
    }
    if (entries.exists(_.isEmpty)) return None
    val gathered = entries.flatten
    if (gathered.size < 2 || gathered.forall(_.segmentId.isEmpty)) return None

    val terms = gathered.groupBy(_.source).toVector.flatMap { case (source, sourceEntries) =>
      val byDestination = sourceEntries.sortBy(_.destinationOffset)
      val destinationContiguous = byDestination.sliding(2).forall {
        case Vector(left, right) => left.destinationOffset + left.width == right.destinationOffset
        case _                   => true
      }
      val bySource = sourceEntries.sortBy(_.sourceOffset)
      val sameOrder = bySource.map(_.destinationLane) == byDestination.map(_.destinationLane)
      val sourceNonOverlapping = bySource.sliding(2).forall {
        case Vector(left, right) => left.sourceOffset + left.width <= right.sourceOffset
        case _                   => true
      }
      if (!destinationContiguous || !sameOrder || !sourceNonOverlapping) None
      else {
        val sourceMask = bySource.foldLeft(BigInt(0)) { case (mask, entry) =>
          mask | (((BigInt(1) << entry.width) - 1) << entry.sourceOffset)
        }
        Some(SlpSparseGatherTerm(
          source,
          sourceMask,
          byDestination.head.destinationOffset,
          byDestination.map(_.width).sum
        ))
      }
    }.sortBy(_.destinationOffset)
    if (terms.size != gathered.map(_.source).distinct.size || terms.size == gathered.size) return None
    val coversOutput = terms.headOption.exists(_.destinationOffset == 0) && terms.sliding(2).forall {
      case Vector(left, right) => left.destinationOffset + left.width == right.destinationOffset
      case _                   => true
    } && terms.lastOption.exists(term => term.destinationOffset + term.width == alignment.lanes.map(_.width).sum)
    if (!coversOutput) None
    else {
      val signature = SlpSparseGatherSignature(terms, alignment.lanes.map(_.width).sum)
      Some(SlpSparseGather(
        alignment.id,
        signature,
        gathered.flatMap(_.segmentId).toSet
      ))
    }
  }

  private val eqPackedSources: Map[Int, SlpEqPackedSource] =
    plan.packGraph.packs.filter(_.shape.opcode == SlpEqConst).flatMap { pack =>
      val laneOperations = pack.nodeIds.map(operations)
      val inputWidth = laneOperations.headOption.flatMap(_.operands.headOption).map(_.width)
      // EqConst lowering supports every UInt<2..17> literal. The producer
      // layout, rather than the literal value, determines whether an existing
      // packed input can be reused directly.
      val supportsDirectReuse = inputWidth.exists(width => width >= 2 && width <= 17)
      scalarInputs.get((pack.id, 0)).flatMap { alignment =>
        val unpacked = alignment.lanes.collect { case lane: SlpUnpackedInputLane => lane }
        val packedRegisters = alignment.lanes.collect { case lane: SlpRegInputLane => lane }
        val candidate = if (unpacked.size == alignment.lanes.size && unpacked.nonEmpty &&
            unpacked.map(_.sourcePackId).distinct.size == 1) {
          val sourcePack = plan.packGraph.pack(unpacked.head.sourcePackId)
          Some(SlpEqPackedSource(
            packName(sourcePack.id),
            unpacked.map(lane => sourcePack.outputOffsets(lane.sourceLaneIndex)),
            alignment.id,
            unpacked.flatMap(_.segmentAlignmentId).toSet
          ))
        } else if (packedRegisters.size == alignment.lanes.size && packedRegisters.nonEmpty &&
            packedRegisters.map(_.regPackId).distinct.size == 1) {
          regPacking.flatMap(_.packs.find(_.id == packedRegisters.head.regPackId)).map { sourcePack =>
            SlpEqPackedSource(
              SlpRegStorageNames.state(sourcePack.id),
              packedRegisters.map(lane => sourcePack.lanes(lane.sourceLaneIndex).offset),
              alignment.id,
              packedRegisters.flatMap(_.segmentAlignmentId).toSet
            )
          }
        } else None
        candidate.filter(source =>
          supportsDirectReuse && alignment.lanes.forall(_.width == inputWidth.get) &&
            source.sourceOffsets == source.sourceOffsets.sorted &&
            source.sourceOffsets.distinct.size == source.sourceOffsets.size &&
            (inputWidth.contains(2) || source.sourceOffsets.zipWithIndex.forall {
              case (offset, index) => offset == source.sourceOffsets.head + index * inputWidth.get
            })
        )
      }.map(pack.id -> _)
    }.toMap
  private val bypassedEqAlignmentIds: Set[Int] =
    eqPackedSources.valuesIterator.map(_.bypassAlignmentId).toSet


  private val alignmentScheduleIndex: Map[Int, Int] =
    plan.topologicalSchedule.zipWithIndex.collect {
      case (SlpAlignmentScheduleNode(alignmentId), index) => alignmentId -> index
    }.toMap

  /** Exact common-subexpression reuse for every materialized alignment.
    *
    * The emission plan excludes bypassed and fused alignments from reuse
    * because they do not materialize an `_armor_slp_align_*` value.
    * Sparse packed gathers retain their existing source-aware reuse path.
    * Packed and register lanes include their exact source/segment identity;
    * this deliberately performs CSE only when composeInputTerms would read
    * the same values in the same destination layout.
    */
  private def materializedAlignmentSignature(
    alignment: SlpScalarToPackAlignment
  ): SlpMaterializedAlignmentSignature = {
    val laneSignatures: Vector[SlpAlignmentLaneSignature] = alignment.lanes.map {
      case lane: SlpScalarInputLane =>
        SlpScalarSignalSignature(lane.signalName, lane.width, lane.producerNodeId)
      case lane: SlpConstantInputLane =>
        SlpScalarConstantSignature(lane.value, lane.width)
      case lane: SlpUnpackedInputLane =>
        SlpUnpackedLaneSignature(
          lane.signalName,
          lane.width,
          lane.sourcePackId,
          lane.sourceLaneIndex,
          lane.sourceNodeId,
          lane.segmentAlignmentId
        )
      case lane: SlpRegInputLane =>
        SlpPackedRegLaneSignature(
          lane.registerName,
          lane.width,
          lane.regPackId,
          lane.sourceLaneIndex,
          lane.segmentAlignmentId
        )
    }
    SlpMaterializedAlignmentSignature(laneSignatures, alignment.laneOffsets)
  }

  private val alignmentSignaturesById: Map[Int, SlpMaterializedAlignmentSignature] =
    plan.alignPlan.scalarToPack.iterator.map(alignment =>
      alignment.id -> materializedAlignmentSignature(alignment)
    ).toMap

  private sealed trait AlignmentRecipe
  private case object OrdinaryAlignment extends AlignmentRecipe
  private final case class BitSliceAlignment(gather: SlpBitSliceGather) extends AlignmentRecipe
  private final case class SparseAlignment(gather: SlpSparseGather) extends AlignmentRecipe

  private sealed trait AlignmentEmission
  private final case class MaterializeAlignment(recipe: AlignmentRecipe) extends AlignmentEmission
  private final case class ReuseAlignment(sourceId: Int, recipe: AlignmentRecipe) extends AlignmentEmission
  private final case class BypassAlignment(reason: String) extends AlignmentEmission
  // This alignment emits the destination pack itself, rather than an alignment value.
  private final case class EmitFusedPack(pack: SlpPack) extends AlignmentEmission

  /** One decision shared by CSE, name resolution, liveness and emission.
    * Only materialized values can become reuse sources. Aliases always point
    * directly to an earlier materialized value, never another alias or bypass.
    */
  private final class AlignmentEmissionPlan(val entries: Map[Int, AlignmentEmission]) {
    entries.foreach {
      case (id, ReuseAlignment(sourceId, _)) =>
        require(entries(sourceId).isInstanceOf[MaterializeAlignment],
          s"alignment $id reuses non-materialized alignment $sourceId")
        require(alignmentScheduleIndex(sourceId) < alignmentScheduleIndex(id),
          s"alignment $id reuses an alignment that is not scheduled earlier: $sourceId")
      case _ =>
    }

    def materializedId(id: Int): Int = entries(id) match {
      case MaterializeAlignment(_) => id
      case ReuseAlignment(sourceId, _) => sourceId
      case other => throw new IllegalStateException(
        s"alignment $id has no materialized value: $other"
      )
    }

    def recipe(id: Int): Option[AlignmentRecipe] = entries(id) match {
      case MaterializeAlignment(value) => Some(value)
      case ReuseAlignment(_, value) => Some(value)
      case _ => None
    }
  }

  private val alignmentEmissionPlan: AlignmentEmissionPlan = {
    // Op-specific fast paths only decide their own input disposition here.
    // All later code consumes this plan instead of repeating bypass predicates.
    val initial: Map[Int, AlignmentEmission] = plan.alignPlan.scalarToPack.map { alignment =>
      val emission: AlignmentEmission =
        if (bypassedEqAlignmentIds(alignment.id)) BypassAlignment("direct packed equality")
        else if (bypassedDirectBitSelectAlignmentIds(alignment.id))
          BypassAlignment("direct bit select")
        else fusedMaskedAndByAlignmentId.get(alignment.id) match {
          case Some(pack) => EmitFusedPack(pack)
          case None =>
            val recipe = bitSliceGatherFor(alignment).map(BitSliceAlignment)
              .orElse(sparseGatherFor(alignment).map(SparseAlignment))
              .getOrElse(OrdinaryAlignment)
            MaterializeAlignment(recipe)
        }
      alignment.id -> emission
    }.toMap

    // Preserve the two existing equivalence rules: sparse gathers use their
    // exact bit mapping; other materializations use the exact input lane layout.
    val sparseGroups = initial.toVector.collect {
      case (id, MaterializeAlignment(SparseAlignment(gather))) => gather.signature -> id
    }.groupMap(_._1)(_._2).values
    val ordinaryGroups = initial.toVector.collect {
      case (id, MaterializeAlignment(recipe)) if !recipe.isInstanceOf[SparseAlignment] =>
        alignmentSignaturesById(id) -> id
    }.groupMap(_._1)(_._2).values
    val recipesById = initial.collect {
      case (id, MaterializeAlignment(recipe)) => id -> recipe
    }
    val aliases = (sparseGroups ++ ordinaryGroups).flatMap { ids =>
      val sourceId = ids.minBy(alignmentScheduleIndex)
      ids.filterNot(_ == sourceId).map(id => id -> ReuseAlignment(sourceId, recipesById(id)))
    }.toMap
    new AlignmentEmissionPlan(initial ++ aliases)
  }

  private val sparseGathersByAlignmentId: Map[Int, SlpSparseGather] =
    alignmentEmissionPlan.entries.keysIterator.flatMap { id =>
      alignmentEmissionPlan.recipe(id).collect {
        case SparseAlignment(gather) => id -> gather
      }
    }.toMap
  private val sparseGatherSegmentIds: Set[Int] =
    sparseGathersByAlignmentId.valuesIterator.flatMap(_.segmentIds).toSet

  /** Conservative schedule epoch for alignment reuse across state commits.
    * Combinational and scalar sources are immutable, but packed register
    * storage is updated by RegUpdate schedule nodes. Restricting reuse to one
    * epoch prevents an earlier snapshot from replacing a later state read.
    */
  private val alignmentScheduleEpoch: Map[Int, Int] = {
    var epoch = 0
    plan.topologicalSchedule.flatMap {
      case SlpRegUpdateScheduleNode(_, _) =>
        epoch += 1
        None
      case SlpAlignmentScheduleNode(alignmentId) => Some(alignmentId -> epoch)
      case _ => None
    }.toMap
  }
  private val packScheduleEpoch: Map[Int, Int] = {
    var epoch = 0
    plan.topologicalSchedule.flatMap {
      case SlpRegUpdateScheduleNode(_, _) =>
        epoch += 1
        None
      case SlpPackScheduleNode(packId) => Some(packId -> epoch)
      case _ => None
    }.toMap
  }

  private def alignmentProjectionCseKey(
    alignmentId: Int,
    term:        SlpAlignmentProjectionTerm
  ): SlpProjectionCseKey = {
    val epoch = term.source match {
      case _: SlpProjectionRegPack => Some(alignmentScheduleEpoch(alignmentId))
      case _                       => None
    }
    SlpProjectionCseKey(
      source = term.source,
      sourceWidth = term.sourceWidth,
      destinationWidth = term.destinationWidth,
      transfers = term.transfers,
      epoch = epoch
    )
  }

  private def packProjectionCseKey(
    packId:      Int,
    projection:  SlpPackProjection
  ): SlpProjectionCseKey = {
    val epoch = projection.source match {
      case _: SlpProjectionRegPack => Some(packScheduleEpoch(packId))
      case _                       => None
    }
    SlpProjectionCseKey(
      source = projection.source,
      sourceWidth = projection.sourceWidth,
      destinationWidth = projection.destinationWidth,
      transfers = projection.transfers,
      epoch = epoch
    )
  }

  private def alignmentProjectionPathIsEmitted(
    alignment: SlpScalarToPackAlignment
  ): Boolean = alignmentEmissionPlan.entries(alignment.id) match {
    case MaterializeAlignment(OrdinaryAlignment) => true
    case _ => false
  }

  private val alignmentProjectionCseUses: Vector[SlpProjectionCsePlanner.AlignmentUse] =
    plan.topologicalSchedule.zipWithIndex.flatMap {
      case (SlpAlignmentScheduleNode(alignmentId), scheduleIndex) =>
        scalarToPackByAlignmentId.get(alignmentId).filter(alignmentProjectionPathIsEmitted)
          .toVector.flatMap { _ =>
            alignmentProjectionsById.get(alignmentId).toVector.flatMap { projection =>
              projection.terms.zipWithIndex.map { case (term, termIndex) =>
                val key = alignmentProjectionCseKey(alignmentId, term)
                SlpProjectionCsePlanner.AlignmentUse(alignmentId, termIndex, scheduleIndex, key)
              }
            }
          }
      case _ => Vector.empty
    }.toVector

  private def emittedPackProjections(pack: SlpPack): Vector[SlpPackProjection] = {
    if (fusedMaskedAndByPackId.contains(pack.id) ||
        directBitSelectInputsByPackId.contains(pack.id)) Vector.empty
    else {
      val projections = projectionsByPackId.getOrElse(pack.id, Vector.empty)
      if (pack.shape.opcode == SlpCat) {
        Option.when(isCompleteCatProjection(pack, projections) &&
          projections.forall(_.canUseBitMapping))(projections.sortBy(_.argumentIndex))
          .getOrElse(Vector.empty)
      } else {
        projections.headOption.filter(_.canUseBitMapping).toVector
      }
    }
  }

  private val packProjectionCseUses: Vector[SlpProjectionCsePlanner.PackUse] =
    plan.topologicalSchedule.zipWithIndex.flatMap {
      case (SlpPackScheduleNode(packId), scheduleIndex) =>
        emittedPackProjections(plan.packGraph.pack(packId)).map { projection =>
          val key = packProjectionCseKey(packId, projection)
          SlpProjectionCsePlanner.PackUse(
            packId = packId,
            argumentIndex = projection.argumentIndex,
            scheduleIndex = scheduleIndex,
            key = key
          )
        }
      case _ => Vector.empty
    }.toVector

  private val projectionCsePlan: SlpProjectionCsePlan =
    SlpProjectionCsePlanner.build(
      alignmentUses = alignmentProjectionCseUses,
      packUses = packProjectionCseUses
    )

  private val ordinaryMaterializedAlignmentIds: Set[Int] =
    alignmentEmissionPlan.entries.iterator.collect {
      case (id, MaterializeAlignment(recipe)) if !recipe.isInstanceOf[SparseAlignment] => id
    }.toSet

  private val materializedAlignmentIds: Set[Int] =
    alignmentEmissionPlan.entries.iterator.collect {
      case (id, MaterializeAlignment(_)) => id
    }.toSet

  private def chooseAlignmentSegments(
    destinationLaneCount: Int,
    candidates:           Vector[SlpAlignmentSegmentReuse]
  ): Vector[SlpAlignmentSegmentReuse] = {
    val byBegin = candidates.groupBy(_.destinationLaneBegin).view.mapValues { matches =>
      matches.groupBy(reuse => reuse.destinationLaneBegin -> reuse.destinationLaneEnd).values.map { sameRange =>
        sameRange.minBy(reuse => (reuse.sourceScheduleIndex, reuse.sourceAlignmentId))
      }.toVector.sortBy(reuse =>
        (reuse.destinationLaneEnd, reuse.sourceScheduleIndex, reuse.sourceAlignmentId)
      )
    }.toMap

    def tieKey(selection: SlpAlignmentSegmentSelection): String = selection.segments.map { reuse =>
      f"${reuse.destinationLaneBegin}%03d:${reuse.destinationLaneEnd}%03d:" +
        f"${reuse.sourceScheduleIndex}%08d:${reuse.sourceAlignmentId}%08d"
    }.mkString(";")

    def better(
      left:  SlpAlignmentSegmentSelection,
      right: SlpAlignmentSegmentSelection
    ): SlpAlignmentSegmentSelection = {
      if (left.benefit != right.benefit) {
        if (left.benefit > right.benefit) left else right
      } else if (left.coveredBits != right.coveredBits) {
        if (left.coveredBits > right.coveredBits) left else right
      } else if (left.segments.size != right.segments.size) {
        if (left.segments.size < right.segments.size) left else right
      } else if (tieKey(left) <= tieKey(right)) left else right
    }

    val empty = SlpAlignmentSegmentSelection(0, 0, Vector.empty)
    val bestFrom = Array.fill(destinationLaneCount + 1)(empty)
    for (laneIndex <- (0 until destinationLaneCount).reverse) {
      var best = bestFrom(laneIndex + 1)
      byBegin.getOrElse(laneIndex, Vector.empty).foreach { reuse =>
        val tail = bestFrom(reuse.destinationLaneEnd)
        val withReuse = SlpAlignmentSegmentSelection(
          reuse.benefit + tail.benefit,
          reuse.width + tail.coveredBits,
          reuse +: tail.segments
        )
        best = better(best, withReuse)
      }
      bestFrom(laneIndex) = best
    }
    bestFrom(0).segments
  }

  private val segmentReusesByAlignmentId: Map[Int, Vector[SlpAlignmentSegmentReuse]] = {
    val alignmentsById = plan.alignPlan.scalarToPack.iterator.map(alignment =>
      alignment.id -> alignment
    ).toMap

    def signatureWidth(signature: SlpMaterializedAlignmentSignature): Int =
      signature.lanes.map(_.width).sum

    def segmentKey(
      signature: SlpMaterializedAlignmentSignature,
      begin:     Int,
      end:       Int
    ): SlpAlignmentSegmentKey = {
      require(begin >= 0 && begin < end && end <= signature.lanes.size)
      val bitOffset = signature.laneOffsets(begin)
      SlpAlignmentSegmentKey(
        signature.lanes.slice(begin, end),
        signature.laneOffsets.slice(begin, end).map(_ - bitOffset)
      )
    }

    def segmentWidth(
      signature: SlpMaterializedAlignmentSignature,
      begin:     Int,
      end:       Int
    ): Int =
      signature.lanes.slice(begin, end).map(_.width).sum

    val materializedEntries = materializedAlignmentIds.toVector.sorted.map { alignmentId =>
      val signature = alignmentSignaturesById(alignmentId)
      SlpMaterializedAlignmentEntry(
        alignmentId = alignmentId,
        signature = signature,
        scheduleIndex = alignmentScheduleIndex(alignmentId),
        epoch = alignmentScheduleEpoch(alignmentId),
        laneCount = signature.lanes.size,
        width = signatureWidth(signature)
      )
    }

    val fullSourceEntriesByKey: Map[SlpAlignmentSegmentKey, Vector[SlpMaterializedAlignmentEntry]] =
      materializedEntries
        .filter(_.laneCount >= 2)
        .groupBy(entry => segmentKey(entry.signature, 0, entry.laneCount))
        .view.mapValues(_.sortBy(entry => (entry.scheduleIndex, entry.alignmentId))).toMap

    val sourceSegmentEntriesByKey: Map[SlpAlignmentSegmentKey, Vector[SlpMaterializedAlignmentSegmentEntry]] =
      materializedEntries.flatMap { entry =>
        if (entry.laneCount < 3) Vector.empty
        else {
          (0 until entry.laneCount).flatMap { begin =>
            (begin + 2 to entry.laneCount).filter(end =>
              begin != 0 || end != entry.laneCount
            ).map { end =>
              SlpMaterializedAlignmentSegmentEntry(
                source = entry,
                sourceLaneBegin = begin,
                sourceLaneEnd = end,
                sourceBitOffset = entry.signature.laneOffsets(begin),
                width = segmentWidth(entry.signature, begin, end)
              )
            }
          }.toVector
        }
      }.groupBy(segment => segmentKey(segment.source.signature, segment.sourceLaneBegin, segment.sourceLaneEnd))
        .view.mapValues(_.sortBy(segment =>
          (segment.source.scheduleIndex, segment.source.alignmentId, segment.sourceLaneBegin, segment.sourceLaneEnd)
        )).toMap

    ordinaryMaterializedAlignmentIds.toVector.sorted.flatMap { destinationId =>
      val destination = alignmentsById(destinationId)
      val destinationSignature = alignmentSignaturesById(destinationId)
      val destinationScheduleIndex = alignmentScheduleIndex(destinationId)
      val destinationEpoch = alignmentScheduleEpoch(destinationId)
      val destinationLaneCount = destinationSignature.lanes.size
      val destinationWidth = signatureWidth(destinationSignature)
      val sourceInsideDestination =
        if (destinationLaneCount < 3) Vector.empty
        else {
          (0 until destinationLaneCount).flatMap { begin =>
            (begin + 2 to destinationLaneCount).filter(end =>
              begin != 0 || end != destinationLaneCount
            ).flatMap { end =>
              val key = segmentKey(destinationSignature, begin, end)
              val width = segmentWidth(destinationSignature, begin, end)
              val destinationBitOffset = destinationSignature.laneOffsets(begin)
              fullSourceEntriesByKey.getOrElse(key, Vector.empty).flatMap { source =>
                Option.when(
                  source.laneCount == end - begin &&
                    source.scheduleIndex < destinationScheduleIndex &&
                    source.epoch == destinationEpoch &&
                    destinationBitOffset + width <= 64
                )(SlpAlignmentSegmentReuse(
                  sourceAlignmentId = source.alignmentId,
                  destinationAlignmentId = destinationId,
                  destinationLaneBegin = begin,
                  destinationLaneEnd = end,
                  sourceBitOffset = 0,
                  destinationBitOffset = destinationBitOffset,
                  width = width,
                  sourceScheduleIndex = source.scheduleIndex
                ))
              }
            }
          }.toVector
        }

      val destinationInsideSource =
        if (destinationLaneCount < 2) Vector.empty
        else {
          val key = segmentKey(destinationSignature, 0, destinationLaneCount)
          sourceSegmentEntriesByKey.getOrElse(key, Vector.empty).flatMap { segment =>
            val source = segment.source
            Option.when(
              source.laneCount > destinationLaneCount &&
                source.scheduleIndex < destinationScheduleIndex &&
                source.epoch == destinationEpoch &&
                segment.width == destinationWidth
            )(SlpAlignmentSegmentReuse(
              sourceAlignmentId = source.alignmentId,
              destinationAlignmentId = destinationId,
              destinationLaneBegin = 0,
              destinationLaneEnd = destinationLaneCount,
              sourceBitOffset = segment.sourceBitOffset,
              destinationBitOffset = 0,
              width = destinationWidth,
              sourceScheduleIndex = source.scheduleIndex
            ))
          }
        }
      val candidates = sourceInsideDestination ++ destinationInsideSource
      val selected = chooseAlignmentSegments(destination.lanes.size, candidates)
      Option.when(selected.nonEmpty)(destinationId -> selected)
    }.toMap
  }

  private def uncoveredAlignmentLanes(
    alignment: SlpScalarToPackAlignment
  ): Vector[SlpPackInputLane] = {
    val covered = coveredAlignmentLaneSet(alignment)
    alignment.lanes.filterNot(lane => covered(lane.destinationLane))
  }

  private def projectionCoveredLaneSet(alignment: SlpScalarToPackAlignment): Set[Int] =
    alignmentProjectionsById.get(alignment.id).iterator
      .flatMap(_.coveredDestinationLanes).toSet

  private def effectiveSegmentReuses(
    alignment: SlpScalarToPackAlignment
  ): Vector[SlpAlignmentSegmentReuse] = {
    val projectionCovered = projectionCoveredLaneSet(alignment)
    segmentReusesByAlignmentId.getOrElse(alignment.id, Vector.empty).filter { reuse =>
      (reuse.destinationLaneBegin until reuse.destinationLaneEnd).forall(lane =>
        !projectionCovered(lane)
      )
    }
  }

  private def coveredAlignmentLaneSet(alignment: SlpScalarToPackAlignment): Set[Int] = {
    val segmentCovered = effectiveSegmentReuses(alignment).iterator.flatMap { reuse =>
      reuse.destinationLaneBegin until reuse.destinationLaneEnd
    }.toSet
    projectionCoveredLaneSet(alignment) ++ segmentCovered
  }

  private val liveSegmentAlignmentIds: Set[Int] = {
    val scalarUses = plan.alignPlan.scalarToPack.iterator
      .filter(alignment => alignmentEmissionPlan.recipe(alignment.id).exists {
        case SparseAlignment(_) => false
        case _ => true
      })
      .flatMap(alignment => uncoveredAlignmentLanes(alignment).iterator.flatMap {
        case lane: SlpUnpackedInputLane => lane.segmentAlignmentId
        case lane: SlpRegInputLane      => lane.segmentAlignmentId
        case _                          => None
      })
    val registerUses = plan.alignPlan.regWriteInputs.iterator.flatMap(_.lanes.iterator.flatMap {
      case lane: SlpUnpackedInputLane => lane.segmentAlignmentId
      case lane: SlpRegInputLane      => lane.segmentAlignmentId
      case _                          => None
    })
    (scalarUses ++ registerUses).toSet
  }
  private val deadSegmentAlignmentIds: Set[Int] =
    (eqPackedSources.valuesIterator.flatMap(_.segmentIds).toSet ++
      sparseGatherSegmentIds ++
      plan.alignPlan.alignmentProjections.coveredSegmentAlignmentIds) --
      liveSegmentAlignmentIds
  private val emittedRegViewNames = mutable.HashSet.empty[String]
  private val useInternalRegViewNames =
    java.lang.Boolean.getBoolean("armor.slp.internalRegViewNames")
  private val regViewNameByView = plan.regViews.map { view =>
    val name = if (useInternalRegViewNames)
      SlpRegStorageNames.view(view.regPackId, view.laneIndex)
    else rn.removeDots(rn.emit(view.lane.registerName))
    view -> name
  }.toMap
  private val regViewByName = regViewNameByView.map { case (view, name) => name -> view }

  plan.regViews.foreach { view =>
    rn.installEmitAlias(
      view.lane.registerName,
      regViewNameByView(view)
    )
  }

  private def packName(packId: Int): String = s"_armor_slp_pack_$packId"
  private def alignmentName(alignmentId: Int): String = s"_armor_slp_align_$alignmentId"
  private def materializedAlignmentName(alignmentId: Int): String =
    alignmentName(alignmentEmissionPlan.materializedId(alignmentId))

  private def loweredStatementComments(nodeIds: Vector[Int]): Vector[String] =
    nodeIds.distinct.sorted.map { nodeId =>
      val statement = context.graph.node(nodeId).statement
      val lowered = emitStmt(statement).mkString(" ")
      s"//parallel List( $lowered )"
    } :+ ""

  private def scalarProjectionComments(
    internalNodeIds: Vector[Int],
    rootNodeId:     Int
  ): Vector[String] =
    loweredStatementComments(internalNodeIds :+ rootNodeId)

  private def hierarchicalReferenceName(expression: Expression): Option[String] = expression match {
    case Reference(name, _, _, _) => Some(name)
    case SubField(base, name, _, _) => hierarchicalReferenceName(base).map(prefix => s"$prefix.$name")
    case _ => None
  }

  private def indexedMuxStatementComments(rootNodeId: Int): Vector[String] =
    loweredStatementComments(Vector(rootNodeId))

  /** Lower a normalized indexed vector read directly from a packed register.
    * This avoids materializing N scalar register views followed by N-1 Eq/Mux
    * operations.  Lanes may be any common UInt width as long as the complete
    * register pack fits in one uint64_t.  Any other indexed read uses the
    * scalar fallback in essent.Emitter, preserving general semantics. */
  private def emitDirectIndexedRegisterReadFrom(
    rootNodeId: Int,
    node:       DefNode,
    index:      Expression,
    values:     Seq[Expression],
    resultType: Type
  ): Option[Vector[String]] = {
    if (values.isEmpty || values.size > 64) None
    else {
      val lanes = values.map(hierarchicalReferenceName).map(_.flatMap(packedRegisterLaneByName.get))
      val indexWidth = index.tpe match {
        case UIntType(IntWidth(width)) if width > 0 && width.isValidInt => Some(width.toInt)
        case _ => None
      }
      val resultWidth = resultType match {
        case UIntType(IntWidth(width)) if width > 0 && width.isValidInt && width <= 64 => Some(width.toInt)
        case _ => None
      }
      (lanes, indexWidth, resultWidth) match {
        case (resolved, Some(width), Some(elementWidth))
            if resolved.forall(_.nonEmpty) && width <= 6 && (1 << width) == values.size =>
          val concrete = resolved.flatten
          val packIds = concrete.map(_._1).distinct
          val offsets = concrete.map(_._2.offset)
          val laneWidths = concrete.map(_._2.width).distinct
          val expectedOffsets = values.indices.map(_ * elementWidth).toVector
          if (packIds.size == 1 && laneWidths == Vector(elementWidth) &&
              offsets == expectedOffsets && regPacksById(packIds.head).totalWidth <= 64) {
            val state = SlpRegStorageNames.state(packIds.head)
            val result = rn.emit(node.name)
            val indexWord = s"${emitExprWrap(index)}.as_single_word()"
            val shift = if (elementWidth == 1) indexWord else s"($indexWord * $elementWidth)"
            val mask = (BigInt(1) << elementWidth) - 1
            val optimized = Vector(
              s"UInt<$elementWidth> $result = UInt<$elementWidth>(($state >> $shift) & " +
                s"UINT64_C(0x${mask.toString(16)}));"
            )
            Some(optimized ++ indexedMuxStatementComments(rootNodeId))
          } else None
        case _ => None
      }
    }
  }

  private def emitDirectIndexedRegisterRead(rootNodeId: Int): Option[Vector[String]] =
    context.graph.node(rootNodeId).statement match {
    case node @ DefNode(_, _, DoPrim(ArmorIndexedMux, index +: values, Seq(), resultType))
        if values.nonEmpty && values.size <= 64 =>
      emitDirectIndexedRegisterReadFrom(rootNodeId, node, index, values, resultType)
    case _ => None
  }

  /** Emit a planned direct read from a combinational pack.  Unlike register
    * direct reads, lane order may be non-dense; the planner provides a compact
    * semantic-index to physical-offset table for such layouts. */
  private def indexedFragmentShift(indexVar: String, fragment: SlpIndexedReadFragment): String = {
    val delta = fragment.sourceOffset - fragment.indexStart
    if (delta == 0) indexVar
    else if (delta > 0) s"($indexVar + UINT64_C(0x${delta.toHexString}))"
    else s"($indexVar - UINT64_C(0x${(-delta).toHexString}))"
  }

  private def emitFragmentedIndexedPackRead(
    node:     DefNode,
    read:     SlpIndexedPackRead,
    original: Vector[String]
  ): Vector[String] = {
    val base = s"_armor_slp_indexed_${read.rootNodeId}"
    val indexVar = s"${base}_index"
    val valueVar = s"${base}_value"
    val executable = Vector.newBuilder[String]
    executable += s"uint64_t $indexVar = ${emitExprWrap(read.index)}.as_single_word();"
    executable += s"uint64_t $valueVar = UINT64_C(0);"
    read.fragments.zipWithIndex.foreach { case (fragment, fragmentIndex) =>
      val source = packName(fragment.sourcePackId)
      val branch =
        if (fragmentIndex == read.fragments.size - 1) "else"
        else if (fragmentIndex == 0) s"if ($indexVar <= UINT64_C(0x${fragment.indexEnd.toHexString}))"
        else s"else if ($indexVar <= UINT64_C(0x${fragment.indexEnd.toHexString}))"
      val shift = indexedFragmentShift(indexVar, fragment)
      executable += s"$branch {"
      executable += s"  $valueVar = ($source >> $shift) & UINT64_C(0x1);"
      executable += "}"
    }
    (executable.result() ++ emitStmtWithRhs(node, s"UInt<${read.resultWidth}>($valueVar)").toVector) ++ original
  }

  private def emitIndexedPackRead(read: SlpIndexedPackRead): Vector[String] = {
    val node = context.graph.node(read.rootNodeId).statement match {
      case value: DefNode => value
      case other => throw new IllegalStateException(
        s"indexed pack read root ${read.rootNodeId} is not a DefNode: $other"
      )
    }
    val resultMask = (BigInt(1) << read.resultWidth) - 1
    val index = s"${emitExprWrap(read.index)}.as_single_word()"
    // Emit the executable direct-read lowering first. The original scalar
    // ArmorIndexedMux lowering then follows as multiline trace-only code.
    val original = indexedMuxStatementComments(read.rootNodeId)
    val rhs = read.kind match {
      case SlpIndexedDensePackRead =>
        val source = packName(read.sourcePackId)
        val shift = if (read.resultWidth == 1) index else s"($index * ${read.resultWidth})"
        s"UInt<${read.resultWidth}>(($source >> $shift) & UINT64_C(0x${resultMask.toString(16)}))"
      case SlpIndexedOffsetTablePackRead =>
        val source = packName(read.sourcePackId)
        val base = s"_armor_slp_indexed_${read.rootNodeId}"
        val offsetMask = (BigInt(1) << read.offsetBits) - 1
        val table = read.offsetTable.getOrElse(throw new IllegalStateException(
          s"offset-table indexed read ${read.rootNodeId} has no table"
        ))
        val shift = if (read.offsetBits == 1) s"${base}_index" else s"(${base}_index * ${read.offsetBits})"
        return (Vector(
          s"uint64_t ${base}_index = $index;",
          s"uint64_t ${base}_offset = (UINT64_C(0x${table.toString(16)}) >> $shift) & " +
            s"UINT64_C(0x${offsetMask.toString(16)});"
        ) ++ emitStmtWithRhs(node,
          s"UInt<${read.resultWidth}>(($source >> ${base}_offset) & UINT64_C(0x${resultMask.toString(16)}))"
        )) ++ original
      case SlpIndexedFragmentedPackRead =>
        return emitFragmentedIndexedPackRead(node, read, original)
    }
    emitStmtWithRhs(node, rhs).toVector ++ original
  }

  /** Scalar fallback for an indexed mux whose values cannot be read directly
    * from one packed register word.
    *
    * Do not hand this node to the generic expression emitter: its expression
    * form intentionally prints ArmorIndexedMux as one deeply nested C++
    * conditional.  Keeping one temporary per Mux level preserves the
    * decomposition performed on the FIRRTL expression graph and avoids a
    * single enormous C++ expression.  The index tests are mutually exclusive,
    * so this is equivalent to the priority-Mux form with lane zero as the
    * default value.
    */
  private var scalarIndexedMuxTemporaryId = 0

  private def uintLiteralValue(expression: Expression, resultWidth: Int): Option[BigInt] = expression match {
    case literal @ UIntLiteral(value, _) =>
      val literalWidth = bitWidth(literal.tpe).toInt
      Option.when(literalWidth <= resultWidth && value >= 0 && value < (BigInt(1) << resultWidth))(value)
    case _ => None
  }

  private def indexedMuxConstantLut(values: Seq[Expression], resultWidth: Int): Option[BigInt] = {
    if (resultWidth <= 0 || resultWidth > 64 || values.isEmpty ||
        values.size * resultWidth > 64) None
    else {
      val constants = values.map(uintLiteralValue(_, resultWidth))
      Option.when(constants.forall(_.nonEmpty)) {
        val laneMask = (BigInt(1) << resultWidth) - 1
        constants.flatten.zipWithIndex.foldLeft(BigInt(0)) {
          case (bits, (value, lane)) => bits | ((value & laneMask) << (lane * resultWidth))
        }
      }
    }
  }

  private def indexedMuxShift(indexWord: String, resultWidth: Int): String =
    if (resultWidth == 1) indexWord
    else if (isPowerOfTwo(resultWidth)) s"($indexWord << ${Integer.numberOfTrailingZeros(resultWidth)})"
    else s"($indexWord * $resultWidth)"

  private def emitScalarIndexedMuxChain(
    node:        DefNode,
    index:       Expression,
    values:      Seq[Expression],
    resultType:  Type,
    indexWidth:  Int,
    temporaryId: Int,
    commentOnly: Boolean
  ): Vector[String] = {
    val cppType = genCppType(resultType)
    val indexExpr = emitExprWrap(index)
    val baseName = s"_armor_indexed_mux_$temporaryId"
    val firstName = s"${baseName}_0"
    val initial = Vector(s"$cppType $firstName = ${emitExprWrap(values.head)};")
    val (layers, finalName) = (1 until values.size).foldLeft((Vector.empty[String], firstName)) {
      case ((lines, previousName), lane) =>
        val currentName = s"${baseName}_$lane"
        val condition = s"$indexExpr == UInt<$indexWidth>(0x${lane.toHexString})"
        val line = s"$cppType $currentName = $condition ? ${emitExprWrap(values(lane))} : $previousName;"
        (lines :+ line, currentName)
    }
    val executable = initial ++ layers ++ emitStmtWithRhs(node, finalName).toVector
    if (commentOnly) Vector.empty else executable
  }

  private def emitScalarIndexedMux(statement: Statement): Option[Vector[String]] = statement match {
    case node @ DefNode(_, name, DoPrim(ArmorIndexedMux, index +: values, Seq(), resultType))
        if values.nonEmpty && (values.size & (values.size - 1)) == 0 =>
      val indexWidth = index.tpe match {
        case UIntType(IntWidth(width)) if width > 0 && width.isValidInt => Some(width.toInt)
        case _ => None
      }
      indexWidth.filter(width => (1 << width) == values.size).map { width =>
        val temporaryId = scalarIndexedMuxTemporaryId
        scalarIndexedMuxTemporaryId += 1

        val resultWidth = bitWidth(resultType).toInt
        indexedMuxConstantLut(values, resultWidth) match {
          case Some(lut) =>
            val indexWord = s"${emitExprWrap(index)}.as_single_word()"
            val shift = indexedMuxShift(indexWord, resultWidth)
            val mask = (BigInt(1) << resultWidth) - 1
            val rhs = s"UInt<$resultWidth>((${uint64Constant(lut)} >> $shift) & ${uint64Constant(mask)})"
            emitStmtWithRhs(node, rhs).toVector ++
              emitScalarIndexedMuxChain(
                node = node,
                index = index,
                values = values,
                resultType = resultType,
                indexWidth = width,
                temporaryId = temporaryId,
                commentOnly = true
              )
          case None =>
            emitScalarIndexedMuxChain(
              node = node,
              index = index,
              values = values,
              resultType = resultType,
              indexWidth = width,
              temporaryId = temporaryId,
              commentOnly = false
            )
        }
      }
    case _ => None
  }

  private def emitResidualIndexedMux(rootNodeId: Int): Option[Vector[String]] =
    residualIndexedMuxByRootNodeId.get(rootNodeId).flatMap { mux =>
      context.graph.node(rootNodeId).statement match {
        case node: DefNode =>
          emitDirectIndexedRegisterReadFrom(rootNodeId, node, mux.selector, mux.values, mux.resultType)
            .orElse {
              val temporaryId = scalarIndexedMuxTemporaryId
              scalarIndexedMuxTemporaryId += 1

              val original = indexedMuxStatementComments(rootNodeId)
              val resultWidth = bitWidth(mux.resultType).toInt
              indexedMuxConstantLut(mux.values, resultWidth) match {
                case Some(lut) =>
                  val indexWord = s"${emitExprWrap(mux.selector)}.as_single_word()"
                  val shift = indexedMuxShift(indexWord, resultWidth)
                  val mask = (BigInt(1) << resultWidth) - 1
                  val rhs = s"UInt<$resultWidth>((${uint64Constant(lut)} >> $shift) & ${uint64Constant(mask)})"
                  Some(emitStmtWithRhs(node, rhs).toVector ++ original)
                case None =>
                  Some(
                    emitScalarIndexedMuxChain(
                      node = node,
                      index = mux.selector,
                      values = mux.values,
                      resultType = mux.resultType,
                      indexWidth = mux.selectorWidth,
                      temporaryId = temporaryId,
                      commentOnly = false
                    ) ++ original
                  )
              }
            }
        case _ => None
      }
    }

  private def emitResidualScalarRewrite(
    rewrite: SlpResidualScalarRewrite
  ): Vector[String] = rewrite match {
    case membership: SlpResidualMembershipRewrite =>
      context.graph.node(membership.rootNodeId).statement match {
        case node: DefNode =>
          val source = s"${emitExprWrap(membership.source)}.as_single_word()"
          val rhs = s"UInt<1>((${uint64Constant(membership.mask)} >> $source) & UINT64_C(0x1))"
          emitStmtWithRhs(node, rhs).toVector ++
            Vector("// residual scalar membership lowering") ++
            loweredStatementComments(membership.originalNodeIds)
        case statement =>
          emitStmt(statement).toVector
      }
  }

  /** Keep truncation for partial words, but never emit an identity AND for a
    * value which already occupies the complete uint64_t storage word.
    */
  private def truncateWord(value: String, width: Int, mask: BigInt): String = {
    require(width > 0 && width <= 64)
    if (width == 64) value else s"$value & UINT64_C(0x${mask.toString(16)})"
  }

  /** Coalesce only adjacent direct-write fragments in the already-final
    * lowering schedule.  Schedule adjacency means no scalar statement, pack,
    * alignment, or register view can observe the storage between the two
    * commits.  Keeping the individual nodes in SlpPlan preserves all graph
    * dependency reasoning; this is solely an equivalent emission rewrite.
    */
  private val coalescedRegCommitFragments: Map[(Int, Int), Vector[Int]] = {
    val directWritePackIds = regPacking.toVector.flatMap { packing =>
      packing.directWrites.map(_.regPackId) ++ packing.muxWrites.map(_.regPackId)
    }.toSet
    val scheduled = plan.topologicalSchedule.zipWithIndex.collect {
      case (SlpRegUpdateScheduleNode(regPackId, fragmentId), scheduleIndex)
          if directWritePackIds(regPackId) => (regPackId, fragmentId, scheduleIndex)
    }
    scheduled.groupBy(_._1).flatMap { case (regPackId, entries) =>
      val ordered = entries.sortBy(_._3)
      val runs = ordered.foldLeft(Vector.empty[Vector[(Int, Int, Int)]]) {
        case (Vector(), entry) => Vector(Vector(entry))
        case (existing, entry) =>
          val previousRun = existing.last
          if (entry._3 == previousRun.last._3 + 1)
            existing.dropRight(1) :+ (previousRun :+ entry)
          else existing :+ Vector(entry)
      }
      runs.collect {
        case run if run.size >= 2 =>
          (regPackId, run.head._2) -> run.map(_._2).toVector
      }
    }
  }

  private val suppressedRegCommitFragments: Set[(Int, Int)] =
    coalescedRegCommitFragments.iterator.flatMap { case ((regPackId, _), fragmentIds) =>
      fragmentIds.drop(1).map(fragmentId => regPackId -> fragmentId)
    }.toSet

  private def emitRegView(view: SlpRegView): String = {
    val lane = view.lane
    val viewName = regViewNameByView(view)
    s"UInt<${lane.width}> $viewName = UInt<${lane.width}>(armor_slp::unpack_bits(" +
      s"${SlpRegStorageNames.state(view.regPackId)}, ${lane.offset}, ${lane.width}));"
  }

  def emitRegViews(): Vector[String] = plan.regViews.map(emitRegView)

  def regViewName(view: SlpRegView): String = regViewNameByView(view)

  /** Materialize a register lane immediately before its first emitted use.
    *
    * Renamer aliases are installed when the emitter is constructed, so the
    * generated lines contain the exact view names. Discovering uses from those
    * final lines avoids approximating liveness from graph edges and also covers
    * fallback statements and packed RegUpdate expressions.
    */
  def emitRegViewsUsedBy(lines: Vector[String]): Vector[String] = {
    val executableLines = lines.filterNot(_.trim.startsWith("//"))
    val usedNames = regViewByName.keySet.filter(name => executableLines.exists(_.contains(name)))
    plan.regViews.iterator.filter { view =>
      val name = regViewNameByView(view)
      usedNames(name) && !emittedRegViewNames(name)
    }.map { view =>
      val name = regViewNameByView(view)
      emittedRegViewNames += name
      emitRegView(view)
    }.toVector
  }

  private def emitRegUpdatePack(regPackId: Int, fragmentId: Int): Vector[String] = {
    if (suppressedRegCommitFragments((regPackId, fragmentId))) return Vector.empty
    val regPack = regPacking.flatMap(_.packs.find(_.id == regPackId)).getOrElse(
      throw new IllegalStateException(s"unknown packed RegUpdate $regPackId")
    )
    val emittedFragmentIds = coalescedRegCommitFragments.getOrElse(
      (regPackId, fragmentId), Vector(fragmentId)
    )
    val emittedLaneIndices = emittedFragmentIds.flatMap(regPack.fragment(_).laneIndices).distinct.sorted
    val fragmentLanes = emittedLaneIndices.map(regPack.lanes)
    val emittedMask = emittedFragmentIds.foldLeft(BigInt(0)) { (mask, id) =>
      mask | regPack.fragmentMask(id)
    }
    val directWrite = regPacking.toVector.flatMap(_.directWrites).find(_.regPackId == regPackId)
    val muxWrite = regPacking.toVector.flatMap(_.muxWrites).find(_.regPackId == regPackId)
    val lowered = directWrite match {
      case Some(write) =>
        val value = truncateWord(packName(write.sourcePackId), regPack.totalWidth, regPack.validMask)
        if (emittedLaneIndices == regPack.lanes.indices.toVector) {
          Vector(
            "if (update_registers) {",
            s"  ${SlpRegStorageNames.state(regPack.id)} = $value;",
            "}"
          )
        } else {
          val mask = s"UINT64_C(0x${emittedMask.toString(16)})"
          Vector(
            "if (update_registers) {",
            s"  ${SlpRegStorageNames.state(regPack.id)} = " +
              s"(${SlpRegStorageNames.state(regPack.id)} & ~$mask) | ($value & $mask);",
            "}"
          )
        }
      case None if muxWrite.nonEmpty =>
        val write = muxWrite.get
        require(
          emittedLaneIndices == regPack.lanes.indices.toVector,
          s"packed reset-Mux write $regPackId must commit all lanes together"
        )
        val value = truncateWord(
          s"(${scalarWord(write.conditionName)} ? UINT64_C(0) : ${packName(write.falseSourcePackId)})",
          regPack.totalWidth,
          regPack.validMask
        )
        Vector(
          "if (update_registers) {",
          s"  ${SlpRegStorageNames.state(regPack.id)} = $value;",
          "}"
        )
      case None =>
        require(
          emittedFragmentIds == Vector(fragmentId) && regPack.commitFragments.size == 1,
          s"non-direct packed RegUpdate $regPackId cannot have multiple commit fragments"
        )
        val nextName = SlpRegStorageNames.next(regPack.id)
        regWriteInputs.get(regPackId) match {
          case Some(input) =>
            Vector(
              "if (update_registers) {"
            ) ++ emitPackConstruction(
              nextName,
              composeInputConstruction(input.lanes, input.laneOffsets),
              indent = "  "
            ) ++ Vector(
              s"  ${SlpRegStorageNames.state(regPack.id)} = ${truncateWord(nextName, regPack.totalWidth, regPack.validMask)};",
              "}"
            )
          case None =>
            val nextWrites = regPack.lanes.map { lane =>
              val update = context.graph.node(lane.updateNodeId).statement.asInstanceOf[RegUpdate]
              val value = s"(${emitExpr(update.expr)}).as_single_word()"
              SlpPackWordWrite(value, lane.width, lane.offset)
            }
            Vector(
              "if (update_registers) {"
            ) ++ emitPackCallConstruction(nextName, nextWrites, indent = "  ") ++ Vector(
              s"  ${SlpRegStorageNames.state(regPack.id)} = ${truncateWord(nextName, regPack.totalWidth, regPack.validMask)};",
              "}"
            )
        }
    }
    val coalescingComment = Option.when(emittedFragmentIds.size > 1)(
      s"// coalesced RegUpdate fragments ${emittedFragmentIds.mkString(",")}"
    ).toVector
    lowered ++ coalescingComment ++ Vector(s"// ${regPack.discoveryPhase}") ++
      loweredStatementComments(regPack.lanes.map(_.updateNodeId))
  }

  private def laneSplatMultiplier(laneWidth: Int, laneCount: Int): BigInt = {
    require(laneWidth > 0)
    require(laneCount > 0)
    require(laneWidth * laneCount <= 64,
      s"lane splat exceeds one machine word: width=$laneWidth lanes=$laneCount")
    (0 until laneCount).foldLeft(BigInt(0)) { case (bits, lane) =>
      bits | (BigInt(1) << (lane * laneWidth))
    }
  }

  private def emitLaneSplatExpression(
    sourceExpr: String,
    laneWidth:  Int,
    laneCount:  Int
  ): String = {
    require(sourceExpr.nonEmpty)
    require(laneWidth > 0)
    require(laneCount > 0)
    require(laneWidth * laneCount <= 64,
      s"lane splat exceeds one machine word: width=$laneWidth lanes=$laneCount")

    val bounded = s"($sourceExpr & ${maskLiteral(laneWidth)})"
    if (laneCount == 1) bounded
    else s"($bounded * ${uint64Constant(laneSplatMultiplier(laneWidth, laneCount))})"
  }

  private def broadcastValueExpression(value: SlpBroadcastValue): String = value match {
    case SlpBroadcastSignal(name, _, _) => scalarWord(name)
    case SlpBroadcastConstant(value, _) => uint64Constant(value)
    case SlpBroadcastPacked(sourcePackId, _, _, _, offset) =>
      if (offset == 0) packName(sourcePackId) else s"(${packName(sourcePackId)} >> $offset)"
    case SlpBroadcastReg(regPackId, _, _, offset) =>
      val state = SlpRegStorageNames.state(regPackId)
      if (offset == 0) state else s"($state >> $offset)"
  }

  /** Materialize one value repeated in every lane of a packed operand. */
  private def broadcastPackedInput(input: SlpBroadcastInput): String = {
    val destination = plan.packGraph.pack(input.destinationPackId)
    val laneOperations = destination.nodeIds.map(operations)
    require(laneOperations.nonEmpty)
    val widths = laneOperations.map(_.operands(input.argumentIndex).width)
    require(widths.nonEmpty && widths.distinct.size == 1,
      s"broadcast input ${input.destinationPackId}:${input.argumentIndex} has non-uniform lane widths")
    val width = widths.head
    require(width == input.value.width,
      s"broadcast input ${input.destinationPackId}:${input.argumentIndex} has width $width, " +
        s"but value width is ${input.value.width}")
    val totalWidth = widths.sum
    require(totalWidth <= 64,
      s"broadcast input ${input.destinationPackId}:${input.argumentIndex} exceeds one machine word")

    emitLaneSplatExpression(broadcastValueExpression(input.value), width, widths.size)
  }

  private def packedInput(packId: Int, argumentIndex: Int): String =
    directInputs.get((packId, argumentIndex)) match {
      case Some(input) => packName(input.sourcePackId)
      case None => directRegInputs.get((packId, argumentIndex)) match {
        case Some(input) => SlpRegStorageNames.state(input.regPackId)
        case None => broadcastInputs.get((packId, argumentIndex)) match {
          case Some(input) => broadcastPackedInput(input)
          case None => scalarInputs.get((packId, argumentIndex)) match {
              case Some(alignment) => materializedAlignmentName(alignment.id)
              case None => throw new IllegalStateException(
                s"missing SLP input for pack $packId argument $argumentIndex"
              )
          }
        }
      }
    }

  private def packedArgument(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation],
    argumentIndex:  Int
  ): String = {
    val operands = laneOperations.map(_.operands(argumentIndex))
    if (operands.forall(_.isInstanceOf[SlpUIntConstant])) {
      val offsets = operands.map(_.width).scanLeft(0)(_ + _).dropRight(1)
      require(operands.map(_.width).sum <= 64,
        s"constant argument $argumentIndex of pack ${pack.id} exceeds uint64_t")
      val value = operands.zip(offsets).foldLeft(BigInt(0)) {
        case (bits, (constant: SlpUIntConstant, offset)) =>
          val mask = (BigInt(1) << constant.width) - 1
          bits | ((constant.value & mask) << offset)
        case (bits, _) => bits
      }
      s"UINT64_C(0x${value.toString(16)})"
    } else packedInput(pack.id, argumentIndex)
  }

  private def maskLiteral(width: Int, offset: Int = 0): String = {
    require(width > 0 && width <= 64, s"invalid SLP mask width $width")
    require(offset >= 0 && offset + width <= 64,
      s"invalid SLP mask range offset=$offset width=$width")
    val value = ((BigInt(1) << width) - 1) << offset
    s"UINT64_C(0x${value.toString(16)})"
  }

  private def isPowerOfTwo(width: Int): Boolean =
    width > 0 && (width & (width - 1)) == 0

  private def scalarWord(name: String): String = s"${rn.emit(name)}.as_single_word()"

  private def composeInputConstruction(
    lanes:       Vector[SlpPackInputLane],
    laneOffsets: Vector[Int]
  ): SlpPackWordConstruction = {
    val scalarWrites = lanes.zip(laneOffsets).collect {
      case (lane: SlpConstantInputLane, offset) =>
        SlpPackWordWrite(uint64Constant(lane.value), lane.width, offset)
      case (lane: SlpScalarInputLane, offset) =>
        SlpPackWordWrite(scalarWord(lane.signalName), lane.width, offset)
    }

    val packedTerms = composeInputTerms(lanes, laneOffsets, includeScalarConstants = false)

    SlpPackWordConstruction(packedTerms, scalarWrites)
  }

  private def emitPackCallConstruction(
    resultName: String,
    writes:     Seq[SlpPackWordWrite],
    indent:     String = ""
  ): Vector[String] =
    emitPackConstruction(resultName, SlpPackWordConstruction(Vector.empty, writes.toVector), indent)

  private def emitPackConstruction(
    resultName:    String,
    construction:  SlpPackWordConstruction,
    indent:        String = ""
  ): Vector[String] = {
    val init = construction.terms.headOption match {
      case Some(first) =>
        Vector(s"${indent}uint64_t $resultName = $first;") ++
          construction.terms.tail.map(term => s"${indent}$resultName |= $term;")
      case None =>
        Vector(s"${indent}uint64_t $resultName = UINT64_C(0);")
    }
    init ++ construction.writes.map { write =>
      s"${indent}armor_slp::pack_bits($resultName, ${write.valueExpr}, ${write.offset}, ${write.width});"
    }
  }

  private def composeInputTerms(
    lanes:       Vector[SlpPackInputLane],
    laneOffsets: Vector[Int],
    includeScalarConstants: Boolean = true
  ): Vector[String] = {
    var constantBits = BigInt(0)
    lanes.zip(laneOffsets).foreach {
      case (lane: SlpConstantInputLane, offset) =>
        if (includeScalarConstants) {
          val mask = (BigInt(1) << lane.width) - 1
          constantBits |= (lane.value & mask) << offset
        }
      case _ =>
    }

    def sameScalarRun(left: SlpScalarInputLane, right: SlpScalarInputLane): Boolean =
      left.signalName == right.signalName && left.width == right.width &&
        left.producerNodeId == right.producerNodeId &&
        right.destinationLane == left.destinationLane + 1

    val scalarRuns = Vector.newBuilder[Vector[SlpScalarInputLane]]
    var scalarRun = Vector.empty[SlpScalarInputLane]
    def flushScalar(): Unit = if (scalarRun.nonEmpty) {
      scalarRuns += scalarRun
      scalarRun = Vector.empty
    }
    lanes.foreach {
      case lane: SlpScalarInputLane if includeScalarConstants =>
        if (scalarRun.nonEmpty && !sameScalarRun(scalarRun.last, lane)) flushScalar()
        scalarRun :+= lane
      case _ => flushScalar()
    }
    flushScalar()

    val scalarTerms = scalarRuns.result().map { run =>
      val lane = run.head
      val source = emitLaneSplatExpression(scalarWord(lane.signalName), lane.width, run.size)
      val offset = laneOffsets(lane.destinationLane)
      if (offset == 0) source else s"($source << $offset)"
    }

    def samePackedRun(left: SlpPackInputLane, right: SlpPackInputLane): Boolean = (left, right) match {
      case (a: SlpUnpackedInputLane, b: SlpUnpackedInputLane) =>
        a.sourcePackId == b.sourcePackId && a.segmentAlignmentId == b.segmentAlignmentId &&
          b.sourceLaneIndex == a.sourceLaneIndex + 1 && b.destinationLane == a.destinationLane + 1
      case (a: SlpRegInputLane, b: SlpRegInputLane) =>
        a.regPackId == b.regPackId && a.segmentAlignmentId == b.segmentAlignmentId &&
          b.sourceLaneIndex == a.sourceLaneIndex + 1 && b.destinationLane == a.destinationLane + 1
      case _ => false
    }

    def samePackedLane(left: SlpPackInputLane, right: SlpPackInputLane): Boolean = (left, right) match {
      case (a: SlpUnpackedInputLane, b: SlpUnpackedInputLane) =>
        a.sourcePackId == b.sourcePackId && a.sourceLaneIndex == b.sourceLaneIndex &&
          a.sourceNodeId == b.sourceNodeId && a.width == b.width &&
          a.segmentAlignmentId == b.segmentAlignmentId &&
          b.destinationLane == a.destinationLane + 1
      case (a: SlpRegInputLane, b: SlpRegInputLane) =>
        a.regPackId == b.regPackId && a.sourceLaneIndex == b.sourceLaneIndex &&
          a.registerName == b.registerName && a.width == b.width &&
          a.segmentAlignmentId == b.segmentAlignmentId &&
          b.destinationLane == a.destinationLane + 1
      case _ => false
    }

    def canAppendPacked(run: Vector[SlpPackInputLane], lane: SlpPackInputLane): Boolean = {
      require(run.nonEmpty)
      if (run.size == 1) samePackedRun(run.last, lane) || samePackedLane(run.last, lane)
      else if (samePackedLane(run(0), run(1))) samePackedLane(run.last, lane)
      else samePackedRun(run.last, lane)
    }

    val packedRuns = Vector.newBuilder[Vector[SlpPackInputLane]]
    var current = Vector.empty[SlpPackInputLane]
    def flush(): Unit = if (current.nonEmpty) {
      packedRuns += current
      current = Vector.empty
    }
    lanes.foreach {
      case lane: SlpUnpackedInputLane =>
        if (current.nonEmpty && !canAppendPacked(current, lane)) flush()
        current :+= lane
      case lane: SlpRegInputLane =>
        if (current.nonEmpty && !canAppendPacked(current, lane)) flush()
        current :+= lane
      case _ => flush()
    }
    flush()

    val packedTerms = packedRuns.result().map { run =>
      val source = run.head match {
        case lane: SlpUnpackedInputLane =>
          lane.segmentAlignmentId.map(alignmentName).getOrElse(packName(lane.sourcePackId))
        case lane: SlpRegInputLane =>
          lane.segmentAlignmentId.map(alignmentName)
            .getOrElse(SlpRegStorageNames.state(lane.regPackId))
        case other => throw new IllegalStateException(s"invalid packed input run: $other")
      }
      val repeatedLane = run.size > 1 && samePackedLane(run(0), run(1))
      val value = if (!repeatedLane) source else {
        val width = run.head.width
        require(run.forall(_.width == width))
        val sourceMask = (BigInt(1) << width) - 1
        val extracted = s"($source & UINT64_C(0x${sourceMask.toString(16)}))"
        if (width == 1) {
          val destinationMask = (BigInt(1) << run.size) - 1
          s"((UINT64_C(0) - $extracted) & UINT64_C(0x${destinationMask.toString(16)}))"
        } else {
          val replicationMask = (0 until run.size).foldLeft(BigInt(0)) { case (mask, index) =>
            mask | (BigInt(1) << (index * width))
          }
          s"($extracted * UINT64_C(0x${replicationMask.toString(16)}))"
        }
      }
      val offset = laneOffsets(run.head.destinationLane)
      if (offset == 0) value else s"($value << $offset)"
    }

    val constantTerms = if (constantBits == 0) Vector.empty else Vector(uint64Constant(constantBits))
    constantTerms ++ scalarTerms ++ packedTerms
  }

  /** Emit a packed concatenation without constructing one unbounded C++ OR
    * expression.  Keeping one source term per statement makes large
    * pack-to-pack gathers readable while preserving the exact operations and
    * evaluation order selected by the alignment planner.
    */
  private def emitPackWordConstruction(
    resultName: String,
    terms:      Vector[String],
    indent:     String = ""
  ): Vector[String] =
    terms.headOption match {
      case Some(first) =>
        Vector(s"${indent}uint64_t $resultName = $first;") ++
          terms.tail.map(term => s"${indent}$resultName |= $term;")
      case None => Vector(s"${indent}uint64_t $resultName = UINT64_C(0);")
    }

  private def emitOrAccumulation(resultName: String, terms: Vector[String]): Vector[String] =
    emitPackWordConstruction(resultName, terms)

  private def emitBitRange(source: String, sourceBitOffset: Int, width: Int, sourceWidth: Int): String = {
    require(source.nonEmpty)
    require(sourceBitOffset >= 0)
    require(width > 0 && width <= 64)
    require(sourceWidth > 0 && sourceWidth <= 64)
    require(sourceBitOffset + width <= sourceWidth)
    if (sourceBitOffset == 0 && width == sourceWidth) source
    else {
      val shifted = if (sourceBitOffset == 0) source else s"($source >> $sourceBitOffset)"
      if (width == 64) shifted else s"($shifted & ${maskLiteral(width)})"
    }
  }

  private def projectionSourceExpression(source: SlpProjectionSource): String = source match {
    case SlpProjectionCombPack(packId)       => packName(packId)
    case SlpProjectionRegPack(regPackId)     => SlpRegStorageNames.state(regPackId)
    case SlpProjectionAlignment(alignmentId) => materializedAlignmentName(alignmentId)
    case SlpProjectionConstant(value)        => uint64Constant(value)
  }

  private def projectionCseName(entry: SlpProjectionCseEntry): String =
    entry.firstUser match {
      case _: SlpAlignmentProjectionCseUser => s"_armor_slp_projection_cse_${entry.id}"
      case _: SlpPackProjectionCseUser      => s"_armor_slp_pack_projection_cse_${entry.id}"
    }

  private def lowerAlignmentProjectionTerm(term: SlpAlignmentProjectionTerm): String =
    lowerBitMapping(projectionSourceExpression(term.source), term.bitMapping).getOrElse(
      throw new IllegalStateException(
        s"alignment projection term has non-lowerable bit mapping"
      )
    )

  private def lowerPackProjectionTerm(projection: SlpPackProjection): String =
    lowerBitMapping(projectionSourceExpression(projection.source), projection.bitMapping).getOrElse(
      throw new IllegalStateException(
        s"pack projection ${projection.destinationPackId}:${projection.argumentIndex} has non-lowerable bit mapping"
      )
    )

  private def alignmentProjectionTerms(
    alignmentId: Int,
    projection:  SlpAlignmentProjection
  ): Vector[String] =
    projection.terms.zipWithIndex.map { case (term, termIndex) =>
      projectionCsePlan.alignmentUsers.get(alignmentId -> termIndex)
        .map(projectionCseName)
        .getOrElse(lowerAlignmentProjectionTerm(term))
    }

  private def alignmentProjectionCsePrelude(alignmentId: Int): Vector[String] =
    projectionCsePlan.firstAlignmentUsers.getOrElse(alignmentId, Vector.empty).map { entry =>
      val expression = entry.firstUser match {
        case user: SlpAlignmentProjectionCseUser =>
          val term = alignmentProjectionsById(user.alignmentId).terms(user.termIndex)
          lowerAlignmentProjectionTerm(term)
        case other =>
          throw new IllegalStateException(s"unexpected projection CSE first user $other for alignment $alignmentId")
      }
      s"uint64_t ${projectionCseName(entry)} = $expression;"
    }

  private def packProjectionTerm(
    packId:     Int,
    projection: SlpPackProjection
  ): String =
    projectionCsePlan.packUsers.get(packId -> projection.argumentIndex)
      .map(projectionCseName)
      .getOrElse(lowerPackProjectionTerm(projection))

  private def packProjectionCsePrelude(packId: Int): Vector[String] =
    projectionCsePlan.firstPackUsers.getOrElse(packId, Vector.empty).map { entry =>
      val expression = entry.firstUser match {
        case user: SlpPackProjectionCseUser =>
          val projection = projectionsByPackId.getOrElse(user.packId, Vector.empty)
            .find(_.argumentIndex == user.argumentIndex)
            .getOrElse(throw new IllegalStateException(
              s"missing pack projection ${user.packId}:${user.argumentIndex}"
            ))
          lowerPackProjectionTerm(projection)
        case other =>
          throw new IllegalStateException(s"unexpected projection CSE first user $other for pack $packId")
      }
      s"uint64_t ${projectionCseName(entry)} = $expression;"
    }

  private def segmentReuseTerms(
    alignment: SlpScalarToPackAlignment,
    reuses:    Vector[SlpAlignmentSegmentReuse]
  ): Vector[String] = {
    require(reuses.forall(_.destinationAlignmentId == alignment.id))
    reuses.sortBy(_.destinationLaneBegin).map { reuse =>
      val source = materializedAlignmentName(reuse.sourceAlignmentId)
      val sourceWidth = alignmentSignaturesById(reuse.sourceAlignmentId).lanes.map(_.width).sum
      val extracted = emitBitRange(source, reuse.sourceBitOffset, reuse.width, sourceWidth)
      if (reuse.destinationBitOffset == 0) extracted
      else s"($extracted << ${reuse.destinationBitOffset})"
    }
  }

  private def emitOptimizedAlignment(
    alignment: SlpScalarToPackAlignment
  ): Option[Vector[String]] = {
    val projectionTerms = alignmentProjectionsById.get(alignment.id).toVector
      .flatMap(alignmentProjectionTerms(alignment.id, _))
    val reuseTerms = segmentReuseTerms(alignment, effectiveSegmentReuses(alignment))
    if (projectionTerms.isEmpty && reuseTerms.isEmpty) None
    else Some(alignmentProjectionCsePrelude(alignment.id) ++ emitOrAccumulation(
      alignmentName(alignment.id),
      projectionTerms ++ reuseTerms ++ composeInputTerms(uncoveredAlignmentLanes(alignment), alignment.laneOffsets)
    ))
  }

  /** A one-bit scalar alignment can be rebuilt directly from one source word
    * when every lane is an ArmorBitSelect of a distinct bit of that word.
    * The pack destination order does not have to match source bit order; the
    * lowering records source-bit to destination-bit moves and composes them
    * as contiguous shift/mask runs.
    */
  private final case class SlpBitSliceGatherGroup(
    sourceName:             String,
    sourceWidth:            Int,
    bitMoves:               Vector[(Int, Int)]
  ) {
    require(sourceName.nonEmpty)
    require(sourceWidth > 0 && sourceWidth <= 64)
    require(bitMoves.nonEmpty)
    require(bitMoves.map(_._1).distinct.size == bitMoves.size)
    require(bitMoves.map(_._2).distinct.size == bitMoves.size)
    require(bitMoves.forall { case (sourceBit, destinationBit) =>
      sourceBit >= 0 && sourceBit < sourceWidth && destinationBit >= 0 && destinationBit < 64
    })
  }

  private final case class SlpBitSliceGather(
    groups:                 Vector[SlpBitSliceGatherGroup],
    producerNodeIds:        Vector[Int],
    coveredConsumerNodeIds: Vector[Int]
  ) {
    require(groups.nonEmpty)
    require(groups.flatMap(_.bitMoves.map(_._2)).distinct.size == groups.map(_.bitMoves.size).sum)
    require(producerNodeIds.size == groups.map(_.bitMoves.size).sum)
    require(coveredConsumerNodeIds.size == groups.map(_.bitMoves.size).sum)
    require(producerNodeIds.forall(_ >= 0))
    require(coveredConsumerNodeIds.forall(_ >= 0))
  }

  private def bitSliceGatherFor(alignment: SlpScalarToPackAlignment): Option[SlpBitSliceGather] = {
    if (alignment.lanes.exists(_.width != 1)) None
    else {
      val destinationPack = plan.packGraph.pack(alignment.destinationPackId)
      val selections = alignment.lanes.zip(alignment.laneOffsets).map {
        case (SlpScalarInputLane(destinationLane, _, 1, Some(producerNodeId)), destinationOffset) =>
          destinationPack.nodeIds.lift(destinationLane).flatMap { consumerNodeId =>
            operations.get(producerNodeId).collect {
              case SlpOperation(
                    SlpBitSelect, 1, _, Vector(SlpSignal(sourceName, sourceWidth)),
                    Vector(bitPosition), _
                  )
                  if sourceWidth <= 64 && bitPosition >= 0 && bitPosition < sourceWidth &&
                    destinationOffset >= 0 && destinationOffset < 64 =>
                (sourceName, sourceWidth, bitPosition.toInt, destinationOffset,
                  producerNodeId, consumerNodeId)
            }
          }
        case _ => None
      }
      if (selections.exists(_.isEmpty)) None
      else {
        val values = selections.flatten
        val producerNodeIds = values.map(_._5)
        val coveredConsumerNodeIds = values.map(_._6)
        val destinationBits = values.map(_._4)
        val groupKeys = values.map { case (sourceName, sourceWidth, _, _, _, _) =>
          sourceName -> sourceWidth
        }.distinct
        val groups = groupKeys.map { case (sourceName, sourceWidth) =>
          val bitMoves = values.collect {
            case (`sourceName`, `sourceWidth`, bitPosition, destinationOffset, _, _) =>
              bitPosition -> destinationOffset
          }
          (sourceName, sourceWidth, bitMoves)
        }
        if (destinationBits.distinct.size != destinationBits.size ||
            groups.exists { case (_, _, bitMoves) =>
              bitMoves.map(_._1).distinct.size != bitMoves.size ||
                bitMoves.map(_._2).distinct.size != bitMoves.size
            }) None
        else {
          val hasUsefulMultiSourceRun =
            groups.size == 1 || groups.exists { case (_, _, bitMoves) =>
              buildBitMoveRuns(bitMoves).exists(_.width > 1)
            }
          if (!hasUsefulMultiSourceRun) None
          else {
            val gatherGroups = groups.map { case (sourceName, sourceWidth, bitMoves) =>
              SlpBitSliceGatherGroup(sourceName, sourceWidth, bitMoves)
            }
            Some(SlpBitSliceGather(gatherGroups, producerNodeIds, coveredConsumerNodeIds))
          }
        }
      }
    }
  }

  private lazy val emittedBitSliceGathersByAlignmentId: Map[Int, SlpBitSliceGather] =
    alignmentEmissionPlan.entries.iterator.collect {
      case (id, MaterializeAlignment(BitSliceAlignment(gather))) => id -> gather
    }.toMap

  private lazy val bitMoveGatherCoveredConsumerPairs: Set[(Int, Int)] =
    emittedBitSliceGathersByAlignmentId.valuesIterator.flatMap { gather =>
      gather.producerNodeIds.zip(gather.coveredConsumerNodeIds)
    }.toSet

  private lazy val suppressedBitMoveGatherProducerNodeIds: Set[Int] =
    emittedBitSliceGathersByAlignmentId.valuesIterator.flatMap(_.producerNodeIds).toSet.filter { producerNodeId =>
      val coveredConsumers = bitMoveGatherCoveredConsumerPairs.collect {
        case (`producerNodeId`, consumerNodeId) => consumerNodeId
      }
      val fanouts = context.graph.validFanoutIds(producerNodeId).toSet
      fanouts.nonEmpty && fanouts.subsetOf(coveredConsumers)
    }

  private sealed trait SlpRepeatedBitRunSource
  private final case class SlpRepeatedBitRunSignal(
    signalName:     String,
    producerNodeId: Option[Int]
  ) extends SlpRepeatedBitRunSource {
    require(signalName.nonEmpty)
    require(producerNodeId.forall(_ >= 0))
  }
  private final case class SlpRepeatedBitRunConstant(value: BigInt)
      extends SlpRepeatedBitRunSource {
    require(value == 0 || value == 1)
  }

  private final case class SlpRepeatedBitRun(
    source: SlpRepeatedBitRunSource,
    destLo: Int,
    width:  Int
  ) {
    require(destLo >= 0)
    require(width > 0)
    require(destLo + width <= 64)
  }

  private def repeatedBitRunFor(alignment: SlpScalarToPackAlignment): Option[Vector[SlpRepeatedBitRun]] = {
    if (alignment.lanes.exists(_.width != 1) || alignment.laneOffsets.lastOption.exists(_ >= 64)) None
    else {
      val sources = alignment.lanes.zip(alignment.laneOffsets).map {
        case (SlpScalarInputLane(_, signalName, 1, producerNodeId), offset) =>
          Some(offset -> SlpRepeatedBitRunSignal(signalName, producerNodeId))
        case (SlpConstantInputLane(_, value, 1), offset) =>
          Some(offset -> SlpRepeatedBitRunConstant(value & BigInt(1)))
        case _ => None
      }
      if (sources.exists(_.isEmpty)) None
      else {
        val sorted = sources.flatten.sortBy(_._1)
        val destinationBits = sorted.map(_._1)
        if (destinationBits.distinct.size != destinationBits.size) None
        else {
          val runs = sorted.tail.foldLeft(Vector(SlpRepeatedBitRun(sorted.head._2, sorted.head._1, 1))) {
            case (acc, (offset, source)) =>
              val last = acc.last
              if (source == last.source && offset == last.destLo + last.width) {
                acc.dropRight(1) :+ last.copy(width = last.width + 1)
              } else {
                acc :+ SlpRepeatedBitRun(source, offset, 1)
              }
          }
          if (runs.exists(run => run.width > 1 && run.source.isInstanceOf[SlpRepeatedBitRunSignal]))
            Some(runs)
          else None
        }
      }
    }
  }

  private def emitRepeatedBitRunTerm(run: SlpRepeatedBitRun): Option[String] = run.source match {
    case SlpRepeatedBitRunSignal(signalName, _) =>
      val bit = s"(${scalarWord(signalName)} & UINT64_C(0x1))"
      val repeated = s"((UINT64_C(0) - $bit) & ${maskLiteral(run.width)})"
      Some(if (run.destLo == 0) repeated else s"($repeated << ${run.destLo})")
    case SlpRepeatedBitRunConstant(value) =>
      if (value == 0) None
      else {
        val literal = maskLiteral(run.width, run.destLo)
        Some(literal)
      }
  }

  private def emitScalarToPack(alignment: SlpScalarToPackAlignment): Vector[String] = {
    alignmentEmissionPlan.entries(alignment.id) match {
      case BypassAlignment(_) | ReuseAlignment(_, _) => return Vector.empty
      case MaterializeAlignment(BitSliceAlignment(gather)) =>
        val resultName = alignmentName(alignment.id)
        val sourceLines = gather.groups.zipWithIndex.map { case (group, index) =>
          val sourceName =
            if (gather.groups.size == 1) s"${resultName}_bitselect_src"
            else s"${resultName}_bitselect_src_$index"
          sourceName -> s"uint64_t $sourceName = ${scalarWord(group.sourceName)};"
        }
        val terms = gather.groups.zip(sourceLines).map { case (group, (sourceName, _)) =>
          s"(${emitBitMoveComposition(sourceName, group.bitMoves)})"
        }
        return sourceLines.map(_._2) ++ emitOrAccumulation(resultName, terms)
      case MaterializeAlignment(SparseAlignment(gather)) =>
        val terms = gather.signature.terms.map { term =>
          val source = term.source match {
            case SlpCombSegmentSource(sourcePackId) => packName(sourcePackId)
            case SlpRegSegmentSource(regPackId)      => SlpRegStorageNames.state(regPackId)
          }
          val extracted = emitPext(source, term.sourceMask)
          if (term.destinationOffset == 0) extracted
          else s"($extracted << ${term.destinationOffset})"
        }
        return emitOrAccumulation(alignmentName(alignment.id), terms)
      case EmitFusedPack(pack) =>
        require(alignment.lanes.size == pack.lanes.size)
        val resultName = packName(pack.id)
        val writes = alignment.lanes.zip(pack.outputOffsets).zip(pack.lanes).map {
          case ((lane: SlpConstantInputLane, offset), packedLane) =>
            SlpPackWordWrite(uint64Constant(lane.value), packedLane.resultWidth, offset)
          case ((lane: SlpScalarInputLane, offset), packedLane) =>
            SlpPackWordWrite(scalarWord(lane.signalName), packedLane.resultWidth, offset)
          case ((lane, _), _) =>
            throw new IllegalStateException(s"unsupported fused masked-And input lane: $lane")
        }
        return emitPackCallConstruction(resultName, writes)
      case MaterializeAlignment(OrdinaryAlignment) =>
    }

    emitOptimizedAlignment(alignment).foreach(result => return result)

    val resultName = alignmentName(alignment.id)
    repeatedBitRunFor(alignment).foreach { runs =>
      val terms = runs.flatMap(emitRepeatedBitRunTerm)
      return emitOrAccumulation(resultName, terms)
    }

    // Preserve the normal scalar-to-pack alignment identity for repeated
    // multi-bit values.  This lets projection lowering (notably Cat) place
    // the materialized value with PDEP instead of falling back to per-lane
    // unpack/cat/pack.  The multiplication is carry-safe because the source
    // is bounded to one lane before being copied to each lane start.
    val replicatedScalar = alignment.lanes match {
      case lanes if lanes.size >= 2 && lanes.head.width >= 2 && lanes.head.width <= 63 &&
          lanes.map(_.width).distinct.size == 1 &&
          lanes.map(_.width).sum <= 64 && lanes.forall {
            case SlpScalarInputLane(_, name, width, producer) =>
              lanes.head match {
                case SlpScalarInputLane(_, firstName, firstWidth, firstProducer) =>
                  name == firstName && width == firstWidth && producer == firstProducer
                case _ => false
              }
            case _ => false
          } =>
        val first = lanes.head.asInstanceOf[SlpScalarInputLane]
        val laneWidth = first.width
        Some(emitLaneSplatExpression(scalarWord(first.signalName), laneWidth, lanes.size))
      case _ => None
    }
    replicatedScalar.foreach { expression =>
      return Vector(s"uint64_t $resultName = $expression;")
    }
    emitPackConstruction(resultName, composeInputConstruction(alignment.lanes, alignment.laneOffsets))
  }

  private def emitPackSegment(alignment: SlpPackSegmentAlignment): Vector[String] = {
    if (deadSegmentAlignmentIds(alignment.id)) return Vector.empty
    val source = alignment.source match {
      case SlpCombSegmentSource(sourcePackId) => packName(sourcePackId)
      case SlpRegSegmentSource(regPackId)      => SlpRegStorageNames.state(regPackId)
    }
    Vector(
      s"uint64_t ${alignmentName(alignment.id)} = armor_slp::unpack_bits(" +
        s"$source, ${alignment.sourceBitOffset}, ${alignment.width});"
    )
  }

  /** Rebuild a cheap scalar projection from its still-materialized scalar
    * source instead of round-tripping through a pack.  A ScalarInputLane is
    * the align planner's proof that the source is not owned by another pack;
    * packed and register inputs deliberately fall back to unpack_bits.
    */
  private def rematerializeScalarLane(
    sourcePack: SlpPack,
    lane:       SlpMaterializedLane
  ): Option[String] = {
    val operation = operations(sourcePack.nodeIds(lane.sourceLaneIndex))
    val canRebuild = operation.opcode match {
      case SlpMove | SlpMaskedAnd | SlpBitSelect | SlpShlConst(_) | SlpShrConst(_) => true
      case _                                                       => false
    }
    if (!canRebuild) return None

    val scalarSource = scalarInputs.get((sourcePack.id, 0)).flatMap { alignment =>
      alignment.lanes.lift(lane.sourceLaneIndex).collect {
        case input: SlpScalarInputLane => input
      }
    }
    val sourceMatches = scalarSource.exists { input =>
      operation.operands.headOption.contains(SlpSignal(input.signalName, input.width))
    }
    if (!sourceMatches) None
    else emitStmt(operation.statement).headOption
  }

  private def emitPackToScalar(alignment: SlpPackToScalarAlignment): Vector[String] = {
    val sourceName = packName(alignment.sourcePackId)
    val sourcePack = plan.packGraph.pack(alignment.sourcePackId)
    alignment.lanes.filterNot { lane =>
      suppressedPackedSideEffectSourceNodeIds(lane.sourceNodeId) ||
        suppressedPackedMemWriteSourceNodeIds(lane.sourceNodeId) ||
        suppressedScalarProjectionLeafNodeIds(lane.sourceNodeId) ||
        suppressedScalarReductionLeafNodeIds(lane.sourceNodeId) ||
        suppressedLaneBitwiseReductionLeafNodeIds(lane.sourceNodeId)
    }.map { lane =>
      rematerializeScalarLane(sourcePack, lane).getOrElse {
        val outputName = rn.emit(lane.outputName)
        val rhs = s"UInt<${lane.width}>(armor_slp::unpack_bits(" +
          s"$sourceName, ${sourcePack.outputOffsets(lane.sourceLaneIndex)}, ${lane.width}))"
        if (rn.decLocal(lane.outputName)) s"UInt<${lane.width}> $outputName = $rhs;"
        else s"$outputName = $rhs;"
      }
    }
  }

  /** Emit a scalar Cat-tree view directly from its source pack.  A zero-offset
    * full-width view is just a UInt construction; a proper contiguous slice
    * keeps one ordinary unpack_bits operation rather than rebuilding every
    * leaf lane. */
  private def emitScalarProjection(projection: SlpScalarPackProjection): Vector[String] = {
    val source = packName(projection.sourcePackId)
    val sourcePack = plan.packGraph.pack(projection.sourcePackId)
    val word = if (projection.sourceBitOffset == 0 &&
        projection.resultWidth == sourcePack.totalResultWidth) source
      else s"armor_slp::unpack_bits($source, ${projection.sourceBitOffset}, ${projection.resultWidth})"
    val rhs = s"UInt<${projection.resultWidth}>($word)"
    emitStmtWithRhs(context.graph.node(projection.rootNodeId).statement, rhs).toVector ++
      scalarProjectionComments(projection.internalCatNodeIds, projection.rootNodeId)
  }

  /** Lower a scalar UInt<1> And/Or tree as tests over the packed source
    * masks.  The masks make sparse lanes and non-full-width packs safe: no
    * inactive high bit can affect the scalar reduction. */
  private def emitScalarReductionProjection(
    projection: SlpPackReductionProjection
  ): Vector[String] = {
    def packTerm(source: SlpPackReductionSource): String = {
      val pack = plan.packGraph.pack(source.packId)
      val fullMask = (BigInt(1) << pack.totalResultWidth) - 1
      val name = packName(source.packId)
      if (source.mask == fullMask && pack.totalResultWidth == 64) name
      else s"($name & ${uint64Constant(source.mask)})"
    }
    val scalarWords = projection.scalarLeafNodeIds.map { nodeId =>
      s"${rn.emit(context.graph.node(nodeId).name)}.as_single_word()"
    }
    val rhs = projection.kind match {
      case SlpOrReduction =>
        val terms = scalarWords ++ projection.packedSources.map(packTerm)
        s"UInt<1>((${terms.mkString(" | ")}) != UINT64_C(0))"
      case SlpAndReduction =>
        val scalarTests = scalarWords.map(word => s"($word != UINT64_C(0))")
        val packedTests = projection.packedSources.map { source =>
          val term = packTerm(source)
          s"($term == ${uint64Constant(source.mask)})"
        }
        s"UInt<1>(${(scalarTests ++ packedTests).mkString(" && ")})"
    }
    emitStmtWithRhs(context.graph.node(projection.rootNodeId).statement, rhs).toVector ++
      scalarProjectionComments(projection.internalReductionNodeIds, projection.rootNodeId)
  }

  /** Reduce equal-width contiguous pack lanes into the low lane with a binary
    * tree of word shifts.  The planner proves every leaf is private to this
    * final reduction, so no scalar prefix view is required. */
  private def emitLaneBitwiseReductionProjection(
    projection: SlpLaneBitwiseReductionProjection
  ): Vector[String] = {
    val sourcePack = plan.packGraph.pack(projection.sourcePackId)
    val reducedName = s"_armor_slp_lane_reduce_${projection.rootNodeId}"
    val totalWidth = projection.laneWidth * projection.laneCount
    val source = if (projection.sourceBitOffset == 0 && totalWidth == sourcePack.totalResultWidth)
      packName(projection.sourcePackId)
    else s"armor_slp::unpack_bits(${packName(projection.sourcePackId)}, " +
      s"${projection.sourceBitOffset}, $totalWidth)"
    val shifts = Iterator.iterate(projection.laneWidth)(_ * 2)
      .takeWhile(_ < totalWidth).toVector
    val lowering = Vector(s"uint64_t $reducedName = $source;") ++ shifts.map { shift =>
      s"$reducedName ${projection.kind.assignmentOperator} $reducedName >> $shift;"
    }
    val reducedValue = projection.scalarSeedNodeId match {
      case Some(seedNodeId) =>
        s"($reducedName ${projection.kind.binaryOperator} " +
          s"${scalarWord(context.graph.node(seedNodeId).name)})"
      case None => reducedName
    }
    val rhs = s"UInt<${projection.laneWidth}>($reducedValue)"
    lowering ++ emitStmtWithRhs(context.graph.node(projection.rootNodeId).statement, rhs).toVector ++
      scalarProjectionComments(projection.internalNodeIds, projection.rootNodeId)
  }

  private def uint64Constant(value: BigInt): String =
    s"UINT64_C(0x${value.toString(16)})"

  private def emitPext(input: String, mask: BigInt): String =
    CppBitUtils.emitPext(input, mask)

  private def emitPrintfCall(print: Print): String = {
    val formatters = "(%h)|(%x)|(%d)|(%ld)".r.findAllIn(print.string.serialize).toList
    val argWidths = print.args.map(arg => bitWidth(arg.tpe))
    if (!(argWidths forall { _ <= 64 })) throw new Exception("Can't print wide signals")
    val replacements = formatters zip argWidths map { case (format, width) =>
      if (format == "%h" || format == "%x") {
        val printWidth = math.ceil(width.toDouble / 4).toInt
        (format, s"""%0${printWidth}" PRIx64 """)
      } else {
        val printWidth = math.ceil(math.log10((1L << width.toInt).toDouble)).toInt
        (format, s"""%${printWidth}" PRIu64 """)
      }
    }
    val formatString = replacements.foldLeft(print.string.serialize) {
      case (text, (searchFor, replaceWith)) => text.replaceFirst(searchFor, replaceWith)
    }
    val arguments = Seq(s"\"$formatString\"") ++
      print.args.map(arg => s"${emitExprWrap(arg)}.as_single_word()")
    s"printf(${arguments.mkString(", ")});"
  }

  private def emitPackedSideEffectGroup(group: SlpPackedSideEffectGroup): Vector[String] = {
    val pack = packName(group.sourcePackId)
    val mask = uint64Constant(group.activeMask)
    val activeName = s"_armor_slp_side_effect_${group.members.head.nodeId}"
    group match {
      case printGroup: SlpPackedPrintGroup =>
        val prints = printGroup.members.map(_.statement.asInstanceOf[Print])
        val identicalOutput = prints.tail.forall { print =>
          print.string == prints.head.string && print.args == prints.head.args
        }
        if (identicalOutput) {
          // A group with identical messages and arguments has no lane-specific
          // observable output.  Coalesce simultaneous assertions to one line.
          Vector(
            s"// SLP coalesced Print conditions (${printGroup.members.size} lanes)",
            s"if (UNLIKELY(done_reset && update_registers && verbose && ($pack & $mask))) {",
            s"  ${emitPrintfCall(prints.head)}",
            "}"
          )
        } else {
          Vector(
            s"// SLP packed Print conditions (${printGroup.members.size} lanes)",
            s"if (UNLIKELY(done_reset && update_registers && verbose && ($pack & $mask))) {",
            s"  uint64_t $activeName = $pack & $mask;"
          ) ++ printGroup.members.map { member =>
            val print = member.statement.asInstanceOf[Print]
            s"  if ($activeName & ${uint64Constant(BigInt(1) << member.sourceOffset)}) ${emitPrintfCall(print)}"
          } ++ Vector("}")
        }

      case stopGroup: SlpPackedStopGroup =>
        val stops = stopGroup.members.map(_.statement.asInstanceOf[Stop])
        val sameReturn = stops.map(_.ret).distinct.size == 1
        val header = Vector(
          s"// SLP packed Stop conditions (${stopGroup.members.size} lanes)",
          s"if (UNLIKELY($pack & $mask)) {",
          s"  uint64_t $activeName = $pack & $mask;",
          "  assert_triggered = true;"
        )
        val assignments = if (sameReturn) Vector(s"  assert_exit_code = ${stops.head.ret};")
        else stopGroup.members.zip(stops).map { case (member, stop) =>
          s"  if ($activeName & ${uint64Constant(BigInt(1) << member.sourceOffset)}) assert_exit_code = ${stop.ret};"
        }
        header ++ assignments ++ Vector("}")

      case interleaved: SlpPackedInterleavedSideEffectGroup =>
        val prints = interleaved.members.collect { case member if member.statement.isInstanceOf[Print] =>
          member -> member.statement.asInstanceOf[Print]
        }
        val stops = interleaved.members.collect { case member if member.statement.isInstanceOf[Stop] =>
          member -> member.statement.asInstanceOf[Stop]
        }
        val identicalPrints = prints.nonEmpty && prints.tail.forall { case (_, print) =>
          print.string == prints.head._2.string && print.args == prints.head._2.args
        }
        val identicalStops = stops.nonEmpty && stops.forall(_._2.ret == stops.head._2.ret)

        if (identicalPrints && identicalStops) {
          // Diagnostic-only coalescing requested for replicated assertions:
          // duplicate messages carry no lane-specific information, and all
          // Stops have the same externally visible return code.
          val printMask = prints.foldLeft(BigInt(0)) { case (value, (member, _)) =>
            value | (BigInt(1) << member.sourceOffset)
          }
          val stopMask = stops.foldLeft(BigInt(0)) { case (value, (member, _)) =>
            value | (BigInt(1) << member.sourceOffset)
          }
          Vector(
            s"// SLP coalesced interleaved side-effect conditions (${interleaved.members.size} statements, " +
              s"${interleaved.members.map(_.sourceOffset).distinct.size} lanes)",
            s"uint64_t $activeName = $pack & $mask;",
            s"if (UNLIKELY($activeName)) {",
            s"  if (UNLIKELY(done_reset && update_registers && verbose && ($activeName & ${uint64Constant(printMask)}))) ${emitPrintfCall(prints.head._2)}",
            s"  if (UNLIKELY($activeName & ${uint64Constant(stopMask)})) {assert_triggered = true; assert_exit_code = ${stops.head._2.ret};}",
            "}"
          )
        } else {
          // Preserve source order when the outputs differ.  The shared active
          // word still replaces the pack-to-scalar unpack views.
          val header = Vector(
            s"// SLP packed interleaved side-effect conditions (${interleaved.members.size} statements, " +
              s"${interleaved.members.map(_.sourceOffset).distinct.size} lanes)",
            s"uint64_t $activeName = $pack & $mask;",
            s"if (UNLIKELY($activeName)) {"
          )
          val body = interleaved.members.flatMap { member =>
            val bit = uint64Constant(BigInt(1) << member.sourceOffset)
            member.statement match {
              case print: Print =>
                Vector(s"  if (UNLIKELY(done_reset && update_registers && verbose && ($activeName & $bit))) ${emitPrintfCall(print)}")
              case stop: Stop =>
                Vector(s"  if (UNLIKELY($activeName & $bit)) {assert_triggered = true; assert_exit_code = ${stop.ret};}")
              case other =>
                throw new IllegalStateException(s"unexpected interleaved SLP side effect: ${other.serialize}")
            }
          }
          header ++ body ++ Vector("}")
        }
    }
  }

  private def emitPackedMemWriteData(member: SlpPackedMemWriteMember): String = {
    member.dataLane match {
      case Some(dataRef) =>
        val offset = member.dataOffset.getOrElse(
          throw new IllegalStateException(s"missing packed MemWrite data offset for node ${member.nodeId}")
        )
        s"UInt<${dataRef.lane.width}>(armor_slp::unpack_bits(" +
          s"${packName(dataRef.sourcePackId)}, $offset, ${dataRef.lane.width}))"
      case None =>
        emitExpr(member.statement.wrData)
    }
  }

  private def emitPackedMemWriteGroup(group: SlpPackedMemWriteGroup): Vector[String] = {
    val enPack = packName(group.enPackId)
    val mask = uint64Constant(group.activeMask)
    val activeName = s"_armor_slp_mem_write_active_${group.members.head.nodeId}"
    Vector(
      s"// SLP packed MemWrite enables (${group.members.size} lanes)",
      s"uint64_t $activeName = $enPack & $mask;",
      s"if (UNLIKELY(update_registers && $activeName)) {"
    ) ++ group.members.map { member =>
      val write = member.statement
      val bit = uint64Constant(BigInt(1) << member.enOffset)
      val address = emitExprWrap(write.wrAddr)
      val data = emitPackedMemWriteData(member)
      s"  if ($activeName & $bit) ${write.memName}[$address.as_single_word()] = $data;"
    } ++ Vector("}")
  }

  private def laneOperations(pack: SlpPack): Vector[SlpOperation] =
    pack.nodeIds.map(nodeId => operations.getOrElse(
      nodeId,
      throw new IllegalStateException(s"missing operation for packed node $nodeId")
    ))

  private def argumentOffsets(laneOperations: Vector[SlpOperation], argumentIndex: Int): Vector[Int] =
    laneOperations.map(_.operands(argumentIndex).width).scanLeft(0)(_ + _).dropRight(1)

  private def extractedInput(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation],
    argumentIndex:  Int,
    laneIndex:      Int
  ): String = {
    laneOperations(laneIndex).operands(argumentIndex) match {
      case constant: SlpUIntConstant => s"UINT64_C(0x${constant.value.toString(16)})"
      case operand =>
        val offset = argumentOffsets(laneOperations, argumentIndex)(laneIndex)
        s"armor_slp::unpack_bits(${packedArgument(pack, laneOperations, argumentIndex)}, " +
          s"$offset, ${operand.width})"
    }
  }

  private def laneExpression(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation],
    laneIndex:      Int
  ): String = {
    def input(argumentIndex: Int): String =
      extractedInput(pack, laneOperations, argumentIndex, laneIndex)

    val operation = laneOperations(laneIndex)
    operation.opcode match {
      case SlpAdd       => s"(${input(0)} + ${input(1)})"
      case SlpTruncatingAdd =>
        throw new IllegalStateException("truncating Add region must use packed lowering")
      case SlpSub => throw new IllegalStateException("Sub requires truncating-region lowering")
      case SlpTruncatingSub =>
        throw new IllegalStateException("truncating Sub region must use packed lowering")
      case SlpAnd       => s"(${input(0)} & ${input(1)})"
      case SlpOr        => s"(${input(0)} | ${input(1)})"
      case SlpXor       => s"(${input(0)} ^ ${input(1)})"
      case SlpNot       => s"(~${input(0)})"
      case SlpMove      => input(0)
      case SlpCat       => s"((${input(0)} << ${operation.operands(1).width}) | ${input(1)})"
      case SlpMaskedAnd => s"(${input(0)} & ${input(1)})"
      case SlpBitSelect =>
        val bitPosition = operation.parameters.head.toInt
        s"((${input(0)} >> $bitPosition) & UINT64_C(1))"
      case SlpBits =>
        val hi = operation.parameters(0).toInt
        val lo = operation.parameters(1).toInt
        val width = hi - lo + 1
        s"((${input(0)} >> $lo) & ${maskLiteral(width)})"
      case SlpBitGather =>
        val mask = operation.parameters.head
        emitPext(input(0), mask)
      case SlpShlConst(amount) => s"(${input(0)} << $amount)"
      case SlpShrConst(amount) => s"(${input(0)} >> $amount)"
      case SlpDshlSmall(_, _, _) => s"(${input(0)} << ${input(1)})"
      case SlpDshrSmall(_, _)  => s"(${input(0)} >> ${input(1)})"
      case SlpOrr       => throw new IllegalStateException("Orr must use packed lowering")
      case SlpAndr      => throw new IllegalStateException("Andr must use packed lowering")
      case SlpLeqLowMask => throw new IllegalStateException("ArmorLeqLowMask must use packed lowering")
      case SlpLeqConst => throw new IllegalStateException("ArmorLeqConst must use packed lowering")
      case SlpEq        => s"(${input(0)} == ${input(1)})"
      case SlpEqConst   => throw new IllegalStateException("EqConst must use packed lowering")
      case SlpGeq       => throw new IllegalStateException("ArmorGeq must use packed lowering")
      case SlpLt        => throw new IllegalStateException("ArmorLt must use packed lowering")
      case SlpNeq       => throw new IllegalStateException("ArmorNeq must use packed lowering")
      case SlpOneHot    => throw new IllegalStateException("ArmorOneHot must use packed lowering")
      case SlpMux       => s"(${input(0)} ? ${input(1)} : ${input(2)})"
    }
  }

  private def hasOutputLayoutOperands(pack: SlpPack, laneOperations: Vector[SlpOperation]): Boolean =
    laneOperations.head.operands.indices.forall { argumentIndex =>
      laneOperations.map(_.operands(argumentIndex).width) == pack.lanes.map(_.resultWidth)
    }

  private def repeatedLaneResultSplat(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Option[String] = {
    val resultWidths = pack.lanes.map(_.resultWidth)
    val laneWidth = resultWidths.distinct match {
      case Vector(width) if width > 0 => width
      case _                          => return None
    }
    if (resultWidths.sum > 64) return None
    if (pack.outputOffsets != resultWidths.scanLeft(0)(_ + _).dropRight(1)) return None

    val laneExpressions = pack.lanes.indices.map { laneIndex =>
      try Some(laneExpression(pack, laneOperations, laneIndex))
      catch {
        case _: IllegalStateException => None
      }
    }
    if (laneExpressions.exists(_.isEmpty)) None
    else {
      val expressions = laneExpressions.flatten
      if (expressions.size >= 2 && expressions.distinct.size == 1)
        Some(emitLaneSplatExpression(expressions.head, laneWidth, expressions.size))
      else None
    }
  }

  private def broadcastLowTruncationResultSplat(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Option[String] = {
    val resultWidths = pack.lanes.map(_.resultWidth)
    val resultWidth = resultWidths.distinct match {
      case Vector(width) if width > 0 => width
      case _                          => return None
    }
    if (resultWidths.sum > 64) return None
    if (pack.outputOffsets != resultWidths.scanLeft(0)(_ + _).dropRight(1)) return None

    def broadcastArg(argumentIndex: Int): Option[SlpBroadcastInput] =
      broadcastInputs.get((pack.id, argumentIndex)).filter { input =>
        input.value.width >= resultWidth &&
          laneOperations.forall(operation =>
            argumentIndex < operation.operands.size &&
              operation.operands(argumentIndex).width == input.value.width &&
              operation.resultWidth == resultWidth
          )
      }

    def lowMask(operand: SlpOperand): Boolean = operand match {
      case SlpUIntConstant(value, width) =>
        width == resultWidth && value == ((BigInt(1) << resultWidth) - 1)
      case _ => false
    }

    val source = pack.shape.opcode match {
      case SlpMove =>
        broadcastArg(0)
      case SlpMaskedAnd =>
        val candidates = Vector(0 -> 1, 1 -> 0)
        candidates.collectFirst {
          case (broadcastIndex, maskIndex)
              if broadcastArg(broadcastIndex).nonEmpty &&
                laneOperations.forall(operation =>
                  maskIndex < operation.operands.size && lowMask(operation.operands(maskIndex))
                ) =>
            broadcastArg(broadcastIndex).get
        }
      case _ => None
    }

    source.map(input =>
      emitLaneSplatExpression(broadcastValueExpression(input.value), resultWidth, pack.lanes.size)
    )
  }

  /** Each packed argument is confined to its declared lane layout. A Mux
    * cannot create a one bit outside that layout when both data operands use
    * the result layout, so a final partial-word truncation would be redundant.
    */
  private def muxDataOperandsMatchOutputLayout(
    pack: SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Boolean = {
    require(pack.shape.opcode == SlpMux)
    laneOperations.forall(_.operands.size == 3) &&
      (1 to 2).forall { argumentIndex =>
        laneOperations.map(_.operands(argumentIndex).width) == pack.lanes.map(_.resultWidth)
      }
  }

  private def fastExpression(pack: SlpPack, laneOperations: Vector[SlpOperation]): Option[String] = {
    val expression = pack.shape.opcode match {
      case SlpAdd       => None
      case SlpTruncatingAdd => None
      case SlpSub       => None
      case SlpTruncatingSub => None
      case SlpMaskedAnd => None
      case SlpBitSelect => None
      case SlpBits      => None
      case SlpBitGather => None
      case SlpShlConst(_) | SlpShrConst(_) | SlpDshlSmall(_, _, _) | SlpDshrSmall(_, _) => None
      case SlpEq        => None
      case SlpEqConst   => None
      case SlpGeq       => None
      case SlpLt        => None
      case SlpNeq       => None
      case SlpOneHot    => None
      case SlpLeqConst  => None
      case SlpCat       => None
      case _ if !hasOutputLayoutOperands(pack, laneOperations) => None
      case _ =>
        val inputs = laneOperations.head.operands.indices.map(argumentIndex =>
          packedArgument(pack, laneOperations, argumentIndex)
        )
        pack.shape.opcode match {
          case SlpAdd  => None
          case SlpTruncatingAdd => None
          case SlpSub => None
          case SlpTruncatingSub => None
          case SlpAnd  => Some(s"(${inputs(0)} & ${inputs(1)})")
          case SlpOr   => Some(s"(${inputs(0)} | ${inputs(1)})")
          case SlpXor  => Some(s"(${inputs(0)} ^ ${inputs(1)})")
          case SlpNot  => Some(s"(~${inputs(0)})")
          case SlpMove => Some(inputs(0))
          case SlpCat  => None
          case SlpEq   => None
          case SlpMux  => None
          case SlpMaskedAnd | SlpBitSelect | SlpBits | SlpBitGather | SlpShlConst(_) | SlpShrConst(_) | SlpDshlSmall(_, _, _) | SlpDshrSmall(_, _) | SlpEq | SlpEqConst |
              SlpGeq | SlpLt | SlpNeq | SlpOneHot | SlpLeqConst | SlpOrr | SlpAndr | SlpLeqLowMask =>
            throw new IllegalStateException("unreachable compact op")
        }
    }
    expression.map { value =>
      if (pack.shape.opcode == SlpNot && pack.totalResultWidth < 64)
        s"($value & ${maskLiteral(pack.totalResultWidth)})"
      else value
    }
  }

  private def broadcastCondition(packId: Int): Option[String] = {
    def lowBit(value: String, width: Int): String =
      if (width == 1) value else s"($value & UINT64_C(1))"

    broadcastInputs.get((packId, 0)).map(_.value match {
      case signal: SlpBroadcastSignal =>
        lowBit(scalarWord(signal.signalName), signal.width)
      case constant: SlpBroadcastConstant =>
        if ((constant.value & 1) == 0) "UINT64_C(0)" else "UINT64_C(1)"
      case packed: SlpBroadcastPacked =>
        lowBit(
          s"armor_slp::unpack_bits(${packName(packed.sourcePackId)}, ${packed.offset}, ${packed.width})",
          packed.width
        )
      case packed: SlpBroadcastReg =>
        lowBit(
          s"armor_slp::unpack_bits(${SlpRegStorageNames.state(packed.regPackId)}, " +
            s"${packed.offset}, ${packed.width})",
          packed.width
        )
    })
  }

  private def isOneBitMux(pack: SlpPack): Boolean =
    pack.shape.opcode == SlpMux && pack.lanes.forall(_.resultWidth == 1)

  /** Expand one packed condition bit into each equally-sized result lane.
    *
    * PDEP places condition i at the low bit of result lane i. Multiplication
    * by the low-one lane mask then fills that lane without carries because
    * result lanes are disjoint.
    */
  private def depositedMuxMaskConstants(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Option[(BigInt, BigInt)] = {
    val conditionWidths = laneOperations.map(_.operands.head.width)
    val conditionOffsets = argumentOffsets(laneOperations, 0)
    val resultWidths = pack.lanes.map(_.resultWidth)
    val uniformWidth = resultWidths.distinct match {
      case Vector(width) if width > 1 => Some(width)
      case _                          => None
    }
    uniformWidth.filter { width =>
      conditionWidths.forall(_ == 1) &&
        conditionOffsets == pack.lanes.indices.toVector &&
        pack.outputOffsets == pack.lanes.indices.map(_ * width).toVector
    }.map { width =>
      val laneStarts = pack.outputOffsets.foldLeft(BigInt(0)) { case (mask, offset) =>
        mask | (BigInt(1) << offset)
      }
      val laneValueMask = (BigInt(1) << width) - 1
      laneStarts -> laneValueMask
    }
  }

  private def muxKind(pack: SlpPack): String =
    if (broadcastCondition(pack.id).nonEmpty) "broadcast"
    else if (isOneBitMux(pack)) "one_bit"
    else "lane_mask"

  private def emitMuxPack(pack: SlpPack, laneOperations: Vector[SlpOperation]): Vector[String] = {
    val resultName = packName(pack.id)
    val trueInput = packedArgument(pack, laneOperations, 1)
    val falseInput = packedArgument(pack, laneOperations, 2)
    val maskValue = (BigInt(1) << pack.totalResultWidth) - 1
    val canElideResultMask =
      pack.totalResultWidth < 64 && muxDataOperandsMatchOutputLayout(pack, laneOperations)
    def truncateMux(value: String): String = {
      if (canElideResultMask) {
        elidedMuxResultMasks += 1
        value
      } else truncateWord(value, pack.totalResultWidth, maskValue)
    }
    broadcastCondition(pack.id) match {
      case Some("UINT64_C(0)") => Vector(s"uint64_t $resultName = $falseInput;")
      case Some("UINT64_C(1)") => Vector(s"uint64_t $resultName = $trueInput;")
      case Some(condition) =>
        Vector(s"uint64_t $resultName = $condition ? $trueInput : $falseInput;")
      case None if isOneBitMux(pack) =>
        val conditionInput = packedArgument(pack, laneOperations, 0)
        Vector(
          s"uint64_t $resultName = ${truncateMux(s"($falseInput ^ (($trueInput ^ $falseInput) & $conditionInput))")};"
        )
      case None =>
        val conditionInput = packedArgument(pack, laneOperations, 0)
        val maskName = s"${resultName}_condition_mask"
        val buildMask = depositedMuxMaskConstants(pack, laneOperations) match {
          case Some((laneStarts, laneValueMask)) =>
            Vector(
              s"uint64_t $maskName = _pdep_u64($conditionInput, " +
                s"UINT64_C(0x${laneStarts.toString(16)})) * " +
                s"UINT64_C(0x${laneValueMask.toString(16)});"
            )
          case None =>
            val conditionOffsets = argumentOffsets(laneOperations, 0)
            Vector(s"uint64_t $maskName = UINT64_C(0);") ++ pack.lanes.indices.map { laneIndex =>
              val conditionOffset = conditionOffsets(laneIndex)
              val outputOffset = pack.outputOffsets(laneIndex)
              val width = pack.lanes(laneIndex).resultWidth
              val laneMask = maskLiteral(width, outputOffset)
              s"$maskName |= (UINT64_C(0) - (($conditionInput >> $conditionOffset) & UINT64_C(1))) & $laneMask;"
            }
        }
        buildMask ++ Vector(
          s"uint64_t $resultName = ${truncateMux(s"($falseInput ^ (($trueInput ^ $falseInput) & $maskName))")};"
        )
    }
  }

  /** Lower lane-local UInt<W> dynamic left shift by a UInt<1> or UInt<2> amount.
    *
    * FIRRTL dynamic left shift widens the result lane to W + 2^S - 1.  The
    * packed value operand is first projected from dense W-bit lanes into the
    * low W bits of dense result-width lanes.  Then each shift bit conditionally
    * applies one fixed lane-local left shift by 2^i.
    *
    * A plain word left shift would leak the high bits of lane i into the low
    * bits of lane i+1.  Masking each lane down to the low resultWidth-amount
    * source bits before the shift removes that cross-lane leakage.
    */
  private def emitDshlSmallPack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Vector[String] = {
    val SlpDshlSmall(valueWidth, shiftWidth, resultWidth) = pack.shape.opcode
    require(shiftWidth == 1 || shiftWidth == 2)
    require(resultWidth == valueWidth + ((1 << shiftWidth) - 1))
    require(laneOperations.size == pack.parallelDegree)
    require(laneOperations.nonEmpty)
    require(laneOperations.forall {
      case SlpOperation(SlpDshlSmall(opValueWidth, opShiftWidth, opResultWidth),
          laneResultWidth, storageWidth, Vector(valueOperand, SlpSignal(_, shiftOperandWidth)),
          parameters, _) =>
        opValueWidth == valueWidth &&
          opShiftWidth == shiftWidth &&
          opResultWidth == resultWidth &&
          valueOperand.width == valueWidth &&
          shiftOperandWidth == shiftWidth &&
          laneResultWidth == resultWidth &&
          storageWidth == resultWidth &&
          parameters.isEmpty
      case _ => false
    })

    val laneCount = laneOperations.size
    require(pack.totalResultWidth == resultWidth * laneCount)
    require(pack.outputOffsets == laneOperations.indices.map(_ * resultWidth).toVector,
      "DshlSmall requires dense result lanes")
    require(argumentOffsets(laneOperations, 0) == laneOperations.indices.map(_ * valueWidth).toVector,
      "DshlSmall requires dense value operand lanes")
    require(argumentOffsets(laneOperations, 1) == laneOperations.indices.map(_ * shiftWidth).toVector,
      "DshlSmall requires dense shift operand lanes")

    val resultName = packName(pack.id)
    val stateName = s"${resultName}_dshl_value"
    val valueInput = packedArgument(pack, laneOperations, 0)
    val shiftInput = packedArgument(pack, laneOperations, 1)
    val totalMask = (BigInt(1) << pack.totalResultWidth) - 1
    val valueInputWidth = valueWidth * laneCount
    val valueInputMask = (BigInt(1) << valueInputWidth) - 1
    val valueDestinationMask = laneBitRangeMask(resultWidth, laneCount, 0, valueWidth)
    val laneStarts = laneBitMask(resultWidth, 0, laneCount)
    val laneResultMask = (BigInt(1) << resultWidth) - 1
    val shiftInputMask = (BigInt(1) << (shiftWidth * laneCount)) - 1
    val compactValue = truncateWord(valueInput, valueInputWidth, valueInputMask)
    val valueExpr = s"_pdep_u64($compactValue, ${uint64Constant(valueDestinationMask)})"

    def shiftBitPackExpression(bitIndex: Int): String = {
      require(bitIndex >= 0 && bitIndex < shiftWidth)
      if (shiftWidth == 1) {
        truncateWord(shiftInput, laneCount, (BigInt(1) << laneCount) - 1)
      } else {
        val shiftBitMask = laneBitMask(shiftWidth, bitIndex, laneCount)
        emitPext(truncateWord(shiftInput, shiftWidth * laneCount, shiftInputMask), shiftBitMask)
      }
    }

    val stagedLowering = (0 until shiftWidth).toVector.flatMap { stage =>
      val amount = 1 << stage
      val selectName = s"${resultName}_dshl_s${stage}_select"
      val selectExpr =
        s"_pdep_u64(${shiftBitPackExpression(stage)}, ${uint64Constant(laneStarts)}) * " +
          s"${uint64Constant(laneResultMask)}"
      val selectDecl = s"uint64_t $selectName = $selectExpr;"
      if (amount >= resultWidth) {
        Vector(
          selectDecl,
          s"$stateName &= ~$selectName;"
        )
      } else {
        val shiftedName = s"${resultName}_dshl_s${stage}_shifted"
        val validSourceMask = laneBitRangeMask(resultWidth, laneCount, 0, resultWidth - amount)
        Vector(
          selectDecl,
          s"uint64_t $shiftedName = ($stateName & ${uint64Constant(validSourceMask)}) << $amount;",
          s"$stateName = $stateName ^ (($stateName ^ $shiftedName) & $selectName);"
        )
      }
    }

    Vector(s"uint64_t $stateName = $valueExpr;") ++
      stagedLowering ++
      Vector(s"uint64_t $resultName = ${truncateWord(stateName, pack.totalResultWidth, totalMask)};")
  }

  /** Lower lane-local UInt<W> dynamic right shift by a UInt<1> or UInt<2> amount.
    *
    * This is a packed barrel-shifter: shift bit i conditionally applies a
    * fixed lane-local right shift by 2^i.  The per-lane shift bit is expanded
    * into a full-lane select mask, then a mask-select updates the packed word.
    *
    * A plain word shift would leak bit0 of lane i+1 into the top bit of lane i.
    * Masking with the low W-amount bits of every lane removes that cross-lane
    * bit.  When amount >= W, the shifted candidate is zero, so the selected
    * lanes are cleared directly.
    */
  private def emitDshrSmallPack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Vector[String] = {
    val SlpDshrSmall(valueWidth, shiftWidth) = pack.shape.opcode
    require(shiftWidth >= 1 && shiftWidth <= 3)
    require(valueWidth >= 2 && valueWidth <= 8)
    require(laneOperations.size == pack.parallelDegree)
    require(laneOperations.nonEmpty)
    require(laneOperations.forall {
      case SlpOperation(SlpDshrSmall(opValueWidth, opShiftWidth), resultWidth, storageWidth,
          Vector(SlpSignal(_, inputWidth), shiftOperand), parameters, _) =>
        opValueWidth == valueWidth &&
          opShiftWidth == shiftWidth &&
          inputWidth == valueWidth &&
          shiftOperand.width == shiftWidth &&
          resultWidth == valueWidth &&
          storageWidth == valueWidth &&
          parameters.isEmpty
      case _ => false
    })

    val laneCount = laneOperations.size
    require(pack.totalResultWidth == valueWidth * laneCount)
    require(pack.outputOffsets == laneOperations.indices.map(_ * valueWidth).toVector,
      "DshrSmall requires dense result lanes")
    require(argumentOffsets(laneOperations, 0) == laneOperations.indices.map(_ * valueWidth).toVector,
      "DshrSmall requires dense value operand lanes")
    require(argumentOffsets(laneOperations, 1) == laneOperations.indices.map(_ * shiftWidth).toVector,
      "DshrSmall requires dense shift operand lanes")

    val resultName = packName(pack.id)
    val stateName = s"${resultName}_dshr_value"
    val valueInput = packedArgument(pack, laneOperations, 0)
    val shiftInput = packedArgument(pack, laneOperations, 1)
    val totalMask = (BigInt(1) << pack.totalResultWidth) - 1
    val laneStarts = laneBitMask(valueWidth, 0, laneCount)
    val laneValueMask = (BigInt(1) << valueWidth) - 1
    val shiftInputMask = (BigInt(1) << (shiftWidth * laneCount)) - 1
    val valueExpr = truncateWord(valueInput, pack.totalResultWidth, totalMask)

    def shiftBitPackExpression(bitIndex: Int): String = {
      require(bitIndex >= 0 && bitIndex < shiftWidth)
      if (shiftWidth == 1) {
        truncateWord(shiftInput, laneCount, (BigInt(1) << laneCount) - 1)
      } else {
        val shiftBitMask = laneBitMask(shiftWidth, bitIndex, laneCount)
        emitPext(truncateWord(shiftInput, shiftWidth * laneCount, shiftInputMask), shiftBitMask)
      }
    }

    val stagedLowering = (0 until shiftWidth).toVector.flatMap { stage =>
      val amount = 1 << stage
      val selectName = s"${resultName}_dshr_s${stage}_select"
      val selectExpr =
        s"_pdep_u64(${shiftBitPackExpression(stage)}, ${uint64Constant(laneStarts)}) * " +
          s"${uint64Constant(laneValueMask)}"
      val selectDecl = s"uint64_t $selectName = $selectExpr;"
      if (amount >= valueWidth) {
        Vector(
          selectDecl,
          s"$stateName &= ~$selectName;"
        )
      } else {
        val shiftedName = s"${resultName}_dshr_s${stage}_shifted"
        val shiftedMask = laneBitRangeMask(valueWidth, laneCount, 0, valueWidth - amount)
        Vector(
          selectDecl,
          s"uint64_t $shiftedName = ($stateName >> $amount) & ${uint64Constant(shiftedMask)};",
          s"$stateName = $stateName ^ (($stateName ^ $shiftedName) & $selectName);"
        )
      }
    }

    Vector(s"uint64_t $stateName = $valueExpr;") ++
      stagedLowering ++
      Vector(s"uint64_t $resultName = ${truncateWord(stateName, pack.totalResultWidth, totalMask)};")
  }

  private def laneBitMask(laneWidth: Int, bitPosition: Int, laneCount: Int): BigInt = {
    require(laneWidth > 0)
    require(bitPosition >= 0 && bitPosition < laneWidth)
    (0 until laneCount).foldLeft(BigInt(0)) { case (mask, lane) =>
      mask | (BigInt(1) << (lane * laneWidth + bitPosition))
    }
  }

  private def laneBitRangeMask(
    laneWidth:   Int,
    laneCount:   Int,
    lo:          Int,
    hiExclusive: Int
  ): BigInt = {
    require(laneWidth > 0)
    require(laneCount > 0)
    require(0 <= lo && lo <= hiExclusive && hiExclusive <= laneWidth,
      s"invalid lane bit range [$lo, $hiExclusive) for lane width $laneWidth")
    if (lo == hiExclusive) BigInt(0)
    else {
      val laneField = ((BigInt(1) << (hiExclusive - lo)) - 1) << lo
      (0 until laneCount).foldLeft(BigInt(0)) { case (mask, laneIndex) =>
        mask | (laneField << (laneIndex * laneWidth))
      }
    }
  }

  /** Emit packed UInt<1>(1) << index for UInt<1..3> index lanes.
    *
    * The UInt<1> case has a smaller direct form.  Wider indices use a staged
    * lane-local decode: before stage i, the one-hot bit in every lane lies in
    * [0, 2^i); selecting index bit i either retains it or shifts it by 2^i.
    * The invariant makes each word shift lane-safe without a boundary mask.
    */
  private def emitOneHotPack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Vector[String] = {
    require(pack.shape.opcode == SlpOneHot)
    require(laneOperations.size == pack.parallelDegree)
    require(laneOperations.nonEmpty)
    require(laneOperations.forall {
      case SlpOperation(SlpOneHot, resultWidth, storageWidth,
          Vector(SlpSignal(_, inputWidth)), parameters, _) =>
        inputWidth >= 1 && inputWidth <= 3 && resultWidth == (1 << inputWidth) &&
          storageWidth == resultWidth && parameters.isEmpty
      case _ => false
    })

    val inputWidth = laneOperations.head.operands.head.width
    val resultWidth = laneOperations.head.resultWidth
    val laneCount = laneOperations.size
    require(laneOperations.forall(operation =>
      operation.operands.head.width == inputWidth && operation.resultWidth == resultWidth))
    require(argumentOffsets(laneOperations, 0) == laneOperations.indices.map(_ * inputWidth).toVector,
      "ArmorOneHot requires a dense packed input layout")
    require(pack.outputOffsets == laneOperations.indices.map(_ * resultWidth).toVector,
      "ArmorOneHot requires a dense packed output layout")
    require(inputWidth * laneCount <= 64 && resultWidth * laneCount <= 64)

    val input = packedArgument(pack, laneOperations, 0)
    val resultName = packName(pack.id)
    val inputMask = uint64Constant((BigInt(1) << (inputWidth * laneCount)) - 1)
    val inputBits = if (inputWidth * laneCount == 64) input else s"($input & $inputMask)"

    inputWidth match {
      case 1 =>
        val laneMask = uint64Constant((BigInt(1) << laneCount) - 1)
        val lowPlane = s"((~$inputBits) & $laneMask)"
        val highPlane = inputBits
        Vector(
          s"uint64_t $resultName = _pdep_u64($lowPlane, ${uint64Constant(laneBitMask(resultWidth, 0, laneCount))}) | " +
            s"_pdep_u64($highPlane, ${uint64Constant(laneBitMask(resultWidth, 1, laneCount))});"
        )
      case 2 | 3 =>
        val stateName = s"${resultName}_onehot_value"
        val laneStarts = laneBitMask(resultWidth, 0, laneCount)
        val laneValueMask = (BigInt(1) << resultWidth) - 1
        val totalMask = (BigInt(1) << pack.totalResultWidth) - 1

        def indexBitPackExpression(bitIndex: Int): String = {
          require(bitIndex >= 0 && bitIndex < inputWidth)
          emitPext(inputBits, laneBitMask(inputWidth, bitIndex, laneCount))
        }

        val stages = (0 until inputWidth).toVector.flatMap { stage =>
          val amount = 1 << stage
          val selectName = s"${resultName}_onehot_s${stage}_select"
          val shiftedName = s"${resultName}_onehot_s${stage}_shifted"
          Vector(
            s"uint64_t $selectName = _pdep_u64(${indexBitPackExpression(stage)}, ${uint64Constant(laneStarts)}) * ${uint64Constant(laneValueMask)};",
            s"uint64_t $shiftedName = $stateName << $amount;",
            s"$stateName = $stateName ^ (($stateName ^ $shiftedName) & $selectName);"
          )
        }

        Vector(s"uint64_t $stateName = ${uint64Constant(laneStarts)};") ++
          stages ++
          Vector(s"uint64_t $resultName = ${truncateWord(stateName, pack.totalResultWidth, totalMask)};")
    }
  }

  /** Emit a lane-local zero test for tight packed lanes.
    *
    * For every lane, `diff = lane ^ const`.  Equality is `diff == 0`.
    * The add-lowmask idiom raises the lane MSB when any low lane bit is set:
    *
    *   zero_msb = ~(((diff & low_mask) + low_mask) | diff | low_mask) & msb_mask
    *
    * This does not borrow across lanes.  The maximum low-lane addition is
    * `(2^(W-1)-1) + (2^(W-1)-1) = 2^W - 2`, so carry can reach the lane MSB
    * but never exits the lane.
    */
  private def emitLaneLocalZeroMsbAddLowMaskPack(
    prefix:    String,
    diffExpr:  String,
    laneWidth: Int,
    laneCount: Int
  ): (Vector[String], BigInt, String) = {
    require(prefix.nonEmpty)
    require(laneWidth >= 2)
    require(laneCount > 0)
    require(laneWidth * laneCount <= 64,
      s"lane-local zero-test lowering requires tight width <= 64, got " +
        s"laneWidth=$laneWidth laneCount=$laneCount")

    val dataMask = laneBitRangeMask(laneWidth, laneCount, 0, laneWidth)
    val lowMask = laneBitRangeMask(laneWidth, laneCount, 0, laneWidth - 1)
    val msbMask = laneBitMask(laneWidth, laneWidth - 1, laneCount)
    val diffName = s"${prefix}_diff"
    val zeroMsbName = s"${prefix}_zero_msb"
    val maskedDiff =
      if (laneWidth * laneCount == 64) diffExpr
      else s"($diffExpr & ${uint64Constant(dataMask)})"
    (Vector(
      s"uint64_t $diffName = $maskedDiff;",
      s"uint64_t $zeroMsbName = (~((($diffName & ${uint64Constant(lowMask)}) + " +
        s"${uint64Constant(lowMask)}) | $diffName | ${uint64Constant(lowMask)})) & " +
        s"${uint64Constant(msbMask)};"
    ), msbMask, zeroMsbName)
  }

  private def tightEqConstSourceGroup(
    input:         String,
    sourceOffsets: Vector[Int],
    beginLane:     Int,
    laneCount:     Int,
    laneWidth:     Int
  ): String = {
    require(laneCount > 0)
    require(beginLane >= 0 && beginLane + laneCount <= sourceOffsets.size)
    val sourceOffset = sourceOffsets(beginLane)
    require((0 until laneCount).forall { lane =>
      sourceOffsets(beginLane + lane) == sourceOffset + lane * laneWidth
    }, s"EqConst tight source group requires contiguous $laneWidth-bit lanes")
    val sourceWidth = laneCount * laneWidth
    require(sourceWidth > 0 && sourceWidth <= 64)
    if (sourceOffset == 0) input else s"($input >> $sourceOffset)"
  }

  private def emitEqConstTightZeroTestPack(
    pack:           SlpPack,
    input:          String,
    sourceOffsets:  Vector[Int],
    constants:      Vector[Int],
    inputWidth:     Int
  ): Vector[String] = {
    val resultName = packName(pack.id)
    val lanesPerGroup = 64 / inputWidth
    require(lanesPerGroup > 0)
    val chunks = sourceOffsets.indices.grouped(lanesPerGroup).toVector
    val lines = Vector.newBuilder[String]
    if (chunks.size > 1) lines += s"uint64_t $resultName = UINT64_C(0);"

    chunks.foreach { chunk =>
      val beginLane = chunk.head
      val laneCount = chunk.size
      val source = tightEqConstSourceGroup(input, sourceOffsets, beginLane, laneCount, inputWidth)
      val packedConstant = chunk.zipWithIndex.foldLeft(BigInt(0)) {
        case (value, (sourceIndex, localLane)) =>
          value | (BigInt(constants(sourceIndex)) << (localLane * inputWidth))
      }
      val diffExpr =
        if (packedConstant == 0) source else s"($source ^ ${uint64Constant(packedConstant)})"
      val prefix = s"${resultName}_eq_tight_$beginLane"
      val (zeroTestLines, msbMask, zeroMsbName) =
        emitLaneLocalZeroMsbAddLowMaskPack(prefix, diffExpr, inputWidth, laneCount)
      lines ++= zeroTestLines

      val compactEqual = emitPext(zeroMsbName, msbMask)
      val outputOffset = pack.outputOffsets(beginLane)
      val deposited = if (outputOffset == 0) compactEqual else s"($compactEqual << $outputOffset)"
      if (chunks.size == 1) lines += s"uint64_t $resultName = $deposited;"
      else lines += s"$resultName |= $deposited;"
    }

    lines.result()
  }

  private def emitEqConstGuardSubtractPack(
    pack:           SlpPack,
    input:          String,
    sourceOffsets:  Vector[Int],
    constants:      Vector[Int],
    inputWidth:     Int
  ): Vector[String] = {
    val resultName = packName(pack.id)
    val cellWidth = inputWidth + 1
    val laneValueMask = (BigInt(1) << inputWidth) - 1
    val lanesPerGroup = 64 / cellWidth
    val chunks = sourceOffsets.indices.grouped(lanesPerGroup).toVector
    def zeroFlags(chunk: Seq[Int]): String = {
      val laneCount = chunk.size
      val dataMask = (0 until laneCount).foldLeft(BigInt(0)) { case (mask, laneIndex) =>
        mask | (laneValueMask << (laneIndex * cellWidth))
      }
      val lsbMask = (0 until laneCount).foldLeft(BigInt(0)) { case (mask, laneIndex) =>
        mask | (BigInt(1) << (laneIndex * cellWidth))
      }
      val guardMask = (0 until laneCount).foldLeft(BigInt(0)) { case (mask, laneIndex) =>
        mask | (BigInt(1) << (laneIndex * cellWidth + inputWidth))
      }
      val sourceOffset = sourceOffsets(chunk.head)
      val source = if (sourceOffset == 0) input else s"($input >> $sourceOffset)"
      val expanded = s"_pdep_u64($source, ${uint64Constant(dataMask)})"
      val packedConstant = chunk.zipWithIndex.foldLeft(BigInt(0)) {
        case (value, (sourceIndex, laneIndex)) =>
          value | (BigInt(constants(sourceIndex)) << (laneIndex * cellWidth))
      }
      val different = if (packedConstant == 0) expanded
        else s"($expanded ^ ${uint64Constant(packedConstant)})"
      val packed = emitPext(
        s"~(($different | ${uint64Constant(guardMask)}) - ${uint64Constant(lsbMask)}) & ${uint64Constant(guardMask)}",
        guardMask
      )
      val destinationOffset = pack.outputOffsets(chunk.head)
      if (destinationOffset == 0) packed else s"($packed << $destinationOffset)"
    }
    val terms = chunks.map(zeroFlags)
    if (terms.size == 1) Vector(s"uint64_t $resultName = ${terms.head};")
    else Vector(s"uint64_t $resultName = UINT64_C(0);") ++ terms.map(term => s"$resultName |= $term;")
  }

  private def shouldUseEqConstTightZeroTest(
    inputWidth:    Int,
    sourceOffsets: Vector[Int]
  ): Boolean = {
    val tight = sourceOffsets.zipWithIndex.forall { case (offset, index) =>
      offset == sourceOffsets.head + index * inputWidth
    }
    tight && 64 / inputWidth > 0
  }

  private def emitEqConstPack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Vector[String] = {
    require(pack.shape.opcode == SlpEqConst)
    require(laneOperations.size == pack.parallelDegree)
    require(laneOperations.forall(operation =>
      operation.resultWidth == 1 && (operation.operands match {
        case Vector(SlpSignal(_, width), SlpUIntConstant(value, literalWidth)) =>
          width >= 2 && width <= 17 && literalWidth == width && value >= 0 &&
            value < (BigInt(1) << width)
        case _ => false
      })
    ))

    val (input, sourceOffsets) = eqPackedSources.get(pack.id) match {
      case Some(source) => source.sourceName -> source.sourceOffsets
      case None         => packedArgument(pack, laneOperations, 0) -> argumentOffsets(laneOperations, 0)
    }
    require(sourceOffsets == sourceOffsets.sorted)
    require(sourceOffsets.distinct.size == sourceOffsets.size)
    val constants = laneOperations.map(_.operands(1).asInstanceOf[SlpUIntConstant].value.toInt)
    val resultName = packName(pack.id)
    val inputWidth = laneOperations.head.operands.head.width
    inputWidth match {
      case 2 =>
        val laneLsbMask = sourceOffsets.foldLeft(BigInt(0)) { case (mask, offset) =>
          mask | (BigInt(1) << offset)
        }
        constants.distinct match {
          case Vector(0) => Vector(
            s"uint64_t $resultName = ${emitPext(s"(~$input) & ~($input >> 1)", laneLsbMask)};"
          )
          case Vector(1) => Vector(
            s"uint64_t $resultName = ${emitPext(s"$input & ~($input >> 1)", laneLsbMask)};"
          )
          case Vector(2) => Vector(
            s"uint64_t $resultName = ${emitPext(s"(~$input) & ($input >> 1)", laneLsbMask)};"
          )
          case Vector(3) => Vector(
            s"uint64_t $resultName = ${emitPext(s"$input & ($input >> 1)", laneLsbMask)};"
          )
          case _ =>
            val packedConstant = constants.zip(sourceOffsets).foldLeft(BigInt(0)) {
              case (value, (constant, offset)) => value | (BigInt(constant) << offset)
            }
            val differentName = s"${resultName}_different"
            Vector(
              s"uint64_t $differentName = $input ^ UINT64_C(0x${packedConstant.toString(16)});",
              s"uint64_t $resultName = ${emitPext(s"~($differentName | ($differentName >> 1))", laneLsbMask)};"
            )
        }
      case width if width >= 3 && width <= 17 =>
        val laneValueMask = (BigInt(1) << inputWidth) - 1
        require(constants.forall(value => value >= 0 && value <= laneValueMask),
          s"UInt<$inputWidth> EqConst constant must fit its input lane")
        require(sourceOffsets.zipWithIndex.forall { case (offset, index) =>
          offset == sourceOffsets.head + index * inputWidth
        }, s"UInt<$inputWidth> EqConst requires contiguous input lanes")
        if (shouldUseEqConstTightZeroTest(inputWidth, sourceOffsets)) {
          emitEqConstTightZeroTestPack(pack, input, sourceOffsets, constants, inputWidth)
        } else {
          emitEqConstGuardSubtractPack(pack, input, sourceOffsets, constants, inputWidth)
        }
      case other =>
        throw new IllegalStateException(s"unsupported EqConst input width: $other")
    }
  }

  /** Emit lane-wise UInt equality without scalarizing either operand.
    *
    * Each comparison cell has one guard bit above the widest input. PDEP
    * zero-extends both compact packed operands into the low cell bits; after
    * XOR, the guard-bit subtraction idiom produces one equality bit per cell.
    * A pack may be split into consecutive groups when the guard layout would
    * otherwise exceed 64 bits.
    */
  private def emitEqPack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Vector[String] = {
    require(pack.shape.opcode == SlpEq)
    require(laneOperations.size == pack.parallelDegree)
    require(pack.totalResultWidth == pack.parallelDegree)
    require(laneOperations.forall {
      case SlpOperation(SlpEq, 1, storageWidth,
          Vector(SlpSignal(_, leftWidth), SlpSignal(_, rightWidth)), parameters, _) =>
        leftWidth > 0 && rightWidth > 0 && leftWidth <= 63 && rightWidth <= 63 &&
          storageWidth == leftWidth.max(rightWidth) && parameters.isEmpty
      case _ => false
    })

    val leftWidth = laneOperations.head.operands.head.width
    val rightWidth = laneOperations.head.operands(1).width
    require(laneOperations.forall(operation =>
      operation.operands.head.width == leftWidth && operation.operands(1).width == rightWidth))
    val comparisonWidth = leftWidth.max(rightWidth)
    val resultName = packName(pack.id)
    val leftInput = packedArgument(pack, laneOperations, 0)
    val rightInput = packedArgument(pack, laneOperations, 1)

    if (comparisonWidth == 1) {
      return Vector(
        s"uint64_t $resultName = (~($leftInput ^ $rightInput) & " +
          s"${maskLiteral(pack.parallelDegree)});"
      )
    }

    def lowMaskValue(width: Int): BigInt = {
      require(width > 0 && width <= 64)
      (BigInt(1) << width) - 1
    }

    def cellDataMask(laneCount: Int, cellWidth: Int, inputWidth: Int): BigInt =
      (0 until laneCount).foldLeft(BigInt(0)) { case (mask, laneIndex) =>
        mask | (lowMaskValue(inputWidth) << (laneIndex * cellWidth))
      }

    def cellGuardMask(laneCount: Int, cellWidth: Int): BigInt =
      (0 until laneCount).foldLeft(BigInt(0)) { case (mask, laneIndex) =>
        mask | (BigInt(1) << (laneIndex * cellWidth + cellWidth - 1))
      }

    def cellLsbMask(laneCount: Int, cellWidth: Int): BigInt =
      (0 until laneCount).foldLeft(BigInt(0)) { case (mask, laneIndex) =>
        mask | (BigInt(1) << (laneIndex * cellWidth))
      }

    def compactGroup(input: String, argumentIndex: Int, beginLane: Int, endLane: Int): String = {
      val offsets = argumentOffsets(laneOperations, argumentIndex)
      val sourceOffset = offsets(beginLane)
      val sourceWidth = laneOperations.slice(beginLane, endLane)
        .map(_.operands(argumentIndex).width).sum
      require(sourceWidth > 0 && sourceWidth <= 64)
      if (sourceOffset == 0 && sourceWidth == 64) input
      else {
        val shifted = if (sourceOffset == 0) input else s"($input >> $sourceOffset)"
        s"($shifted & ${uint64Constant(lowMaskValue(sourceWidth))})"
      }
    }

    val cellWidth = comparisonWidth + 1
    val lanesPerGroup = 64 / cellWidth
    require(lanesPerGroup > 0)
    val lines = Vector.newBuilder[String]
    lines += s"uint64_t $resultName = UINT64_C(0);"
    (0 until pack.parallelDegree by lanesPerGroup).foreach { beginLane =>
      val endLane = (beginLane + lanesPerGroup).min(pack.parallelDegree)
      val laneCount = endLane - beginLane
      val leftDataMask = cellDataMask(laneCount, cellWidth, leftWidth)
      val rightDataMask = cellDataMask(laneCount, cellWidth, rightWidth)
      val guardMask = cellGuardMask(laneCount, cellWidth)
      val lsbMask = cellLsbMask(laneCount, cellWidth)
      val suffix = s"${pack.id}_$beginLane"
      val leftExpanded = s"${resultName}_eq_left_$suffix"
      val rightExpanded = s"${resultName}_eq_right_$suffix"
      val different = s"${resultName}_eq_diff_$suffix"
      val equalBits = s"${resultName}_eq_bits_$suffix"
      val leftCompact = compactGroup(leftInput, 0, beginLane, endLane)
      val rightCompact = compactGroup(rightInput, 1, beginLane, endLane)

      lines += s"uint64_t $leftExpanded = _pdep_u64($leftCompact, ${uint64Constant(leftDataMask)});"
      lines += s"uint64_t $rightExpanded = _pdep_u64($rightCompact, ${uint64Constant(rightDataMask)});"
      lines += s"uint64_t $different = $leftExpanded ^ $rightExpanded;"
      lines += s"uint64_t $equalBits = ${emitPext(
        s"~(($different | ${uint64Constant(guardMask)}) - ${uint64Constant(lsbMask)}) & ${uint64Constant(guardMask)}",
        guardMask
      )};"
      val outputOffset = pack.outputOffsets(beginLane)
      val deposited = if (outputOffset == 0) equalBits else s"($equalBits << $outputOffset)"
      lines += s"$resultName |= $deposited;"
    }
    lines.result()
  }

  /** Emit lane-wise unsigned a >= b or a < b.
    *
    * Each W-bit lane is expanded into a W+1-bit cell.  The left operand gets
    * the guard bit set; subtracting the right operand clears that guard bit
    * exactly when the lane borrowed, i.e. when a < b.  PEXT compacts guard
    * bits back into a one-bit-per-lane comparison result.
    */
  private def emitUnsignedComparePack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation],
    layout:         SlpUnsignedCompareLowering.Layout,
    lessThan:       Boolean,
    label:          String
  ): Vector[String] = {
    val resultName = packName(pack.id)
    val leftInput = packedArgument(pack, laneOperations, 0)
    val rightInput = packedArgument(pack, laneOperations, 1)
    val resultMask = maskLiteral(pack.parallelDegree)

    if (layout.laneWidth == 1) {
      val expression =
        if (lessThan) s"((~$leftInput & $rightInput) & $resultMask)"
        else s"(($leftInput | (~$rightInput)) & $resultMask)"
      return Vector(s"uint64_t $resultName = $expression;")
    }

    def lowMaskValue(width: Int): BigInt = {
      require(width > 0 && width <= 64)
      (BigInt(1) << width) - 1
    }

    def compactGroup(input: String, beginLane: Int, endLane: Int): String = {
      val sourceOffset = beginLane * layout.laneWidth
      val sourceWidth = (endLane - beginLane) * layout.laneWidth
      require(sourceWidth > 0 && sourceWidth <= 64)
      if (sourceOffset == 0 && sourceWidth == 64) input
      else {
        val shifted = if (sourceOffset == 0) input else s"($input >> $sourceOffset)"
        s"($shifted & ${uint64Constant(lowMaskValue(sourceWidth))})"
      }
    }

    val cellWidth = layout.laneWidth + 1
    val chunks = (0 until layout.parallelDegree).grouped(layout.lanesPerGroup).toVector

    def chunkFlags(chunk: Seq[Int]): Vector[String] = {
      val beginLane = chunk.head
      val endLane = chunk.last + 1
      val laneCount = chunk.size
      val dataMask = (0 until laneCount).foldLeft(BigInt(0)) { case (mask, laneIndex) =>
        mask | (lowMaskValue(layout.laneWidth) << (laneIndex * cellWidth))
      }
      val guardMask = (0 until laneCount).foldLeft(BigInt(0)) { case (mask, laneIndex) =>
        mask | (BigInt(1) << (laneIndex * cellWidth + layout.laneWidth))
      }
      val suffix = s"${pack.id}_$beginLane"
      val leftExpanded = s"${resultName}_${label}_left_$suffix"
      val rightExpanded = s"${resultName}_${label}_right_$suffix"
      val diff = s"${resultName}_${label}_diff_$suffix"
      val compareBits = s"${resultName}_${label}_bits_$suffix"
      val leftCompact = compactGroup(leftInput, beginLane, endLane)
      val rightCompact = compactGroup(rightInput, beginLane, endLane)
      val guardBits = emitPext(s"$diff & ${uint64Constant(guardMask)}", guardMask)
      val flags =
        if (lessThan) s"(~$guardBits & ${maskLiteral(laneCount)})"
        else guardBits
      val deposited = if (pack.outputOffsets(beginLane) == 0) compareBits
      else s"($compareBits << ${pack.outputOffsets(beginLane)})"

      Vector(
        s"uint64_t $leftExpanded = _pdep_u64($leftCompact, ${uint64Constant(dataMask)}) | " +
          s"${uint64Constant(guardMask)};",
        s"uint64_t $rightExpanded = _pdep_u64($rightCompact, ${uint64Constant(dataMask)});",
        s"uint64_t $diff = $leftExpanded - $rightExpanded;",
        s"uint64_t $compareBits = $flags;",
        if (chunks.size == 1) s"uint64_t $resultName = $deposited;" else s"$resultName |= $deposited;"
      )
    }

    val body = chunks.flatMap(chunkFlags)
    if (chunks.size == 1) body
    else s"uint64_t $resultName = UINT64_C(0);" +: body
  }

  private def emitGeqPack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Vector[String] =
    emitUnsignedComparePack(
      pack,
      laneOperations,
      SlpGeqLowering.layout(pack, laneOperations).getOrElse(
        throw new IllegalStateException(s"ArmorGeq pack ${pack.id} is not lowerable")
      ),
      lessThan = false,
      label = "geq"
    )

  private def emitLtPack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Vector[String] =
    emitUnsignedComparePack(
      pack,
      laneOperations,
      SlpLtLowering.layout(pack, laneOperations).getOrElse(
        throw new IllegalStateException(s"ArmorLt pack ${pack.id} is not lowerable")
      ),
      lessThan = true,
      label = "lt"
    )

  /** Emit lane-wise UInt inequality without scalarizing either operand.
    *
    * XOR identifies differing bits in each lane.  The guard-cell non-zero
    * idiom then converts every lane-local non-zero value into one result bit.
    */
  private def emitNeqPack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Vector[String] = {
    val layout = SlpNeqLowering.layout(pack, laneOperations).getOrElse(
      throw new IllegalStateException(s"ArmorNeq pack ${pack.id} is not lowerable")
    )
    val resultName = packName(pack.id)
    val leftInput = packedArgument(pack, laneOperations, 0)
    val rightInput = packedArgument(pack, laneOperations, 1)

    def lowMaskValue(width: Int): BigInt = {
      require(width > 0 && width <= 64)
      (BigInt(1) << width) - 1
    }

    def compactGroup(input: String, beginLane: Int, endLane: Int): String = {
      val sourceOffset = beginLane * layout.laneWidth
      val sourceWidth = (endLane - beginLane) * layout.laneWidth
      require(sourceWidth > 0 && sourceWidth <= 64)
      if (sourceOffset == 0 && sourceWidth == 64) input
      else {
        val shifted = if (sourceOffset == 0) input else s"($input >> $sourceOffset)"
        s"($shifted & ${uint64Constant(lowMaskValue(sourceWidth))})"
      }
    }

    val cellWidth = layout.laneWidth + 1
    val chunks = (0 until layout.parallelDegree).grouped(layout.lanesPerGroup).toVector

    def chunkFlags(chunk: Seq[Int]): Vector[String] = {
      val beginLane = chunk.head
      val endLane = chunk.last + 1
      val laneCount = chunk.size
      val dataMask = (0 until laneCount).foldLeft(BigInt(0)) { case (mask, laneIndex) =>
        mask | (lowMaskValue(layout.laneWidth) << (laneIndex * cellWidth))
      }
      val guardMask = (0 until laneCount).foldLeft(BigInt(0)) { case (mask, laneIndex) =>
        mask | (BigInt(1) << (laneIndex * cellWidth + layout.laneWidth))
      }
      val lsbMask = (0 until laneCount).foldLeft(BigInt(0)) { case (mask, laneIndex) =>
        mask | (BigInt(1) << (laneIndex * cellWidth))
      }
      val suffix = s"${pack.id}_$beginLane"
      val leftExpanded = s"${resultName}_neq_left_$suffix"
      val rightExpanded = s"${resultName}_neq_right_$suffix"
      val different = s"${resultName}_neq_diff_$suffix"
      val neqBits = s"${resultName}_neq_bits_$suffix"
      val leftCompact = compactGroup(leftInput, beginLane, endLane)
      val rightCompact = compactGroup(rightInput, beginLane, endLane)
      val flags = emitPext(
        s"(($different | ${uint64Constant(guardMask)}) - ${uint64Constant(lsbMask)}) & ${uint64Constant(guardMask)}",
        guardMask
      )
      val deposited = if (pack.outputOffsets(beginLane) == 0) neqBits
      else s"($neqBits << ${pack.outputOffsets(beginLane)})"

      Vector(
        s"uint64_t $leftExpanded = _pdep_u64($leftCompact, ${uint64Constant(dataMask)});",
        s"uint64_t $rightExpanded = _pdep_u64($rightCompact, ${uint64Constant(dataMask)});",
        s"uint64_t $different = $leftExpanded ^ $rightExpanded;",
        s"uint64_t $neqBits = $flags;",
        if (chunks.size == 1) s"uint64_t $resultName = $deposited;" else s"$resultName |= $deposited;"
      )
    }

    val body = chunks.flatMap(chunkFlags)
    if (chunks.size == 1) body
    else s"uint64_t $resultName = UINT64_C(0);" +: body
  }

  /** Emit lane-local OR reductions.  Narrow and full-word lanes use the
    * shift/OR fold; all intermediate widths use a guard-cell non-zero test.
    * The latter halves the operation count for common 3..63-bit lanes while
    * retaining independent lane semantics.
    */
  private def emitOrrPack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Vector[String] = {
    require(pack.shape.opcode == SlpOrr)
    require(laneOperations.size == pack.parallelDegree)
    require(pack.totalResultWidth == pack.parallelDegree)
    require(laneOperations.forall {
      case SlpOperation(SlpOrr, 1, storageWidth, Vector(SlpSignal(_, inputWidth)), parameters, _) =>
        inputWidth > 1 && inputWidth <= 64 && storageWidth == inputWidth && parameters.isEmpty
      case _ => false
    })

    val laneWidth = laneOperations.head.operands.head.width
    require(laneOperations.forall(_.operands.head.width == laneWidth))
    require(laneWidth * pack.parallelDegree <= 64)
    require(argumentOffsets(laneOperations, 0) ==
      laneOperations.indices.map(_ * laneWidth).toVector,
      "Orr requires a dense packed input layout")

    val input = packedArgument(pack, laneOperations, 0)
    val resultName = packName(pack.id)
    if (laneWidth >= 3 && laneWidth <= 63) {
      val cellWidth = laneWidth + 1
      val lanesPerGroup = 64 / cellWidth
      val chunks = laneOperations.indices.grouped(lanesPerGroup).toVector
      val inputOffsets = argumentOffsets(laneOperations, 0)
      val lines = Vector.newBuilder[String]
      if (chunks.size > 1) lines += s"uint64_t $resultName = UINT64_C(0);"

      chunks.foreach { chunk =>
        val beginLane = chunk.head
        val laneCount = chunk.size
        val dataMask = chunk.indices.foldLeft(BigInt(0)) { case (bits, lane) =>
          bits | (((BigInt(1) << laneWidth) - 1) << (lane * cellWidth))
        }
        val guardMask = chunk.indices.foldLeft(BigInt(0)) { case (bits, lane) =>
          bits | (BigInt(1) << (lane * cellWidth + laneWidth))
        }
        val lsbMask = chunk.indices.foldLeft(BigInt(0)) { case (bits, lane) =>
          bits | (BigInt(1) << (lane * cellWidth))
        }
        val sourceOffset = inputOffsets(beginLane)
        val compactInput = if (sourceOffset == 0) input else s"($input >> $sourceOffset)"
        val expandedName = s"${resultName}_orr_expand_$beginLane"
        val flags = emitPext(
          s"(($expandedName | ${uint64Constant(guardMask)}) - ${uint64Constant(lsbMask)}) & ${uint64Constant(guardMask)}",
          guardMask
        )
        lines += s"uint64_t $expandedName = _pdep_u64($compactInput, UINT64_C(0x${dataMask.toString(16)}));"
        if (chunks.size == 1) lines += s"uint64_t $resultName = $flags;"
        else {
          val outputOffset = pack.outputOffsets(beginLane)
          val deposited = if (outputOffset == 0) flags else s"($flags << $outputOffset)"
          lines += s"$resultName |= $deposited;"
        }
      }
      lines.result()
    } else {
      def repeatedMask(width: Int): BigInt =
        laneOperations.indices.foldLeft(BigInt(0)) { case (bits, lane) =>
          bits | (((BigInt(1) << width) - 1) << (lane * laneWidth))
        }

      val stages = Vector.newBuilder[String]
      var current = input
      var activeWidth = laneWidth
      while (activeWidth > 1) {
        val shift = activeWidth / 2
        val nextName = s"${resultName}_orr_$shift"
        val mask = repeatedMask(shift)
        stages += s"uint64_t $nextName = ($current | ($current >> $shift)) & " +
          s"UINT64_C(0x${mask.toString(16)});"
        current = nextName
        activeWidth = shift
      }
      val laneLsbMask = repeatedMask(1)
      stages.result() :+ s"uint64_t $resultName = ${emitPext(current, laneLsbMask)};"
    }
  }

  /** Emit lane-local AND reductions.  Power-of-two lane widths use a compact
    * shift/AND fold because selected lane LSBs cannot receive bits from the
    * next lane.  Non-power-of-two lanes use the guard-cell zero test on the
    * inverted lane data, preserving lane independence.
    */
  private def emitAndrPack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Vector[String] = {
    require(pack.shape.opcode == SlpAndr)
    require(laneOperations.size == pack.parallelDegree)
    require(pack.totalResultWidth == pack.parallelDegree)
    require(laneOperations.forall {
      case SlpOperation(SlpAndr, 1, storageWidth, Vector(SlpSignal(_, inputWidth)), parameters, _) =>
        inputWidth > 1 && inputWidth <= 64 && storageWidth == inputWidth && parameters.isEmpty
      case _ => false
    })

    val laneWidth = laneOperations.head.operands.head.width
    require(laneOperations.forall(_.operands.head.width == laneWidth))
    require(laneWidth * pack.parallelDegree <= 64)
    require(argumentOffsets(laneOperations, 0) ==
      laneOperations.indices.map(_ * laneWidth).toVector,
      "Andr requires a dense packed input layout")

    val input = packedArgument(pack, laneOperations, 0)
    val resultName = packName(pack.id)
    if (isPowerOfTwo(laneWidth)) {
      val foldName = s"${resultName}_andr_fold"
      val lines = Vector.newBuilder[String]
      lines += s"uint64_t $foldName = $input;"
      var shift = 1
      while (shift < laneWidth) {
        lines += s"$foldName &= ($foldName >> $shift);"
        shift <<= 1
      }
      lines.result() :+
        s"uint64_t $resultName = ${emitPext(foldName, laneBitMask(laneWidth, 0, laneOperations.size))};"
    } else {
      val cellWidth = laneWidth + 1
      val lanesPerGroup = 64 / cellWidth
      val chunks = laneOperations.indices.grouped(lanesPerGroup).toVector
      val inputOffsets = argumentOffsets(laneOperations, 0)
      val lines = Vector.newBuilder[String]
      if (chunks.size > 1) lines += s"uint64_t $resultName = UINT64_C(0);"

      chunks.foreach { chunk =>
        val beginLane = chunk.head
        val dataMask = chunk.indices.foldLeft(BigInt(0)) { case (bits, lane) =>
          bits | (((BigInt(1) << laneWidth) - 1) << (lane * cellWidth))
        }
        val guardMask = chunk.indices.foldLeft(BigInt(0)) { case (bits, lane) =>
          bits | (BigInt(1) << (lane * cellWidth + laneWidth))
        }
        val lsbMask = chunk.indices.foldLeft(BigInt(0)) { case (bits, lane) =>
          bits | (BigInt(1) << (lane * cellWidth))
        }
        val laneMask = (BigInt(1) << chunk.size) - 1
        val sourceOffset = inputOffsets(beginLane)
        val compactInput = if (sourceOffset == 0) input else s"($input >> $sourceOffset)"
        val expandedName = s"${resultName}_andr_expand_$beginLane"
        val invertedName = s"${resultName}_andr_inverted_$beginLane"
        val nonAllOnes = emitPext(
          s"(($invertedName | ${uint64Constant(guardMask)}) - ${uint64Constant(lsbMask)}) & ${uint64Constant(guardMask)}",
          guardMask
        )
        val flags = s"(~$nonAllOnes & ${uint64Constant(laneMask)})"
        lines += s"uint64_t $expandedName = _pdep_u64($compactInput, ${uint64Constant(dataMask)});"
        lines += s"uint64_t $invertedName = (~$expandedName) & ${uint64Constant(dataMask)};"
        if (chunks.size == 1) lines += s"uint64_t $resultName = $flags;"
        else {
          val outputOffset = pack.outputOffsets(beginLane)
          val deposited = if (outputOffset == 0) flags else s"($flags << $outputOffset)"
          lines += s"$resultName |= $deposited;"
        }
      }
      lines.result()
    }
  }

  /** Emit identical bit-slices from every packed lane.
    *
    * FIRRTL `bits<hi,lo>` is a projection from each input lane.  When all
    * lanes use the same slice and both the input and output packs are dense,
    * a single PEXT expresses the whole pack-to-pack projection and avoids the
    * scalar unpack -> bits -> pack boundary.
    */
  private def emitBitsPack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Vector[String] = {
    require(pack.shape.opcode == SlpBits)
    require(laneOperations.size == pack.parallelDegree)
    require(laneOperations.nonEmpty)

    val first = laneOperations.head
    val inputWidth = first.operands.head.width
    val hi = first.parameters(0).toInt
    val lo = first.parameters(1).toInt
    val resultWidth = hi - lo + 1

    require(laneOperations.forall {
      case SlpOperation(SlpBits, laneResultWidth, storageWidth,
          Vector(SlpSignal(_, laneInputWidth)), parameters, _) =>
        laneInputWidth == inputWidth &&
          laneResultWidth == resultWidth &&
          storageWidth == inputWidth &&
          parameters == Vector(BigInt(hi), BigInt(lo))
      case _ => false
    })
    require(inputWidth * pack.parallelDegree <= 64)
    require(resultWidth * pack.parallelDegree <= 64)
    require(argumentOffsets(laneOperations, 0) ==
      laneOperations.indices.map(_ * inputWidth).toVector,
      "Bits requires a dense packed input layout")
    require(pack.outputOffsets ==
      laneOperations.indices.map(_ * resultWidth).toVector,
      "Bits requires a dense packed output layout")

    val input = packedArgument(pack, laneOperations, 0)
    val resultName = packName(pack.id)
    if (lo == 0 && resultWidth == inputWidth) {
      Vector(s"uint64_t $resultName = $input;")
    } else {
      val laneMask = (BigInt(1) << resultWidth) - 1
      val sourceMask = laneOperations.indices.foldLeft(BigInt(0)) { case (bits, laneIndex) =>
        bits | (laneMask << (laneIndex * inputWidth + lo))
      }
      Vector(s"uint64_t $resultName = ${emitPext(input, sourceMask)};")
    }
  }

  /** Emit identical arbitrary bit-gathers from every packed lane.
    *
    * ArmorBitGather is PEXT semantics.  When every lane uses the same mask and
    * both input and output layouts are dense, one word-level PEXT expresses
    * the whole pack-to-pack projection.  A contiguous mask is intentionally
    * treated as the same operation; any future shift/mask fast path belongs
    * here and does not affect SLP discovery.
    */
  private def emitBitGatherPack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Vector[String] = {
    require(pack.shape.opcode == SlpBitGather)
    require(laneOperations.size == pack.parallelDegree)
    require(laneOperations.nonEmpty)

    val first = laneOperations.head
    val inputWidth = first.operands.head.width
    val mask = first.parameters.head
    val resultWidth = first.resultWidth

    require(laneOperations.forall {
      case SlpOperation(SlpBitGather, laneResultWidth, storageWidth,
          Vector(SlpSignal(_, laneInputWidth)), parameters, _) =>
        laneInputWidth == inputWidth &&
          laneResultWidth == resultWidth &&
          storageWidth == inputWidth &&
          parameters == Vector(mask)
      case _ => false
    })
    require(inputWidth * pack.parallelDegree <= 64)
    require(resultWidth * pack.parallelDegree <= 64)
    require(argumentOffsets(laneOperations, 0) ==
      laneOperations.indices.map(_ * inputWidth).toVector,
      "ArmorBitGather requires a dense packed input layout")
    require(pack.outputOffsets ==
      laneOperations.indices.map(_ * resultWidth).toVector,
      "ArmorBitGather requires a dense packed output layout")

    val input = packedArgument(pack, laneOperations, 0)
    val resultName = packName(pack.id)
    val fullInputMask = (BigInt(1) << inputWidth) - 1
    if (mask == fullInputMask && resultWidth == inputWidth) {
      Vector(s"uint64_t $resultName = $input;")
    } else {
      val sourceMask = laneOperations.indices.foldLeft(BigInt(0)) { case (bits, laneIndex) =>
        bits | (mask << (laneIndex * inputWidth))
      }
      Vector(s"uint64_t $resultName = ${emitPext(input, sourceMask)};")
    }
  }

  /** Emit x <= 2^K-1 by OR-reducing each lane's bits K through W-1.  The
    * final mask selects only lane bit zero, so whole-word shifts cannot leak
    * adjacent-lane bits into the result.  PEXT compacts those inverted flags
    * to the one-bit output pack layout.
    */
  private def emitLeqLowMaskPack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Vector[String] = {
    require(pack.shape.opcode == SlpLeqLowMask)
    require(laneOperations.size == pack.parallelDegree)
    require(pack.totalResultWidth == pack.parallelDegree)
    require(laneOperations.forall {
      case SlpOperation(SlpLeqLowMask, 1, storageWidth,
          Vector(SlpSignal(_, inputWidth)), Vector(allowedLowBits), _) =>
        storageWidth == inputWidth && allowedLowBits >= 0 && allowedLowBits < inputWidth
      case _ => false
    })

    val laneWidth = laneOperations.head.operands.head.width
    val allowedLowBits = laneOperations.head.parameters.head.toInt
    require(laneOperations.forall(operation =>
      operation.operands.head.width == laneWidth && operation.parameters.head.toInt == allowedLowBits))
    require(laneWidth * pack.parallelDegree <= 64)
    require(argumentOffsets(laneOperations, 0) ==
      laneOperations.indices.map(_ * laneWidth).toVector,
      "ArmorLeqLowMask requires a dense packed input layout")

    val laneLsbMask = laneOperations.indices.foldLeft(BigInt(0)) { case (bits, lane) =>
      bits | (BigInt(1) << (lane * laneWidth))
    }
    val input = packedArgument(pack, laneOperations, 0)
    val resultName = packName(pack.id)
    val highName = s"${resultName}_high_nonzero"
    val lines = Vector.newBuilder[String]
    val first = if (allowedLowBits == 0) input else s"($input >> $allowedLowBits)"
    lines += s"uint64_t $highName = $first;"
    ((allowedLowBits + 1) until laneWidth).foreach { bit =>
      lines += s"$highName |= ($input >> $bit);"
    }
    lines += s"$highName &= UINT64_C(0x${laneLsbMask.toString(16)});"
    lines.result() :+ s"uint64_t $resultName = ${emitPext(s"~$highName", laneLsbMask)};"
  }

  private def trailingOneBits(value: BigInt, width: Int): Int = {
    require(width >= 0)
    var count = 0
    while (count < width && value.testBit(count)) count += 1
    count
  }

  private def trailingZeroBits(value: BigInt, width: Int): Int = {
    require(width >= 0)
    var count = 0
    while (count < width && !value.testBit(count)) count += 1
    count
  }

  /** Emit x <= C as a guarded per-lane subtract when trailing-one stripping
    * leaves an unused bit inside every lane:
    *
    *   x <= C, C low bits are all ones
    *   y = x >> trailingOnes(C)
    *   x <= C  <=>  y < ((C >> trailingOnes(C)) + 1)
    *
    * Each lane is laid out as W dense bits.  If y only occupies R<W bits, bit R
    * is a per-lane guard bit.  Setting that guard bit before subtracting the
    * threshold prevents borrow propagation across lanes.  The guard bit remains
    * set iff y >= threshold, so its inverse is the packed <= result.
    */
  private def emitLeqConstGuardSubtractPack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation],
    laneWidth:      Int,
    constant:       BigInt,
    input:          String,
    resultName:     String
  ): Option[Vector[String]] = {
    val degree = pack.parallelDegree
    val strippedLowBits = trailingOneBits(constant, laneWidth)
    if (strippedLowBits <= 0 || strippedLowBits >= laneWidth) return None

    val reducedWidth = laneWidth - strippedLowBits
    if (reducedWidth <= 0 || reducedWidth >= laneWidth) return None

    val threshold = (constant >> strippedLowBits) + 1
    if (threshold <= 0 || threshold >= (BigInt(1) << reducedWidth)) return None

    val maxGuardBit = (degree - 1) * laneWidth + reducedWidth
    if (maxGuardBit >= 64) return None

    val reducedLaneMask = (BigInt(1) << reducedWidth) - 1
    val fieldMask = laneOperations.indices.foldLeft(BigInt(0)) { case (bits, lane) =>
      bits | (reducedLaneMask << (lane * laneWidth))
    }
    val guardMask = laneOperations.indices.foldLeft(BigInt(0)) { case (bits, lane) =>
      bits | (BigInt(1) << (lane * laneWidth + reducedWidth))
    }
    val thresholdMask = laneOperations.indices.foldLeft(BigInt(0)) { case (bits, lane) =>
      bits | (threshold << (lane * laneWidth))
    }

    val reducedName = s"${resultName}_leq_reduced"
    val geName = s"${resultName}_leq_ge"
    Some(Vector(
      s"uint64_t $reducedName = ($input >> $strippedLowBits) & ${uint64Constant(fieldMask)};",
      s"uint64_t $geName = (($reducedName | ${uint64Constant(guardMask)}) - ${uint64Constant(thresholdMask)}) & ${uint64Constant(guardMask)};",
      s"uint64_t $resultName = ${emitPext(s"(~$geName) & ${uint64Constant(guardMask)}", guardMask)};"
    ))
  }

  /** Emit x <= (2^(W-1)-2).
    *
    * For every W-bit lane, x > (2^(W-1)-2) iff either the lane MSB is set or
    * the lower W-1 bits are all ones.  Adding one to the lower W-1-bit field
    * raises the lane MSB exactly for the all-ones case and cannot carry out of
    * the lane.
    */
  private def emitLeqConstLowHalfMinusTwoPack(
    laneOperations: Vector[SlpOperation],
    laneWidth:      Int,
    constant:       BigInt,
    input:          String,
    resultName:     String
  ): Option[Vector[String]] = {
    if (laneWidth < 2) return None
    val expected = (BigInt(1) << (laneWidth - 1)) - 2
    if (constant != expected || expected < 0) return None

    val laneCount = laneOperations.size
    val lowMask = laneBitRangeMask(laneWidth, laneCount, 0, laneWidth - 1)
    val lsbMask = laneBitMask(laneWidth, 0, laneCount)
    val msbMask = laneBitMask(laneWidth, laneWidth - 1, laneCount)
    val badName = s"${resultName}_leq_low_half_bad"
    Some(Vector(
      s"uint64_t $badName = (((($input & ${uint64Constant(lowMask)}) + " +
        s"${uint64Constant(lsbMask)}) | $input) & ${uint64Constant(msbMask)});",
      s"uint64_t $resultName = ${emitPext(s"(~$badName) & ${uint64Constant(msbMask)}", msbMask)};"
    ))
  }

  /** Emit x <= 2^(W-1).
    *
    * Values above the midpoint have the lane MSB set and at least one lower bit
    * set.  The `(low | msbMask) - lsbMask` idiom raises the lane MSB iff the
    * lower field is non-zero, with no cross-lane borrow because each lane's
    * MSB is pre-set before subtraction.
    */
  private def emitLeqConstMidpointPack(
    laneOperations: Vector[SlpOperation],
    laneWidth:      Int,
    constant:       BigInt,
    input:          String,
    resultName:     String
  ): Option[Vector[String]] = {
    if (laneWidth < 2) return None
    val expected = BigInt(1) << (laneWidth - 1)
    if (constant != expected) return None

    val laneCount = laneOperations.size
    val lowMask = laneBitRangeMask(laneWidth, laneCount, 0, laneWidth - 1)
    val lsbMask = laneBitMask(laneWidth, 0, laneCount)
    val msbMask = laneBitMask(laneWidth, laneWidth - 1, laneCount)
    val lowName = s"${resultName}_leq_mid_low"
    val lowNonzeroName = s"${resultName}_leq_mid_low_nonzero"
    val badName = s"${resultName}_leq_mid_bad"
    Some(Vector(
      s"uint64_t $lowName = $input & ${uint64Constant(lowMask)};",
      s"uint64_t $lowNonzeroName = (($lowName | ${uint64Constant(msbMask)}) - " +
        s"${uint64Constant(lsbMask)}) & ${uint64Constant(msbMask)};",
      s"uint64_t $badName = $input & $lowNonzeroName;",
      s"uint64_t $resultName = ${emitPext(s"(~$badName) & ${uint64Constant(msbMask)}", msbMask)};"
    ))
  }

  /** Emit x <= (2^W - 2^T), T in [1, W).
    *
    * This covers constants with an all-ones high prefix and a zero low suffix,
    * e.g. UInt<4> <= 0xc or <= 0xe.  A lane is greater than the constant iff
    * all prefix bits are one and any suffix bit is one.
    */
  private def emitLeqConstHighPrefixLowZeroPack(
    laneOperations: Vector[SlpOperation],
    laneWidth:      Int,
    constant:       BigInt,
    input:          String,
    resultName:     String
  ): Option[Vector[String]] = {
    if (laneWidth < 2 || constant <= 0) return None
    val zeroLowBits = trailingZeroBits(constant, laneWidth)
    if (zeroLowBits <= 0 || zeroLowBits >= laneWidth) return None

    val expected = (BigInt(1) << laneWidth) - (BigInt(1) << zeroLowBits)
    if (constant != expected) return None

    val laneLsbMask = laneOperations.indices.foldLeft(BigInt(0)) { case (bits, lane) =>
      bits | (BigInt(1) << (lane * laneWidth))
    }
    val lowNonzeroName = s"${resultName}_leq_prefix_low_nonzero"
    val highAllName = s"${resultName}_leq_prefix_high_all"
    val badName = s"${resultName}_leq_prefix_bad"
    val lines = Vector.newBuilder[String]

    lines += s"uint64_t $lowNonzeroName = $input;"
    (1 until zeroLowBits).foreach { bit =>
      lines += s"$lowNonzeroName |= ($input >> $bit);"
    }
    lines += s"$lowNonzeroName &= ${uint64Constant(laneLsbMask)};"

    lines += s"uint64_t $highAllName = ($input >> $zeroLowBits);"
    ((zeroLowBits + 1) until laneWidth).foreach { bit =>
      lines += s"$highAllName &= ($input >> $bit);"
    }
    lines += s"$highAllName &= ${uint64Constant(laneLsbMask)};"

    lines += s"uint64_t $badName = $highAllName & $lowNonzeroName;"
    lines += s"uint64_t $resultName = ${emitPext(s"(~$badName) & ${uint64Constant(laneLsbMask)}", laneLsbMask)};"
    Some(lines.result())
  }

  /** Emit a uniform unsigned x <= C comparison for every dense input lane.
    *
    * `equal` and `less` occupy only the least-significant bit of each input
    * lane.  The MSB-to-LSB recurrence is the ordinary unsigned comparator,
    * so this is independent of the input width and of C; only the generated
    * constants change.  PEXT finally compacts the one-bit lane results.
    */
  private def emitLeqConstPack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Vector[String] = {
    require(pack.shape.opcode == SlpLeqConst)
    require(laneOperations.size == pack.parallelDegree)
    require(pack.totalResultWidth == pack.parallelDegree)
    require(laneOperations.forall {
      case SlpOperation(SlpLeqConst, 1, storageWidth,
          Vector(SlpSignal(_, inputWidth)), Vector(constant), _) =>
        storageWidth == inputWidth && inputWidth >= 2 && inputWidth <= 17 &&
          constant >= 0 && constant < (BigInt(1) << inputWidth)
      case _ => false
    })

    val laneWidth = laneOperations.head.operands.head.width
    val constant = laneOperations.head.parameters.head
    require(laneOperations.forall(operation =>
      operation.operands.head.width == laneWidth && operation.parameters == Vector(constant)),
      "ArmorLeqConst requires one input width and one constant per pack")
    require(laneWidth * pack.parallelDegree <= 64)
    require(argumentOffsets(laneOperations, 0) ==
      laneOperations.indices.map(_ * laneWidth).toVector,
      "ArmorLeqConst requires a dense packed input layout")

    val laneLsbMask = laneOperations.indices.foldLeft(BigInt(0)) { case (bits, lane) =>
      bits | (BigInt(1) << (lane * laneWidth))
    }
    val mask = s"UINT64_C(0x${laneLsbMask.toString(16)})"
    val input = packedArgument(pack, laneOperations, 0)
    val resultName = packName(pack.id)
    emitLeqConstGuardSubtractPack(
      pack = pack,
      laneOperations = laneOperations,
      laneWidth = laneWidth,
      constant = constant,
      input = input,
      resultName = resultName
    ).orElse(emitLeqConstLowHalfMinusTwoPack(
      laneOperations = laneOperations,
      laneWidth = laneWidth,
      constant = constant,
      input = input,
      resultName = resultName
    )).orElse(emitLeqConstMidpointPack(
      laneOperations = laneOperations,
      laneWidth = laneWidth,
      constant = constant,
      input = input,
      resultName = resultName
    )).orElse(emitLeqConstHighPrefixLowZeroPack(
      laneOperations = laneOperations,
      laneWidth = laneWidth,
      constant = constant,
      input = input,
      resultName = resultName
    )).getOrElse {
    val equalName = s"${resultName}_leq_equal"
    val lessName = s"${resultName}_leq_less"
    val lines = Vector.newBuilder[String]
    lines += s"uint64_t $equalName = $mask;"
    lines += s"uint64_t $lessName = UINT64_C(0);"
    (laneWidth - 1 to 0 by -1).foreach { bit =>
      val bitName = s"${resultName}_leq_bit_$bit"
      lines += s"uint64_t $bitName = ($input >> $bit) & $mask;"
      if (constant.testBit(bit)) {
        lines += s"$lessName |= $equalName & (~$bitName);"
        lines += s"$equalName &= $bitName;"
      } else {
        lines += s"$equalName &= ~$bitName;"
      }
    }
    lines += s"uint64_t ${resultName}_leq_bits = ($lessName | $equalName) & $mask;"
    lines.result() :+ s"uint64_t $resultName = ${emitPext(s"${resultName}_leq_bits", laneLsbMask)};"
    }
  }

  private def emitAddPack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Vector[String] = {
    require(pack.shape.opcode == SlpAdd)
    require(pack.totalResultWidth <= 64)
    require(laneOperations.size == pack.parallelDegree)
    require(laneOperations.forall { operation =>
      operation.opcode == SlpAdd && operation.operands.size == 2 &&
        operation.operands.exists(_.isInstanceOf[SlpSignal]) &&
        operation.resultWidth == operation.operands.map(_.width).max + 1 &&
        operation.storageWidth == operation.resultWidth && operation.parameters.isEmpty
    })

    def packedConstant(argumentIndex: Int): String = {
      val value = laneOperations.zip(pack.outputOffsets).foldLeft(BigInt(0)) {
        case (bits, (operation, outputOffset)) =>
          val constant = operation.operands(argumentIndex).asInstanceOf[SlpUIntConstant]
          val mask = (BigInt(1) << constant.width) - 1
          bits | ((constant.value & mask) << outputOffset)
      }
      s"UINT64_C(0x${value.toString(16)})"
    }

    def swarExpansion(input: String, argumentIndex: Int): String = {
      val inputOffsets = argumentOffsets(laneOperations, argumentIndex)
      laneOperations.indices.map { laneIndex =>
        val width = laneOperations(laneIndex).operands(argumentIndex).width
        val inputOffset = inputOffsets(laneIndex)
        val outputOffset = pack.outputOffsets(laneIndex)
        val laneMask = s"UINT64_C(0x${((BigInt(1) << width) - 1).toString(16)})"
        val extracted = if (inputOffset == 0) s"($input & $laneMask)"
        else s"(($input >> $inputOffset) & $laneMask)"
        if (outputOffset == 0) extracted else s"($extracted << $outputOffset)"
      }.mkString("(", " | ", ")")
    }

    def expandedArgument(argumentIndex: Int): String = {
      val operands = laneOperations.map(_.operands(argumentIndex))
      if (operands.forall(_.isInstanceOf[SlpUIntConstant])) packedConstant(argumentIndex)
      else {
        val input = packedArgument(pack, laneOperations, argumentIndex)
        val inputOffsets = argumentOffsets(laneOperations, argumentIndex)
        val mapping = SlpBitMapping(
          sourceWidth = operands.map(_.width).sum,
          destinationWidth = pack.totalResultWidth,
          transfers = operands.indices.map { laneIndex =>
            SlpBitTransfer(
              inputOffsets(laneIndex),
              pack.outputOffsets(laneIndex),
              operands(laneIndex).width
            )
          }.toVector
        )
        require(mapping.canUseBitMapping)
        packedAddMode match {
          case "pdep" => lowerBitMapping(input, mapping).get
          case "swar" => swarExpansion(input, argumentIndex)
        }
      }
    }

    val left = expandedArgument(0)
    val right = expandedArgument(1)
    Vector(
      s"uint64_t ${packName(pack.id)} = $left + $right;"
    )
  }

  private def emitTruncatingAddPack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Vector[String] = {
    require(pack.shape.opcode == SlpTruncatingAdd)
    require(pack.totalResultWidth <= 64)
    require(laneOperations.size == pack.parallelDegree)
    require(laneOperations.forall {
      case SlpOperation(SlpTruncatingAdd, 16, 16,
          Vector(SlpSignal(_, 16), SlpUIntConstant(value, width)), parameters, _) =>
        value == 1 && width <= 16 && parameters == Vector(BigInt(17))
      case _ => false
    })

    val input = packedArgument(pack, laneOperations, 0)
    val laneHighBits = pack.outputOffsets.foldLeft(BigInt(0)) { case (mask, offset) =>
      mask | (BigInt(1) << (offset + 15))
    }
    val laneOnes = pack.outputOffsets.foldLeft(BigInt(0)) { case (mask, offset) =>
      mask | (BigInt(1) << offset)
    }
    val highMask = s"UINT64_C(0x${laneHighBits.toString(16)})"
    val ones = s"UINT64_C(0x${laneOnes.toString(16)})"
    Vector(
      s"uint64_t ${packName(pack.id)} = (($input & ~$highMask) + $ones) ^ ($input & $highMask);"
    )
  }

  /** Lower (left - right) mod 2^W without materializing the source Sub's
    * W+1-bit result.  Every temporary field has one additional guard bit set,
    * so a lane-local underflow cannot borrow from the following field.  The
    * first implementation intentionally requires dense W-bit signal layouts;
    * any required shuffle belongs in the projection/alignment planner.
    */
  private def emitTruncatingSubPack(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Vector[String] = {
    require(pack.shape.opcode == SlpTruncatingSub)
    require(pack.totalResultWidth <= 64)
    require(laneOperations.size == pack.parallelDegree)
    require(laneOperations.forall {
      case SlpOperation(SlpTruncatingSub, resultWidth, storageWidth,
          operands, parameters, _) =>
        resultWidth > 0 && resultWidth <= 63 && storageWidth == resultWidth &&
          parameters == Vector(BigInt(resultWidth + 1)) &&
          operands.size == 2 &&
          operands.exists(_.isInstanceOf[SlpSignal]) &&
          operands.forall {
            case SlpSignal(_, width) => width <= resultWidth
            case SlpUIntConstant(value, width) => value >= 0 && width <= resultWidth
          }
      case _ => false
    })

    val laneWidth = pack.shape.resultWidth
    val lanesPerChunk = 64 / (laneWidth + 1)
    require(lanesPerChunk > 0)
    require(pack.outputOffsets == laneOperations.indices.map(_ * laneWidth).toVector,
      "TruncatingSub requires a dense packed output layout")
    require(laneOperations.forall(_.operands.forall(_.width == laneWidth)),
      "TruncatingSub currently requires both operands to occupy the low-width result layout")
    (0 until 2).foreach { argumentIndex =>
      require(argumentOffsets(laneOperations, argumentIndex) ==
        laneOperations.indices.map(_ * laneWidth).toVector,
        s"TruncatingSub requires a dense packed input layout for argument $argumentIndex")
    }

    val resultName = packName(pack.id)
    val inputs = Vector(
      packedArgument(pack, laneOperations, 0),
      packedArgument(pack, laneOperations, 1)
    )
    val lines = Vector.newBuilder[String]
    lines += s"uint64_t $resultName = UINT64_C(0);"

    laneOperations.indices.grouped(lanesPerChunk).zipWithIndex.foreach {
      case (chunkIndices, chunkId) =>
        val chunk = chunkIndices.toVector
        val chunkLanes = chunk.size
        val inputOffset = chunk.head * laneWidth
        val outputOffset = inputOffset
        val fieldWidth = laneWidth + 1
        val dataMask = (0 until chunkLanes).foldLeft(BigInt(0)) { case (mask, lane) =>
          mask | (((BigInt(1) << laneWidth) - 1) << (lane * fieldWidth))
        }
        val guardMask = (0 until chunkLanes).foldLeft(BigInt(0)) { case (mask, lane) =>
          mask | (BigInt(1) << (lane * fieldWidth + laneWidth))
        }
        val dataMaskLiteral = s"UINT64_C(0x${dataMask.toString(16)})"
        val guardMaskLiteral = s"UINT64_C(0x${guardMask.toString(16)})"
        def expandedOperand(argumentIndex: Int, label: String): String = {
          val laneMask = (BigInt(1) << laneWidth) - 1
          val operands = chunk.map(laneOperations(_).operands(argumentIndex))
          if (operands.forall(_.isInstanceOf[SlpUIntConstant])) {
            val fieldValue = operands.zipWithIndex.foldLeft(BigInt(0)) {
              case (bits, (constant: SlpUIntConstant, lane)) =>
                bits | ((constant.value & laneMask) << (lane * fieldWidth))
              case (bits, _) => bits
            }
            s"UINT64_C(0x${fieldValue.toString(16)})"
          } else {
            val input = inputs(argumentIndex)
            val source = if (inputOffset == 0) input else s"($input >> $inputOffset)"
            val expandedName = s"${resultName}_sub_${chunkId}_$label"
            lines += s"uint64_t $expandedName = _pdep_u64($source, $dataMaskLiteral);"
            expandedName
          }
        }

        val diffName = s"${resultName}_sub_${chunkId}_diff"
        val compact = emitPext(diffName, dataMask)
        val leftExpanded = expandedOperand(argumentIndex = 0, label = "left")
        val rightExpanded = expandedOperand(argumentIndex = 1, label = "right")
        lines += s"uint64_t $diffName = ($leftExpanded | $guardMaskLiteral) - $rightExpanded;"
        val shifted = if (outputOffset == 0) compact else s"($compact << $outputOffset)"
        lines += s"$resultName |= $shifted;"
    }
    lines.result()
  }

  private def lowerBitMapping(input: String, mapping: SlpBitMapping): Option[String] = {
    if (!mapping.canUseBitMapping) return None

    val expression = if (mapping.hasIdenticalBitPositions) {
      if (mapping.destinationMask == (BigInt(1) << 64) - 1) input
      else s"($input & UINT64_C(0x${mapping.destinationMask.toString(16)}))"
    } else {
      val gathered = mapping.sourceContiguousRange match {
        case Some((0, width)) if width == mapping.sourceWidth => input
        case Some((0, 64)) => input
        case Some((offset, width)) =>
          val shifted = if (offset == 0) input else s"($input >> $offset)"
          if (width == 64) shifted
          else s"($shifted & UINT64_C(0x${((BigInt(1) << width) - 1).toString(16)}))"
        case None =>
          emitPext(input, mapping.sourceMask)
      }
      mapping.destinationContiguousRange match {
        case Some((0, _)) => gathered
        case Some((offset, _)) => s"($gathered << $offset)"
        case None =>
          s"_pdep_u64($gathered, UINT64_C(0x${mapping.destinationMask.toString(16)}))"
      }
    }
    Some(expression)
  }

  private def emitProjection(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation],
    projection:     SlpPackProjection
  ): Option[Vector[String]] = {
    require(projection.destinationPackId == pack.id)
    val resultName = packName(pack.id)
    Option.when(projection.canUseBitMapping)(
      packProjectionCsePrelude(pack.id) ++
        Vector(s"uint64_t $resultName = ${packProjectionTerm(pack.id, projection)};")
    )
  }

  /** Merge multiple opcode-independent projections into one packed result.
    * Cat is the first consumer: one projection maps the high operand and one
    * maps the low operand into non-overlapping result bits.
    */
  private def emitProjections(
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation],
    projections:    Vector[SlpPackProjection]
  ): Option[Vector[String]] = {
    val terms = projections.sortBy(_.argumentIndex).map { projection =>
      require(projection.destinationPackId == pack.id)
      Option.when(projection.canUseBitMapping)(packProjectionTerm(pack.id, projection))
    }
    if (terms.exists(_.isEmpty)) None
    else Some(packProjectionCsePrelude(pack.id) ++
      emitOrAccumulation(packName(pack.id), terms.flatten))
  }

  private def isCompleteCatProjection(
    pack:        SlpPack,
    projections: Vector[SlpPackProjection]
  ): Boolean = {
    if (pack.shape.opcode != SlpCat || projections.map(_.argumentIndex) != Vector(0, 1) ||
        !projections.forall(_.canUseBitMapping)) false
    else {
      val destinationMask = projections.foldLeft(BigInt(0)) { case (mask, projection) =>
        mask | projection.destinationMask
      }
      val selectedBits = projections.map(_.selectedWidth).sum
      val expectedMask = (BigInt(1) << pack.totalResultWidth) - 1
      destinationMask == expectedMask && destinationMask.bitCount == selectedBits
    }
  }

  private def originalNodesFor(pack: SlpPack): Vector[Int] = {
    val internal = pack.nodeIds.flatMap(nodeId =>
      regionsByRootNodeId.get(nodeId).toVector.flatMap(_.internalNodeIds)
    )
    internal ++ pack.nodeIds
  }

  private def isDshlSmallOpcode(opcode: SlpOpcode): Boolean = opcode match {
    case SlpDshlSmall(_, _, _) => true
    case _                     => false
  }

  private def isDshrSmallOpcode(opcode: SlpOpcode): Boolean = opcode match {
    case SlpDshrSmall(_, _) => true
    case _                  => false
  }

  private def emitPack(pack: SlpPack): Vector[String] = {
    val operationsForLanes = laneOperations(pack)
    val resultName = packName(pack.id)
    val projections = emittedPackProjections(pack)
    val projectionLowering = if (pack.shape.opcode == SlpCat) {
      Option.when(isCompleteCatProjection(pack, projections))(
        emitProjections(pack, operationsForLanes, projections)
      ).flatten
    } else {
      projections.headOption.flatMap(projection => emitProjection(pack, operationsForLanes, projection))
    }
    val lowered = if (fusedMaskedAndByPackId.contains(pack.id)) {
      Vector.empty
    } else if (directBitSelectInputsByPackId.contains(pack.id)) {
      val input = directBitSelectInputsByPackId(pack.id)
      val sourceName = s"${resultName}_bitselect_src"
      val gathered = emitBitMoveComposition(sourceName, input.bitMoves)
      Vector(
        s"uint64_t $sourceName = ${scalarWord(input.sourceName)};",
        s"uint64_t $resultName = ($gathered);"
      )
    } else if (projectionLowering.nonEmpty) {
      projectionLowering.get
    } else if (pack.shape.opcode == SlpTruncatingAdd) {
      emitTruncatingAddPack(pack, operationsForLanes)
    } else if (pack.shape.opcode == SlpTruncatingSub) {
      emitTruncatingSubPack(pack, operationsForLanes)
    } else if (pack.shape.opcode == SlpAdd) {
      emitAddPack(pack, operationsForLanes)
    } else if (pack.shape.opcode == SlpEqConst) {
      emitEqConstPack(pack, operationsForLanes)
    } else if (pack.shape.opcode == SlpEq) {
      emitEqPack(pack, operationsForLanes)
    } else if (pack.shape.opcode == SlpGeq) {
      emitGeqPack(pack, operationsForLanes)
    } else if (pack.shape.opcode == SlpLt) {
      emitLtPack(pack, operationsForLanes)
    } else if (pack.shape.opcode == SlpNeq) {
      emitNeqPack(pack, operationsForLanes)
    } else if (pack.shape.opcode == SlpOneHot) {
      emitOneHotPack(pack, operationsForLanes)
    } else if (pack.shape.opcode == SlpOrr) {
      emitOrrPack(pack, operationsForLanes)
    } else if (pack.shape.opcode == SlpAndr) {
      emitAndrPack(pack, operationsForLanes)
    } else if (pack.shape.opcode == SlpBits) {
      emitBitsPack(pack, operationsForLanes)
    } else if (pack.shape.opcode == SlpBitGather) {
      emitBitGatherPack(pack, operationsForLanes)
    } else if (pack.shape.opcode == SlpLeqLowMask) {
      emitLeqLowMaskPack(pack, operationsForLanes)
    } else if (pack.shape.opcode == SlpLeqConst) {
      emitLeqConstPack(pack, operationsForLanes)
    } else if (isDshlSmallOpcode(pack.shape.opcode)) {
      emitDshlSmallPack(pack, operationsForLanes)
    } else if (isDshrSmallOpcode(pack.shape.opcode)) {
      emitDshrSmallPack(pack, operationsForLanes)
    } else if (pack.shape.opcode == SlpMux) {
      emitMuxPack(pack, operationsForLanes)
    } else broadcastLowTruncationResultSplat(pack, operationsForLanes) match {
      case Some(expression) => Vector(s"uint64_t $resultName = $expression;")
      case None =>
        fastExpression(pack, operationsForLanes) match {
          case Some(expression) => Vector(s"uint64_t $resultName = $expression;")
          case None =>
            repeatedLaneResultSplat(pack, operationsForLanes) match {
              case Some(expression) => Vector(s"uint64_t $resultName = $expression;")
              case None =>
                val writes = pack.lanes.indices.toVector.map { laneIndex =>
                  SlpPackWordWrite(
                    laneExpression(pack, operationsForLanes, laneIndex),
                    pack.lanes(laneIndex).resultWidth,
                    pack.outputOffsets(laneIndex)
                  )
                }
                emitPackCallConstruction(resultName, writes)
            }
        }
    }
    lowered ++ pack.discoveryPhase.map(phase => s"// $phase").toVector ++
      loweredStatementComments(originalNodesFor(pack))
  }

  def emit(node: SlpScheduleNode): Vector[String] = node match {
    case SlpScalarScheduleNode(nodeId) =>
      laneBitwiseReductionProjectionByRootNodeId.get(nodeId).map(emitLaneBitwiseReductionProjection)
        .orElse(scalarReductionProjectionByRootNodeId.get(nodeId).map(emitScalarReductionProjection))
        .orElse(scalarProjectionByRootNodeId.get(nodeId).map(emitScalarProjection))
        .orElse(packedSideEffectGroupByLeaderNodeId.get(nodeId).map(emitPackedSideEffectGroup))
        .orElse(packedMemWriteGroupByLeaderNodeId.get(nodeId).map(emitPackedMemWriteGroup))
        .orElse(residualScalarRewriteByRootNodeId.get(nodeId).map(emitResidualScalarRewrite))
        .getOrElse {
          if (suppressedPackedSideEffectNodeIds(nodeId) ||
              suppressedPackedMemWriteNodeIds(nodeId) ||
              suppressedScalarProjectionInternalNodeIds(nodeId) ||
              suppressedScalarReductionInternalNodeIds(nodeId) ||
              suppressedLaneBitwiseReductionInternalNodeIds(nodeId) ||
              suppressedResidualScalarRewriteNodeIds(nodeId)) Vector.empty
          else if (suppressedBitMoveGatherProducerNodeIds(nodeId)) {
            loweredStatementComments(Vector(nodeId))
          }
          else indexedPackReadsByRootNodeId.get(nodeId).map(emitIndexedPackRead)
            .orElse(emitDirectIndexedRegisterRead(nodeId))
            .orElse(emitResidualIndexedMux(nodeId))
            .orElse(emitScalarIndexedMux(context.graph.node(nodeId).statement))
            .getOrElse(emitStmt(context.graph.node(nodeId).statement).toVector)
        }
    case SlpPackScheduleNode(packId)   => emitPack(plan.packGraph.pack(packId))
    case SlpRegUpdateScheduleNode(regPackId, fragmentId) => emitRegUpdatePack(regPackId, fragmentId)
    case SlpAlignmentScheduleNode(alignmentId) =>
      if (unpackAlignments(alignmentId)) {
        emitPackToScalar(plan.alignPlan.packToScalar.find(_.id == alignmentId).get)
      } else if (segmentAlignments.contains(alignmentId)) {
        emitPackSegment(segmentAlignments(alignmentId))
      } else {
        emitScalarToPack(plan.alignPlan.scalarToPack.find(_.id == alignmentId).getOrElse(
          throw new IllegalStateException(s"unknown SLP alignment $alignmentId")
        ))
      }
  }

  lazy val stats: SlpEmissionStats = {
    val muxPacks = plan.packGraph.packs.filter(_.shape.opcode == SlpMux)
    val broadcastMuxPacks = muxPacks.count(pack => muxKind(pack) == "broadcast")
    val oneBitMuxPacks = muxPacks.count(pack => muxKind(pack) == "one_bit")
    val laneMaskMuxPacks = muxPacks.count(pack => muxKind(pack) == "lane_mask")
    val fastPacks = plan.packGraph.packs.count { pack =>
      if (pack.shape.opcode == SlpCat)
        isCompleteCatProjection(pack, projectionsByPackId.getOrElse(pack.id, Vector.empty))
      else if (projectionsByPackId.get(pack.id).exists(_.head.canUseBitMapping)) true
      else if (pack.shape.opcode == SlpAdd || pack.shape.opcode == SlpTruncatingAdd ||
          pack.shape.opcode == SlpTruncatingSub ||
          pack.shape.opcode == SlpEq || pack.shape.opcode == SlpEqConst || pack.shape.opcode == SlpGeq ||
          pack.shape.opcode == SlpLt || pack.shape.opcode == SlpNeq || pack.shape.opcode == SlpOneHot ||
          pack.shape.opcode == SlpOrr || pack.shape.opcode == SlpAndr || pack.shape.opcode == SlpBits ||
          pack.shape.opcode == SlpLeqLowMask ||
          pack.shape.opcode == SlpLeqConst) true
      else if (pack.shape.opcode == SlpMux)
        muxKind(pack) != "lane_mask" || depositedMuxMaskConstants(pack, laneOperations(pack)).nonEmpty
      else fastExpression(pack, laneOperations(pack)).nonEmpty
    }
    SlpEmissionStats(
      scalarNodes = plan.scalarFallbackNodeIds.size,
      packNodes = plan.packGraph.packs.size,
      fastBitwisePacks = fastPacks,
      laneWisePacks = plan.packGraph.packs.size - fastPacks,
      scalarToPackNodes = plan.alignPlan.scalarToPack.size,
      packToScalarNodes = plan.alignPlan.packToScalar.size,
      packSegmentNodes = plan.alignPlan.packSegments.size,
      regUpdatePacks = regPacking.map(_.packs.size).getOrElse(0),
      scalarRegViews = plan.regViews.size,
      broadcastMuxPacks = broadcastMuxPacks,
      oneBitMuxPacks = oneBitMuxPacks,
      laneMaskMuxPacks = laneMaskMuxPacks,
      elidedMuxResultMasks = elidedMuxResultMasks
    )
  }
}
