package armor.slp

import essent.ir.{MemWrite, RegUpdate}
import firrtl.ir.{Connect, DefNode, Expression, IntWidth, Print, Reference, Statement, Stop, SubField, UIntLiteral, UIntType}

import scala.collection.mutable

sealed trait SlpAlignment {
  def id: Int
  def kind: String
}

sealed trait SlpLaneConsumer {
  def sortKey: (Int, Int, Int, Int)
  def description: String
}

final case class SlpScalarConsumer(nodeId: Int) extends SlpLaneConsumer {
  require(nodeId >= 0)
  def sortKey: (Int, Int, Int, Int) = (0, nodeId, -1, -1)
  def description: String = s"scalar:$nodeId"
}

final case class SlpPackArgumentConsumer(
  destinationPackId: Int,
  argumentIndex:     Int,
  destinationLane:   Int
) extends SlpLaneConsumer {
  require(destinationPackId >= 0)
  require(argumentIndex >= 0)
  require(destinationLane >= 0)
  def sortKey: (Int, Int, Int, Int) = (1, destinationPackId, argumentIndex, destinationLane)
  def description: String = s"pack:$destinationPackId:arg:$argumentIndex:lane:$destinationLane"
}

final case class SlpMaterializedLane(
  sourceLaneIndex: Int,
  sourceNodeId:    Int,
  outputName:      String,
  width:           Int,
  consumers:       Vector[SlpLaneConsumer],
  observable:      Boolean
) {
  require(sourceLaneIndex >= 0)
  require(sourceNodeId >= 0)
  require(outputName.nonEmpty)
  require(width > 0)
  require(consumers.nonEmpty || observable)
  require(consumers == consumers.distinct.sortBy(_.sortKey))
}

final case class SlpPackToScalarAlignment(
  id:           Int,
  sourcePackId: Int,
  lanes:        Vector[SlpMaterializedLane]
) extends SlpAlignment {
  require(id >= 0)
  require(sourcePackId >= 0)
  require(lanes.nonEmpty)
  require(lanes.map(_.sourceLaneIndex) == lanes.map(_.sourceLaneIndex).distinct.sorted)
  val kind = "pack_to_scalar"
}

sealed trait SlpPackInputLane {
  def destinationLane: Int
  def width: Int
}

final case class SlpScalarInputLane(
  destinationLane: Int,
  signalName:      String,
  width:           Int,
  producerNodeId:  Option[Int]
) extends SlpPackInputLane {
  require(destinationLane >= 0)
  require(signalName.nonEmpty)
  require(width > 0)
  require(producerNodeId.forall(_ >= 0))
}

final case class SlpConstantInputLane(
  destinationLane: Int,
  value:           BigInt,
  width:           Int
) extends SlpPackInputLane {
  require(destinationLane >= 0)
  require(value >= 0)
  require(width > 0)
}

final case class SlpUnpackedInputLane(
  destinationLane:        Int,
  signalName:             String,
  width:                  Int,
  sourcePackId:           Int,
  sourceLaneIndex:        Int,
  sourceNodeId:           Int,
  segmentAlignmentId:     Option[Int]
) extends SlpPackInputLane {
  require(destinationLane >= 0)
  require(signalName.nonEmpty)
  require(width > 0)
  require(sourcePackId >= 0)
  require(sourceLaneIndex >= 0)
  require(sourceNodeId >= 0)
  require(segmentAlignmentId.forall(_ >= 0))
}

final case class SlpRegInputLane(
  destinationLane:    Int,
  registerName:       String,
  width:              Int,
  regPackId:          Int,
  sourceLaneIndex:    Int,
  segmentAlignmentId: Option[Int]
) extends SlpPackInputLane {
  require(destinationLane >= 0)
  require(registerName.nonEmpty)
  require(width > 0)
  require(regPackId >= 0)
  require(sourceLaneIndex >= 0)
  require(segmentAlignmentId.forall(_ >= 0))
}

final case class SlpScalarToPackAlignment(
  id:                Int,
  destinationPackId: Int,
  argumentIndex:     Int,
  lanes:             Vector[SlpPackInputLane],
  laneOffsets:       Vector[Int]
) extends SlpAlignment {
  require(id >= 0)
  require(destinationPackId >= 0)
  require(argumentIndex >= 0)
  require(lanes.nonEmpty)
  require(lanes.map(_.destinationLane) == lanes.indices.toVector)
  require(laneOffsets == lanes.map(_.width).scanLeft(0)(_ + _).dropRight(1))
  val kind = "scalar_to_pack"
}

sealed trait SlpSegmentSource {
  def sourceId: Int
  def sortKind: Int
}

final case class SlpCombSegmentSource(sourceId: Int) extends SlpSegmentSource {
  require(sourceId >= 0)
  val sortKind = 0
}

final case class SlpRegSegmentSource(sourceId: Int) extends SlpSegmentSource {
  require(sourceId >= 0)
  val sortKind = 1
}

/** One reusable extraction of a continuous lane interval. This is the direct
  * immutable equivalent of the old AlignKey(source, begin, end).
  */
final case class SlpPackSegmentAlignment(
  id:              Int,
  source:          SlpSegmentSource,
  sourceLaneBegin: Int,
  sourceLaneEnd:   Int,
  sourceBitOffset: Int,
  width:           Int
) extends SlpAlignment {
  require(id >= 0)
  require(sourceLaneBegin >= 0)
  require(sourceLaneEnd > sourceLaneBegin)
  require(sourceBitOffset >= 0)
  require(width > 0 && width <= 64)
  require(sourceBitOffset + width <= 64)
  val kind = "pack_segment"
}

final case class SlpRegWriteInput(
  regPackId:   Int,
  lanes:       Vector[SlpPackInputLane],
  laneOffsets: Vector[Int]
) {
  require(regPackId >= 0)
  require(lanes.nonEmpty)
  require(lanes.map(_.destinationLane) == lanes.indices.toVector)
  require(laneOffsets == lanes.map(_.width).scanLeft(0)(_ + _).dropRight(1))
}

/** A direct input is legal only when every destination lane consumes the
  * corresponding lane of one source pack, with identical widths and offsets.
  */
final case class SlpDirectPackInput(
  sourcePackId:      Int,
  destinationPackId: Int,
  argumentIndex:     Int,
  sourceNodeIds:     Vector[Int],
  laneWidths:        Vector[Int],
  laneOffsets:       Vector[Int]
) {
  require(sourcePackId >= 0)
  require(destinationPackId >= 0)
  require(sourcePackId != destinationPackId)
  require(argumentIndex >= 0)
  require(sourceNodeIds.nonEmpty)
  require(sourceNodeIds.size == laneWidths.size)
  require(laneWidths.forall(_ > 0))
  require(laneOffsets == laneWidths.scanLeft(0)(_ + _).dropRight(1))
}

final case class SlpDirectRegInput(
  regPackId:         Int,
  destinationPackId: Int,
  argumentIndex:     Int,
  laneWidths:        Vector[Int],
  laneOffsets:       Vector[Int]
) {
  require(regPackId >= 0)
  require(destinationPackId >= 0)
  require(argumentIndex >= 0)
  require(laneWidths.nonEmpty)
  require(laneWidths.forall(_ > 0))
  require(laneOffsets == laneWidths.scanLeft(0)(_ + _).dropRight(1))
}

sealed trait SlpBroadcastValue {
  def width: Int
}

final case class SlpBroadcastSignal(
  signalName:     String,
  width:          Int,
  producerNodeId: Option[Int]
) extends SlpBroadcastValue {
  require(signalName.nonEmpty)
  require(width > 0)
  require(producerNodeId.forall(_ >= 0))
}

final case class SlpBroadcastConstant(value: BigInt, width: Int) extends SlpBroadcastValue {
  require(value >= 0)
  require(width > 0)
}

final case class SlpBroadcastPacked(
  sourcePackId:    Int,
  sourceLaneIndex: Int,
  sourceNodeId:    Int,
  width:           Int,
  offset:          Int
) extends SlpBroadcastValue {
  require(sourcePackId >= 0)
  require(sourceLaneIndex >= 0)
  require(sourceNodeId >= 0)
  require(width > 0)
  require(offset >= 0)
}

final case class SlpBroadcastReg(
  regPackId:      Int,
  sourceLaneIndex: Int,
  width:           Int,
  offset:          Int
) extends SlpBroadcastValue {
  require(regPackId >= 0)
  require(sourceLaneIndex >= 0)
  require(width > 0)
  require(offset >= 0)
}

/** One scalar value consumed by every lane of one packed argument.
  *
  * Mux conditions are intentionally represented separately from a normal
  * scalar-to-pack alignment: a shared condition is a broadcast control bit,
  * not a lane vector which should be packed repeatedly.
  */
final case class SlpBroadcastInput(
  destinationPackId: Int,
  argumentIndex:     Int,
  value:             SlpBroadcastValue
) {
  require(destinationPackId >= 0)
  require(argumentIndex >= 0)
}

/** Scalar identity of every packed result, whether or not Phase 3 needs to
  * materialize it.  This is the fallback mapping a future lowering uses to
  * restore the original StatementGraph name.
  */
final case class SlpPackedOutput(
  sourcePackId:              Int,
  sourceLaneIndex:           Int,
  sourceNodeId:              Int,
  outputName:                String,
  width:                     Int,
  offset:                    Int,
  materializationAlignmentId: Option[Int]
) {
  require(sourcePackId >= 0)
  require(sourceLaneIndex >= 0)
  require(sourceNodeId >= 0)
  require(outputName.nonEmpty)
  require(width > 0)
  require(offset >= 0)
  require(materializationAlignmentId.forall(_ >= 0))
}

final case class SlpAlignPlan(
  directPackInputs:       Vector[SlpDirectPackInput],
  directRegInputs:        Vector[SlpDirectRegInput],
  broadcastInputs:        Vector[SlpBroadcastInput],
  packToScalar:           Vector[SlpPackToScalarAlignment],
  packSegments:           Vector[SlpPackSegmentAlignment],
  scalarToPack:           Vector[SlpScalarToPackAlignment],
  alignmentProjections:   SlpAlignmentProjectionPlan,
  regWriteInputs:         Vector[SlpRegWriteInput],
  packedOutputs:          Vector[SlpPackedOutput],
  inputCount:             Int,
  materializedNodeIds:    Vector[Int]
) {
  val alignments: Vector[SlpAlignment] = (packToScalar ++ packSegments ++ scalarToPack).sortBy(_.id)
  require(alignments.map(_.id) == alignments.indices.toVector)
  require(inputCount == directPackInputs.size + directRegInputs.size + broadcastInputs.size +
    scalarToPack.size)
  require(materializedNodeIds == materializedNodeIds.distinct.sorted)
  require(packedOutputs.map(_.sourceNodeId).distinct.size == packedOutputs.size)
  require(packedOutputs == packedOutputs.sortBy(output => (output.sourcePackId, output.sourceLaneIndex)))
}

object SlpAlignPlanner {
  private sealed trait RawLane {
    def destinationLane: Int
    def width: Int
  }

  private final case class RawScalar(
    destinationLane: Int,
    signalName: String,
    width: Int,
    producerNodeId: Option[Int]
  ) extends RawLane

  private final case class RawConstant(
    destinationLane: Int,
    value: BigInt,
    width: Int
  ) extends RawLane

  private final case class RawPacked(
    destinationLane: Int,
    signalName: String,
    width: Int,
    sourcePackId: Int,
    sourceLaneIndex: Int,
    sourceNodeId: Int
  ) extends RawLane

  private final case class RawReg(
    destinationLane: Int,
    registerName: String,
    width: Int,
    regPackId: Int,
    sourceLaneIndex: Int
  ) extends RawLane

  private final case class SegmentKey(
    source: SlpSegmentSource,
    begin:  Int,
    end:    Int
  ) {
    require(begin >= 0 && end > begin)
    def sortKey: (Int, Int, Int, Int) = (source.sortKind, source.sourceId, begin, end)
  }

  private final case class RawInput(
    destinationPackId: Int,
    argumentIndex: Int,
    lanes: Vector[RawLane]
  )

  private final case class RawRegWrite(regPackId: Int, lanes: Vector[RawLane])

  private final case class LaneUse(
    consumers: Set[SlpLaneConsumer] = Set.empty,
    observable: Boolean = false
  )

  private final case class ProjectionOrigin(
    source:              SlpProjectionSource,
    sourceWidth:         Int,
    sourceBitOffset:     Int,
    destinationBitOffset: Int,
    width:               Int,
    destinationLane:     Int,
    segmentAlignmentId:  Option[Int]
  )

  def build(
    context: SlpAnalysisContext,
    packGraph: SlpPackGraph,
    regPacking: Option[SlpRegPackingResult] = None,
    coveredScalarUses: Set[(Int, Int)] = Set.empty,
    extraScalarUses: Set[(Int, Int)] = Set.empty
  ): SlpAlignPlan = {
    val view = context.graph
    val classifiedOperations = context.classifications.collect {
      case (nodeId, SlpSupported(operation)) => nodeId -> operation
    }.toMap
    val operations = classifiedOperations ++ packGraph.operationOverrides

    def producerId(name: String): Option[Int] =
      view.graph.nameToID.get(name).filter(id => id >= 0 && id < view.nodes.size)

    val regLaneByName: Map[String, (SlpRegPack, Int)] = regPacking.toVector
      .flatMap(_.packs)
      .flatMap(pack => pack.lanes.indices.map(index => pack.lanes(index).registerName -> (pack, index)))
      .toMap

    def rawLane(operand: SlpOperand, destinationLane: Int): RawLane = operand match {
      case SlpUIntConstant(value, width) => RawConstant(destinationLane, value, width)
      case SlpSignal(name, width) =>
        regLaneByName.get(name) match {
          case Some((regPack, sourceLaneIndex)) =>
            require(regPack.lanes(sourceLaneIndex).width == width)
            RawReg(destinationLane, name, width, regPack.id, sourceLaneIndex)
          case None =>
            val producer = producerId(name)
            producer.flatMap(packGraph.nodeToPackId.get) match {
              case Some(sourcePackId) =>
                val sourcePack = packGraph.pack(sourcePackId)
                val sourceNodeId = producer.get
                RawPacked(
                  destinationLane,
                  name,
                  width,
                  sourcePackId,
                  sourcePack.nodeIds.indexOf(sourceNodeId),
                  sourceNodeId
                )
              case None => RawScalar(destinationLane, name, width, producer)
            }
        }
    }

    val rawInputs = packGraph.packs.flatMap { destinationPack =>
      val laneOperations = destinationPack.nodeIds.map(operations)
      val runtimeArgumentIndices = laneOperations.head.operands.indices.filter { argumentIndex =>
        laneOperations.exists(_.operands(argumentIndex).isInstanceOf[SlpSignal]) ||
          (destinationPack.shape.opcode == SlpMux && argumentIndex == 0)
      }.toVector
      runtimeArgumentIndices.map { argumentIndex =>
        RawInput(
          destinationPack.id,
          argumentIndex,
          laneOperations.zipWithIndex.map { case (operation, destinationLane) =>
            rawLane(operation.operands(argumentIndex), destinationLane)
          }
        )
      }
    }.sortBy(input => (input.destinationPackId, input.argumentIndex))

    def directInput(input: RawInput): Option[SlpDirectPackInput] = {
      val packed = input.lanes.collect { case lane: RawPacked => lane }
      if (packed.size != input.lanes.size || packed.isEmpty) return None

      val sourcePackIds = packed.map(_.sourcePackId).distinct
      if (sourcePackIds.size != 1 || sourcePackIds.head == input.destinationPackId) return None
      val sourcePack = packGraph.pack(sourcePackIds.head)
      val sourceNodeIds = packed.map(_.sourceNodeId)
      val laneWidths = packed.map(_.width)
      val expectedOffsets = laneWidths.scanLeft(0)(_ + _).dropRight(1)
      val exactLayout =
        sourceNodeIds == sourcePack.nodeIds &&
        packed.map(_.sourceLaneIndex) == sourcePack.lanes.indices.toVector &&
        laneWidths == sourcePack.lanes.map(_.resultWidth) &&
        expectedOffsets == sourcePack.outputOffsets

      if (exactLayout) Some(SlpDirectPackInput(
        sourcePack.id,
        input.destinationPackId,
        input.argumentIndex,
        sourceNodeIds,
        laneWidths,
        expectedOffsets
      )) else None
    }

    val directByInput = rawInputs.flatMap(input => directInput(input).map((input.destinationPackId, input.argumentIndex) -> _)).toMap
    val directRegByInput = regPacking.toVector.flatMap(_.stateReads).flatMap { read =>
      packGraph.packsById.get(read.destinationPackId).flatMap { destinationPack =>
        val regPack = regPacking.get.packs.find(_.id == read.regPackId).get
        val laneOperations = destinationPack.nodeIds.map(operations)
        if (read.argumentIndex < laneOperations.head.operands.size) {
          val widths = laneOperations.map(_.operands(read.argumentIndex).width)
          val offsets = widths.scanLeft(0)(_ + _).dropRight(1)
          if (widths == regPack.laneWidths && offsets == regPack.laneOffsets)
            Some((read.destinationPackId, read.argumentIndex) -> SlpDirectRegInput(
              read.regPackId,
              read.destinationPackId,
              read.argumentIndex,
              widths,
              offsets
            ))
          else None
        } else None
      }
    }.toMap
    def splattableLanes(lanes: Vector[RawLane]): Boolean =
      lanes.nonEmpty && lanes.map(_.width).distinct.size == 1 && lanes.map(_.width).sum <= 64

    val broadcastByInput = rawInputs.flatMap { input =>
      input.lanes match {
        case lanes if splattableLanes(lanes) && lanes.forall {
          case RawScalar(_, name, width, producer) =>
            lanes.head match {
              case RawScalar(_, firstName, firstWidth, firstProducer) =>
                name == firstName && width == firstWidth && producer == firstProducer
              case _ => false
            }
          case _ => false
        } =>
          val first = lanes.head.asInstanceOf[RawScalar]
          Some((input.destinationPackId, input.argumentIndex) -> SlpBroadcastInput(
            input.destinationPackId,
            input.argumentIndex,
            SlpBroadcastSignal(first.signalName, first.width, first.producerNodeId)
          ))
        case lanes if splattableLanes(lanes) && lanes.forall {
          case RawConstant(_, value, width) =>
            lanes.head match {
              case RawConstant(_, firstValue, firstWidth) => value == firstValue && width == firstWidth
              case _ => false
            }
          case _ => false
        } =>
          val first = lanes.head.asInstanceOf[RawConstant]
          Some((input.destinationPackId, input.argumentIndex) -> SlpBroadcastInput(
            input.destinationPackId,
            input.argumentIndex,
            SlpBroadcastConstant(first.value, first.width)
          ))
        case lanes if splattableLanes(lanes) && lanes.forall {
          case RawPacked(_, name, width, sourcePackId, sourceLaneIndex, sourceNodeId) =>
            lanes.head match {
              case RawPacked(_, firstName, firstWidth, firstPackId, firstLaneIndex, firstNodeId) =>
                name == firstName && width == firstWidth && sourcePackId == firstPackId &&
                  sourceLaneIndex == firstLaneIndex && sourceNodeId == firstNodeId
              case _ => false
            }
          case _ => false
        } =>
          val first = lanes.head.asInstanceOf[RawPacked]
          val sourcePack = packGraph.pack(first.sourcePackId)
          Some((input.destinationPackId, input.argumentIndex) -> SlpBroadcastInput(
            input.destinationPackId,
            input.argumentIndex,
            SlpBroadcastPacked(
              first.sourcePackId,
              first.sourceLaneIndex,
              first.sourceNodeId,
              first.width,
              sourcePack.outputOffsets(first.sourceLaneIndex)
            )
          ))
        case lanes if splattableLanes(lanes) && lanes.forall {
          case RawReg(_, name, width, regPackId, sourceLaneIndex) =>
            lanes.head match {
              case RawReg(_, firstName, firstWidth, firstPackId, firstLaneIndex) =>
                name == firstName && width == firstWidth && regPackId == firstPackId &&
                  sourceLaneIndex == firstLaneIndex
              case _ => false
            }
          case _ => false
        } =>
          val first = lanes.head.asInstanceOf[RawReg]
          val regPack = regPacking.get.packs.find(_.id == first.regPackId).get
          Some((input.destinationPackId, input.argumentIndex) -> SlpBroadcastInput(
            input.destinationPackId,
            input.argumentIndex,
            SlpBroadcastReg(
              first.regPackId,
              first.sourceLaneIndex,
              first.width,
              regPack.laneOffsets(first.sourceLaneIndex)
            )
          ))
        case _ => None
      }
    }.toMap
    val nonDirectInputs = rawInputs.filterNot { input =>
      val key = (input.destinationPackId, input.argumentIndex)
      directByInput.contains(key) || directRegByInput.contains(key) || broadcastByInput.contains(key)
    }

    def expressionName(expression: Expression): Option[String] = expression match {
      case Reference(name, _, _, _)   => Some(name)
      case SubField(base, name, _, _) => expressionName(base).map(prefix => s"$prefix.$name")
      case _                          => None
    }

    // A terminal Mux write is already emitted directly by SlpEmitter, just
    // like an exact packed producer. Do not build a scalar RegUpdate input
    // alignment for either closed state-write form.
    val directWriteRegPackIds = regPacking.toVector.flatMap { packing =>
      packing.directWrites.map(_.regPackId) ++ packing.muxWrites.map(_.regPackId)
    }.toSet
    val rawRegWrites = regPacking.toVector.flatMap(_.packs).filterNot(pack =>
      directWriteRegPackIds(pack.id)
    ).map { regPack =>
      val lanes = regPack.lanes.zipWithIndex.map { case (lane, destinationLane) =>
        val expression = view.node(lane.updateNodeId).statement.asInstanceOf[RegUpdate].expr
        expression match {
          case UIntLiteral(value, IntWidth(_)) =>
            RawConstant(destinationLane, value, lane.width)
          case _ =>
            val name = expressionName(expression).getOrElse(
              throw new IllegalStateException(
                s"packed RegUpdate ${lane.updateNodeId} has a non-leaf update expression"
              )
            )
            rawLane(SlpSignal(name, lane.width), destinationLane)
        }
      }
      RawRegWrite(regPack.id, lanes)
    }

    def sameSegment(left: RawLane, right: RawLane): Boolean = (left, right) match {
      case (a: RawPacked, b: RawPacked) =>
        a.sourcePackId == b.sourcePackId && b.sourceLaneIndex == a.sourceLaneIndex + 1 &&
          b.destinationLane == a.destinationLane + 1
      case (a: RawReg, b: RawReg) =>
        a.regPackId == b.regPackId && b.sourceLaneIndex == a.sourceLaneIndex + 1 &&
          b.destinationLane == a.destinationLane + 1
      case _ => false
    }

    def packedRuns(lanes: Vector[RawLane]): Vector[Vector[RawLane]] = {
      val result = Vector.newBuilder[Vector[RawLane]]
      var current = Vector.empty[RawLane]
      def flush(): Unit = if (current.nonEmpty) {
        result += current
        current = Vector.empty
      }
      lanes.foreach {
        case lane: RawPacked =>
          if (current.nonEmpty && !sameSegment(current.last, lane)) flush()
          current :+= lane
        case lane: RawReg =>
          if (current.nonEmpty && !sameSegment(current.last, lane)) flush()
          current :+= lane
        case _ => flush()
      }
      flush()
      result.result()
    }

    def segmentKey(run: Vector[RawLane]): Option[SegmentKey] = run.head match {
      case first: RawPacked =>
        val sourcePack = packGraph.pack(first.sourcePackId)
        val begin = first.sourceLaneIndex
        val end = begin + run.size
        if (begin == 0 && end == sourcePack.lanes.size) None
        else Some(SegmentKey(SlpCombSegmentSource(first.sourcePackId), begin, end))
      case first: RawReg =>
        val sourcePack = regPacking.get.packs.find(_.id == first.regPackId).get
        val begin = first.sourceLaneIndex
        val end = begin + run.size
        if (begin == 0 && end == sourcePack.lanes.size) None
        else Some(SegmentKey(SlpRegSegmentSource(first.regPackId), begin, end))
      case _ => None
    }

    val allSegmentKeys = (nonDirectInputs.map(_.lanes) ++ rawRegWrites.map(_.lanes))
      .flatMap(packedRuns)
      .flatMap(segmentKey)
      .distinct
      .sortBy(_.sortKey)

    val laneUses = mutable.HashMap.empty[Int, LaneUse].withDefaultValue(LaneUse())
    val packedRegUpdateNodeIds = regPacking.toVector.flatMap(_.packs).flatMap(_.nodeIds).toSet
    // Only executable scalar fallback nodes require a scalar view.  Region
    // internals are absent from nodeToPackId, but are absorbed by their root
    // pack and never emitted as scalar statements.  Treating them as scalar
    // consumers used to materialize dead unpack_bits views for every such
    // edge, even when the real downstream use had a direct packed path.
    val nonScalarConsumerNodeIds =
      packGraph.nodeToPackId.keySet ++ packedRegUpdateNodeIds ++ packGraph.absorbedNodeIds

    /** StatementGraph fanout intentionally bypasses simple aliases and may
      * therefore contain transitive consumers.  A packed source only needs a
      * scalar materialization for a statement that directly reads its named
      * value.  Using the transitive graph fanout here created dead scalar
      * unpack views when the direct reader was lowered through a packed path.
      */
    def expressionReferences(expression: Expression): Vector[String] = {
      expressionName(expression) match {
        case Some(name) => Vector(name)
        case None =>
          val names = Vector.newBuilder[String]
          expression.foreachExpr(child => names ++= expressionReferences(child))
          names.result()
      }
    }

    def statementInputNames(statement: Statement): Vector[String] = statement match {
      case DefNode(_, _, value) => expressionReferences(value)
      case Connect(_, _, expr)  => expressionReferences(expr)
      case update: RegUpdate    => expressionReferences(update.expr)
      case write: MemWrite      =>
        Vector(write.wrEn, write.wrMask, write.wrAddr, write.wrData)
          .flatMap(expressionReferences)
      // Print and Stop are scalar side-effecting consumers.  Their values are
      // not represented as normal dataflow nodes, but must still be
      // materialized when they read a value produced by a pack.
      case print: Print => expressionReferences(print.en) ++ print.args.flatMap(expressionReferences)
      case stop: Stop   => expressionReferences(stop.en)
      case _ => Vector.empty
    }

    val directConsumerIdsBySignal = (view.validNodeIds.flatMap { consumerNodeId =>
      statementInputNames(view.node(consumerNodeId).statement).distinct
        .map(_ -> consumerNodeId)
    } ++ extraScalarUses.toVector.flatMap { case (sourceNodeId, consumerNodeId) =>
      Option.when(sourceNodeId >= 0 && sourceNodeId < view.nodes.size &&
          consumerNodeId >= 0 && consumerNodeId < view.nodes.size) {
        view.node(sourceNodeId).name -> consumerNodeId
      }
    }).groupMap(_._1)(_._2).view.mapValues(_.distinct.sorted).toMap

    def addConsumer(sourceNodeId: Int, consumer: SlpLaneConsumer): Unit = {
      val current = laneUses(sourceNodeId)
      laneUses.update(sourceNodeId, current.copy(consumers = current.consumers + consumer))
    }

    packGraph.packs.foreach { sourcePack =>
      sourcePack.nodeIds.foreach { sourceNodeId =>
        directConsumerIdsBySignal.getOrElse(view.node(sourceNodeId).name, Vector.empty)
          .filterNot(nonScalarConsumerNodeIds)
          .filterNot(consumerNodeId => coveredScalarUses(sourceNodeId -> consumerNodeId))
          .foreach(consumerNodeId => addConsumer(sourceNodeId, SlpScalarConsumer(consumerNodeId)))

        val sourceNode = view.node(sourceNodeId)
        val observable = view.externalNames.contains(sourceNode.name) && sourceNode.statement.isInstanceOf[Connect]
        if (observable) {
          val current = laneUses(sourceNodeId)
          laneUses.update(sourceNodeId, current.copy(observable = true))
        }
      }
    }

    val packToScalar = packGraph.packs.flatMap { sourcePack =>
      val lanes = sourcePack.lanes.zipWithIndex.flatMap { case (lane, sourceLaneIndex) =>
        laneUses.get(lane.nodeId).filter(use => use.consumers.nonEmpty || use.observable).map { use =>
          SlpMaterializedLane(
            sourceLaneIndex,
            lane.nodeId,
            view.node(lane.nodeId).name,
            lane.resultWidth,
            use.consumers.toVector.sortBy(_.sortKey),
            use.observable
          )
        }
      }
      if (lanes.nonEmpty) Some(sourcePack.id -> lanes) else None
    }.zipWithIndex.map { case ((sourcePackId, lanes), alignmentId) =>
      SlpPackToScalarAlignment(alignmentId, sourcePackId, lanes)
    }
    val unpackByPack = packToScalar.iterator.map(alignment => alignment.sourcePackId -> alignment).toMap

    val packSegments = allSegmentKeys.zipWithIndex.map { case (key, index) =>
      val (offset, width) = key.source match {
        case SlpCombSegmentSource(sourcePackId) =>
          val sourcePack = packGraph.pack(sourcePackId)
          sourcePack.outputOffsets(key.begin) ->
            sourcePack.lanes.slice(key.begin, key.end).map(_.resultWidth).sum
        case SlpRegSegmentSource(regPackId) =>
          val sourcePack = regPacking.get.packs.find(_.id == regPackId).get
          sourcePack.laneOffsets(key.begin) -> sourcePack.laneWidths.slice(key.begin, key.end).sum
      }
      SlpPackSegmentAlignment(
        packToScalar.size + index,
        key.source,
        key.begin,
        key.end,
        offset,
        width
      )
    }
    val segmentIdByKey = allSegmentKeys.zip(packSegments.map(_.id)).toMap

    def convertLanes(rawLanes: Vector[RawLane]): Vector[SlpPackInputLane] = {
      val alignmentByDestinationLane = packedRuns(rawLanes).flatMap { run =>
        val alignmentId = segmentKey(run).map(segmentIdByKey)
        run.map(_.destinationLane -> alignmentId)
      }.toMap
      rawLanes.map {
        case RawScalar(destinationLane, signalName, width, producerNodeId) =>
          SlpScalarInputLane(destinationLane, signalName, width, producerNodeId)
        case RawConstant(destinationLane, value, width) =>
          SlpConstantInputLane(destinationLane, value, width)
        case RawPacked(destinationLane, signalName, width, sourcePackId, sourceLaneIndex, sourceNodeId) =>
          SlpUnpackedInputLane(
            destinationLane,
            signalName,
            width,
            sourcePackId,
            sourceLaneIndex,
            sourceNodeId,
            alignmentByDestinationLane(destinationLane)
          )
        case RawReg(destinationLane, registerName, width, regPackId, sourceLaneIndex) =>
          SlpRegInputLane(
            destinationLane,
            registerName,
            width,
            regPackId,
            sourceLaneIndex,
            alignmentByDestinationLane(destinationLane)
          )
      }
    }

    val scalarToPack = nonDirectInputs.zipWithIndex.map { case (input, index) =>
      val lanes = convertLanes(input.lanes)
      SlpScalarToPackAlignment(
        packToScalar.size + packSegments.size + index,
        input.destinationPackId,
        input.argumentIndex,
        lanes,
        lanes.map(_.width).scanLeft(0)(_ + _).dropRight(1)
      )
    }

    val regWriteInputs = rawRegWrites.map { input =>
      val lanes = convertLanes(input.lanes)
      SlpRegWriteInput(
        input.regPackId,
        lanes,
        lanes.map(_.width).scanLeft(0)(_ + _).dropRight(1)
      )
    }

    def projectionOrigins(
      lanes:       Vector[SlpPackInputLane],
      laneOffsets: Vector[Int]
    ): Vector[ProjectionOrigin] =
      lanes.zip(laneOffsets).flatMap {
        case (lane: SlpUnpackedInputLane, destinationBitOffset) =>
          val sourcePack = packGraph.pack(lane.sourcePackId)
          Some(ProjectionOrigin(
            source = SlpProjectionCombPack(lane.sourcePackId),
            sourceWidth = sourcePack.totalResultWidth,
            sourceBitOffset = sourcePack.outputOffsets(lane.sourceLaneIndex),
            destinationBitOffset = destinationBitOffset,
            width = lane.width,
            destinationLane = lane.destinationLane,
            segmentAlignmentId = lane.segmentAlignmentId
          ))
        case (lane: SlpRegInputLane, destinationBitOffset) =>
          regPacking.flatMap(_.packs.find(_.id == lane.regPackId)).map { sourcePack =>
            ProjectionOrigin(
              source = SlpProjectionRegPack(lane.regPackId),
              sourceWidth = sourcePack.totalWidth,
              sourceBitOffset = sourcePack.laneOffsets(lane.sourceLaneIndex),
              destinationBitOffset = destinationBitOffset,
              width = lane.width,
              destinationLane = lane.destinationLane,
              segmentAlignmentId = lane.segmentAlignmentId
            )
          }
        case _ => None
      }

    def buildAlignmentProjection(
      alignment: SlpScalarToPackAlignment
    ): Option[SlpAlignmentProjection] = {
      val destinationWidth = alignment.lanes.map(_.width).sum
      if (destinationWidth > 64) return None

      val terms = projectionOrigins(alignment.lanes, alignment.laneOffsets)
        .groupBy(origin => origin.source -> origin.sourceWidth)
        .toVector
        .flatMap { case ((source, sourceWidth), origins) =>
          val sorted = origins.sortBy(_.destinationBitOffset)
          // A one-lane projection usually just renames one pack segment and
          // does not reduce work. Keep it on the existing scalar path.
          if (sorted.size < 2) None
          else {
            val transfers = sorted.map(origin =>
              SlpBitTransfer(
                sourceOffset = origin.sourceBitOffset,
                destinationOffset = origin.destinationBitOffset,
                width = origin.width
              )
            )
            val term = SlpAlignmentProjectionTerm(
              source = source,
              sourceWidth = sourceWidth,
              destinationWidth = destinationWidth,
              transfers = transfers,
              coveredDestinationLanes = sorted.map(_.destinationLane).distinct.sorted,
              segmentAlignmentIds = sorted.flatMap(_.segmentAlignmentId).toSet
            )
            Option.when(term.canUseBitMapping)(term)
          }
        }
        .sortBy(term => (term.coveredDestinationLanes.head, term.source.toString))

      Option.when(terms.nonEmpty)(SlpAlignmentProjection(alignment.id, terms))
    }

    val alignmentProjections = SlpAlignmentProjectionPlan(
      scalarToPack.flatMap(buildAlignmentProjection).sortBy(_.alignmentId)
    )

    val packedOutputs = packGraph.packs.flatMap { sourcePack =>
      val materializationId = unpackByPack.get(sourcePack.id).map(_.id)
      sourcePack.lanes.zipWithIndex.map { case (lane, sourceLaneIndex) =>
        val isMaterialized = unpackByPack.get(sourcePack.id)
          .exists(_.lanes.exists(_.sourceLaneIndex == sourceLaneIndex))
        SlpPackedOutput(
          sourcePack.id,
          sourceLaneIndex,
          lane.nodeId,
          view.node(lane.nodeId).name,
          lane.resultWidth,
          sourcePack.outputOffsets(sourceLaneIndex),
          if (isMaterialized) materializationId else None
        )
      }
    }

    SlpAlignPlan(
      directPackInputs = directByInput.values.toVector.sortBy(input =>
        (input.destinationPackId, input.argumentIndex, input.sourcePackId)
      ),
      directRegInputs = directRegByInput.values.toVector.sortBy(input =>
        (input.destinationPackId, input.argumentIndex, input.regPackId)
      ),
      broadcastInputs = broadcastByInput.values.toVector.sortBy(input =>
        (input.destinationPackId, input.argumentIndex)
      ),
      packToScalar = packToScalar,
      packSegments = packSegments,
      scalarToPack = scalarToPack,
      alignmentProjections = alignmentProjections,
      regWriteInputs = regWriteInputs,
      packedOutputs = packedOutputs,
      inputCount = rawInputs.size,
      materializedNodeIds = packToScalar.flatMap(_.lanes.map(_.sourceNodeId)).distinct.sorted
    )
  }
}
