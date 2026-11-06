package armor.slp

import armor.ArmorIndexedMux
import firrtl.ir.{DefNode, DoPrim, Expression, IntWidth, Reference, SubField, SubIndex, Type, UIntType}

/** A scalar ArmorIndexedMux which can read its selected value directly from a
  * combinational SLP pack.  semanticLaneOffsets is indexed by the semantic
  * vector index, not by the producer pack's physical lane order. */
sealed trait SlpIndexedPackReadKind
case object SlpIndexedDensePackRead extends SlpIndexedPackReadKind
case object SlpIndexedOffsetTablePackRead extends SlpIndexedPackReadKind
case object SlpIndexedFragmentedPackRead extends SlpIndexedPackReadKind

final case class SlpIndexedReadFragment(
  indexStart:   Int,
  laneCount:    Int,
  sourcePackId: Int,
  sourceOffset: Int
) {
  require(indexStart >= 0)
  require(laneCount > 0)
  require(sourcePackId >= 0)
  require(sourceOffset >= 0)

  def indexEnd: Int = indexStart + laneCount - 1
}

final case class SlpIndexedPackRead(
  rootNodeId:          Int,
  sourcePackId:        Int,
  index:               Expression,
  resultWidth:         Int,
  sourceWidth:         Int,
  semanticLaneOffsets: Vector[Int],
  kind:                SlpIndexedPackReadKind,
  offsetTable:         Option[BigInt],
  offsetBits:          Int,
  coveredSourceNodeIds: Vector[Int],
  fragments:           Vector[SlpIndexedReadFragment] = Vector.empty
) {
  require(rootNodeId >= 0)
  require(sourcePackId >= 0)
  require(resultWidth > 0 && resultWidth <= 64)
  require(sourceWidth > 0 && sourceWidth <= 64)
  require(semanticLaneOffsets.nonEmpty)
  require(semanticLaneOffsets.size == coveredSourceNodeIds.size)
  require(offsetBits >= 0)
  require(kind == SlpIndexedDensePackRead ||
    kind == SlpIndexedOffsetTablePackRead ||
    kind == SlpIndexedFragmentedPackRead)
  if (kind == SlpIndexedFragmentedPackRead) {
    require(resultWidth == 1)
    require(offsetTable.isEmpty)
    require(offsetBits == 0)
    require(fragments.nonEmpty)
    require(fragments.map(_.indexStart).sorted == fragments.map(_.indexStart))
    require(fragments.head.indexStart == 0)
    require(fragments.last.indexEnd == semanticLaneOffsets.size - 1)
    require(fragments.sliding(2).forall {
      case Vector(left, right) => left.indexEnd + 1 == right.indexStart
      case _                   => true
    })
  } else {
    require(fragments.isEmpty)
    require(semanticLaneOffsets.forall(offset => offset >= 0 && offset + resultWidth <= sourceWidth))
    require(kind == SlpIndexedDensePackRead || offsetTable.nonEmpty)
  }

  val sourcePackIds: Vector[Int] =
    if (kind == SlpIndexedFragmentedPackRead) fragments.map(_.sourcePackId).distinct.sorted
    else Vector(sourcePackId)

  val coveredScalarUses: Set[(Int, Int)] =
    coveredSourceNodeIds.iterator.map(_ -> rootNodeId).toSet
}

final case class SlpIndexedPackReadPlan(reads: Vector[SlpIndexedPackRead]) {
  require(reads.map(_.rootNodeId) == reads.map(_.rootNodeId).distinct.sorted)

  val byRootNodeId: Map[Int, SlpIndexedPackRead] =
    reads.iterator.map(read => read.rootNodeId -> read).toMap
  val coveredScalarUses: Set[(Int, Int)] =
    reads.iterator.flatMap(_.coveredScalarUses).toSet
}

object SlpIndexedPackReadPlan {
  val Empty: SlpIndexedPackReadPlan = SlpIndexedPackReadPlan(Vector.empty)
}

/** Plan direct reads from an existing combinational pack without changing the
  * meaning of ArmorIndexedMux.  Unsupported layouts deliberately receive no
  * plan and retain the normal scalar layered-Mux fallback. */
object SlpIndexedPackReadPlanner {
  private val MaxFragmentedIndexedReadFragments = 4

  private final case class ResolvedIndexedLane(
    index:        Int,
    nodeId:       Int,
    sourcePackId: Int,
    sourceOffset: Int,
    sourceWidth:  Int,
    laneWidth:    Int
  )

  private def uintWidth(expression: Expression): Option[Int] = expression.tpe match {
    case UIntType(IntWidth(width)) if width > 0 && width.isValidInt => Some(width.toInt)
    case _                                                          => None
  }

  private def uintTypeWidth(tpe: Type): Option[Int] = tpe match {
    case UIntType(IntWidth(width)) if width > 0 && width.isValidInt => Some(width.toInt)
    case _                                                          => None
  }

  private def referenceName(expression: Expression): Option[String] = expression match {
    case Reference(name, _, _, _)       => Some(name)
    case SubField(base, name, _, _)     => referenceName(base).map(prefix => s"$prefix.$name")
    case SubIndex(base, index, _, _)    => referenceName(base).map(prefix => s"${prefix}_$index")
    case _                              => None
  }

  private def ceilLog2(value: Int): Int = {
    require(value > 0)
    if (value <= 1) 0 else Integer.SIZE - Integer.numberOfLeadingZeros(value - 1)
  }

  private def contiguousFragments(lanes: Vector[ResolvedIndexedLane]): Vector[SlpIndexedReadFragment] = {
    require(lanes.nonEmpty)

    val builder = Vector.newBuilder[SlpIndexedReadFragment]
    var start = lanes.head.index
    var count = 1
    var sourcePackId = lanes.head.sourcePackId
    var sourceOffset = lanes.head.sourceOffset

    def flush(): Unit =
      builder += SlpIndexedReadFragment(start, count, sourcePackId, sourceOffset)

    lanes.tail.foreach { lane =>
      val expectedIndex = start + count
      val expectedSourceOffset = sourceOffset + count
      if (lane.index == expectedIndex &&
          lane.sourcePackId == sourcePackId &&
          lane.sourceOffset == expectedSourceOffset) {
        count += 1
      } else {
        flush()
        start = lane.index
        count = 1
        sourcePackId = lane.sourcePackId
        sourceOffset = lane.sourceOffset
      }
    }
    flush()
    builder.result()
  }

  private def planSingleSource(
    nodeId:      Int,
    index:       Expression,
    resultWidth: Int,
    lanes:       Vector[ResolvedIndexedLane]
  ): Option[SlpIndexedPackRead] = {
    val sourcePackIds = lanes.map(_.sourcePackId).distinct
    if (sourcePackIds.size != 1) None
    else {
      val sourcePackId = sourcePackIds.head
      val sourceWidth = lanes.head.sourceWidth
      val offsets = lanes.map(_.sourceOffset)
      val dense = offsets == lanes.indices.map(_ * resultWidth).toVector
      val offsetBits = math.max(1, ceilLog2(sourceWidth))
      val tableBits = offsetBits * lanes.size
      val kind =
        Option.when(dense)(SlpIndexedDensePackRead: SlpIndexedPackReadKind)
          .orElse(Option.when(tableBits <= 64)(SlpIndexedOffsetTablePackRead: SlpIndexedPackReadKind))
      kind.map { readKind =>
        val table = if (dense) None else Some(offsets.zipWithIndex.foldLeft(BigInt(0)) {
          case (bits, (offset, laneIndex)) => bits | (BigInt(offset) << (laneIndex * offsetBits))
        })
        SlpIndexedPackRead(
          rootNodeId = nodeId,
          sourcePackId = sourcePackId,
          index = index,
          resultWidth = resultWidth,
          sourceWidth = sourceWidth,
          semanticLaneOffsets = offsets,
          kind = readKind,
          offsetTable = table,
          offsetBits = offsetBits,
          coveredSourceNodeIds = lanes.map(_.nodeId)
        )
      }
    }
  }

  private def planFragmented(
    nodeId:      Int,
    index:       Expression,
    resultWidth: Int,
    lanes:       Vector[ResolvedIndexedLane]
  ): Option[SlpIndexedPackRead] = {
    if (resultWidth != 1 || !lanes.forall(_.laneWidth == 1)) None
    else {
      val fragments = contiguousFragments(lanes)
      val profitable =
        fragments.size >= 2 &&
          fragments.size <= MaxFragmentedIndexedReadFragments &&
          fragments.size * 3 < lanes.size
      Option.when(profitable) {
        SlpIndexedPackRead(
          rootNodeId = nodeId,
          sourcePackId = fragments.head.sourcePackId,
          index = index,
          resultWidth = resultWidth,
          sourceWidth = lanes.map(_.sourceWidth).max,
          semanticLaneOffsets = lanes.map(_.sourceOffset),
          kind = SlpIndexedFragmentedPackRead,
          offsetTable = None,
          offsetBits = 0,
          coveredSourceNodeIds = lanes.map(_.nodeId),
          fragments = fragments
        )
      }
    }
  }

  private def planIndexedMux(
    context: SlpAnalysisContext,
    packGraph: SlpPackGraph,
    laneByNodeId: Map[Int, (Int, Int)],
    nodeId: Int,
    index: Expression,
    values: Seq[Expression],
    resultType: Type
  ): Option[SlpIndexedPackRead] = {
    if (values.isEmpty || (values.size & (values.size - 1)) != 0) None
    else {
      for {
        indexWidth <- uintWidth(index)
        resultWidth <- uintTypeWidth(resultType)
        if indexWidth > 0 && indexWidth <= 6 && resultWidth <= 64
        if (1 << indexWidth) == values.size
        valueNodeIds <- {
          val resolved = values.map(referenceName).map(_.flatMap(context.graph.graph.nameToID.get))
          Option.when(resolved.forall(_.nonEmpty))(resolved.flatten.toVector)
        }
        resolvedLanes <- {
          val lanes = valueNodeIds.zipWithIndex.map { case (valueNodeId, semanticIndex) =>
            laneByNodeId.get(valueNodeId).flatMap { case (sourcePackId, laneIndex) =>
              val sourcePack = packGraph.pack(sourcePackId)
              Option.when(sourcePack.totalResultWidth > 0 && sourcePack.totalResultWidth <= 64) {
                ResolvedIndexedLane(
                  index = semanticIndex,
                  nodeId = valueNodeId,
                  sourcePackId = sourcePackId,
                  sourceOffset = sourcePack.outputOffsets(laneIndex),
                  sourceWidth = sourcePack.totalResultWidth,
                  laneWidth = sourcePack.lanes(laneIndex).resultWidth
                )
              }
            }
          }
          Option.when(lanes.forall(_.nonEmpty))(lanes.flatten.toVector)
        }
        if resolvedLanes.forall(_.laneWidth == resultWidth)
        read <- planSingleSource(nodeId, index, resultWidth, resolvedLanes)
          .orElse(planFragmented(nodeId, index, resultWidth, resolvedLanes))
      } yield read
    }
  }

  private def planNode(
    context: SlpAnalysisContext,
    packGraph: SlpPackGraph,
    laneByNodeId: Map[Int, (Int, Int)],
    nodeId: Int
  ): Option[SlpIndexedPackRead] = context.graph.node(nodeId).statement match {
    case DefNode(_, _, DoPrim(ArmorIndexedMux, index +: values, Seq(), resultType)) =>
      planIndexedMux(context, packGraph, laneByNodeId, nodeId, index, values, resultType)
    case _ => None
  }

  def build(
    context: SlpAnalysisContext,
    packGraph: SlpPackGraph,
    residualIndexedMuxPlan: SlpResidualIndexedMuxPlan = SlpResidualIndexedMuxPlan.Empty
  ): SlpIndexedPackReadPlan = {
    val laneByNodeId = packGraph.packs.flatMap { pack =>
      pack.nodeIds.zipWithIndex.map { case (nodeId, laneIndex) => nodeId -> (pack.id, laneIndex) }
    }.toMap
    val graphReads = context.graph.validNodeIds.flatMap(nodeId =>
      planNode(context, packGraph, laneByNodeId, nodeId)
    )
    val residualReads = residualIndexedMuxPlan.muxes.flatMap { mux =>
      planIndexedMux(
        context,
        packGraph,
        laneByNodeId,
        mux.rootNodeId,
        mux.selector,
        mux.values,
        mux.resultType
      )
    }
    SlpIndexedPackReadPlan(
      (graphReads ++ residualReads).groupBy(_.rootNodeId).values.map(_.head).toVector.sortBy(_.rootNodeId)
    )
  }
}
