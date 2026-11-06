package armor.slp

import scala.collection.mutable

sealed trait SlpProjectionSource
final case class SlpProjectionCombPack(packId: Int) extends SlpProjectionSource {
  require(packId >= 0)
}
final case class SlpProjectionRegPack(regPackId: Int) extends SlpProjectionSource {
  require(regPackId >= 0)
}
final case class SlpProjectionAlignment(alignmentId: Int) extends SlpProjectionSource {
  require(alignmentId >= 0)
}
final case class SlpProjectionConstant(value: BigInt) extends SlpProjectionSource {
  require(value >= 0)
}

final case class SlpBitTransfer(
  sourceOffset:      Int,
  destinationOffset: Int,
  width:             Int
) {
  require(sourceOffset >= 0)
  require(destinationOffset >= 0)
  require(width > 0)
  require(sourceOffset + width <= 64)
  require(destinationOffset + width <= 64)
}

/** Opcode-independent mapping between two packed bit layouts.
  *
  * Projection operations use one mapping from an input to their result. A
  * full-carry Add uses one mapping per operand to place both packed arguments
  * in the result-lane layout before the machine-word addition.
  */
final case class SlpBitMapping(
  sourceWidth:      Int,
  destinationWidth: Int,
  transfers:        Vector[SlpBitTransfer]
) {
  require(sourceWidth > 0 && sourceWidth <= 64)
  require(destinationWidth > 0 && destinationWidth <= 64)
  require(transfers.nonEmpty)
  require(transfers.forall(transfer => transfer.sourceOffset + transfer.width <= sourceWidth))
  require(transfers.forall(transfer => transfer.destinationOffset + transfer.width <= destinationWidth))

  private def bitMask(offset: Int, width: Int): BigInt =
    ((BigInt(1) << width) - 1) << offset

  val sourceMask: BigInt = transfers.foldLeft(BigInt(0)) { case (mask, transfer) =>
    mask | bitMask(transfer.sourceOffset, transfer.width)
  }
  val destinationMask: BigInt = transfers.foldLeft(BigInt(0)) { case (mask, transfer) =>
    mask | bitMask(transfer.destinationOffset, transfer.width)
  }
  val selectedWidth: Int = transfers.map(_.width).sum

  val hasDisjointSourceBits: Boolean = sourceMask.bitCount == selectedWidth
  val hasDisjointDestinationBits: Boolean = destinationMask.bitCount == selectedWidth
  val preservesBitOrder: Boolean = {
    val sourceOrder = transfers.indices.sortBy(index => transfers(index).sourceOffset)
    val destinationOrder = transfers.indices.sortBy(index => transfers(index).destinationOffset)
    sourceOrder == destinationOrder
  }
  val canUseBitMapping: Boolean =
    hasDisjointSourceBits && hasDisjointDestinationBits && preservesBitOrder
  val hasIdenticalBitPositions: Boolean =
    transfers.forall(transfer => transfer.sourceOffset == transfer.destinationOffset)

  private def contiguousMask(mask: BigInt): Option[(Int, Int)] = {
    if (mask == 0) None
    else {
      val offset = mask.lowestSetBit
      val width = mask.bitCount
      Option.when((mask >> offset) == ((BigInt(1) << width) - 1))(offset -> width)
    }
  }

  val sourceContiguousRange: Option[(Int, Int)] = contiguousMask(sourceMask)
  val destinationContiguousRange: Option[(Int, Int)] = contiguousMask(destinationMask)
  val loweringKind: String = {
    if (!canUseBitMapping) "fallback"
    else if (hasIdenticalBitPositions) "identity_mask"
    else (sourceContiguousRange, destinationContiguousRange) match {
      case (Some(_), Some(_)) => "shift_mask"
      case (None, Some(_))    => "pext"
      case (Some(_), None)    => "pdep"
      case (None, None)       => "pext_pdep"
    }
  }
}

/** A pure bit projection from one materialized packed argument to one result
  * pack. Transfers preserve bit order inside each range. The emitter selects
  * identity, shift/mask, PEXT, PDEP, or a safe lane-wise fallback solely from
  * this mapping.
  */
final case class SlpPackProjection(
  destinationPackId: Int,
  argumentIndex:     Int,
  source:            SlpProjectionSource,
  sourceWidth:       Int,
  destinationWidth:  Int,
  transfers:         Vector[SlpBitTransfer]
) {
  require(destinationPackId >= 0)
  require(argumentIndex >= 0)
  require(sourceWidth > 0 && sourceWidth <= 64)
  require(destinationWidth > 0 && destinationWidth <= 64)
  require(transfers.nonEmpty)
  require(transfers.forall(transfer => transfer.sourceOffset + transfer.width <= sourceWidth))
  require(transfers.forall(transfer => transfer.destinationOffset + transfer.width <= destinationWidth))

  val bitMapping: SlpBitMapping = SlpBitMapping(sourceWidth, destinationWidth, transfers)
  val sourceMask: BigInt = bitMapping.sourceMask
  val destinationMask: BigInt = bitMapping.destinationMask
  val selectedWidth: Int = bitMapping.selectedWidth
  val hasDisjointSourceBits: Boolean = bitMapping.hasDisjointSourceBits
  val hasDisjointDestinationBits: Boolean = bitMapping.hasDisjointDestinationBits
  val preservesBitOrder: Boolean = bitMapping.preservesBitOrder
  val canUseBitMapping: Boolean = bitMapping.canUseBitMapping
  val hasIdenticalBitPositions: Boolean = bitMapping.hasIdenticalBitPositions
  val sourceContiguousRange: Option[(Int, Int)] = bitMapping.sourceContiguousRange
  val destinationContiguousRange: Option[(Int, Int)] = bitMapping.destinationContiguousRange
  val loweringKind: String = bitMapping.loweringKind
}

final case class SlpPackProjectionPlan(projections: Vector[SlpPackProjection]) {
  require(projections.map(projection => projection.destinationPackId -> projection.argumentIndex)
    .distinct.size == projections.size)
  require(projections == projections.sortBy(projection =>
    projection.destinationPackId -> projection.argumentIndex))

  val byDestinationPackId: Map[Int, Vector[SlpPackProjection]] =
    projections.groupBy(_.destinationPackId).view.mapValues(_.sortBy(_.argumentIndex)).toMap
}

/** A direct projection from one already-materialized source word into a
  * scalar-to-pack alignment.  Unlike [[SlpPackProjection]], this does not
  * describe the packed operation result itself; it replaces part of an input
  * alignment which would otherwise be rebuilt from scalar lanes or
  * single-lane pack segments.
  */
final case class SlpAlignmentProjectionTerm(
  source:                  SlpProjectionSource,
  sourceWidth:             Int,
  destinationWidth:        Int,
  transfers:               Vector[SlpBitTransfer],
  coveredDestinationLanes: Vector[Int],
  segmentAlignmentIds:     Set[Int]
) {
  require(sourceWidth > 0 && sourceWidth <= 64)
  require(destinationWidth > 0 && destinationWidth <= 64)
  require(transfers.nonEmpty)
  require(coveredDestinationLanes.nonEmpty)
  require(coveredDestinationLanes == coveredDestinationLanes.distinct.sorted)
  require(segmentAlignmentIds.forall(_ >= 0))

  val bitMapping: SlpBitMapping = SlpBitMapping(sourceWidth, destinationWidth, transfers)
  val sourceMask: BigInt = bitMapping.sourceMask
  val destinationMask: BigInt = bitMapping.destinationMask
  val selectedWidth: Int = bitMapping.selectedWidth
  val canUseBitMapping: Boolean = bitMapping.canUseBitMapping
  val loweringKind: String = bitMapping.loweringKind
}

final case class SlpAlignmentProjection(
  alignmentId: Int,
  terms:       Vector[SlpAlignmentProjectionTerm]
) {
  require(alignmentId >= 0)
  require(terms.nonEmpty)

  val coveredDestinationLanes: Vector[Int] =
    terms.flatMap(_.coveredDestinationLanes).distinct.sorted
  val segmentAlignmentIds: Set[Int] =
    terms.flatMap(_.segmentAlignmentIds).toSet
}

final case class SlpAlignmentProjectionPlan(projections: Vector[SlpAlignmentProjection]) {
  require(projections.map(_.alignmentId).distinct.size == projections.size)
  require(projections == projections.sortBy(_.alignmentId))

  val byAlignmentId: Map[Int, SlpAlignmentProjection] =
    projections.map(projection => projection.alignmentId -> projection).toMap
  val coveredSegmentAlignmentIds: Set[Int] =
    projections.flatMap(_.segmentAlignmentIds).toSet
}

/** A scalar value reconstructed directly from a contiguous range of one
  * combinational pack.  This is deliberately separate from
  * [[SlpPackProjection]]: the latter maps one pack argument into another
  * pack, whereas this plan replaces a closed scalar Cat tree at the SLP
  * boundary.
  */
final case class SlpScalarPackProjection(
  rootNodeId:          Int,
  sourcePackId:        Int,
  sourceBitOffset:     Int,
  resultWidth:         Int,
  internalCatNodeIds:  Vector[Int],
  elidedLeafNodeIds:   Vector[Int]
) {
  require(rootNodeId >= 0)
  require(sourcePackId >= 0)
  require(sourceBitOffset >= 0)
  require(resultWidth > 0 && resultWidth <= 64)
  require(internalCatNodeIds == internalCatNodeIds.distinct.sorted)
  require(!internalCatNodeIds.contains(rootNodeId))
  require(elidedLeafNodeIds == elidedLeafNodeIds.distinct.sorted)
}

final case class SlpScalarPackProjectionPlan(projections: Vector[SlpScalarPackProjection]) {
  require(projections.map(_.rootNodeId).distinct.size == projections.size)
  require(projections == projections.sortBy(_.rootNodeId))

  val byRootNodeId: Map[Int, SlpScalarPackProjection] =
    projections.map(projection => projection.rootNodeId -> projection).toMap
  val internalCatNodeIds: Set[Int] = projections.flatMap(_.internalCatNodeIds).toSet
  val elidedLeafNodeIds: Set[Int] = projections.flatMap(_.elidedLeafNodeIds).toSet
}

/** Finds closed scalar Cat trees whose leaves are contiguous lanes of the
  * same already-materialized pack.  Such a tree is just a scalar view of the
  * pack, so emitting every leaf unpack and every Cat is redundant.
  *
  * This planner only accepts order-preserving contiguous ranges.  Sparse,
  * reordered, or mixed-pack trees stay on the ordinary scalar path; they need
  * a real shuffle and must not be silently reinterpreted as a direct view.
  */
object SlpScalarPackProjectionPlanner {
  private final case class CatTree(
    width:          Int,
    sourcePackId:   Int,
    transfers:      Vector[SlpBitTransfer],
    catNodeIds:     Set[Int],
    leafNodeIds:    Set[Int]
  )

  def build(
    context:                SlpAnalysisContext,
    packGraph:              SlpPackGraph,
    alignPlan:              SlpAlignPlan,
    scalarFallbackNodeIds:  Vector[Int]
  ): SlpScalarPackProjectionPlan = {
    val view = context.graph
    val scalarFallbackSet = scalarFallbackNodeIds.toSet
    val classifiedOperations = context.classifications.collect {
      case (nodeId, SlpSupported(operation)) => nodeId -> operation
    }.toMap
    val operations = classifiedOperations ++ packGraph.operationOverrides
    val packedLanesByNodeId = packGraph.packs.flatMap { pack =>
      pack.nodeIds.zipWithIndex.map { case (nodeId, laneIndex) =>
        nodeId -> (pack.id, laneIndex)
      }
    }.toMap
    val materializedLanesBySourceNodeId = alignPlan.packToScalar.flatMap { alignment =>
      alignment.lanes.map(lane => lane.sourceNodeId -> lane)
    }.groupBy(_._1).view.mapValues(_.map(_._2)).toMap

    def signalNodeId(operand: SlpOperand): Option[Int] = operand match {
      case SlpSignal(name, _) => view.graph.nameToID.get(name)
      case _                  => None
    }

    // Cat trees are shared heavily in generated hardware.  Memoizing both
    // successes and rejections keeps this boundary analysis linear in the
    // number of graph nodes instead of re-walking every shared suffix per
    // scalar Cat root.
    val treeCache = mutable.HashMap.empty[Int, Option[CatTree]]
    def treeFor(nodeId: Int, visiting: Set[Int] = Set.empty): Option[CatTree] = {
      if (visiting(nodeId)) None
      else treeCache.getOrElseUpdate(nodeId, packedLanesByNodeId.get(nodeId).map { case (packId, laneIndex) =>
        val pack = packGraph.pack(packId)
        val width = pack.lanes(laneIndex).resultWidth
        CatTree(
          width = width,
          sourcePackId = packId,
          transfers = Vector(SlpBitTransfer(pack.outputOffsets(laneIndex), 0, width)),
          catNodeIds = Set.empty,
          leafNodeIds = Set(nodeId)
        )
      }.orElse {
        if (!scalarFallbackSet(nodeId)) None
        else operations.get(nodeId).collect {
          case SlpOperation(SlpCat, resultWidth, _, Vector(high, low), _, _) =>
            for {
              highNodeId <- signalNodeId(high)
              lowNodeId <- signalNodeId(low)
              highTree <- treeFor(highNodeId, visiting + nodeId)
              lowTree <- treeFor(lowNodeId, visiting + nodeId)
              if highTree.sourcePackId == lowTree.sourcePackId
              if highTree.width == high.width && lowTree.width == low.width
              if resultWidth == highTree.width + lowTree.width
            } yield {
              val highTransfers = highTree.transfers.map(transfer =>
                transfer.copy(destinationOffset = transfer.destinationOffset + lowTree.width)
              )
              CatTree(
                width = resultWidth,
                sourcePackId = highTree.sourcePackId,
                transfers = lowTree.transfers ++ highTransfers,
                catNodeIds = highTree.catNodeIds ++ lowTree.catNodeIds + nodeId,
                leafNodeIds = highTree.leafNodeIds ++ lowTree.leafNodeIds
              )
            }
        }.flatten
      })
    }

    def materializationCanBeElided(leafNodeId: Int, treeCatNodeIds: Set[Int]): Boolean =
      materializedLanesBySourceNodeId.get(leafNodeId).exists { lanes =>
        lanes.nonEmpty && lanes.forall { lane =>
          !lane.observable && lane.consumers.nonEmpty && lane.consumers.forall {
            case SlpScalarConsumer(consumerNodeId) => treeCatNodeIds(consumerNodeId)
            case _                                 => false
          }
        }
      }

    val raw = scalarFallbackNodeIds.flatMap { rootNodeId =>
      treeFor(rootNodeId).flatMap { tree =>
        val mapping = SlpBitMapping(
          sourceWidth = packGraph.pack(tree.sourcePackId).totalResultWidth,
          destinationWidth = tree.width,
          transfers = tree.transfers
        )
        val closedInternalCats = (tree.catNodeIds - rootNodeId).forall { nodeId =>
          view.validFanoutIds(nodeId).toSet.subsetOf(tree.catNodeIds)
        }
        val directlyViewable = mapping.canUseBitMapping &&
          mapping.sourceContiguousRange.contains(tree.transfers.map(_.sourceOffset).min -> tree.width) &&
          mapping.destinationContiguousRange.contains(0 -> tree.width)
        if (!closedInternalCats || !directlyViewable) None
        else Some((rootNodeId, tree, mapping.sourceContiguousRange.get._1))
      }
    }

    // Keep only outermost trees.  An inner Cat can be a valid view too, but
    // emitting its enclosing view is strictly cheaper and owns the inner node.
    val projections = raw.map {
      case (rootNodeId, tree, sourceBitOffset) =>
        val internalCatNodeIds = (tree.catNodeIds - rootNodeId).toVector.sorted
        val elidedLeafNodeIds = tree.leafNodeIds.filter { leafNodeId =>
          materializationCanBeElided(leafNodeId, tree.catNodeIds)
        }.toVector.sorted
        SlpScalarPackProjection(
          rootNodeId = rootNodeId,
          sourcePackId = tree.sourcePackId,
          sourceBitOffset = sourceBitOffset,
          resultWidth = tree.width,
          internalCatNodeIds = internalCatNodeIds,
          elidedLeafNodeIds = elidedLeafNodeIds
        )
    }.sortBy(_.rootNodeId)

    // A root may be present inside another candidate tree.  The condition
    // above intentionally rejects it; spell out the invariant so a future
    // change cannot accidentally emit both views.
    val outermost = projections.filterNot { projection =>
      projections.exists(other => other.rootNodeId != projection.rootNodeId &&
        other.internalCatNodeIds.contains(projection.rootNodeId))
    }
    SlpScalarPackProjectionPlan(outermost)
  }
}

object SlpPackProjectionPlanner {
  private def lowMask(width: Int): BigInt = (BigInt(1) << width) - 1

  def build(
    context:   SlpAnalysisContext,
    packGraph: SlpPackGraph,
    alignPlan: SlpAlignPlan
  ): SlpPackProjectionPlan = {
    val classifiedOperations = context.classifications.collect {
      case (nodeId, SlpSupported(operation)) => nodeId -> operation
    }.toMap
    val operations = classifiedOperations ++ packGraph.operationOverrides
    val directPackInputs = alignPlan.directPackInputs.map(input =>
      (input.destinationPackId, input.argumentIndex) -> input
    ).toMap
    val directRegInputs = alignPlan.directRegInputs.map(input =>
      (input.destinationPackId, input.argumentIndex) -> input
    ).toMap
    val scalarInputs = alignPlan.scalarToPack.map(input =>
      (input.destinationPackId, input.argumentIndex) -> input
    ).toMap
    val broadcastInputs = alignPlan.broadcastInputs.map(input =>
      (input.destinationPackId, input.argumentIndex) -> input
    ).toMap

    def sourceFor(pack: SlpPack, argumentIndex: Int, laneOperations: Vector[SlpOperation]):
        SlpProjectionSource = {
      val key = pack.id -> argumentIndex
      directPackInputs.get(key).map(input => SlpProjectionCombPack(input.sourcePackId))
        .orElse(directRegInputs.get(key).map(input => SlpProjectionRegPack(input.regPackId)))
        .orElse(scalarInputs.get(key).map(input => SlpProjectionAlignment(input.id)))
        .getOrElse {
          val operands = laneOperations.map(_.operands(argumentIndex))
          require(operands.forall(_.isInstanceOf[SlpUIntConstant]),
            s"projection input $argumentIndex of pack ${pack.id} has no materialized source")
          val offsets = operands.map(_.width).scanLeft(0)(_ + _).dropRight(1)
          val value = operands.zip(offsets).foldLeft(BigInt(0)) {
            case (bits, (constant: SlpUIntConstant, offset)) =>
              bits | ((constant.value & lowMask(constant.width)) << offset)
            case (bits, _) => bits
          }
          SlpProjectionConstant(value)
        }
    }

    val projections = packGraph.packs.flatMap { pack =>
      val laneOperations = pack.nodeIds.map(operations)
      def sourceOffsets(argumentIndex: Int): Vector[Int] =
        laneOperations.map(_.operands(argumentIndex).width).scanLeft(0)(_ + _).dropRight(1)

      val projectionSpecs: Vector[(Int, Vector[SlpBitTransfer])] = pack.shape.opcode match {
        case SlpMaskedAnd =>
          val offsets = sourceOffsets(0)
          Vector(0 -> laneOperations.indices.map { laneIndex =>
            val operation = laneOperations(laneIndex)
            val keptWidth = operation.operands(1).asInstanceOf[SlpUIntConstant].width
              .min(operation.operands.head.width).min(operation.resultWidth)
            SlpBitTransfer(
              offsets(laneIndex),
              pack.outputOffsets(laneIndex),
              keptWidth
            )
          }.toVector)
        case SlpBitSelect =>
          val offsets = sourceOffsets(0)
          Vector(0 -> laneOperations.indices.map { laneIndex =>
            SlpBitTransfer(
              offsets(laneIndex) + laneOperations(laneIndex).parameters.head.toInt,
              pack.outputOffsets(laneIndex),
              1
            )
          }.toVector)
        case SlpShlConst(amount) =>
          val offsets = sourceOffsets(0)
          Vector(0 -> laneOperations.indices.map { laneIndex =>
            SlpBitTransfer(
              offsets(laneIndex),
              pack.outputOffsets(laneIndex) + amount,
              laneOperations(laneIndex).operands.head.width
            )
          }.toVector)
        case SlpShrConst(amount) =>
          val offsets = sourceOffsets(0)
          Vector(0 -> laneOperations.indices.map { laneIndex =>
            SlpBitTransfer(
              offsets(laneIndex) + amount,
              pack.outputOffsets(laneIndex),
              laneOperations(laneIndex).resultWidth
            )
          }.toVector)
        case SlpMove =>
          val offsets = sourceOffsets(0)
          Vector(0 -> laneOperations.indices.map { laneIndex =>
            SlpBitTransfer(
              offsets(laneIndex),
              pack.outputOffsets(laneIndex),
              laneOperations(laneIndex).operands.head.width.min(pack.lanes(laneIndex).resultWidth)
            )
          }.toVector)
        case SlpCat =>
          val highOffsets = sourceOffsets(0)
          val lowOffsets = sourceOffsets(1)
          val highTransfers = laneOperations.indices.map { laneIndex =>
            val operation = laneOperations(laneIndex)
            val lowWidth = operation.operands(1).width
            SlpBitTransfer(
              highOffsets(laneIndex),
              pack.outputOffsets(laneIndex) + lowWidth,
              operation.operands.head.width
            )
          }.toVector
          val lowTransfers = laneOperations.indices.map { laneIndex =>
            val operation = laneOperations(laneIndex)
            SlpBitTransfer(
              lowOffsets(laneIndex),
              pack.outputOffsets(laneIndex),
              operation.operands(1).width
            )
          }.toVector
          Vector(0 -> highTransfers, 1 -> lowTransfers)
        case _ => Vector.empty
      }

      // A one-bit broadcast is materialized directly in the destination lane
      // layout by SlpEmitter.  It has one source bit/value intentionally used
      // by several transfers, which is not a one-to-one bit projection.
      // Leave such arguments to ordinary opcode lowering instead of forcing a
      // projection source with overlapping bits.
      projectionSpecs.filterNot { case (argumentIndex, _) =>
        broadcastInputs.contains(pack.id -> argumentIndex)
      }.map { case (argumentIndex, transfers) =>
        SlpPackProjection(
          destinationPackId = pack.id,
          argumentIndex = argumentIndex,
          source = sourceFor(pack, argumentIndex, laneOperations),
          sourceWidth = laneOperations.map(_.operands(argumentIndex).width).sum,
          destinationWidth = pack.totalResultWidth,
          transfers = transfers
        )
      }
    }.sortBy(projection => projection.destinationPackId -> projection.argumentIndex)

    SlpPackProjectionPlan(projections)
  }
}
