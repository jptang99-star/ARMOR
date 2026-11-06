package armor.slp

import scala.collection.mutable

/** A scalar result formed by reducing contiguous, equal-width lanes of one
  * combinational pack.  The result remains scalar, but its internal And/Or
  * tree is evaluated with a word-level horizontal reduction. */
sealed trait SlpLaneReductionKind {
  def opcode: SlpOpcode
  def assignmentOperator: String
  def binaryOperator: String
}
case object SlpLaneOrReduction extends SlpLaneReductionKind {
  val opcode: SlpOpcode = SlpOr
  val assignmentOperator = "|="
  val binaryOperator = "|"
}
case object SlpLaneAndReduction extends SlpLaneReductionKind {
  val opcode: SlpOpcode = SlpAnd
  val assignmentOperator = "&="
  val binaryOperator = "&"
}

final case class SlpLaneBitwiseReductionProjection(
  rootNodeId:        Int,
  kind:              SlpLaneReductionKind,
  sourcePackId:      Int,
  sourceBitOffset:   Int,
  laneWidth:         Int,
  laneCount:         Int,
  scalarSeedNodeId:  Option[Int],
  internalNodeIds:   Vector[Int],
  elidedLeafNodeIds: Vector[Int]
) {
  require(rootNodeId >= 0)
  require(sourcePackId >= 0)
  require(sourceBitOffset >= 0)
  require(laneWidth > 1 && laneWidth <= 64)
  require(laneCount >= 4)
  require(laneWidth * laneCount <= 64)
  require(sourceBitOffset + laneWidth * laneCount <= 64)
  require(internalNodeIds == internalNodeIds.distinct.sorted)
  require(!internalNodeIds.contains(rootNodeId))
  require(elidedLeafNodeIds == elidedLeafNodeIds.distinct.sorted)
  require(!scalarSeedNodeId.contains(rootNodeId))
  require(!scalarSeedNodeId.exists(internalNodeIds.contains))
  require(!scalarSeedNodeId.exists(elidedLeafNodeIds.contains))
}

final case class SlpLaneBitwiseReductionProjectionPlan(
  projections: Vector[SlpLaneBitwiseReductionProjection]
) {
  require(projections.map(_.rootNodeId).distinct.size == projections.size)
  require(projections == projections.sortBy(_.rootNodeId))

  val byRootNodeId: Map[Int, SlpLaneBitwiseReductionProjection] =
    projections.map(projection => projection.rootNodeId -> projection).toMap
  val internalNodeIds: Set[Int] = projections.flatMap(_.internalNodeIds).toSet
  val elidedLeafNodeIds: Set[Int] = projections.flatMap(_.elidedLeafNodeIds).toSet
}

/** Discovers closed scalar UInt<W> And/Or trees whose leaves are a contiguous
  * run of lanes from one pack, optionally combined with one scalar seed of the
  * same width. Prefix trees are intentionally excluded: all intermediate nodes
  * must be private to the final reduction root. */
object SlpLaneBitwiseReductionProjectionPlanner {
  private final case class ReductionTree(
    sourcePackId:      Option[Int],
    packedLeafNodeIds: Vector[Int],
    scalarSeedNodeId:  Option[Int],
    internalIds:       Set[Int]
  ) {
    def combine(other: ReductionTree): Option[ReductionTree] = {
      val combinedPackId = (sourcePackId, other.sourcePackId) match {
        case (Some(left), Some(right)) if left == right => Some(left)
        case (Some(left), None)                         => Some(left)
        case (None, Some(right))                        => Some(right)
        case _                                          => None
      }
      val scalarSeeds = Vector(scalarSeedNodeId, other.scalarSeedNodeId).flatten
      Option.when(combinedPackId.nonEmpty && scalarSeeds.size <= 1)(ReductionTree(
        sourcePackId = combinedPackId,
        packedLeafNodeIds = packedLeafNodeIds ++ other.packedLeafNodeIds,
        scalarSeedNodeId = scalarSeeds.headOption,
        internalIds = internalIds ++ other.internalIds
      ))
    }
  }

  def build(
    context:               SlpAnalysisContext,
    packGraph:             SlpPackGraph,
    alignPlan:             SlpAlignPlan,
    scalarFallbackNodeIds: Vector[Int]
  ): SlpLaneBitwiseReductionProjectionPlan = {
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

    def packedLeaf(nodeId: Int, laneWidth: Int): Option[ReductionTree] =
      packedLanesByNodeId.get(nodeId).flatMap { case (packId, laneIndex) =>
        Option.when(packGraph.pack(packId).lanes(laneIndex).resultWidth == laneWidth)(
          ReductionTree(Some(packId), Vector(nodeId), None, Set.empty)
        )
      }

    /** A scalar seed remains materialized.  Restrict it to a non-reduction
      * operation so a partially matched And/Or subtree cannot be silently
      * treated as one opaque seed. */
    def scalarSeed(nodeId: Int, kind: SlpLaneReductionKind, laneWidth: Int): Option[ReductionTree] =
      operations.get(nodeId).flatMap { operation =>
        Option.when(
          scalarFallbackSet(nodeId) &&
            !packedLanesByNodeId.contains(nodeId) &&
            view.node(nodeId).isPure &&
            operation.resultWidth == laneWidth &&
            operation.opcode != kind.opcode
        )(
          ReductionTree(None, Vector.empty, Some(nodeId), Set.empty)
        )
      }

    def treeFor(
      nodeId: Int,
      kind: SlpLaneReductionKind,
      laneWidth: Int,
      visiting: Set[Int],
      cache: mutable.HashMap[Int, Option[ReductionTree]]
    ): Option[ReductionTree] = {
      if (visiting(nodeId)) None
      else cache.getOrElseUpdate(nodeId, {
        val recursiveTree = packedLeaf(nodeId, laneWidth).orElse {
          operations.get(nodeId) match {
            case Some(SlpOperation(opcode, resultWidth, _, operands, _, _))
                if opcode == kind.opcode && resultWidth == laneWidth &&
                   scalarFallbackSet(nodeId) && operands.size == 2 &&
                   operands.forall(_.width == laneWidth) =>
              for {
                leftNodeId <- signalNodeId(operands(0))
                rightNodeId <- signalNodeId(operands(1))
                left <- treeFor(leftNodeId, kind, laneWidth, visiting + nodeId, cache)
                right <- treeFor(rightNodeId, kind, laneWidth, visiting + nodeId, cache)
                combined <- left.combine(right)
              } yield combined.copy(internalIds = combined.internalIds + nodeId)
            case _ => None
          }
        }
        recursiveTree.orElse(scalarSeed(nodeId, kind, laneWidth))
      })
    }

    def materializationCanBeElided(leafNodeId: Int, treeNodeIds: Set[Int]): Boolean =
      materializedLanesBySourceNodeId.get(leafNodeId).exists { lanes =>
        lanes.nonEmpty && lanes.forall { lane =>
          !lane.observable && lane.consumers.nonEmpty && lane.consumers.forall {
            case SlpScalarConsumer(consumerNodeId) => treeNodeIds(consumerNodeId)
            case _                                 => false
          }
        }
      }

    val raw = Vector[SlpLaneReductionKind](SlpLaneOrReduction, SlpLaneAndReduction).flatMap {
      kind =>
        scalarFallbackNodeIds.flatMap { rootNodeId =>
          operations.get(rootNodeId).toVector.flatMap {
            case SlpOperation(opcode, laneWidth, _, _, _, _) if opcode == kind.opcode && laneWidth > 1 =>
              val cache = mutable.HashMap.empty[Int, Option[ReductionTree]]
              treeFor(rootNodeId, kind, laneWidth, Set.empty, cache).toVector.flatMap { tree =>
                val leafCount = tree.packedLeafNodeIds.size
                val pack = packGraph.pack(tree.sourcePackId.get)
                val offsets = tree.packedLeafNodeIds.flatMap { leafNodeId =>
                  packedLanesByNodeId.get(leafNodeId).collect { case (_, laneIndex) =>
                    pack.outputOffsets(laneIndex)
                  }
                }.sorted
                val base = offsets.headOption.getOrElse(0)
                val expectedOffsets = Vector.tabulate(leafCount)(index => base + index * laneWidth)
                val layoutIsContiguous = leafCount >= 4 &&
                  leafCount * laneWidth <= 64 &&
                  offsets == expectedOffsets &&
                  base + leafCount * laneWidth <= pack.totalResultWidth
                val treeIsClosed = (tree.internalIds - rootNodeId).forall { nodeId =>
                  view.validFanoutIds(nodeId).toSet.subsetOf(tree.internalIds)
                }
                val leavesArePrivate = tree.packedLeafNodeIds.forall(leafNodeId =>
                  materializationCanBeElided(leafNodeId, tree.internalIds)
                )
                if (layoutIsContiguous && treeIsClosed && leavesArePrivate)
                  Vector((rootNodeId, kind, laneWidth, tree, base))
                else Vector.empty
              }
            case _ => Vector.empty
          }
        }
    }

    val candidates = raw.map { case (rootNodeId, kind, laneWidth, tree, sourceBitOffset) =>
      SlpLaneBitwiseReductionProjection(
        rootNodeId = rootNodeId,
        kind = kind,
      sourcePackId = tree.sourcePackId.get,
      sourceBitOffset = sourceBitOffset,
      laneWidth = laneWidth,
      laneCount = tree.packedLeafNodeIds.size,
      scalarSeedNodeId = tree.scalarSeedNodeId,
      internalNodeIds = (tree.internalIds - rootNodeId).toVector.sorted,
      elidedLeafNodeIds = tree.packedLeafNodeIds.distinct.sorted
      )
    }.sortBy(_.rootNodeId)

    val outermost = candidates.filterNot { projection =>
      candidates.exists(other => other.rootNodeId != projection.rootNodeId &&
        other.internalNodeIds.contains(projection.rootNodeId))
    }
    SlpLaneBitwiseReductionProjectionPlan(outermost)
  }
}
