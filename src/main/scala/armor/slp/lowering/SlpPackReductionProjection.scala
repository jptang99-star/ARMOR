package armor.slp

import scala.collection.mutable

/** A scalar Boolean reduction can consume one or more packed 1-bit lanes
  * directly.  This is a boundary lowering plan, distinct from a packed Orr or
  * Andr operation: its result deliberately remains a scalar UInt<1>. */
sealed trait SlpReductionKind {
  def opcode: SlpOpcode
}
case object SlpOrReduction extends SlpReductionKind {
  val opcode: SlpOpcode = SlpOr
}
case object SlpAndReduction extends SlpReductionKind {
  val opcode: SlpOpcode = SlpAnd
}

final case class SlpPackReductionSource(packId: Int, mask: BigInt) {
  require(packId >= 0)
  require(mask > 0 && mask < (BigInt(1) << 64))
}

final case class SlpPackReductionProjection(
  rootNodeId:               Int,
  kind:                     SlpReductionKind,
  packedSources:            Vector[SlpPackReductionSource],
  scalarLeafNodeIds:        Vector[Int],
  internalReductionNodeIds: Vector[Int],
  elidedPackedLeafNodeIds:  Vector[Int]
) {
  require(rootNodeId >= 0)
  require(packedSources.nonEmpty)
  require(packedSources.map(_.packId) == packedSources.map(_.packId).distinct.sorted)
  require(scalarLeafNodeIds == scalarLeafNodeIds.distinct.sorted)
  require(internalReductionNodeIds == internalReductionNodeIds.distinct.sorted)
  require(!internalReductionNodeIds.contains(rootNodeId))
  require(elidedPackedLeafNodeIds == elidedPackedLeafNodeIds.distinct.sorted)
}

final case class SlpPackReductionProjectionPlan(projections: Vector[SlpPackReductionProjection]) {
  require(projections.map(_.rootNodeId).distinct.size == projections.size)
  require(projections == projections.sortBy(_.rootNodeId))

  val byRootNodeId: Map[Int, SlpPackReductionProjection] =
    projections.map(projection => projection.rootNodeId -> projection).toMap
  val internalReductionNodeIds: Set[Int] =
    projections.flatMap(_.internalReductionNodeIds).toSet
  val elidedPackedLeafNodeIds: Set[Int] =
    projections.flatMap(_.elidedPackedLeafNodeIds).toSet
}

/** Finds closed scalar UInt<1> And/Or trees with at least one leaf supplied by
  * a combinational pack.  The accepted projection preserves the scalar root,
  * but replaces the unpack-and-reduce path with machine-word tests.
  */
object SlpPackReductionProjectionPlanner {
  private final case class ReductionTree(
    packedMasks:     Map[Int, BigInt],
    scalarLeafIds:   Set[Int],
    internalNodeIds: Set[Int],
    packedLeafIds:   Set[Int]
  ) {
    def combine(other: ReductionTree): ReductionTree = ReductionTree(
      packedMasks = (packedMasks.keySet ++ other.packedMasks.keySet).iterator.map { packId =>
        packId -> (packedMasks.getOrElse(packId, BigInt(0)) | other.packedMasks.getOrElse(packId, BigInt(0)))
      }.toMap,
      scalarLeafIds = scalarLeafIds ++ other.scalarLeafIds,
      internalNodeIds = internalNodeIds ++ other.internalNodeIds,
      packedLeafIds = packedLeafIds ++ other.packedLeafIds
    )
  }

  private val emptyTree = ReductionTree(Map.empty, Set.empty, Set.empty, Set.empty)

  def build(
    context:               SlpAnalysisContext,
    packGraph:             SlpPackGraph,
    alignPlan:             SlpAlignPlan,
    scalarFallbackNodeIds: Vector[Int]
  ): SlpPackReductionProjectionPlan = {
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

    def neutralConstant(kind: SlpReductionKind, operand: SlpOperand): Boolean = operand match {
      case SlpUIntConstant(value, 1) =>
        (kind == SlpOrReduction && value == 0) || (kind == SlpAndReduction && value == 1)
      case _ => false
    }

    def packedLeaf(nodeId: Int): Option[ReductionTree] = packedLanesByNodeId.get(nodeId).flatMap {
      case (packId, laneIndex) =>
        val pack = packGraph.pack(packId)
        Option.when(pack.lanes(laneIndex).resultWidth == 1) {
          ReductionTree(
            packedMasks = Map(packId -> (BigInt(1) << pack.outputOffsets(laneIndex))),
            scalarLeafIds = Set.empty,
            internalNodeIds = Set.empty,
            packedLeafIds = Set(nodeId)
          )
        }
    }

    def treeFor(
      nodeId: Int,
      kind: SlpReductionKind,
      visiting: Set[Int],
      cache: mutable.HashMap[Int, Option[ReductionTree]]
    ): Option[ReductionTree] = {
      if (visiting(nodeId)) None
      else cache.getOrElseUpdate(nodeId, packedLeaf(nodeId).orElse {
        operations.get(nodeId) match {
          case Some(SlpOperation(opcode, 1, _, operands, _, _)) if opcode == kind.opcode &&
              scalarFallbackSet(nodeId) && operands.size == 2 && operands.forall(_.width == 1) =>
            val children = operands.map {
              case operand if neutralConstant(kind, operand) => Some(emptyTree)
              case operand => signalNodeId(operand).flatMap(childId =>
                treeFor(childId, kind, visiting + nodeId, cache).orElse {
                  Option.when(scalarFallbackSet(childId))(
                    ReductionTree(Map.empty, Set(childId), Set.empty, Set.empty)
                  )
                }
              )
            }
            if (children.exists(_.isEmpty)) None
            else {
              val combined = children.flatten.foldLeft(emptyTree)(_.combine(_))
              Some(combined.copy(internalNodeIds = combined.internalNodeIds + nodeId))
            }
          case _ if scalarFallbackSet(nodeId) =>
            Some(ReductionTree(Map.empty, Set(nodeId), Set.empty, Set.empty))
          case _ => None
        }
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

    val raw = Vector[SlpReductionKind](SlpOrReduction, SlpAndReduction).flatMap { kind =>
      val treeCache = mutable.HashMap.empty[Int, Option[ReductionTree]]
      scalarFallbackNodeIds.flatMap { rootNodeId =>
        operations.get(rootNodeId).toVector.flatMap { rootOperation =>
          if (rootOperation.opcode != kind.opcode || rootOperation.resultWidth != 1) Vector.empty
          else treeFor(rootNodeId, kind, Set.empty, treeCache).toVector.flatMap { tree =>
            val treeNodeIds = tree.internalNodeIds
            if (tree.packedMasks.nonEmpty && (treeNodeIds - rootNodeId).forall(nodeId =>
                view.validFanoutIds(nodeId).toSet.subsetOf(treeNodeIds)
              )) Vector(rootNodeId -> kind -> tree)
            else Vector.empty
          }
        }
      }
    }

    val candidates = raw.map { case ((rootNodeId, kind), tree) =>
      SlpPackReductionProjection(
        rootNodeId = rootNodeId,
        kind = kind,
        packedSources = tree.packedMasks.toVector.sortBy(_._1).map {
          case (packId, mask) => SlpPackReductionSource(packId, mask)
        },
        scalarLeafNodeIds = (tree.scalarLeafIds - rootNodeId).toVector.sorted,
        internalReductionNodeIds = (tree.internalNodeIds - rootNodeId).toVector.sorted,
        elidedPackedLeafNodeIds = tree.packedLeafIds.filter(leafNodeId =>
          materializationCanBeElided(leafNodeId, tree.internalNodeIds)
        ).toVector.sorted
      )
    }.sortBy(_.rootNodeId)

    val outermost = candidates.filterNot { projection =>
      candidates.exists(other => other.rootNodeId != projection.rootNodeId &&
        other.internalReductionNodeIds.contains(projection.rootNodeId))
    }
    SlpPackReductionProjectionPlan(outermost)
  }
}
