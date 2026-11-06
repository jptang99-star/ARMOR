package armor.slp

import scala.collection.mutable

final case class SlpTemporalStateExpansionStats(
  seedGroups:      Int,
  acceptedPacks:   Int,
  acceptedNodes:   Int,
  rejectedNarrow:  Int,
  rejectedTiming:  Int,
  rejectedOverlap: Int
)

final case class SlpTemporalStateExpansionResult(
  result: SlpPackingResult,
  stats:  SlpTemporalStateExpansionStats
)

/** Discover current-cycle consumers of an already-established packed state
  * layout.  This is intentionally a temporal bridge, not a normal graph
  * traversal: registers are previous-cycle values and therefore do not appear
  * as candidate producer nodes in the acyclic combinational graph.
  *
  * The seed order is always the physical register-pack order.  Consequently a
  * resulting pack can read the old state directly, without scalar unpack and
  * re-pack.  The other Mux arm is allowed to be scalar-aligned; its condition
  * must be identical in every lane so normal broadcast lowering is exact.
  */
final class SlpTemporalStateExpansion(context: SlpAnalysisContext) {
  private val view = context.graph
  private val levels = view.levels.toOption.getOrElse(
    throw new IllegalArgumentException("temporal state expansion requires an acyclic graph")
  )
  private val operations = context.classifications.collect {
    case (nodeId, SlpSupported(operation)) => nodeId -> operation
  }.toMap

  private final case class SeedKey(
    regPackId:    Int,
    operandIndex: Int,
    shape:        SlpPackShape,
    level:        Int,
    location:     SlpModuleLocation,
    condition:    SlpOperand
  )

  private def operationOf(nodeId: Int, result: SlpPackingResult): Option[SlpOperation] =
    result.operationOverrides.get(nodeId).orElse(operations.get(nodeId))

  private def isSafeReadBeforeCommit(pack: SlpRegPack, consumerLevel: Int): Boolean =
    pack.commitFragments.forall(fragment => consumerLevel < fragment.level)

  private def hasInternalDependency(nodeIds: Vector[Int]): Boolean = {
    val memberSet = nodeIds.toSet
    nodeIds.exists(nodeId =>
      view.validFaninIds(nodeId).exists(memberSet) || view.validFanoutIds(nodeId).exists(memberSet)
    )
  }

  private def makePack(id: Int, nodeIds: Vector[Int], result: SlpPackingResult): SlpPack = {
    val first = operationOf(nodeIds.head, result).get
    val locations = nodeIds.map(nodeId => view.node(nodeId).module)
    val commonLocation = locations.flatten.distinct match {
      case Vector(location) if locations.forall(_.contains(location)) => Some(location)
      case _                                                          => None
    }
    SlpPack(
      id = id,
      shape = SlpPackShape.from(first),
      lanes = nodeIds.map { nodeId =>
        val operation = operationOf(nodeId, result).get
        SlpLane(nodeId, operation.resultWidth, operation.storageWidth)
      },
      level = levels.levelOf(nodeIds.head).get,
      module = commonLocation,
      laneLocations = locations,
      discoveryPhase = Some("phase2b-temporal-state")
    )
  }

  def run(provisional: SlpPackingResult, state: SlpRegPackingResult): SlpTemporalStateExpansionResult = {
    val occupied = provisional.packs.iterator.flatMap(_.nodeIds).toSet
    val laneByRegister = state.packs.iterator.flatMap { pack =>
      // Cross-level commits are intentionally excluded: a scalar read might
      // observe a write which has already occurred in this eval().
      Option.when(pack.commitFragments.size == 1) {
        pack.lanes.zipWithIndex.map { case (lane, laneIndex) =>
          lane.registerName -> (pack -> laneIndex)
        }
      }.toVector.flatten
    }.toMap

    val grouped = mutable.HashMap.empty[SeedKey, mutable.HashMap[Int, Vector[Int]]]
    operations.foreach { case (nodeId, operation) =>
      if (!occupied(nodeId) && operation.opcode == SlpMux && operation.operands.size == 3) {
        for {
          location <- view.node(nodeId).module
          condition <- operation.operands.headOption
          if operation.operands.headOption.forall(_.width == 1)
          operandIndex <- Vector(1, 2)
          register <- operation.operands(operandIndex) match {
            case SlpSignal(name, _) => laneByRegister.get(name)
            case _                  => None
          }
          (regPack, laneIndex) = register
          level <- levels.levelOf(nodeId)
          if isSafeReadBeforeCommit(regPack, level)
        } {
          val key = SeedKey(regPack.id, operandIndex, SlpPackShape.from(operation), level, location, condition)
          val byLane = grouped.getOrElseUpdate(key, mutable.HashMap.empty)
          byLane.update(laneIndex, (byLane.getOrElse(laneIndex, Vector.empty) :+ nodeId).distinct)
        }
      }
    }

    var seedGroups = 0
    var rejectedNarrow = 0
    var rejectedTiming = 0
    var rejectedOverlap = 0
    val accepted = Vector.newBuilder[SlpPack]
    val claimed = mutable.HashSet.empty[Int]
    var nextPackId = provisional.packs.size

    grouped.toVector.sortBy { case (key, _) =>
      (key.regPackId, key.operandIndex, key.level, key.location.instancePath)
    }.foreach { case (key, byLane) =>
      seedGroups += 1
      val uniqueLanes = byLane.collect { case (lane, Vector(nodeId)) => lane -> nodeId }.toVector.sortBy(_._1)
      val runs = uniqueLanes.foldLeft(Vector.empty[Vector[(Int, Int)]]) {
        case (Vector(), lane) => Vector(Vector(lane))
        case (completed, lane) =>
          val current = completed.last
          if (lane._1 == current.last._1 + 1) completed.dropRight(1) :+ (current :+ lane)
          else completed :+ Vector(lane)
      }
      runs.foreach { run =>
        val nodeIds = run.map(_._2)
        if (nodeIds.size < context.config.minParallelDegree) {
          rejectedNarrow += 1
        } else if (nodeIds.exists(occupied) || nodeIds.exists(claimed) || hasInternalDependency(nodeIds)) {
          rejectedOverlap += 1
        } else {
          accepted += makePack(nextPackId, nodeIds, provisional)
          nextPackId += 1
          claimed ++= nodeIds
        }
      }
    }

    val acceptedPacks = accepted.result()
    val result = provisional.copy(
      packs = (provisional.packs ++ acceptedPacks).zipWithIndex.map { case (pack, id) => pack.copy(id = id) },
      temporalStateStats = Some(SlpTemporalStateExpansionStats(
        seedGroups, acceptedPacks.size, acceptedPacks.map(_.parallelDegree).sum,
        rejectedNarrow, rejectedTiming, rejectedOverlap
      ))
    )
    SlpTemporalStateExpansionResult(result, result.temporalStateStats.get)
  }
}
