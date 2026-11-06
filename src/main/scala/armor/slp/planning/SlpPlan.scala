package armor.slp

import scala.collection.mutable

sealed trait SlpScheduleNode {
  def sortKey: (Int, Int)
  def label: String
}

final case class SlpScalarScheduleNode(nodeId: Int) extends SlpScheduleNode {
  require(nodeId >= 0)
  def sortKey: (Int, Int) = (0, nodeId)
  def label: String = s"scalar:$nodeId"
}

final case class SlpPackScheduleNode(packId: Int) extends SlpScheduleNode {
  require(packId >= 0)
  def sortKey: (Int, Int) = (1, packId)
  def label: String = s"pack:$packId"
}

final case class SlpAlignmentScheduleNode(alignmentId: Int) extends SlpScheduleNode {
  require(alignmentId >= 0)
  def sortKey: (Int, Int) = (2, alignmentId)
  def label: String = s"align:$alignmentId"
}

final case class SlpRegUpdateScheduleNode(regPackId: Int, fragmentId: Int) extends SlpScheduleNode {
  require(regPackId >= 0)
  require(fragmentId >= 0)
  // A pack has at most one fragment per StatementGraph level.  The bounded
  // encoding keeps the existing compact schedule ordering while making every
  // fragment a distinct graph node.
  def sortKey: (Int, Int) = (3, regPackId * 10000 + fragmentId)
  def label: String = s"reg_update:$regPackId:$fragmentId"
}

final case class SlpScheduleEdge(source: SlpScheduleNode, destination: SlpScheduleNode) {
  require(source != destination)
  def sortKey: ((Int, Int), (Int, Int)) = (source.sortKey, destination.sortKey)
}

final case class SlpPlanCycle(remainingNodes: Vector[SlpScheduleNode]) {
  require(remainingNodes.nonEmpty)
  require(remainingNodes == remainingNodes.distinct.sortBy(_.sortKey))
}

final case class SlpRegView(regPackId: Int, laneIndex: Int, lane: SlpRegLane) {
  require(regPackId >= 0)
  require(laneIndex >= 0)
}

final case class SlpPlanStats(
  packDependencies:       Int,
  directPackInputs:       Int,
  directRegInputs:        Int,
  broadcastInputs:        Int,
  packSegmentAlignments:  Int,
  scalarToPackAlignments: Int,
  packToScalarAlignments: Int,
  materializedLanes:      Int,
  scalarFallbackNodes:    Int,
  regUpdatePacks:         Int,
  scalarRegViews:         Int,
  scheduleNodes:          Int,
  scheduleEdges:          Int
) {
  require(packDependencies >= 0)
  require(directPackInputs >= 0)
  require(directRegInputs >= 0)
  require(broadcastInputs >= 0)
  require(packSegmentAlignments >= 0)
  require(scalarToPackAlignments >= 0)
  require(packToScalarAlignments >= 0)
  require(materializedLanes >= 0)
  require(scalarFallbackNodes >= 0)
  require(regUpdatePacks >= 0)
  require(scalarRegViews >= 0)
  require(scheduleNodes >= 0)
  require(scheduleEdges >= 0)
}

/** Complete immutable Phase-3 lowering plan.
  *
  * This remains analysis-only.  The schedule describes the order a future
  * lowering must follow, but Phase 3 never mutates StatementGraph or invokes
  * packed C++ emission.
  */
final case class SlpPlan(
  packGraph:             SlpPackGraph,
  alignPlan:             SlpAlignPlan,
  regPacking:            Option[SlpRegPackingResult],
  regViews:              Vector[SlpRegView],
  scalarFallbackNodeIds: Vector[Int],
  scheduleEdges:         Vector[SlpScheduleEdge],
  topologicalSchedule:   Vector[SlpScheduleNode],
  projectionPlan:        SlpPackProjectionPlan,
  scalarProjectionPlan:  SlpScalarPackProjectionPlan,
  scalarReductionProjectionPlan: SlpPackReductionProjectionPlan,
  laneBitwiseReductionProjectionPlan: SlpLaneBitwiseReductionProjectionPlan,
  indexedPackReadPlan:   SlpIndexedPackReadPlan,
  residualIndexedMuxPlan: SlpResidualIndexedMuxPlan,
  residualScalarRewritePlan: SlpResidualScalarRewritePlan,
  stats:                 SlpPlanStats
) {
  require(scalarFallbackNodeIds == scalarFallbackNodeIds.distinct.sorted)
  require(scheduleEdges == scheduleEdges.distinct.sortBy(_.sortKey))
  require(topologicalSchedule.map(_.label).distinct.size == topologicalSchedule.size)
}

object SlpPlan {
  private implicit val scheduleOrdering: Ordering[SlpScheduleNode] =
    Ordering.by[SlpScheduleNode, (Int, Int)](_.sortKey)

  private def topologicalOrder(
    nodes: Vector[SlpScheduleNode],
    edges: Vector[SlpScheduleEdge]
  ): Either[SlpPlanCycle, Vector[SlpScheduleNode]] = {
    val incoming = mutable.HashMap(nodes.map(_ -> 0): _*)
    val outgoing = mutable.HashMap.empty[SlpScheduleNode, Vector[SlpScheduleNode]]
      .withDefaultValue(Vector.empty)

    edges.foreach { edge =>
      incoming.update(edge.destination, incoming(edge.destination) + 1)
      outgoing.update(
        edge.source,
        (outgoing(edge.source) :+ edge.destination).distinct.sortBy(_.sortKey)
      )
    }

    val ready = mutable.TreeSet(nodes.filter(incoming(_) == 0): _*)
    val result = Vector.newBuilder[SlpScheduleNode]
    var visited = 0
    while (ready.nonEmpty) {
      val node = ready.head
      ready.remove(node)
      result += node
      visited += 1
      outgoing(node).foreach { successor =>
        incoming.update(successor, incoming(successor) - 1)
        if (incoming(successor) == 0) ready.add(successor)
      }
    }

    if (visited == nodes.size) Right(result.result())
    else Left(SlpPlanCycle(nodes.filter(incoming(_) > 0).sortBy(_.sortKey)))
  }

  /** Reproduce the old lowering scheduler.
    *
    * The old backend rebuilt a StatementGraph whose pack node ID was anchored
    * at the minimum original member ID, assigned alignment nodes after all
    * original nodes, and then used dependency-first DFS TopologicalSort. A
    * high-ID alignment was consequently pulled immediately in front of the
    * first low-ID consumer that needed it instead of waiting in a global ready
    * queue behind every scalar node.
    */
  private def depthFirstTopologicalOrder(
    nodes: Vector[SlpScheduleNode],
    edges: Vector[SlpScheduleEdge],
    ordering: Ordering[SlpScheduleNode]
  ): Either[SlpPlanCycle, Vector[SlpScheduleNode]] = {
    val incoming = edges.groupBy(_.destination).view.mapValues { values =>
      values.map(_.source).distinct.sorted(ordering)
    }.toMap.withDefaultValue(Vector.empty)
    val visiting = mutable.HashSet.empty[SlpScheduleNode]
    val finished = mutable.HashSet.empty[SlpScheduleNode]
    val result = Vector.newBuilder[SlpScheduleNode]
    var cycle = false

    def visit(node: SlpScheduleNode): Unit = {
      if (visiting(node)) cycle = true
      else if (!finished(node) && !cycle) {
        visiting += node
        incoming(node).foreach(visit)
        visiting -= node
        if (!finished(node)) {
          finished += node
          result += node
        }
      }
    }

    nodes.sorted(ordering).foreach(visit)
    if (!cycle && finished.size == nodes.size) Right(result.result())
    else Left(SlpPlanCycle(nodes.filterNot(finished).sortBy(_.sortKey)))
  }

  def build(
    context: SlpAnalysisContext,
    packGraph: SlpPackGraph,
    alignPlan: SlpAlignPlan,
    regPacking: Option[SlpRegPackingResult] = None,
    indexedPackReadPlan: SlpIndexedPackReadPlan = SlpIndexedPackReadPlan.Empty,
    residualIndexedMuxPlan: SlpResidualIndexedMuxPlan = SlpResidualIndexedMuxPlan.Empty
  ): Either[SlpPlanCycle, SlpPlan] = {
    val view = context.graph
    val projectionPlan = SlpPackProjectionPlanner.build(context, packGraph, alignPlan)
    val regNodeToPackId = regPacking.toVector.flatMap(_.packs).flatMap { pack =>
      pack.nodeIds.map(_ -> pack.id)
    }.toMap
    val regNodeToScheduleNode = regPacking.toVector.flatMap(_.packs).flatMap { pack =>
      pack.commitFragments.flatMap { fragment =>
        fragment.laneIndices.map { laneIndex =>
          pack.lanes(laneIndex).updateNodeId -> SlpRegUpdateScheduleNode(pack.id, fragment.id)
        }
      }
    }.toMap
    require(
      regNodeToPackId.keySet.intersect(packGraph.nodeToPackId.keySet).isEmpty,
      "a node cannot belong to both a combinational pack and a RegUpdate pack"
    )
    // These terminal Mux nodes are evaluated by the packed state commit. They
    // have been proved to feed only the corresponding RegUpdate lanes, so
    // scheduling them as scalar statements would duplicate next-state work.
    val absorbedRegMuxNodeIds = regPacking.toVector.flatMap(_.muxWrites)
      .filter(_.absorbNextNodes).flatMap(_.nextNodeIds).toSet
    val scalarFallbackNodeIds = view.validNodeIds.filterNot(nodeId =>
      packGraph.nodeToPackId.contains(nodeId) || regNodeToPackId.contains(nodeId) ||
        packGraph.absorbedNodeIds(nodeId) || absorbedRegMuxNodeIds(nodeId) ||
        residualIndexedMuxPlan.absorbedNodeIds(nodeId)
    )
    val scalarFallbackSet = scalarFallbackNodeIds.toSet
    val scalarProjectionPlan = SlpScalarPackProjectionPlanner.build(
      context,
      packGraph,
      alignPlan,
      scalarFallbackNodeIds
    )
    val scalarReductionProjectionPlan = SlpPackReductionProjectionPlanner.build(
      context,
      packGraph,
      alignPlan,
      scalarFallbackNodeIds
    )
    val laneBitwiseReductionProjectionPlan = SlpLaneBitwiseReductionProjectionPlanner.build(
      context,
      packGraph,
      alignPlan,
      scalarFallbackNodeIds
    )
    val residualScalarRewriteBlockedNodeIds =
      packGraph.nodeToPackId.keySet ++
        packGraph.absorbedNodeIds ++
        regNodeToPackId.keySet ++
        absorbedRegMuxNodeIds ++
        indexedPackReadPlan.byRootNodeId.keySet ++
        residualIndexedMuxPlan.byRootNodeId.keySet ++
        residualIndexedMuxPlan.absorbedNodeIds ++
        scalarProjectionPlan.byRootNodeId.keySet ++
        scalarProjectionPlan.internalCatNodeIds ++
        scalarProjectionPlan.elidedLeafNodeIds ++
        scalarReductionProjectionPlan.byRootNodeId.keySet ++
        scalarReductionProjectionPlan.internalReductionNodeIds ++
        scalarReductionProjectionPlan.elidedPackedLeafNodeIds ++
        laneBitwiseReductionProjectionPlan.byRootNodeId.keySet ++
        laneBitwiseReductionProjectionPlan.internalNodeIds ++
        laneBitwiseReductionProjectionPlan.elidedLeafNodeIds
    val residualScalarRewritePlan = SlpResidualScalarRewritePlanner.build(
      context,
      residualScalarRewriteBlockedNodeIds,
      scalarFallbackNodeIds
    )

    val directRegInputs = alignPlan.directRegInputs.flatMap { input =>
      regPacking.toVector.flatMap(_.packs.find(_.id == input.regPackId)).flatMap(_.registerNames)
        .map(name => (input.regPackId, input.destinationPackId, input.argumentIndex, name))
    }.toSet
    val segmentRegInputs = alignPlan.scalarToPack.flatMap { alignment =>
      alignment.lanes.collect {
        case lane: SlpRegInputLane =>
          (lane.regPackId, alignment.destinationPackId, alignment.argumentIndex, lane.registerName)
      }
    }.toSet
    val broadcastRegInputs = alignPlan.broadcastInputs.flatMap { input =>
      input.value match {
        case value: SlpBroadcastReg =>
          regPacking.toVector.flatMap(_.packs.find(_.id == value.regPackId)).map { pack =>
            (value.regPackId, input.destinationPackId, input.argumentIndex,
              pack.lanes(value.sourceLaneIndex).registerName)
          }
        case _ => Vector.empty
      }
    }.toSet
    val regWriteReads = alignPlan.regWriteInputs.flatMap { input =>
      input.lanes.collect {
        case lane: SlpRegInputLane => (lane.regPackId, input.regPackId, lane.registerName)
      }
    }.toSet
    val classifiedOperations = context.classifications.collect {
      case (nodeId, SlpSupported(operation)) => nodeId -> operation
    }.toMap
    val operations = classifiedOperations ++ packGraph.operationOverrides

    def packedConsumerNeedsView(
      regPackId: Int,
      registerName: String,
      consumerNodeId: Int,
      destinationPackId: Int
    ): Boolean = {
      operations.get(consumerNodeId).toVector.flatMap(_.operands.zipWithIndex).collect {
        case (SlpSignal(name, _), argumentIndex) if name == registerName => argumentIndex
      }.exists(argumentIndex =>
        !directRegInputs((regPackId, destinationPackId, argumentIndex, registerName)) &&
          !segmentRegInputs((regPackId, destinationPackId, argumentIndex, registerName)) &&
          !broadcastRegInputs((regPackId, destinationPackId, argumentIndex, registerName))
      )
    }

    val regViews = regPacking.toVector.flatMap(_.packs).flatMap { regPack =>
      regPack.lanes.zipWithIndex.flatMap { case (lane, laneIndex) =>
        val readers = view.graph.nameToID.get(lane.registerName).toVector.flatMap(view.validFanoutIds)
        val needsView = readers.exists { consumerNodeId =>
          packGraph.nodeToPackId.get(consumerNodeId) match {
            case Some(destinationPackId) =>
              packedConsumerNeedsView(regPack.id, lane.registerName, consumerNodeId, destinationPackId)
            case None => regNodeToPackId.get(consumerNodeId) match {
              case Some(destinationRegPackId) =>
                !regWriteReads((regPack.id, destinationRegPackId, lane.registerName))
              case None                       => scalarFallbackSet(consumerNodeId)
            }
          }
        }
        if (needsView) Some(SlpRegView(regPack.id, laneIndex, lane)) else None
      }
    }.sortBy(view => (view.regPackId, view.laneIndex))

    val scalarNodes = scalarFallbackNodeIds.map(SlpScalarScheduleNode)
    val packNodes = packGraph.packs.map(pack => SlpPackScheduleNode(pack.id))
    val alignmentNodes = alignPlan.alignments.map(alignment => SlpAlignmentScheduleNode(alignment.id))
    val regNodes = regPacking.toVector.flatMap(_.packs).flatMap { pack =>
      pack.commitFragments.map(fragment => SlpRegUpdateScheduleNode(pack.id, fragment.id))
    }
    val nodes: Vector[SlpScheduleNode] =
      (scalarNodes ++ packNodes ++ alignmentNodes ++ regNodes).sortBy(_.sortKey)

    def executionNode(nodeId: Int): Option[SlpScheduleNode] =
      packGraph.nodeToPackId.get(nodeId).map(SlpPackScheduleNode)
        .orElse(regNodeToScheduleNode.get(nodeId))
        .orElse(if (scalarFallbackSet(nodeId)) Some(SlpScalarScheduleNode(nodeId)) else None)

    val edgeBuilder = Vector.newBuilder[SlpScheduleEdge]
    def addEdge(source: SlpScheduleNode, destination: SlpScheduleNode): Unit =
      if (source != destination) edgeBuilder += SlpScheduleEdge(source, destination)

    view.nodes.indices.foreach { sourceNodeId =>
      executionNode(sourceNodeId).foreach { source =>
        view.fanoutIds(sourceNodeId).foreach { destinationNodeId =>
          executionNode(destinationNodeId).foreach(destination => addEdge(source, destination))
        }
      }
    }

    // A scalar Cat-tree projection consumes its source pack directly rather
    // than through the leaf pack-to-scalar materializations.  The ordinary
    // use-def edges only describe those scalar leaves, so add the direct data
    // dependency explicitly to keep either scheduler semantically ordered.
    scalarProjectionPlan.projections.foreach { projection =>
      addEdge(
        SlpPackScheduleNode(projection.sourcePackId),
        SlpScalarScheduleNode(projection.rootNodeId)
      )
    }
    scalarReductionProjectionPlan.projections.foreach { projection =>
      projection.packedSources.foreach { source =>
        addEdge(
          SlpPackScheduleNode(source.packId),
          SlpScalarScheduleNode(projection.rootNodeId)
        )
      }
    }
    laneBitwiseReductionProjectionPlan.projections.foreach { projection =>
      addEdge(
        SlpPackScheduleNode(projection.sourcePackId),
        SlpScalarScheduleNode(projection.rootNodeId)
      )
      projection.scalarSeedNodeId.flatMap(executionNode).foreach { seed =>
        addEdge(seed, SlpScalarScheduleNode(projection.rootNodeId))
      }
    }
    indexedPackReadPlan.reads.foreach { read =>
      read.sourcePackIds.foreach { sourcePackId =>
        addEdge(
          SlpPackScheduleNode(sourcePackId),
          SlpScalarScheduleNode(read.rootNodeId)
        )
      }
    }
    residualIndexedMuxPlan.scalarUses.foreach { case (sourceNodeId, rootNodeId) =>
      executionNode(sourceNodeId).foreach { source =>
        if (scalarFallbackSet(rootNodeId)) addEdge(source, SlpScalarScheduleNode(rootNodeId))
      }
    }
    residualScalarRewritePlan.scalarUses.foreach { case (sourceNodeId, rootNodeId) =>
      executionNode(sourceNodeId).foreach { source =>
        if (scalarFallbackSet(rootNodeId)) addEdge(source, SlpScalarScheduleNode(rootNodeId))
      }
    }

    alignPlan.directPackInputs.foreach { input =>
      addEdge(SlpPackScheduleNode(input.sourcePackId), SlpPackScheduleNode(input.destinationPackId))
    }

    alignPlan.broadcastInputs.foreach { input =>
      input.value match {
        case signal: SlpBroadcastSignal =>
          signal.producerNodeId.flatMap(executionNode).foreach { source =>
            addEdge(source, SlpPackScheduleNode(input.destinationPackId))
          }
        case packed: SlpBroadcastPacked =>
          addEdge(
            SlpPackScheduleNode(packed.sourcePackId),
            SlpPackScheduleNode(input.destinationPackId)
          )
        case _: SlpBroadcastReg =>
        case _: SlpBroadcastConstant =>
      }
    }

    alignPlan.packToScalar.foreach { alignment =>
      val alignmentNode = SlpAlignmentScheduleNode(alignment.id)
      addEdge(SlpPackScheduleNode(alignment.sourcePackId), alignmentNode)
      alignment.lanes.flatMap(_.consumers).collect {
        case SlpScalarConsumer(nodeId) => nodeId
      }.distinct.sorted.foreach { consumerNodeId =>
        if (scalarFallbackSet(consumerNodeId)) addEdge(alignmentNode, SlpScalarScheduleNode(consumerNodeId))
      }
    }

    alignPlan.packSegments.foreach { alignment =>
      alignment.source match {
        case SlpCombSegmentSource(sourcePackId) =>
          addEdge(
            SlpPackScheduleNode(sourcePackId),
            SlpAlignmentScheduleNode(alignment.id)
          )
        case _: SlpRegSegmentSource =>
      }
    }

    alignPlan.scalarToPack.foreach { alignment =>
      val alignmentNode = SlpAlignmentScheduleNode(alignment.id)
      alignment.lanes.foreach {
        case lane: SlpScalarInputLane =>
          lane.producerNodeId.flatMap(executionNode).foreach(source => addEdge(source, alignmentNode))
        case lane: SlpUnpackedInputLane =>
          lane.segmentAlignmentId match {
            case Some(segmentId) => addEdge(SlpAlignmentScheduleNode(segmentId), alignmentNode)
            case None            => addEdge(SlpPackScheduleNode(lane.sourcePackId), alignmentNode)
          }
        case lane: SlpRegInputLane =>
          lane.segmentAlignmentId.foreach(segmentId =>
            addEdge(SlpAlignmentScheduleNode(segmentId), alignmentNode)
          )
        case _: SlpConstantInputLane =>
      }
      addEdge(alignmentNode, SlpPackScheduleNode(alignment.destinationPackId))
    }


    alignPlan.regWriteInputs.foreach { input =>
      val destination = SlpRegUpdateScheduleNode(input.regPackId, 0)
      input.lanes.foreach {
        case lane: SlpScalarInputLane =>
          lane.producerNodeId.flatMap(executionNode).foreach(source => addEdge(source, destination))
        case lane: SlpUnpackedInputLane =>
          lane.segmentAlignmentId match {
            case Some(segmentId) => addEdge(SlpAlignmentScheduleNode(segmentId), destination)
            case None            => addEdge(SlpPackScheduleNode(lane.sourcePackId), destination)
          }
        case lane: SlpRegInputLane =>
          lane.segmentAlignmentId.foreach(segmentId =>
            addEdge(SlpAlignmentScheduleNode(segmentId), destination)
          )
        case _: SlpConstantInputLane =>
      }
    }
    regPacking.toVector.flatMap(_.directWrites).foreach { write =>
      regPacking.toVector.flatMap(_.packs.find(_.id == write.regPackId)).foreach { pack =>
        pack.commitFragments.foreach { fragment =>
          addEdge(
            SlpPackScheduleNode(write.sourcePackId),
            SlpRegUpdateScheduleNode(write.regPackId, fragment.id)
          )
        }
      }
    }
    regPacking.toVector.flatMap(_.muxWrites).foreach { write =>
      regPacking.toVector.flatMap(_.packs.find(_.id == write.regPackId)).foreach { pack =>
        pack.commitFragments.foreach { fragment =>
          val destination = SlpRegUpdateScheduleNode(write.regPackId, fragment.id)
          addEdge(SlpPackScheduleNode(write.falseSourcePackId), destination)
          view.graph.nameToID.get(write.conditionName).flatMap(executionNode)
            .foreach(source => addEdge(source, destination))
        }
      }
    }

    val edges = edgeBuilder.result().distinct.sortBy(_.sortKey)
    val useLegacySchedule = java.lang.Boolean.getBoolean("armor.slp.legacySchedule")
    val scheduled = if (useLegacySchedule) {
      val alignmentBase = view.graph.numNodes() + 1
      def legacyAnchor(node: SlpScheduleNode): (Int, Int, Int) = node match {
        case SlpScalarScheduleNode(nodeId) => (nodeId, 0, nodeId)
        case SlpPackScheduleNode(packId) =>
          (packGraph.pack(packId).nodeIds.min, 1, packId)
        case SlpAlignmentScheduleNode(alignmentId) =>
          (alignmentBase + alignmentId, 2, alignmentId)
        case SlpRegUpdateScheduleNode(regPackId, fragmentId) =>
          val anchor = regPacking.toVector.flatMap(_.packs.find(_.id == regPackId))
            .flatMap { pack =>
              pack.fragment(fragmentId).laneIndices.map(pack.lanes(_).updateNodeId).minOption
            }.headOption
            .getOrElse(alignmentBase + edges.size + regPackId)
          (anchor, 3, regPackId * 10000 + fragmentId)
      }
      val legacyOrdering = Ordering.by[SlpScheduleNode, (Int, Int, Int)](legacyAnchor)
      depthFirstTopologicalOrder(nodes, edges, legacyOrdering)
    } else topologicalOrder(nodes, edges)
    scheduled.map { schedule =>
      val stats = SlpPlanStats(
        packDependencies = packGraph.dependencies.size,
        directPackInputs = alignPlan.directPackInputs.size,
        directRegInputs = alignPlan.directRegInputs.size,
        broadcastInputs = alignPlan.broadcastInputs.size,
        packSegmentAlignments = alignPlan.packSegments.size,
        scalarToPackAlignments = alignPlan.scalarToPack.size,
        packToScalarAlignments = alignPlan.packToScalar.size,
        materializedLanes = alignPlan.packToScalar.map(_.lanes.size).sum,
        scalarFallbackNodes = scalarFallbackNodeIds.size,
        regUpdatePacks = regPacking.map(_.packs.size).getOrElse(0),
        scalarRegViews = regViews.size,
        scheduleNodes = nodes.size,
        scheduleEdges = edges.size
      )
      SlpPlan(packGraph, alignPlan, regPacking, regViews, scalarFallbackNodeIds,
        edges, schedule, projectionPlan, scalarProjectionPlan, scalarReductionProjectionPlan,
        laneBitwiseReductionProjectionPlan, indexedPackReadPlan, residualIndexedMuxPlan,
        residualScalarRewritePlan, stats)
    }
  }
}
