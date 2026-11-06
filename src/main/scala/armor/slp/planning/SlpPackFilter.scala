package armor.slp

import essent.ir.RegUpdate
import firrtl.ir.{Expression, Reference, SubField, SubIndex}
import scala.collection.mutable

final case class SlpPackFilterDecision(
  originalPackId: Int,
  nodeIds:        Vector[Int],
  retained:       Boolean,
  reason:         String
) {
  require(originalPackId >= 0)
  require(nodeIds.nonEmpty)
  require(reason.nonEmpty)
}

final case class SlpPackDataReuseInfo(
  originalPackId:            Int,
  densePackId:               Option[Int],
  nodeIds:                   Vector[Int],
  moduleName:                String,
  localNetName:              String,
  opcode:                    String,
  discoveryPhase:           String,
  parallelDegree:           Int,
  resultWidth:              Int,
  packedPredecessorCount:   Int,
  livePackedSuccessorCount: Int,
  directRegReadRoot:         Boolean,
  regUpdateProducer:         Boolean,
  scalarOutputLaneCount:    Int,
  inputArgCount:            Int,
  packedInputArgCount:      Int,
  scalarPackInputArgCount:  Int,
  broadcastInputArgCount:   Int,
  constantInputArgCount:    Int,
  unknownInputArgCount:     Int,
  filterCandidate:          Boolean,
  retained:                 Boolean,
  reason:                   String
) {
  require(originalPackId >= 0)
  require(nodeIds.nonEmpty)
  require(parallelDegree == nodeIds.size)
  require(resultWidth > 0)
  require(packedPredecessorCount >= 0)
  require(livePackedSuccessorCount >= 0)
  require(scalarOutputLaneCount >= 0)
  require(inputArgCount >= 0)
  require(packedInputArgCount >= 0)
  require(scalarPackInputArgCount >= 0)
  require(broadcastInputArgCount >= 0)
  require(constantInputArgCount >= 0)
  require(unknownInputArgCount >= 0)
  require(reason.nonEmpty)
}

final case class SlpPackFilterResult(
  result:         SlpPackingResult,
  plan:           SlpPlan,
  regFiltering:   SlpRegPackFilterResult,
  decisions:      Vector[SlpPackFilterDecision],
  dataReuse:      Vector[SlpPackDataReuseInfo],
  rawPackCount:   Int,
  rawPackedNodes: Int
) {
  require(result.packs.map(_.id) == result.packs.indices.toVector)
  require(decisions == decisions.sortBy(_.originalPackId))
  require(dataReuse == dataReuse.sortBy(_.originalPackId))
  require(rawPackCount >= result.packs.size)
  require(rawPackedNodes >= result.packs.map(_.parallelDegree).sum)
}

/** Minimum-degree, connectivity, and lightweight profitability filter.
  *
  * First reject combinational packs below the retained minimum degree.  The remaining
  * PackGraph keeps every pack which has a predecessor or successor. RegUpdate
  * packs are state endpoints and are retained independently; a combinational
  * pack which produces any packed RegUpdate lane is also connected even when
  * the layouts require alignment.  Finally, a fixed-point pass removes
  * terminal scalar-sink packs whose inputs require scalar->pack construction
  * but whose outputs have no remaining packed reuse.
  */
final class SlpIsolatedPackFilter(context: SlpAnalysisContext) {
  private val view = context.graph
  private val classifiedOperations: Map[Int, SlpOperation] =
    context.classifications.collect { case (nodeId, SlpSupported(operation)) => nodeId -> operation }.toMap

  private def referenceName(expression: Expression): Option[String] = expression match {
    case Reference(name, _, _, _)       => Some(name)
    case SubField(base, name, _, _)     => referenceName(base).map(prefix => s"$prefix.$name")
    case SubIndex(base, index, _, _)    => referenceName(base).map(prefix => s"${prefix}_$index")
    case _                              => None
  }

  private def packGraph(result: SlpPackingResult): SlpPackGraph =
    SlpPackGraph.build(view, result).fold(
      cycle => throw new IllegalStateException(
        s"isolated-pack filter PackGraph cycle: ${cycle.remainingPackIds.mkString(",")}"
      ),
      identity
    )

  private def buildPlan(result: SlpPackingResult): (SlpPlan, SlpRegPackFilterResult) = {
    val graph = packGraph(result)
    val regFiltering = new SlpRegPackFilter().filter(new SlpRegUpdatePacker(context, result).run())
    val registers = regFiltering.result
    val residualIndexedMuxes = SlpResidualIndexedMuxPlanner.build(context, graph, Some(registers))
    val indexedPackReads = SlpIndexedPackReadPlanner.build(context, graph, residualIndexedMuxes)
    val alignPlan = SlpAlignPlanner.build(
      context,
      graph,
      Some(registers),
      indexedPackReads.coveredScalarUses,
      residualIndexedMuxes.scalarUses
    )
    val plan = SlpPlan.build(
      context,
      graph,
      alignPlan,
      Some(registers),
      indexedPackReads,
      residualIndexedMuxes
    ).fold(
      cycle => throw new IllegalStateException(
        s"isolated-pack filter plan cycle: ${cycle.remainingNodes.map(_.label).mkString(",")}"
      ),
      identity
    )
    (plan, regFiltering)
  }

  private sealed trait OperandReuseKind { def name: String }
  private case object PackedInput extends OperandReuseKind { val name = "packed" }
  private case object ScalarPackInput extends OperandReuseKind { val name = "scalar_pack" }
  private case object BroadcastInput extends OperandReuseKind { val name = "broadcast" }
  private case object ConstantInput extends OperandReuseKind { val name = "constant" }
  private case object UnknownInput extends OperandReuseKind { val name = "unknown" }

  private def operationFor(graph: SlpPackGraph, nodeId: Int): Option[SlpOperation] =
    graph.operationOverrides.get(nodeId).orElse(classifiedOperations.get(nodeId))

  private def operandReuseKinds(
    graph: SlpPackGraph,
    pack:  SlpPack,
    live:  mutable.BitSet
  ): Vector[OperandReuseKind] = {
    val operations = pack.nodeIds.flatMap(operationFor(graph, _))
    if (operations.size != pack.nodeIds.size || operations.map(_.operands.size).distinct.size != 1) {
      Vector.fill(pack.shape.operandWidths.size)(UnknownInput)
    } else {
      val operandCount = operations.head.operands.size
      (0 until operandCount).toVector.map { operandIndex =>
        val operands = operations.map(_.operands(operandIndex))
        if (operands.forall(_.isInstanceOf[SlpUIntConstant])) {
          ConstantInput
        } else {
          val signals = operands.collect { case signal: SlpSignal => signal }
          if (signals.size != operands.size) {
            UnknownInput
          } else {
            val names = signals.map(_.name)
            val producerNodeIds = names.flatMap(view.graph.nameToID.get)
            val producerPackIds = producerNodeIds.flatMap(graph.nodeToPackId.get)
            val allFromLivePackedInput =
              producerNodeIds.size == names.size &&
                producerPackIds.size == names.size &&
                producerPackIds.forall(packId => packId != pack.id && live(packId))
            if (allFromLivePackedInput) PackedInput
            else if (names.distinct.size == 1) BroadcastInput
            else ScalarPackInput
          }
        }
      }
    }
  }

  private def scalarOutputLaneCount(
    graph: SlpPackGraph,
    pack:  SlpPack,
    live:  mutable.BitSet
  ): Int = {
    val laneNodeIds = pack.nodeIds.toSet
    pack.nodeIds.count { nodeId =>
      view.validFanoutIds(nodeId).exists { consumerNodeId =>
        !laneNodeIds(consumerNodeId) &&
          graph.nodeToPackId.get(consumerNodeId).forall(packId => !live(packId))
      }
    }
  }

  private def summarizeReuse(
    graph:                SlpPackGraph,
    originalPackId:       Int,
    pack:                 SlpPack,
    live:                 mutable.BitSet,
    directRegReadRootIds: mutable.BitSet,
    regUpdateProducerIds: mutable.BitSet,
    retained:             Boolean,
    reason:               String
  ): SlpPackDataReuseInfo = {
    val operandKinds = operandReuseKinds(graph, pack, live)
    val liveSuccessorCount = graph.successors(pack.id).count(live)
    val moduleName = pack.module.map(_.moduleName)
      .orElse(pack.moduleNet.map(_.moduleName))
      .getOrElse("")
    val localNetName = pack.moduleNet.map(_.localNetName).getOrElse("")
    SlpPackDataReuseInfo(
      originalPackId = originalPackId,
      densePackId = Some(pack.id),
      nodeIds = pack.nodeIds,
      moduleName = moduleName,
      localNetName = localNetName,
      opcode = pack.shape.opcode.name,
      discoveryPhase = pack.discoveryPhase.getOrElse(""),
      parallelDegree = pack.parallelDegree,
      resultWidth = pack.shape.resultWidth,
      packedPredecessorCount = graph.predecessors(pack.id).count(live),
      livePackedSuccessorCount = liveSuccessorCount,
      directRegReadRoot = directRegReadRootIds(pack.id),
      regUpdateProducer = regUpdateProducerIds(pack.id),
      scalarOutputLaneCount = scalarOutputLaneCount(graph, pack, live),
      inputArgCount = operandKinds.size,
      packedInputArgCount = operandKinds.count(_ == PackedInput),
      scalarPackInputArgCount = operandKinds.count(_ == ScalarPackInput),
      broadcastInputArgCount = operandKinds.count(_ == BroadcastInput),
      constantInputArgCount = operandKinds.count(_ == ConstantInput),
      unknownInputArgCount = operandKinds.count(_ == UnknownInput),
      filterCandidate = shouldRejectForProfitability(
        graph,
        pack,
        live,
        directRegReadRootIds,
        regUpdateProducerIds,
        operandKinds
      ),
      retained = retained,
      reason = reason
    )
  }

  private def shouldRejectForProfitability(
    graph:                SlpPackGraph,
    pack:                 SlpPack,
    live:                 mutable.BitSet,
    directRegReadRootIds: mutable.BitSet,
    regUpdateProducerIds: mutable.BitSet,
    operandKinds:         Vector[OperandReuseKind]
  ): Boolean = {
    val protectedStateEndpoint = directRegReadRootIds(pack.id) || regUpdateProducerIds(pack.id)
    val terminalScalarSink =
      graph.successors(pack.id).count(live) == 0 &&
        scalarOutputLaneCount(graph, pack, live) > 0 &&
        !protectedStateEndpoint
    val requiresScalarPackInput = operandKinds.contains(ScalarPackInput)
    val weakPackedInputReuse = operandKinds.count(_ == PackedInput) <= 1
    terminalScalarSink && requiresScalarPackInput && weakPackedInputReuse
  }

  private def retainedReason(
    graph:                SlpPackGraph,
    packId:               Int,
    live:                 mutable.BitSet,
    directRegReadRootIds: mutable.BitSet,
    regUpdateProducerIds: mutable.BitSet
  ): String = {
    if (directRegReadRootIds(packId)) "direct_reg_read_root"
    else if (regUpdateProducerIds(packId)) "reg_update_producer"
    else if (graph.successors(packId).exists(live)) "has_packed_successor"
    else if (graph.predecessors(packId).exists(live)) "has_packed_predecessor"
    else "connected"
  }

  def filter(validated: SlpPackingResult): SlpPackFilterResult = {
    val eligibleOriginalPacks = validated.packs.filter(
      _.parallelDegree >= context.config.minParallelDegree
    )
    val eligibleOriginalToDenseId = eligibleOriginalPacks.zipWithIndex.map {
      case (pack, denseId) => pack.id -> denseId
    }.toMap
    val eligiblePacks = eligibleOriginalPacks.zipWithIndex.map {
      case (pack, denseId) => pack.copy(id = denseId)
    }
    val eligibleRootNodeIds = eligiblePacks.iterator.flatMap(_.nodeIds).toSet
    val eligibleResult = validated.copy(
      packs = eligiblePacks,
      regions = validated.regions.filter(region => eligibleRootNodeIds(region.rootNodeId))
    )
    val eligibleGraph = packGraph(eligibleResult)
    val connectedPackIds = mutable.BitSet.empty

    eligibleGraph.dependencies.foreach { dependency =>
      connectedPackIds += dependency.sourcePackId
      connectedPackIds += dependency.destinationPackId
    }

    // A pack whose only packed input is retained register state has no
    // current-cycle PackGraph predecessor.  Treat these packs as connected
    // when the register layout exactly matches the pack input layout; the
    // AlignPlanner will then emit a SlpDirectRegInput instead of scalar
    // unpack -> scalar op -> scalar pack.
    //
    // This filter receives `validated`, i.e. packs that already passed
    // SlpLoweringValidator in lowering mode.  Keep the connectivity policy
    // independent of opcode semantics: if a direct-reg-read-root pack is
    // present here, it is already considered lowerable/packable by the
    // lowering layer.  Duplicating an opcode whitelist here silently drops
    // valid packs such as Cat/Bits/Mux discovered from retained register
    // reads.
    val directRegReadRootPackIds = mutable.BitSet.empty
    val regReadConnectivity = new SlpRegPackFilter().filter(
      new SlpRegUpdatePacker(context, eligibleResult).run()
    ).result
    regReadConnectivity.stateReads.foreach { read =>
      eligibleGraph.packsById.get(read.destinationPackId).foreach { _ =>
        connectedPackIds += read.destinationPackId
        directRegReadRootPackIds += read.destinationPackId
      }
    }

    // RegUpdate is represented outside the combinational PackGraph in this
    // backend. Recover the old pack -> RegUpdate-pack connectivity from the
    // actual update expression, without imposing an exact-layout constraint.
    // Do not use the post-connect-elimination StatementGraph fan-ins here:
    // those edges can cross scalar Connect nodes which separated packs in the
    // old PackGraph.
    val regUpdateProducerPackIds = mutable.BitSet.empty
    view.validNodeIds.foreach { nodeId =>
      view.node(nodeId).statement match {
        case update: RegUpdate =>
          referenceName(update.expr)
            .flatMap(view.graph.nameToID.get)
            .flatMap(eligibleGraph.nodeToPackId.get)
            .foreach { packId =>
              connectedPackIds += packId
              regUpdateProducerPackIds += packId
            }
        case _ =>
      }
    }

    // Lightweight profitability pass over the already-connected pack graph.
    // It does not inspect lowering decisions and deliberately stays after
    // discovery.  The rule removes terminal packs which would introduce a
    // scalar->pack construction for weak packed reuse and then immediately
    // unpack back to scalar users.
    val livePackIds = mutable.BitSet(connectedPackIds.toSeq: _*)
    val profitabilityRejectReasons = mutable.HashMap.empty[Int, String]
    var changed = true
    while (changed) {
      changed = false
      eligibleGraph.topologicalPackIds.reverse.foreach { packId =>
        if (livePackIds(packId)) {
          val pack = eligibleGraph.pack(packId)
          val operandKinds = operandReuseKinds(eligibleGraph, pack, livePackIds)
          if (shouldRejectForProfitability(
              eligibleGraph,
              pack,
              livePackIds,
              directRegReadRootPackIds,
              regUpdateProducerPackIds,
              operandKinds
            )) {
            livePackIds -= packId
            profitabilityRejectReasons.update(packId, "unprofitable_terminal_scalar_sink")
            changed = true
          }
        }
      }
    }

    val decisions = validated.packs.sortBy(_.id).map { pack =>
      val decision = eligibleOriginalToDenseId.get(pack.id) match {
        case None => (false, "below_min_parallel_degree")
        case Some(denseId) if livePackIds(denseId) =>
          (true, retainedReason(
            eligibleGraph,
            denseId,
            livePackIds,
            directRegReadRootPackIds,
            regUpdateProducerPackIds
          ))
        case Some(denseId) =>
          (false, profitabilityRejectReasons.getOrElse(denseId, "isolated_pack"))
      }
      SlpPackFilterDecision(
        originalPackId = pack.id,
        nodeIds = pack.nodeIds,
        retained = decision._1,
        reason = decision._2
      )
    }

    val dataReuse = validated.packs.sortBy(_.id).map { originalPack =>
      eligibleOriginalToDenseId.get(originalPack.id) match {
        case None =>
          SlpPackDataReuseInfo(
            originalPackId = originalPack.id,
            densePackId = None,
            nodeIds = originalPack.nodeIds,
            moduleName = originalPack.module.map(_.moduleName)
              .orElse(originalPack.moduleNet.map(_.moduleName))
              .getOrElse(""),
            localNetName = originalPack.moduleNet.map(_.localNetName).getOrElse(""),
            opcode = originalPack.shape.opcode.name,
            discoveryPhase = originalPack.discoveryPhase.getOrElse(""),
            parallelDegree = originalPack.parallelDegree,
            resultWidth = originalPack.shape.resultWidth,
            packedPredecessorCount = 0,
            livePackedSuccessorCount = 0,
            directRegReadRoot = false,
            regUpdateProducer = false,
            scalarOutputLaneCount = 0,
            inputArgCount = originalPack.shape.operandWidths.size,
            packedInputArgCount = 0,
            scalarPackInputArgCount = 0,
            broadcastInputArgCount = 0,
            constantInputArgCount = originalPack.shape.operandKinds.count(_ == SlpConstantKind),
            unknownInputArgCount = originalPack.shape.operandKinds.count(_ == SlpSignalKind),
            filterCandidate = false,
            retained = false,
            reason = "below_min_parallel_degree"
          )
        case Some(denseId) =>
          val retained = livePackIds(denseId)
          val reason =
            if (retained) retainedReason(
              eligibleGraph,
              denseId,
              livePackIds,
              directRegReadRootPackIds,
              regUpdateProducerPackIds
            )
            else profitabilityRejectReasons.getOrElse(denseId, "isolated_pack")
          summarizeReuse(
            eligibleGraph,
            originalPack.id,
            eligibleGraph.pack(denseId),
            livePackIds,
            directRegReadRootPackIds,
            regUpdateProducerPackIds,
            retained,
            reason
          )
      }
    }

    val retainedPacks = eligiblePacks.filter(pack => livePackIds(pack.id))
      .zipWithIndex.map { case (pack, newId) => pack.copy(id = newId) }
    val retainedRootNodeIds = retainedPacks.iterator.flatMap(_.nodeIds).toSet
    val retainedRegions = eligibleResult.regions.filter(region => retainedRootNodeIds(region.rootNodeId))
    val result = eligibleResult.copy(packs = retainedPacks, regions = retainedRegions)

    val (plan, regFiltering) = buildPlan(result)
    SlpPackFilterResult(
      result = result,
      plan = plan,
      regFiltering = regFiltering,
      decisions = decisions,
      dataReuse = dataReuse,
      rawPackCount = validated.packs.size,
      rawPackedNodes = validated.packs.map(_.parallelDegree).sum
    )
  }
}
