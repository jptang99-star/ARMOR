package armor.slp

import java.io.{BufferedWriter, File, FileWriter}

object SlpAnalysisWriter {
  private final case class UnpackScalarIncoming(
    alignmentId:     Int,
    sourcePackId:    Int,
    sourceLaneIndex: Int,
    sourceNodeId:    Int,
    sourceNodeName:  String,
    outputName:      String,
    width:           Int,
    offset:          Int
  )

  private final case class UnpackScalarOutgoing(
    kind:             String,
    alignmentId:      String,
    destination:      String,
    argumentIndex:    String,
    destinationLane:  String,
    signalName:       String,
    width:            Int,
    offset:           String
  )

  private def withWriter(file: File)(body: BufferedWriter => Unit): Unit = {
    val writer = new BufferedWriter(new FileWriter(file))
    try body(writer)
    finally writer.close()
  }

  private def line(writer: BufferedWriter, value: String): Unit = {
    writer.write(value)
    writer.newLine()
  }

  private def csv(values: Seq[String]): String = values.map { value =>
    "\"" + value.replace("\"", "\"\"") + "\""
  }.mkString(",")

  private def writeUnpackScalarPackDump(
    context: SlpAnalysisContext,
    plan:    SlpPlan,
    file:    File
  ): Unit = {
    val incomingByScalar = scala.collection.mutable.HashMap.empty[Int, Vector[UnpackScalarIncoming]]
    plan.alignPlan.packToScalar.foreach { alignment =>
      val sourcePack = plan.packGraph.pack(alignment.sourcePackId)
      alignment.lanes.foreach { lane =>
        val sourceOffset = sourcePack.outputOffsets(lane.sourceLaneIndex)
        lane.consumers.collect { case SlpScalarConsumer(nodeId) => nodeId }.foreach { scalarNodeId =>
          val incoming = UnpackScalarIncoming(
            alignment.id,
            alignment.sourcePackId,
            lane.sourceLaneIndex,
            lane.sourceNodeId,
            context.graph.node(lane.sourceNodeId).name,
            lane.outputName,
            lane.width,
            sourceOffset
          )
          incomingByScalar.update(
            scalarNodeId,
            incomingByScalar.getOrElse(scalarNodeId, Vector.empty) :+ incoming
          )
        }
      }
    }

    val outgoingByScalar = scala.collection.mutable.HashMap.empty[Int, Vector[UnpackScalarOutgoing]]
    def addOutgoing(nodeId: Int, outgoing: UnpackScalarOutgoing): Unit =
      outgoingByScalar.update(nodeId, outgoingByScalar.getOrElse(nodeId, Vector.empty) :+ outgoing)

    plan.alignPlan.scalarToPack.foreach { alignment =>
      alignment.lanes.zip(alignment.laneOffsets).foreach {
        case (lane: SlpScalarInputLane, offset) =>
          lane.producerNodeId.foreach { nodeId =>
            addOutgoing(
              nodeId,
              UnpackScalarOutgoing(
                "scalar_to_pack",
                alignment.id.toString,
                s"pack:${alignment.destinationPackId}",
                alignment.argumentIndex.toString,
                lane.destinationLane.toString,
                lane.signalName,
                lane.width,
                offset.toString
              )
            )
          }
        case _ =>
      }
    }

    plan.alignPlan.regWriteInputs.zipWithIndex.foreach { case (input, index) =>
      input.lanes.zip(input.laneOffsets).foreach {
        case (lane: SlpScalarInputLane, offset) =>
          lane.producerNodeId.foreach { nodeId =>
            addOutgoing(
              nodeId,
              UnpackScalarOutgoing(
                "reg_write_input",
                s"reg_write:$index",
                s"reg:${input.regPackId}",
                "",
                lane.destinationLane.toString,
                lane.signalName,
                lane.width,
                offset.toString
              )
            )
          }
        case _ =>
      }
    }

    plan.alignPlan.broadcastInputs.zipWithIndex.foreach { case (input, index) =>
      input.value match {
        case signal: SlpBroadcastSignal =>
          signal.producerNodeId.foreach { nodeId =>
            addOutgoing(
              nodeId,
              UnpackScalarOutgoing(
                "broadcast_input",
                s"broadcast:$index",
                s"pack:${input.destinationPackId}",
                input.argumentIndex.toString,
                "all",
                signal.signalName,
                signal.width,
                "0"
              )
            )
          }
        case _ =>
      }
    }

    val bridgeNodeIds = incomingByScalar.keySet.intersect(outgoingByScalar.keySet).toVector.sorted

    withWriter(file) { writer =>
      line(writer, csv(Vector(
        "scalar_node_id",
        "scalar_name",
        "scalar_op_type",
        "incoming_count",
        "outgoing_count",
        "unpack_alignment_ids",
        "source_pack_ids",
        "source_lanes",
        "source_node_ids",
        "source_node_names",
        "source_widths",
        "source_offsets",
        "materialized_names",
        "outgoing_kinds",
        "outgoing_alignment_ids",
        "destinations",
        "destination_arguments",
        "destination_lanes",
        "outgoing_signal_names",
        "outgoing_widths",
        "outgoing_offsets",
        "scalar_statement"
      )))
      bridgeNodeIds.foreach { nodeId =>
        val node = context.graph.node(nodeId)
        val incoming = incomingByScalar(nodeId).sortBy(item =>
          (item.sourcePackId, item.sourceLaneIndex, item.alignmentId)
        )
        val outgoing = outgoingByScalar(nodeId).sortBy(item =>
          (item.kind, item.destination, item.argumentIndex, item.destinationLane, item.alignmentId)
        )
        line(writer, csv(Vector(
          nodeId.toString,
          node.name,
          SlpOperationStatistics.opType(node.statement),
          incoming.size.toString,
          outgoing.size.toString,
          incoming.map(_.alignmentId).distinct.mkString(";"),
          incoming.map(_.sourcePackId).mkString(";"),
          incoming.map(_.sourceLaneIndex).mkString(";"),
          incoming.map(_.sourceNodeId).mkString(";"),
          incoming.map(_.sourceNodeName).mkString(";"),
          incoming.map(_.width).mkString(";"),
          incoming.map(_.offset).mkString(";"),
          incoming.map(_.outputName).mkString(";"),
          outgoing.map(_.kind).mkString(";"),
          outgoing.map(_.alignmentId).mkString(";"),
          outgoing.map(_.destination).mkString(";"),
          outgoing.map(_.argumentIndex).mkString(";"),
          outgoing.map(_.destinationLane).mkString(";"),
          outgoing.map(_.signalName).mkString(";"),
          outgoing.map(_.width).mkString(";"),
          outgoing.map(_.offset).mkString(";"),
          node.statement.serialize
        )))
      }
    }
  }

  def write(
    context: SlpAnalysisContext,
    result: SlpPackingResult,
    outputDirectory: File,
    circuitName: String,
    mode: String = "analysis",
    regPacking: Option[SlpRegPackingResult] = None,
    packedNodeIds: Set[Int] = Set.empty
  ): Unit = {
    if (!outputDirectory.exists() && !outputDirectory.mkdirs()) {
      throw new java.io.IOException(s"Unable to create SLP output directory: $outputDirectory")
    }

    val stats = result.stats
    withWriter(new File(outputDirectory, "slp-analysis.txt")) { writer =>
      val commonValues = Vector(
        "mode" -> mode,
        "packer" -> result.packerName,
        "circuit" -> circuitName,
        "machine_width" -> context.config.machineWidth.toString,
        "min_parallel_degree" -> context.config.minParallelDegree.toString,
        "allow_cross_module" -> context.config.allowCrossModule.toString,
        "graph_nodes" -> stats.graphNodes.toString,
        "valid_nodes" -> stats.validNodes.toString,
        "supported_nodes" -> stats.supportedNodes.toString,
        "candidate_nodes" -> stats.candidateNodes.toString,
        "seed_candidates" -> stats.seedCandidates.toString,
        "accepted_packs" -> stats.acceptedPacks.toString,
        "pipeline_packs" -> stats.pipelinePacks.toString,
        "packed_nodes" -> stats.packedNodes.toString,
        "use_def_candidates" -> stats.useDefCandidates.toString,
        "def_use_candidates" -> stats.defUseCandidates.toString,
        "rejected_singleton" -> stats.rejectedSingleton.toString,
        "rejected_duplicate" -> stats.rejectedDuplicate.toString,
        "rejected_unsupported" -> stats.rejectedUnsupported.toString,
        "rejected_shape" -> stats.rejectedShape.toString,
        "rejected_level" -> stats.rejectedLevel.toString,
        "rejected_module" -> stats.rejectedModule.toString,
        "rejected_width" -> stats.rejectedWidth.toString,
        "rejected_dependency" -> stats.rejectedDependency.toString,
        "rejected_already_packed" -> stats.rejectedAlreadyPacked.toString,
        "result_utilization" -> f"${stats.resultUtilization}%.6f",
        "storage_utilization" -> f"${stats.storageUtilization}%.6f",
        "opcode_histogram" -> stats.opcodeHistogram.map { case (key, count) => s"$key:$count" }.mkString(";"),
        "parallel_degree_histogram" -> stats.parallelDegreeHistogram.map {
          case (key, count) => s"$key:$count"
        }.mkString(";")
      )
      val diagnosticValues = result.diagnostics match {
        case ICTDiagnostics(
              phase1Packs,
              phase2Packs,
              boundaryPacks,
              indexedBoundaryCandidates,
              indexedBoundaryPacks,
              indexedBoundaryNodes,
              useDefCandidates,
              defUseCandidates,
              exactConcatMerges,
              dataflowReuseRejects,
              stoppedNarrowPackExpansions,
              stateTransitionCandidates,
              stateTransitionPacks,
              priorSeedCandidates,
              priorSeedPacks,
              priorSeedNodes,
              localInstanceEquivCandidates,
              localInstanceEquivPacks,
              localInstanceEquivNodes) => Vector(
          "ict_phase1_packs" -> phase1Packs.toString,
          "ict_phase2_packs" -> phase2Packs.toString,
          "ict_boundary_packs" -> boundaryPacks.toString,
          "ict_indexed_boundary_candidates" -> indexedBoundaryCandidates.toString,
          "ict_indexed_boundary_packs" -> indexedBoundaryPacks.toString,
          "ict_indexed_boundary_nodes" -> indexedBoundaryNodes.toString,
          "ict_use_def_candidates" -> useDefCandidates.toString,
          "ict_def_use_candidates" -> defUseCandidates.toString,
          "ict_exact_concat_merges" -> exactConcatMerges.toString,
          "ict_dataflow_reuse_rejects" -> dataflowReuseRejects.toString,
          "ict_stopped_narrow_pack_expansions" -> stoppedNarrowPackExpansions.toString,
          "ict_state_transition_candidates" -> stateTransitionCandidates.toString,
          "ict_state_transition_packs" -> stateTransitionPacks.toString,
          "ict_prior_seed_candidates" -> priorSeedCandidates.toString,
          "ict_prior_seed_packs" -> priorSeedPacks.toString,
          "ict_prior_seed_nodes" -> priorSeedNodes.toString,
          "ict_local_instance_equiv_candidates" -> localInstanceEquivCandidates.toString,
          "ict_local_instance_equiv_packs" -> localInstanceEquivPacks.toString,
          "ict_local_instance_equiv_nodes" -> localInstanceEquivNodes.toString
        )
      }
      val registerValues = regPacking.toVector.flatMap { registerResult =>
        val registerStats = registerResult.stats
        Vector(
          "reg_update_candidates" -> registerStats.candidates.toString,
          "reg_update_seed_groups" -> registerStats.seedGroups.toString,
          "reg_update_packs" -> registerStats.acceptedPacks.toString,
          "packed_registers" -> registerStats.packedRegisters.toString,
          "direct_packed_reg_reads" -> registerStats.directStateReads.toString,
          "direct_packed_reg_writes" -> registerStats.directStateWrites.toString,
          "reg_update_rejected_singleton" -> registerStats.rejectedSingleton.toString,
          "reg_update_rejected_width" -> registerStats.rejectedWidth.toString,
          "reg_update_rejected_dependency" -> registerStats.rejectedDependency.toString
        )
      }
      val temporalValues = result.temporalStateStats.toVector.flatMap { temporal =>
        Vector(
          "temporal_state_seed_groups" -> temporal.seedGroups.toString,
          "temporal_state_accepted_packs" -> temporal.acceptedPacks.toString,
          "temporal_state_accepted_nodes" -> temporal.acceptedNodes.toString,
          "temporal_state_rejected_narrow" -> temporal.rejectedNarrow.toString,
          "temporal_state_rejected_timing" -> temporal.rejectedTiming.toString,
          "temporal_state_rejected_overlap" -> temporal.rejectedOverlap.toString
        )
      }
      val values = commonValues ++ diagnosticValues ++ registerValues ++ temporalValues
      values.foreach { case (key, value) => line(writer, s"$key=$value") }
    }

    val actualPackedNodeIds =
      if (packedNodeIds.nonEmpty) packedNodeIds
      else result.packs.iterator.flatMap(_.nodeIds).toSet ++ regPacking.iterator.flatMap(_.packs).flatMap(_.nodeIds)
    withWriter(new File(outputDirectory, "slp-op-stats.txt")) { writer =>
      writer.write(SlpOperationStatistics.format(SlpOperationStatistics.rows(context, actualPackedNodeIds)))
    }

    withWriter(new File(outputDirectory, "slp-packs.csv")) { writer =>
      line(writer, csv(Vector(
        "pack_id",
        "opcode",
        "level",
        "instance",
        "module",
        "module_net",
        "lane_instances",
        "node_ids",
        "node_names",
        "result_widths",
        "storage_widths",
        "output_offsets"
      )))
      result.packs.sortBy(_.id).foreach { pack =>
        val location = pack.module.getOrElse(SlpModuleLocation("<cross-module>", "<cross-module>"))
        val nodeNames = pack.nodeIds.map(context.graph.node(_).name)
        val moduleNet = pack.moduleNet
          .map(net => s"${net.moduleName}:${net.localNetName}")
          .getOrElse("")
        val laneInstances = pack.laneLocations.map(
          _.map(_.instancePath).getOrElse("<unknown>")
        )
        line(writer, csv(Vector(
          pack.id.toString,
          pack.shape.opcode.name,
          pack.level.toString,
          location.instancePath,
          location.moduleName,
          moduleNet,
          laneInstances.mkString(";"),
          pack.nodeIds.mkString(";"),
          nodeNames.mkString(";"),
          pack.lanes.map(_.resultWidth).mkString(";"),
          pack.lanes.map(_.storageWidth).mkString(";"),
          pack.outputOffsets.mkString(";")
        )))
      }
    }

    regPacking.foreach { registerResult =>
      withWriter(new File(outputDirectory, "slp-reg-packs.csv")) { writer =>
        line(writer, csv(Vector(
          "reg_pack_id",
          "module",
          "local_register",
          "level",
          "total_width",
          "valid_mask",
          "update_node_ids",
          "register_names",
          "lane_instances",
          "lane_widths",
          "lane_offsets"
        )))
        registerResult.packs.foreach { pack =>
          line(writer, csv(Vector(
            pack.id.toString,
            pack.moduleNet.moduleName,
            pack.moduleNet.localNetName,
            pack.level.toString,
            pack.totalWidth.toString,
            s"0x${pack.validMask.toString(16)}",
            pack.nodeIds.mkString(";"),
            pack.registerNames.mkString(";"),
            pack.lanes.map(_.location.instancePath).mkString(";"),
            pack.laneWidths.mkString(";"),
            pack.laneOffsets.mkString(";")
          )))
        }
      }

      withWriter(new File(outputDirectory, "slp-reg-reuse.csv")) { writer =>
        line(writer, csv(Vector(
          "kind",
          "reg_pack_id",
          "source_pack_id",
          "destination_pack_id",
          "argument_index"
        )))
        registerResult.stateReads.foreach { read =>
          line(writer, csv(Vector(
            "state_read",
            read.regPackId.toString,
            "",
            read.destinationPackId.toString,
            read.argumentIndex.toString
          )))
        }
        registerResult.directWrites.foreach { write =>
          line(writer, csv(Vector(
            "direct_write",
            write.regPackId.toString,
            write.sourcePackId.toString,
            "",
            ""
          )))
        }
      }
    }
  }

  def writePlan(
    context: SlpAnalysisContext,
    plan: SlpPlan,
    outputDirectory: File,
    circuitName: String,
    mode: String = "analysis"
  ): Unit = {
    if (!outputDirectory.exists() && !outputDirectory.mkdirs()) {
      throw new java.io.IOException(s"Unable to create SLP output directory: $outputDirectory")
    }

    val stats = plan.stats
    withWriter(new File(outputDirectory, "slp-plan.txt")) { writer =>
      val values = Vector(
        "mode" -> mode,
        "phase" -> "pack_graph_align_plan",
        "circuit" -> circuitName,
        "packs" -> plan.packGraph.packs.size.toString,
        "pack_dependencies" -> stats.packDependencies.toString,
        "direct_pack_inputs" -> stats.directPackInputs.toString,
        "direct_reg_inputs" -> stats.directRegInputs.toString,
        "broadcast_inputs" -> stats.broadcastInputs.toString,
        "pack_segment_alignments" -> stats.packSegmentAlignments.toString,
        "scalar_to_pack_alignments" -> stats.scalarToPackAlignments.toString,
        "pack_to_scalar_alignments" -> stats.packToScalarAlignments.toString,
        "materialized_lanes" -> stats.materializedLanes.toString,
        "scalar_fallback_nodes" -> stats.scalarFallbackNodes.toString,
        "reg_update_packs" -> stats.regUpdatePacks.toString,
        "scalar_reg_views" -> stats.scalarRegViews.toString,
        "schedule_nodes" -> stats.scheduleNodes.toString,
        "schedule_edges" -> stats.scheduleEdges.toString
      )
      values.foreach { case (key, value) => line(writer, s"$key=$value") }
      plan.packGraph.dependencies.foreach { dependency =>
        val provenance = dependency.nodeDependencies
          .map(edge => s"${edge.sourceNodeId}:${edge.destinationNodeId}").mkString(";")
        line(
          writer,
          s"pack_dependency.${dependency.sourcePackId}.${dependency.destinationPackId}=$provenance"
        )
      }
      plan.topologicalSchedule.zipWithIndex.foreach { case (node, index) =>
        line(writer, f"schedule.$index%08d=${node.label}")
      }
    }

    withWriter(new File(outputDirectory, "slp-scalar-boundary-stats.txt")) { writer =>
      writer.write(SlpScalarBoundaryStatistics.format(SlpScalarBoundaryStatistics.rows(context, plan)))
    }

    writeUnpackScalarPackDump(
      context,
      plan,
      new File(outputDirectory, "slp-unpack-scalar-pack.csv")
    )

    withWriter(new File(outputDirectory, "slp-alignments.csv")) { writer =>
      line(writer, csv(Vector(
        "record_id",
        "kind",
        "source_pack",
        "destination_pack",
        "argument_index",
        "lane_indices",
        "node_ids",
        "widths",
        "offsets",
        "sources",
        "consumers",
        "observable"
      )))

      plan.alignPlan.directPackInputs.zipWithIndex.foreach { case (input, index) =>
        line(writer, csv(Vector(
          s"direct:$index",
          "direct_pack",
          input.sourcePackId.toString,
          input.destinationPackId.toString,
          input.argumentIndex.toString,
          input.sourceNodeIds.indices.mkString(";"),
          input.sourceNodeIds.mkString(";"),
          input.laneWidths.mkString(";"),
          input.laneOffsets.mkString(";"),
          input.sourceNodeIds.map(nodeId => s"pack:${input.sourcePackId}:node:$nodeId").mkString(";"),
          s"pack:${input.destinationPackId}:arg:${input.argumentIndex}",
          "false"
        )))
      }

      plan.alignPlan.directRegInputs.zipWithIndex.foreach { case (input, index) =>
        line(writer, csv(Vector(
          s"direct_reg:$index",
          "direct_reg",
          s"reg:${input.regPackId}",
          input.destinationPackId.toString,
          input.argumentIndex.toString,
          input.laneWidths.indices.mkString(";"),
          "",
          input.laneWidths.mkString(";"),
          input.laneOffsets.mkString(";"),
          s"reg:${input.regPackId}",
          s"pack:${input.destinationPackId}:arg:${input.argumentIndex}",
          "false"
        )))
      }

      plan.alignPlan.broadcastInputs.zipWithIndex.foreach { case (input, index) =>
        val (source, nodeId, width) = input.value match {
          case signal: SlpBroadcastSignal => (
            s"scalar:${signal.producerNodeId.map(_.toString).getOrElse("external")}:${signal.signalName}",
            signal.producerNodeId.map(_.toString).getOrElse(""),
            signal.width.toString
          )
          case constant: SlpBroadcastConstant =>
            (s"constant:${constant.value}", "", constant.width.toString)
          case packed: SlpBroadcastPacked => (
            s"pack:${packed.sourcePackId}:lane:${packed.sourceLaneIndex}",
            packed.sourceNodeId.toString,
            packed.width.toString
          )
          case packed: SlpBroadcastReg => (
            s"reg:${packed.regPackId}:lane:${packed.sourceLaneIndex}",
            "",
            packed.width.toString
          )
        }
        line(writer, csv(Vector(
          s"broadcast:$index",
          "broadcast",
          "",
          input.destinationPackId.toString,
          input.argumentIndex.toString,
          "all",
          nodeId,
          width,
          "0",
          source,
          s"pack:${input.destinationPackId}:arg:${input.argumentIndex}",
          "false"
        )))
      }

      plan.alignPlan.packedOutputs.foreach { output =>
        val materializedLane = output.materializationAlignmentId.flatMap { alignmentId =>
          plan.alignPlan.packToScalar.find(_.id == alignmentId)
            .flatMap(_.lanes.find(_.sourceLaneIndex == output.sourceLaneIndex))
        }
        line(writer, csv(Vector(
          s"output:${output.sourcePackId}:${output.sourceLaneIndex}",
          "packed_output",
          output.sourcePackId.toString,
          "",
          "",
          output.sourceLaneIndex.toString,
          output.sourceNodeId.toString,
          output.width.toString,
          output.offset.toString,
          output.outputName,
          materializedLane.map(_.consumers.map(_.description).mkString("|")).getOrElse(""),
          materializedLane.exists(_.observable).toString
        )))
      }

      plan.alignPlan.packToScalar.foreach { alignment =>
        line(writer, csv(Vector(
          alignment.id.toString,
          alignment.kind,
          alignment.sourcePackId.toString,
          "",
          "",
          alignment.lanes.map(_.sourceLaneIndex).mkString(";"),
          alignment.lanes.map(_.sourceNodeId).mkString(";"),
          alignment.lanes.map(_.width).mkString(";"),
          plan.packGraph.pack(alignment.sourcePackId).outputOffsets
            .zipWithIndex.collect {
              case (offset, index) if alignment.lanes.exists(_.sourceLaneIndex == index) => offset
            }.mkString(";"),
          alignment.lanes.map(_.outputName).mkString(";"),
          alignment.lanes.map(lane => lane.consumers.map(_.description).mkString("|")).mkString(";"),
          alignment.lanes.map(_.observable).mkString(";")
        )))
      }

      plan.alignPlan.packSegments.foreach { alignment =>
        val source = alignment.source match {
          case SlpCombSegmentSource(sourcePackId) => s"pack:$sourcePackId"
          case SlpRegSegmentSource(regPackId)     => s"reg:$regPackId"
        }
        line(writer, csv(Vector(
          alignment.id.toString,
          alignment.kind,
          source,
          "",
          "",
          s"${alignment.sourceLaneBegin}:${alignment.sourceLaneEnd}",
          "",
          alignment.width.toString,
          alignment.sourceBitOffset.toString,
          source,
          "shared",
          "false"
        )))
      }

      plan.alignPlan.scalarToPack.foreach { alignment =>
        val sources = alignment.lanes.map {
          case lane: SlpScalarInputLane =>
            s"scalar:${lane.producerNodeId.map(_.toString).getOrElse("external")}:${lane.signalName}"
          case lane: SlpConstantInputLane => s"constant:${lane.value}"
          case lane: SlpUnpackedInputLane =>
            s"${lane.segmentAlignmentId.map(id => s"align:$id").getOrElse(s"pack:${lane.sourcePackId}")}:lane:${lane.sourceLaneIndex}"
          case lane: SlpRegInputLane =>
            s"${lane.segmentAlignmentId.map(id => s"align:$id").getOrElse(s"reg:${lane.regPackId}")}:lane:${lane.sourceLaneIndex}"
        }
        val nodeIds = alignment.lanes.map {
          case lane: SlpScalarInputLane   => lane.producerNodeId.map(_.toString).getOrElse("")
          case _: SlpConstantInputLane    => ""
          case lane: SlpUnpackedInputLane => lane.sourceNodeId.toString
          case _: SlpRegInputLane          => ""
        }
        line(writer, csv(Vector(
          alignment.id.toString,
          alignment.kind,
          "",
          alignment.destinationPackId.toString,
          alignment.argumentIndex.toString,
          alignment.lanes.map(_.destinationLane).mkString(";"),
          nodeIds.mkString(";"),
          alignment.lanes.map(_.width).mkString(";"),
          alignment.laneOffsets.mkString(";"),
          sources.mkString(";"),
          s"pack:${alignment.destinationPackId}:arg:${alignment.argumentIndex}",
          "false"
        )))
      }
    }

    withWriter(new File(outputDirectory, "slp-projections.csv")) { writer =>
      line(writer, csv(Vector(
        "destination_pack",
        "argument_index",
        "source",
        "source_width",
        "destination_width",
        "source_mask",
        "destination_mask",
        "transfers",
        "lowering"
      )))
      plan.projectionPlan.projections.foreach { projection =>
        val source = projection.source match {
          case SlpProjectionCombPack(packId)       => s"pack:$packId"
          case SlpProjectionRegPack(regPackId)     => s"reg:$regPackId"
          case SlpProjectionAlignment(alignmentId) => s"align:$alignmentId"
          case SlpProjectionConstant(value)        => s"constant:0x${value.toString(16)}"
        }
        val transfers = projection.transfers.map { transfer =>
          s"${transfer.sourceOffset}:${transfer.destinationOffset}:${transfer.width}"
        }.mkString(";")
        line(writer, csv(Vector(
          projection.destinationPackId.toString,
          projection.argumentIndex.toString,
          source,
          projection.sourceWidth.toString,
          projection.destinationWidth.toString,
          s"0x${projection.sourceMask.toString(16)}",
          s"0x${projection.destinationMask.toString(16)}",
          transfers,
          projection.loweringKind
        )))
      }
    }

    withWriter(new File(outputDirectory, "slp-alignment-projections.csv")) { writer =>
      line(writer, csv(Vector(
        "alignment_id",
        "source",
        "source_width",
        "destination_width",
        "source_mask",
        "destination_mask",
        "covered_lanes",
        "segment_alignments",
        "transfers",
        "lowering"
      )))

      def projectionSourceName(source: SlpProjectionSource): String = source match {
        case SlpProjectionCombPack(packId)       => s"pack:$packId"
        case SlpProjectionRegPack(regPackId)     => s"reg:$regPackId"
        case SlpProjectionAlignment(alignmentId) => s"align:$alignmentId"
        case SlpProjectionConstant(value)        => s"constant:0x${value.toString(16)}"
      }

      plan.alignPlan.alignmentProjections.projections.foreach { projection =>
        projection.terms.foreach { term =>
          val transfers = term.transfers.map { transfer =>
            s"${transfer.sourceOffset}:${transfer.destinationOffset}:${transfer.width}"
          }.mkString(";")
          line(writer, csv(Vector(
            projection.alignmentId.toString,
            projectionSourceName(term.source),
            term.sourceWidth.toString,
            term.destinationWidth.toString,
            s"0x${term.sourceMask.toString(16)}",
            s"0x${term.destinationMask.toString(16)}",
            term.coveredDestinationLanes.mkString(";"),
            term.segmentAlignmentIds.toVector.sorted.mkString(";"),
            transfers,
            term.loweringKind
          )))
        }
      }
    }
  }

  def writeLowering(
    stats: SlpEmissionStats,
    rejections: Vector[SlpLoweringRejection],
    outputDirectory: File,
    circuitName: String
  ): Unit = {
    if (!outputDirectory.exists() && !outputDirectory.mkdirs()) {
      throw new java.io.IOException(s"Unable to create SLP output directory: $outputDirectory")
    }
    withWriter(new File(outputDirectory, "slp-lowering.txt")) { writer =>
      val values = Vector(
        "mode" -> "lowering",
        "circuit" -> circuitName,
        "scalar_nodes" -> stats.scalarNodes.toString,
        "pack_nodes" -> stats.packNodes.toString,
        "fast_bitwise_packs" -> stats.fastBitwisePacks.toString,
        "lane_wise_packs" -> stats.laneWisePacks.toString,
        "scalar_to_pack_nodes" -> stats.scalarToPackNodes.toString,
        "pack_to_scalar_nodes" -> stats.packToScalarNodes.toString,
        "pack_segment_nodes" -> stats.packSegmentNodes.toString,
        "reg_update_packs" -> stats.regUpdatePacks.toString,
        "scalar_reg_views" -> stats.scalarRegViews.toString,
        "broadcast_mux_packs" -> stats.broadcastMuxPacks.toString,
        "one_bit_mux_packs" -> stats.oneBitMuxPacks.toString,
        "lane_mask_mux_packs" -> stats.laneMaskMuxPacks.toString,
        "elided_mux_result_masks" -> stats.elidedMuxResultMasks.toString,
        "fallback_packs" -> rejections.size.toString
      )
      values.foreach { case (key, value) => line(writer, s"$key=$value") }
      rejections.foreach { rejection =>
        line(writer, s"fallback.${rejection.originalPackId}=${rejection.reason}")
      }
    }

  }
}
