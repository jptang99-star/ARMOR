package armor.slp

import java.io.{BufferedWriter, File, FileWriter}

object SlpPackFilterWriter {
  private def withWriter(file: File)(body: BufferedWriter => Unit): Unit = {
    val writer = new BufferedWriter(new FileWriter(file))
    try body(writer) finally writer.close()
  }

  private def line(writer: BufferedWriter, value: String): Unit = {
    writer.write(value)
    writer.newLine()
  }

  private def csv(value: String): String =
    if (value.exists(ch => ch == ',' || ch == '"' || ch == '\n' || ch == '\r')) {
      "\"" + value.replace("\"", "\"\"") + "\""
    } else value

  def write(
    result:          SlpPackFilterResult,
    outputDirectory: File,
    circuitName:     String,
    config:          SlpConfig
  ): Unit = {
    val minParallelDegree = config.minParallelDegree
    if (!outputDirectory.exists() && !outputDirectory.mkdirs()) {
      throw new java.io.IOException(s"Unable to create SLP output directory: $outputDirectory")
    }
    val retainedNodes = result.result.packs.map(_.parallelDegree).sum
    val regPacking = result.plan.regPacking
    withWriter(new File(outputDirectory, "slp-pack-filter.txt")) { writer =>
      Vector(
        "mode" -> s"min_parallel_degree_${minParallelDegree}_connected_profitability_filter",
        "min_parallel_degree" -> minParallelDegree.toString,
        "circuit" -> circuitName,
        "raw_packs" -> result.rawPackCount.toString,
        "retained_packs" -> result.result.packs.size.toString,
        "rejected_packs" -> (result.rawPackCount - result.result.packs.size).toString,
        "raw_packed_nodes" -> result.rawPackedNodes.toString,
        "retained_packed_nodes" -> retainedNodes.toString,
        "raw_reg_packs" -> result.regFiltering.rawPackCount.toString,
        "retained_reg_packs" -> regPacking.map(_.packs.size).getOrElse(0).toString,
        "rejected_reg_packs" -> (result.regFiltering.rawPackCount - regPacking.map(_.packs.size).getOrElse(0)).toString,
        "raw_packed_registers" -> result.regFiltering.rawRegisters.toString,
        "retained_packed_registers" -> regPacking.map(_.packs.map(_.lanes.size).sum).getOrElse(0).toString
      ).foreach { case (key, value) => line(writer, s"$key=$value") }
    }

    withWriter(new File(outputDirectory, "slp-pack-filter.csv")) { writer =>
      line(writer, "original_pack_id,node_ids,packed_nodes,decision,reason")
      result.decisions.foreach { decision =>
        line(writer, Vector(
          decision.originalPackId.toString,
          decision.nodeIds.mkString(";"),
          decision.nodeIds.size.toString,
          if (decision.retained) "retain" else "reject",
          decision.reason
        ).mkString(","))
      }
    }

    withWriter(new File(outputDirectory, "slp-pack-data-reuse.csv")) { writer =>
      line(writer, Vector(
        "original_pack_id",
        "dense_pack_id",
        "decision",
        "reason",
        "module_name",
        "local_net_name",
        "opcode",
        "discovery_phase",
        "parallel_degree",
        "result_width",
        "node_ids",
        "packed_predecessors",
        "live_packed_successors",
        "direct_reg_read_root",
        "reg_update_producer",
        "scalar_output_lanes",
        "input_args",
        "packed_input_args",
        "scalar_pack_input_args",
        "broadcast_input_args",
        "constant_input_args",
        "unknown_input_args",
        "filter_candidate"
      ).mkString(","))
      result.dataReuse.foreach { info =>
        line(writer, Vector(
          info.originalPackId.toString,
          info.densePackId.map(_.toString).getOrElse(""),
          if (info.retained) "retain" else "reject",
          info.reason,
          info.moduleName,
          info.localNetName,
          info.opcode,
          info.discoveryPhase,
          info.parallelDegree.toString,
          info.resultWidth.toString,
          info.nodeIds.mkString(";"),
          info.packedPredecessorCount.toString,
          info.livePackedSuccessorCount.toString,
          info.directRegReadRoot.toString,
          info.regUpdateProducer.toString,
          info.scalarOutputLaneCount.toString,
          info.inputArgCount.toString,
          info.packedInputArgCount.toString,
          info.scalarPackInputArgCount.toString,
          info.broadcastInputArgCount.toString,
          info.constantInputArgCount.toString,
          info.unknownInputArgCount.toString,
          info.filterCandidate.toString
        ).map(csv).mkString(","))
      }
    }

    withWriter(new File(outputDirectory, "slp-reg-pack-filter.csv")) { writer =>
      line(writer, "original_reg_pack_id,update_node_ids,packed_registers,decision,reason")
      result.regFiltering.decisions.foreach { decision =>
        line(writer, Vector(
          decision.originalRegPackId.toString,
          decision.updateNodeIds.mkString(";"),
          decision.updateNodeIds.size.toString,
          if (decision.retained) "retain" else "reject",
          decision.reason
        ).mkString(","))
      }
    }
  }
}
