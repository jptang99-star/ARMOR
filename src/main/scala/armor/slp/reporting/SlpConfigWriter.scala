package armor.slp

import java.io.{BufferedWriter, File, FileWriter}

/** Writes the fully resolved SLP configuration for one compiler invocation.
  *
  * Analysis and lowering reports describe what discovery produced.  This
  * companion report records the inputs that selected that behavior, so an
  * output directory remains reproducible without relying on JVM properties
  * or the source defaults used at a later date.
  */
object SlpConfigWriter {
  private def withWriter(file: File)(body: BufferedWriter => Unit): Unit = {
    val writer = new BufferedWriter(new FileWriter(file))
    try body(writer)
    finally writer.close()
  }

  private def line(writer: BufferedWriter, key: String, value: Any): Unit = {
    writer.write(s"$key=$value")
    writer.newLine()
  }

  def write(
    outputDirectory:              File,
    circuitName:                  String,
    mode:                         String,
    config:                       SlpConfig,
    packerConfiguration:          SlpPackerConfiguration,
    phase3Enabled:                Boolean,
    temporalStateExpansionEnabled: Boolean
  ): Unit = {
    if (!outputDirectory.exists() && !outputDirectory.mkdirs()) {
      throw new java.io.IOException(
        s"Unable to create SLP configuration output directory: ${outputDirectory.getPath}"
      )
    }

    val packedAddMode = Option(System.getProperty("armor.slp.packedAddMode"))
      .getOrElse("pdep")
      .toLowerCase
    val common = Vector[(String, Any)](
      "schema_version" -> 1,
      "circuit" -> circuitName,
      "slp_mode" -> mode,
      "slp_packer" -> packerConfiguration.kind.name,
      "slp_enabled" -> config.enabled,
      "machine_width" -> config.machineWidth,
      "min_parallel_degree" -> config.minParallelDegree,
      "allow_cross_module" -> config.allowCrossModule,
      "verify" -> config.verify,
      "phase2_enabled" -> config.enablePhase2,
      "phase3_enabled" -> phase3Enabled,
      "temporal_state_expansion_enabled" -> temporalStateExpansionEnabled,
      "packed_add_mode" -> packedAddMode,
      "legacy_schedule" -> java.lang.Boolean.getBoolean("armor.slp.legacySchedule"),
      "lazy_reg_views" -> java.lang.Boolean.getBoolean("armor.slp.lazyRegViews"),
      "internal_reg_view_names" ->
        java.lang.Boolean.getBoolean("armor.slp.internalRegViewNames")
    )
    val ict = packerConfiguration.ict.toVector.flatMap { value =>
      Vector[(String, Any)](
        "ict_allow_cross_module_pipeline" -> value.allowCrossModulePipeline,
        "ict_allow_def_use_pack_size_mismatch" -> value.allowDefUsePackSizeMismatch,
        "ict_allow_multi_successor_expansion" -> value.allowMultiSuccessorExpansion,
        "ict_exact_concat_merge_enabled" -> value.enableExactConcatMerge,
        "ict_indexed_boundary_expansion_enabled" -> value.enableIndexedBoundaryExpansion,
        "ict_gemmini_reservation_station_prior_enabled" ->
          value.enableGemminiReservationStationPrior,
        "ict_reg_update_read_seed_discovery_enabled" ->
          value.enableRegUpdateReadSeedDiscovery,
        "ict_local_instance_equivalence_enabled" -> value.enableLocalInstanceEquivalence
      )
    }

    withWriter(new File(outputDirectory, "slp-config.txt")) { writer =>
      (common ++ ict).foreach { case (key, value) => line(writer, key, value) }
    }
  }
}
