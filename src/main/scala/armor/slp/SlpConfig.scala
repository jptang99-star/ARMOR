package armor.slp

/** Configuration for the SLP backend.
  *
  * SLP remains disabled by default.  When enabled, this records the
  * discovery and lowering choices for one compiler invocation.
  */
final case class SlpConfig(
  enabled:          Boolean = false,
  machineWidth:     Int = 64,
  /** Smallest actual lane count a pack may have at any SLP stage.  This is a
    * threshold, not a requested layout size: a retained pack can have any
    * `parallelDegree >= minParallelDegree` that fits the machine word.
    */
  minParallelDegree: Int = 4,
  allowCrossModule: Boolean = false,
  /** Enable ICT boundary expansion after Phase 1 discovery. */
  enablePhase2: Boolean = true,
  verify:           Boolean = false
) {
  require(machineWidth > 0, "SLP machine width must be positive")
  require(machineWidth <= 64, "SLP machine width cannot exceed 64 bits")
  require(minParallelDegree >= 2, "SLP minimum parallel degree must be at least two")
}

object SlpConfig {
  val Disabled: SlpConfig = SlpConfig()
  val AnalysisOnly: SlpConfig = SlpConfig(enabled = true)
}
