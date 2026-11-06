package armor.slp

sealed trait SlpPackerKind { def name: String }
case object ICTPackerKind extends SlpPackerKind { val name = "ict" }

object SlpPackerKind {
  def parse(value: String): Option[SlpPackerKind] = value.toLowerCase match {
    case "ict"                    => Some(ICTPackerKind)
    case _                        => None
  }
}

sealed trait SlpPackerDiagnostics
final case class ICTDiagnostics(
  phase1Packs: Int,
  phase2Packs: Int,
  boundaryPacks: Int,
  indexedBoundaryCandidates: Int,
  indexedBoundaryPacks: Int,
  indexedBoundaryNodes: Int,
  useDefCandidates: Int,
  defUseCandidates: Int,
  exactConcatMerges: Int,
  dataflowReuseRejects: Int,
  stoppedNarrowPackExpansions: Int,
  stateTransitionCandidates: Int,
  stateTransitionPacks: Int,
  priorSeedCandidates: Int,
  priorSeedPacks: Int,
  priorSeedNodes: Int,
  localInstanceEquivCandidates: Int,
  localInstanceEquivPacks: Int,
  localInstanceEquivNodes: Int
) extends SlpPackerDiagnostics

trait SlpPacker {
  def name: String
  def run(): SlpPackingResult
}

/** Fully resolved packer configuration for one SLP invocation.
  *
  * Keeping this value explicit makes the discovery behavior observable in
  * `slp-config.txt` and prevents command-line options from being hidden
  * behind factory-local system-property lookups.
  */
final case class SlpPackerConfiguration(
  kind: SlpPackerKind,
  ict:  Option[ICTPackerConfig]
) {
  require(
    (kind == ICTPackerKind) == ict.nonEmpty,
    "ICT configuration must be present exactly for the ICT packer"
  )
}

object SlpPackerFactory {
  def resolveConfiguration(
    kind:   SlpPackerKind,
    config: SlpConfig
  ): SlpPackerConfiguration = kind match {
    case ICTPackerKind =>
      SlpPackerConfiguration(
        ICTPackerKind,
        Some(ICTPackerConfig(
          enablePhase2 = config.enablePhase2,
          enableIndexedBoundaryExpansion =
            java.lang.Boolean.parseBoolean(
              System.getProperty("armor.slp.enableIndexedBoundaryExpansion", "false")
            ),
          enableGemminiReservationStationPrior =
            !java.lang.Boolean.parseBoolean(
              System.getProperty("armor.slp.disableGemminiReservationStationPrior", "false")
            ),
          enableRegUpdateReadSeedDiscovery =
            java.lang.Boolean.getBoolean("armor.slp.enableRegUpdateReadSeedDiscovery"),
          enableLocalInstanceEquivalence =
            java.lang.Boolean.parseBoolean(
              System.getProperty("armor.slp.enableLocalInstanceEquivalence", "false")
            )
        ))
      )
  }

  def create(
    configuration: SlpPackerConfiguration,
    context:       SlpAnalysisContext
  ): SlpPacker = configuration.kind match {
    case ICTPackerKind        => new ICTPacker(context, configuration.ict.get)
  }

  /** Compatibility entry point for callers that do not need the resolved
    * configuration snapshot. */
  def create(kind: SlpPackerKind, context: SlpAnalysisContext): SlpPacker =
    create(resolveConfiguration(kind, context.config), context)
}
