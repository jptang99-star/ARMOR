package armor.slp

final case class SlpClassificationStats(
  validNodes: Int,
  supportedNodes: Int,
  rejectedByReason: Map[String, Int]
) {
  require(validNodes >= 0)
  require(supportedNodes >= 0 && supportedNodes <= validNodes)

  def unsupportedNodes: Int = validNodes - supportedNodes
}

object SlpClassificationStats {
  def from(classifications: Vector[(Int, SlpClassification)]): SlpClassificationStats = {
    val supported = classifications.count(_._2.isInstanceOf[SlpSupported])
    val rejected = classifications.iterator.collect {
      case (_, SlpUnsupported(reason, _)) => reason.code
    }.toSeq.groupBy(identity).view.mapValues(_.size).toMap

    SlpClassificationStats(classifications.size, supported, rejected)
  }
}

final case class SlpPackStats(
  graphNodes: Int,
  validNodes: Int,
  supportedNodes: Int,
  candidateNodes: Int,
  seedCandidates: Int,
  acceptedPacks: Int,
  pipelinePacks: Int,
  packedNodes: Int,
  useDefCandidates: Int,
  defUseCandidates: Int,
  rejectedSingleton: Int,
  rejectedDuplicate: Int,
  rejectedUnsupported: Int,
  rejectedShape: Int,
  rejectedLevel: Int,
  rejectedModule: Int,
  rejectedWidth: Int,
  rejectedDependency: Int,
  rejectedAlreadyPacked: Int,
  opcodeHistogram: Vector[(String, Int)],
  parallelDegreeHistogram: Vector[(Int, Int)],
  resultUtilization: Double,
  storageUtilization: Double
) {
  require(graphNodes >= validNodes)
  require(validNodes >= supportedNodes)
  require(supportedNodes >= candidateNodes)
  require(acceptedPacks >= pipelinePacks)
  require(packedNodes >= acceptedPacks * 2 || acceptedPacks == 0)
  require(resultUtilization >= 0.0 && resultUtilization <= 1.0)
  require(storageUtilization >= 0.0 && storageUtilization <= 1.0)
}
