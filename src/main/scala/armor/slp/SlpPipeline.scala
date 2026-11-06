package armor.slp

import essent.StatementGraph
import firrtl.ir.Circuit

/** Phase-1 analysis result.  It is deliberately disconnected from Compiler
  * and cannot mutate the graph or influence emission.
  */
final case class SlpAnalysisContext(
  config: SlpConfig,
  graph: SlpGraphView,
  classifications: Vector[(Int, SlpClassification)],
  stats: SlpClassificationStats
)

object SlpPipeline {
  def prepare(
    circuit: Circuit,
    graph: StatementGraph,
    config: SlpConfig = SlpConfig.AnalysisOnly
  ): Either[GraphCycle, SlpAnalysisContext] = {
    val view = SlpGraphView(graph, circuit)
    view.levels.map { _ =>
      val classifications = view.validNodeIds.map { nodeId =>
        nodeId -> SlpOpClassifier.classify(view.node(nodeId))
      }
      SlpAnalysisContext(
        config = config,
        graph = view,
        classifications = classifications,
        stats = SlpClassificationStats.from(classifications)
      )
    }
  }
}
