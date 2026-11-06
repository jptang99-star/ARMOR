package armor.slp

import essent.Graph

import scala.collection.mutable

final case class GraphCycle(remainingNodeIds: Vector[Int]) {
  require(remainingNodeIds.nonEmpty, "cycle report must contain at least one node")
}

final case class GraphLevels(
  nodesByLevel: Vector[Vector[Int]],
  levelByNode:  Vector[Int]
) {
  def levelOf(nodeId: Int): Option[Int] =
    if (nodeId >= 0 && nodeId < levelByNode.size && levelByNode(nodeId) >= 0)
      Some(levelByNode(nodeId))
    else None
}

object GraphLevels {
  /** Deterministic Kahn traversal over every graph node, including external
    * and declaration nodes which are not members of validNodes.
    */
  def compute(graph: Graph): Either[GraphCycle, GraphLevels] = {
    val nodeCount = graph.numNodes()
    val inDegree = Array.tabulate(nodeCount)(id => graph.inNeigh(id).distinct.size)
    var ready = mutable.TreeSet.empty[Int]
    (0 until nodeCount).filter(inDegree(_) == 0).foreach(ready.add)

    val levels = Vector.newBuilder[Vector[Int]]
    val levelByNode = Array.fill(nodeCount)(-1)
    var processed = 0
    var level = 0

    while (ready.nonEmpty) {
      val current = ready.toVector
      levels += current
      val next = mutable.TreeSet.empty[Int]

      current.foreach { nodeId =>
        levelByNode(nodeId) = level
        processed += 1
        graph.outNeigh(nodeId).distinct.sorted.foreach { successor =>
          inDegree(successor) -= 1
          if (inDegree(successor) == 0) next.add(successor)
        }
      }

      ready = next
      level += 1
    }

    if (processed != nodeCount) {
      val remaining = (0 until nodeCount).filter(levelByNode(_) < 0).toVector
      Left(GraphCycle(remaining))
    } else {
      Right(GraphLevels(levels.result(), levelByNode.toVector))
    }
  }
}
