package armor.slp

import essent.Extract.{findAllModuleInstances, findExternalPorts}
import essent.StatementGraph
import essent.ir.{MemWrite, RegUpdate}
import firrtl.ir._

final case class SlpModuleLocation(instancePath: String, moduleName: String)

final case class SlpNode(
  id:       Int,
  name:     String,
  statement: Statement,
  valid:    Boolean,
  module:   Option[SlpModuleLocation],
  localNetName: String = "<unknown>"
) {
  def isStateful: Boolean = statement match {
    case _: DefRegister | _: DefMemory | _: RegUpdate | _: MemWrite => true
    case _                                                          => false
  }

  def hasSideEffects: Boolean = statement match {
    case _: RegUpdate | _: MemWrite | _: Print | _: Stop => true
    case _                                                => false
  }

  def isPure: Boolean = valid && !isStateful && !hasSideEffects
}

/** Read-only deterministic adapter around StatementGraph. */
final class SlpGraphView private (
  val graph: StatementGraph,
  val nodes: Vector[SlpNode],
  val levels: Either[GraphCycle, GraphLevels],
  val externalNames: Set[String]
) {
  val validNodeIds: Vector[Int] = nodes.iterator.filter(_.valid).map(_.id).toVector.sorted

  def node(nodeId: Int): SlpNode = nodes(nodeId)

  def faninIds(nodeId: Int): Vector[Int] = graph.inNeigh(nodeId).distinct.sorted.toVector

  def fanoutIds(nodeId: Int): Vector[Int] = graph.outNeigh(nodeId).distinct.sorted.toVector

  def validFaninIds(nodeId: Int): Vector[Int] = faninIds(nodeId).filter(graph.validNodes)

  def validFanoutIds(nodeId: Int): Vector[Int] = fanoutIds(nodeId).filter(graph.validNodes)

  def pathExists(sourceId: Int, destinationId: Int): Boolean = {
    if (sourceId == destinationId) return true

    val visited = scala.collection.mutable.BitSet(sourceId)
    val queue = scala.collection.mutable.Queue[Int](sourceId)
    while (queue.nonEmpty) {
      val current = queue.dequeue()
      fanoutIds(current).foreach { successor =>
        if (successor == destinationId) return true
        if (!visited(successor)) {
          visited.add(successor)
          queue.enqueue(successor)
        }
      }
    }
    false
  }
}

object SlpGraphView {
  def apply(graph: StatementGraph, circuit: Circuit): SlpGraphView = {
    val externalNames = findExternalPorts(circuit).keySet
    val moduleLocations = findAllModuleInstances(circuit).map {
      case (moduleName, rawPrefix) =>
        val instancePath = rawPrefix.stripSuffix(".")
        SlpModuleLocation(instancePath, moduleName)
    }.sortBy(location => (-location.instancePath.length, location.instancePath, location.moduleName))

    def locate(name: String): Option[SlpModuleLocation] =
      moduleLocations.find { location =>
        location.instancePath.isEmpty ||
          name == location.instancePath ||
          name.startsWith(location.instancePath + ".")
      }

    val nodes = (0 until graph.numNodes()).map { id =>
      SlpNode(
        id = id,
        name = graph.idToName(id),
        statement = graph.idToStmt(id),
        valid = graph.validNodes(id),
        module = locate(graph.idToName(id)),
        localNetName = graph.idToName(id).split("\\.").last
      )
    }.toVector

    new SlpGraphView(
      graph = graph,
      nodes = nodes,
      levels = GraphLevels.compute(graph),
      externalNames = externalNames
    )
  }
}
