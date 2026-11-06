package armor.slp

import scala.collection.mutable

final case class SlpNodeDependency(sourceNodeId: Int, destinationNodeId: Int) {
  require(sourceNodeId >= 0)
  require(destinationNodeId >= 0)
  require(sourceNodeId != destinationNodeId)
}

final case class SlpPackDependency(
  sourcePackId:      Int,
  destinationPackId: Int,
  nodeDependencies: Vector[SlpNodeDependency]
) {
  require(sourcePackId >= 0)
  require(destinationPackId >= 0)
  require(sourcePackId != destinationPackId)
  require(nodeDependencies.nonEmpty)
  require(nodeDependencies == nodeDependencies.distinct.sortBy(edge => (edge.sourceNodeId, edge.destinationNodeId)))
}

final case class SlpPackGraphCycle(remainingPackIds: Vector[Int]) {
  require(remainingPackIds.nonEmpty)
  require(remainingPackIds == remainingPackIds.distinct.sorted)
}

/** Immutable dependency graph over Phase-2 packs.
  *
  * Original StatementGraph edges are retained as provenance.  Edges between
  * two lanes in the same pack are deliberately omitted: Phase 2 already
  * rejects packs containing an internal dependency.
  */
final case class SlpPackGraph private (
  packs:             Vector[SlpPack],
  nodeToPackId:      Map[Int, Int],
  dependencies:      Vector[SlpPackDependency],
  topologicalPackIds: Vector[Int],
  regions:            Vector[SlpRegion]
) {
  val packsById: Map[Int, SlpPack] = packs.iterator.map(pack => pack.id -> pack).toMap
  val operationOverrides: Map[Int, SlpOperation] =
    regions.iterator.map(region => region.rootNodeId -> region.operation).toMap
  val absorbedNodeIds: Set[Int] = regions.iterator.flatMap(_.internalNodeIds).toSet

  def pack(packId: Int): SlpPack = packsById(packId)

  def packForNode(nodeId: Int): Option[SlpPack] = nodeToPackId.get(nodeId).map(pack)

  def predecessors(packId: Int): Vector[Int] =
    dependencies.iterator.filter(_.destinationPackId == packId).map(_.sourcePackId).toVector.distinct.sorted

  def successors(packId: Int): Vector[Int] =
    dependencies.iterator.filter(_.sourcePackId == packId).map(_.destinationPackId).toVector.distinct.sorted
}

object SlpPackGraph {
  private def topologicalOrder(
    packIds: Vector[Int],
    dependencies: Vector[SlpPackDependency]
  ): Either[SlpPackGraphCycle, Vector[Int]] = {
    val incoming = mutable.HashMap(packIds.map(_ -> 0): _*)
    val outgoing = mutable.HashMap.empty[Int, Vector[Int]].withDefaultValue(Vector.empty)
    dependencies.foreach { dependency =>
      incoming.update(dependency.destinationPackId, incoming(dependency.destinationPackId) + 1)
      outgoing.update(
        dependency.sourcePackId,
        (outgoing(dependency.sourcePackId) :+ dependency.destinationPackId).distinct.sorted
      )
    }

    val ready = mutable.TreeSet(packIds.filter(incoming(_) == 0): _*)
    val result = Vector.newBuilder[Int]
    var visited = 0
    while (ready.nonEmpty) {
      val packId = ready.head
      ready.remove(packId)
      result += packId
      visited += 1
      outgoing(packId).foreach { successor =>
        incoming.update(successor, incoming(successor) - 1)
        if (incoming(successor) == 0) ready.add(successor)
      }
    }

    if (visited == packIds.size) Right(result.result())
    else Left(SlpPackGraphCycle(packIds.filter(incoming(_) > 0).sorted))
  }

  def build(view: SlpGraphView, result: SlpPackingResult): Either[SlpPackGraphCycle, SlpPackGraph] = {
    val packs = result.packs.sortBy(_.id)
    require(packs.map(_.id) == packs.indices.toVector, "SLP pack IDs must be dense and deterministic")

    val packedNodes = packs.flatMap(pack => pack.nodeIds.map(_ -> pack.id))
    require(
      packedNodes.map(_._1).distinct.size == packedNodes.size,
      "a StatementGraph node cannot belong to more than one SLP pack"
    )
    val nodeToPackId = packedNodes.toMap
    val activeRegions = result.regions.filter(region => nodeToPackId.contains(region.rootNodeId))

    val graphDependencies = for {
      sourceNodeId <- view.nodes.indices.toVector
      destinationNodeId <- view.fanoutIds(sourceNodeId)
      sourcePackId <- nodeToPackId.get(sourceNodeId).toVector
      destinationPackId <- nodeToPackId.get(destinationNodeId).toVector
      if sourcePackId != destinationPackId
    } yield (sourcePackId, destinationPackId, SlpNodeDependency(sourceNodeId, destinationNodeId))

    // A region root depends on its external boundary operands, not on the
    // absorbed internal nodes retained in StatementGraph for provenance.
    val regionDependencies = for {
      region <- activeRegions
      destinationPackId <- nodeToPackId.get(region.rootNodeId).toVector
      signal <- region.operation.operands.collect { case value: SlpSignal => value }
      sourceNodeId <- view.graph.nameToID.get(signal.name).toVector
      sourcePackId <- nodeToPackId.get(sourceNodeId).toVector
      if sourcePackId != destinationPackId
    } yield (sourcePackId, destinationPackId,
      SlpNodeDependency(sourceNodeId, region.rootNodeId))

    val rawDependencies = graphDependencies ++ regionDependencies

    val dependencies = rawDependencies
      .groupBy { case (sourcePackId, destinationPackId, _) => (sourcePackId, destinationPackId) }
      .toVector
      .sortBy(_._1)
      .map { case ((sourcePackId, destinationPackId), entries) =>
        SlpPackDependency(
          sourcePackId,
          destinationPackId,
          entries.map(_._3).distinct.sortBy(edge => (edge.sourceNodeId, edge.destinationNodeId))
        )
      }

    topologicalOrder(packs.map(_.id), dependencies).map { order =>
      SlpPackGraph(packs, nodeToPackId, dependencies, order, activeRegions)
    }
  }
}
