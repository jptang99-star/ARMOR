package armor.slp

/** Operation statistics for scalar nodes at retained SLP pack boundaries.
  *
  * Counts are unique graph-node counts per direction. A scalar node that
  * crosses both directions is intentionally present in both columns and is
  * also reported in `both`.
  */
object SlpScalarBoundaryStatistics {
  final case class Row(opType: String, scalarToPack: Int, packToScalar: Int, both: Int) {
    require(scalarToPack >= both)
    require(packToScalar >= both)
  }

  private def scalarSourceNodeIds(lanes: Iterable[SlpPackInputLane]): Set[Int] =
    lanes.iterator.collect {
      case lane: SlpScalarInputLane if lane.producerNodeId.nonEmpty => lane.producerNodeId.get
    }.toSet

  private def countsByType(context: SlpAnalysisContext, nodeIds: Set[Int]): Map[String, Int] =
    nodeIds.iterator
      .filter(context.graph.validNodeIds.contains)
      .map(nodeId => SlpOperationStatistics.opType(context.graph.node(nodeId).statement))
      .toVector
      .groupMapReduce(identity)(_ => 1)(_ + _)

  def rows(context: SlpAnalysisContext, plan: SlpPlan): Vector[Row] = {
    val scalarToPack =
      plan.alignPlan.scalarToPack.iterator.flatMap(alignment => scalarSourceNodeIds(alignment.lanes)) ++
        plan.alignPlan.regWriteInputs.iterator.flatMap(input => scalarSourceNodeIds(input.lanes)) ++
        plan.alignPlan.broadcastInputs.iterator.flatMap {
          case SlpBroadcastInput(_, _, signal: SlpBroadcastSignal) => signal.producerNodeId
          case _                                                   => None
        }
    val scalarToPackNodeIds = scalarToPack.toSet

    val packToScalarNodeIds = plan.alignPlan.packToScalar.iterator
      .flatMap(_.lanes)
      .flatMap(_.consumers)
      .collect { case consumer: SlpScalarConsumer => consumer.nodeId }
      .toSet

    val scalarToPackByType = countsByType(context, scalarToPackNodeIds)
    val packToScalarByType = countsByType(context, packToScalarNodeIds)
    val bothByType = countsByType(context, scalarToPackNodeIds.intersect(packToScalarNodeIds))
    (scalarToPackByType.keySet ++ packToScalarByType.keySet).toVector.sorted.map { opType =>
      Row(
        opType,
        scalarToPackByType.getOrElse(opType, 0),
        packToScalarByType.getOrElse(opType, 0),
        bothByType.getOrElse(opType, 0)
      )
    }
  }

  def format(rows: Vector[Row]): String = {
    val scalarToPackTotal = rows.map(_.scalarToPack).sum
    val packToScalarTotal = rows.map(_.packToScalar).sum
    val bothTotal = rows.map(_.both).sum
    val header = f" ${"OpType"}%-20s ${"Scalar->Pack"}%16s ${"Pack->Scalar"}%16s ${"Both"}%16s"
    val separator = "-" * 71
    val body = rows.map { row =>
      f" ${row.opType}%-20s ${row.scalarToPack}%16d ${row.packToScalar}%16d ${row.both}%16d"
    }
    val total = f" ${"TOTAL"}%-20s $scalarToPackTotal%16d $packToScalarTotal%16d $bothTotal%16d"
    (Vector(header, separator) ++ body ++ Vector(separator, total)).mkString(System.lineSeparator()) + System.lineSeparator()
  }
}
