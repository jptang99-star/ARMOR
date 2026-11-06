package armor.slp

sealed trait SlpOperandKind {
  def name: String
}

case object SlpSignalKind extends SlpOperandKind { val name = "signal" }
case object SlpConstantKind extends SlpOperandKind { val name = "constant" }

object SlpOperandKind {
  def of(operand: SlpOperand): SlpOperandKind = operand match {
    case _: SlpSignal       => SlpSignalKind
    case _: SlpUIntConstant => SlpConstantKind
  }
}

final case class SlpPackShape(
  opcode:       SlpOpcode,
  resultWidth:  Int,
  storageWidth: Int,
  operandWidths: Vector[Int],
  operandKinds:  Vector[SlpOperandKind]
) {
  require(resultWidth > 0)
  require(storageWidth >= resultWidth)
  require(operandWidths.nonEmpty)
  require(operandWidths.size == operandKinds.size)

  def sortKey: (String, Int, Int, String, String) = (
    opcode.name,
    resultWidth,
    storageWidth,
    operandWidths.mkString(":"),
    operandKinds.map(_.name).mkString(":")
  )
}

object SlpPackShape {
  def from(operation: SlpOperation): SlpPackShape = SlpPackShape(
    opcode = operation.opcode,
    resultWidth = operation.resultWidth,
    storageWidth = operation.storageWidth,
    operandWidths = operation.operandWidths,
    operandKinds = operation.operands.map(SlpOperandKind.of)
  )
}

final case class SlpLane(
  nodeId:       Int,
  resultWidth:  Int,
  storageWidth: Int
) {
  require(nodeId >= 0)
  require(resultWidth > 0)
  require(storageWidth >= resultWidth)
}

final case class SlpModuleNet(moduleName: String, localNetName: String) {
  require(moduleName.nonEmpty)
  require(localNetName.nonEmpty)
}

/** Immutable analysis-only pack.
  *
  * module is None only when a future configuration explicitly permits a
  * cross-module pack.  SLP v1 analysis keeps it defined.
  */
final case class SlpPack(
  id:     Int,
  shape:  SlpPackShape,
  lanes:  Vector[SlpLane],
  level:  Int,
  module: Option[SlpModuleLocation],
  laneLocations: Vector[Option[SlpModuleLocation]] = Vector.empty,
  moduleNet: Option[SlpModuleNet] = None,
  discoveryPhase: Option[String] = None
) {
  require(id >= 0)
  require(lanes.nonEmpty)
  require(lanes.map(_.nodeId).distinct.size == lanes.size)
  require(level >= 0)
  require(lanes.forall(_.resultWidth == shape.resultWidth))
  require(lanes.forall(_.storageWidth == shape.storageWidth))
  require(laneLocations.isEmpty || laneLocations.size == lanes.size)

  val outputOffsets: Vector[Int] =
    lanes.map(_.resultWidth).scanLeft(0)(_ + _).dropRight(1)

  def parallelDegree: Int = lanes.size
  def totalResultWidth: Int = lanes.map(_.resultWidth).sum
  def totalStorageWidth: Int = lanes.map(_.storageWidth).sum
  def nodeIds: Vector[Int] = lanes.map(_.nodeId)
}

final case class SlpPackingResult(
  packerName: String,
  packs: Vector[SlpPack],
  stats: SlpPackStats,
  diagnostics: SlpPackerDiagnostics,
  regUpdateLayouts: Vector[SlpRegUpdateLayout] = Vector.empty,
  stateTransitionProposals: Vector[SlpStateTransitionProposal] = Vector.empty,
  regions: Vector[SlpRegion] = Vector.empty,
  temporalStateStats: Option[SlpTemporalStateExpansionStats] = None
) {
  lazy val operationOverrides: Map[Int, SlpOperation] =
    regions.iterator.map(region => region.rootNodeId -> region.operation).toMap

  lazy val absorbedNodeIds: Set[Int] = regions.iterator.flatMap(_.internalNodeIds).toSet
}

/** A RegUpdate lane group discovered at an ICT state boundary.
  *
  * sourceNodeIds retain the combinational lane identity which reached the
  * state boundary. The layout is deliberately not a SlpPack: RegUpdate is
  * committed at the end of the cycle and must not enter the current-cycle
  * combinational PackGraph.
  */
final case class SlpRegUpdateLayout(
  updateNodeIds: Vector[Int],
  sourceNodeIds: Vector[Int],
  discoveryPhase: String = "ict"
) {
  require(updateNodeIds.size >= 2)
  require(updateNodeIds.distinct.size == updateNodeIds.size)
  require(sourceNodeIds.size == updateNodeIds.size)
}

/** A self-feedback next-state Mux group discovered by ICT, but intentionally
  * not committed during phase 2.  Phase 3 selects a subset whose lane order
  * matches already-retained state consumers, preventing a wide state layout
  * from breaking existing direct register reuse.
  */
final case class SlpStateTransitionProposal(
  nextNodeIds: Vector[Int],
  updateNodeIds: Vector[Int]
) {
  require(nextNodeIds.size >= 2)
  require(nextNodeIds.size == updateNodeIds.size)
  require(nextNodeIds.distinct.size == nextNodeIds.size)
  require(updateNodeIds.distinct.size == updateNodeIds.size)
}
