package armor.slp

object SlpUnsignedCompareLowering {
  final case class Layout(
    laneWidth:      Int,
    parallelDegree: Int,
    lanesPerGroup: Int
  )

  private def argumentOffsets(laneOperations: Vector[SlpOperation], argumentIndex: Int): Vector[Int] =
    laneOperations.map(_.operands(argumentIndex).width).scanLeft(0)(_ + _).dropRight(1)

  def layout(
    opcode:         SlpOpcode,
    pack:           SlpPack,
    laneOperations: Vector[SlpOperation]
  ): Option[Layout] = {
    if (pack.shape.opcode != opcode || laneOperations.size != pack.parallelDegree ||
        pack.totalResultWidth != pack.parallelDegree ||
        pack.outputOffsets != pack.lanes.indices.toVector)
      return None

    val laneWidth = laneOperations.headOption.flatMap(_.operands.headOption).map(_.width).getOrElse(0)
    if (laneWidth <= 0 || laneWidth > 63) return None

    val validOperations = laneOperations.forall {
      case SlpOperation(op, 1, storageWidth, Vector(left, right), parameters, _) =>
        op == opcode && parameters.isEmpty &&
          (left.isInstanceOf[SlpSignal] || right.isInstanceOf[SlpSignal]) &&
          left.width == laneWidth && right.width == laneWidth &&
          storageWidth == laneWidth
      case _ => false
    }
    if (!validOperations) return None

    val denseOffsets = laneOperations.indices.map(_ * laneWidth).toVector
    if (argumentOffsets(laneOperations, 0) != denseOffsets ||
        argumentOffsets(laneOperations, 1) != denseOffsets)
      return None

    val lanesPerGroup = 64 / (laneWidth + 1)
    Option.when(lanesPerGroup > 0)(Layout(laneWidth, pack.parallelDegree, lanesPerGroup))
  }
}
