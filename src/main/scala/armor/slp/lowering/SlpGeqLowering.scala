package armor.slp

object SlpGeqLowering {
  type Layout = SlpUnsignedCompareLowering.Layout

  def layout(pack: SlpPack, laneOperations: Vector[SlpOperation]): Option[Layout] =
    SlpUnsignedCompareLowering.layout(SlpGeq, pack, laneOperations)

  def canLower(pack: SlpPack, laneOperations: Vector[SlpOperation]): Boolean =
    layout(pack, laneOperations).nonEmpty
}

object SlpLtLowering {
  type Layout = SlpUnsignedCompareLowering.Layout

  def layout(pack: SlpPack, laneOperations: Vector[SlpOperation]): Option[Layout] =
    SlpUnsignedCompareLowering.layout(SlpLt, pack, laneOperations)

  def canLower(pack: SlpPack, laneOperations: Vector[SlpOperation]): Boolean =
    layout(pack, laneOperations).nonEmpty
}
