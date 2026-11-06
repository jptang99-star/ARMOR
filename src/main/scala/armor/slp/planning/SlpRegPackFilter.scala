package armor.slp

/** Retention decision for one discovered packed register state group. */
final case class SlpRegPackFilterDecision(
  originalRegPackId: Int,
  updateNodeIds:     Vector[Int],
  retained:          Boolean,
  reason:            String
) {
  require(originalRegPackId >= 0)
  require(updateNodeIds.nonEmpty)
  require(reason.nonEmpty)
}

/** Result of filtering state packs after combinational pack retention.
  *
  * Register pack discovery records structural correspondence.  Retention is
  * stricter: a state pack is useful only when a retained combinational pack
  * supplies its complete next-state layout directly. Read-driven storage packs
  * are also retained when their single commit fragment can safely reassemble
  * the original scalar next-state lanes.
  */
final case class SlpRegPackFilterResult(
  result:       SlpRegPackingResult,
  decisions:    Vector[SlpRegPackFilterDecision],
  rawPackCount: Int,
  rawRegisters: Int
) {
  require(decisions == decisions.sortBy(_.originalRegPackId))
  require(rawPackCount >= result.packs.size)
  require(rawRegisters >= result.packs.map(_.lanes.size).sum)
}

/** Retain only packed-register groups with a proved packed state write.
  *
  * `SlpRegUpdatePacker` proves either an exact producer relation or a terminal
  * common reset-Mux closure, including source identity, lane order, widths and
  * offsets. This filter owns the retention policy and reindexes all state-pack
  * references after removing scalar-write-only groups.
  */
final class SlpRegPackFilter {
  def filter(raw: SlpRegPackingResult): SlpRegPackFilterResult = {
    val directWritesByRegPackId = raw.directWrites.groupBy(_.regPackId)
    val muxWritesByRegPackId = raw.muxWrites.groupBy(_.regPackId)
    val scalarWriteRegPackIds = raw.packs.collect {
      case pack if pack.discoveryPhase == "read_driven_scalar_write" => pack.id
    }.toSet
    val retainedOriginalPacks = raw.packs.filter(pack =>
      directWritesByRegPackId.contains(pack.id) || muxWritesByRegPackId.contains(pack.id) ||
        scalarWriteRegPackIds(pack.id)
    )
    val denseIdByOriginalId = retainedOriginalPacks.zipWithIndex.map {
      case (pack, denseId) => pack.id -> denseId
    }.toMap

    val retainedPacks = retainedOriginalPacks.zipWithIndex.map {
      case (pack, denseId) => pack.copy(id = denseId)
    }
    val retainedStateReads = raw.stateReads.flatMap { read =>
      denseIdByOriginalId.get(read.regPackId).map(denseId => read.copy(regPackId = denseId))
    }.distinct.sortBy(read => (read.regPackId, read.destinationPackId, read.argumentIndex))
    val retainedDirectWrites = raw.directWrites.flatMap { write =>
      denseIdByOriginalId.get(write.regPackId).map(denseId => write.copy(regPackId = denseId))
    }.distinct.sortBy(write => (write.regPackId, write.sourcePackId))
    val retainedMuxWrites = raw.muxWrites.flatMap { write =>
      denseIdByOriginalId.get(write.regPackId).map(denseId => write.copy(regPackId = denseId))
    }.distinct.sortBy(write => (write.regPackId, write.falseSourcePackId, write.conditionName))

    val retainedResult = SlpRegPackingResult(
      retainedPacks,
      retainedStateReads,
      retainedDirectWrites,
      raw.stats.copy(
        acceptedPacks = retainedPacks.size,
        packedRegisters = retainedPacks.map(_.lanes.size).sum,
        directStateReads = retainedStateReads.size,
        directStateWrites = retainedDirectWrites.size
      ),
      retainedMuxWrites
    )
    val decisions = raw.packs.sortBy(_.id).map { pack =>
      val retained = denseIdByOriginalId.contains(pack.id)
      SlpRegPackFilterDecision(
        pack.id,
        pack.nodeIds,
        retained,
        if (!retained) "no_packed_write_closure"
        else if (scalarWriteRegPackIds(pack.id)) "read_driven_scalar_write"
        else if (directWritesByRegPackId.contains(pack.id) &&
          pack.discoveryPhase == "read_driven_direct_closure") "read_driven_direct_closure"
        else if (directWritesByRegPackId.contains(pack.id)) "direct_packed_write"
        else "read_driven_mux_closure"
      )
    }
    SlpRegPackFilterResult(
      retainedResult,
      decisions,
      raw.packs.size,
      raw.packs.map(_.lanes.size).sum
    )
  }
}
