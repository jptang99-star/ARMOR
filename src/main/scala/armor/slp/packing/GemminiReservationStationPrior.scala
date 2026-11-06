package armor.slp

/** Domain-specific Phase-1.5 seeds for Gemmini's reservation station.
  *
  * This recognises a semantic reduction shape, rather than generated `_T_`
  * names: `deps_<kind>_0 | deps_<kind>_1`, followed by
  * `| deps_<kind>_2`, where `kind` is currently `ld` or `ex`.  The indexed
  * `entries_ex_<i>` leaf is the lane identity.  It also recognises consumers
  * of indexed `entries_ld_<i><suffix>` and `entries_st_<i><suffix>` state
  * fields.  The entry kind and complete suffix form the family identity, so
  * unrelated reservation-station fields cannot be merged.  The caller still
  * applies the normal ICT legality and ownership checks before committing a
  * seed.
  */
private[slp] final case class ICTPriorSeed(
  nodeIds:        Vector[Int],
  discoveryPhase: String
) {
  require(nodeIds.size >= 2)
  require(nodeIds.distinct.size == nodeIds.size)
  require(discoveryPhase.nonEmpty)
}

private[slp] object GemminiReservationStationPrior {
  private final case class EntryDependency(index: Int, kind: String, stage: Int)
  private final case class SeedKey(location: SlpModuleLocation, level: Int, kind: String, stage: Int)
  private final case class IndexedReservationEntry(index: Int, kind: String, suffix: String)
  private final case class PriorOperationKey(
    opcode:       String,
    resultWidth:  Int,
    storageWidth: Int,
    operandWidths: Vector[Int],
    parameters:   Vector[BigInt]
  ) {
    def sortKey: (String, Int, Int, String, String) =
      (opcode, resultWidth, storageWidth, operandWidths.mkString(":"), parameters.mkString(":"))
  }
  private final case class IndexedReservationUseKey(
    location:      SlpModuleLocation,
    level:         Int,
    kind:          String,
    suffix:        String,
    argumentIndex: Int,
    operation:     PriorOperationKey
  ) {
    def sortKey: (String, String, Int, String, String, Int, (String, Int, Int, String, String)) =
      (location.instancePath, location.moduleName, level, kind, suffix, argumentIndex, operation.sortKey)
  }

  private val EntryDependencyName =
    "^gemmini\\.reservation_station\\.entries_ex_([0-9]+)_bits_deps_(ld|ex)_([0-9]+)$".r
  private val IndexedReservationEntryName =
    "^gemmini\\.reservation_station\\.entries_(ld|st)_([0-9]+)((?:_.+)?)$".r

  private def entryDependency(name: String): Option[EntryDependency] = name match {
    case EntryDependencyName(index, kind, stage) =>
      Some(EntryDependency(index.toInt, kind, stage.toInt))
    case _ => None
  }

  private def indexedReservationEntry(name: String): Option[IndexedReservationEntry] = name match {
    case IndexedReservationEntryName(kind, index, suffix) =>
      Some(IndexedReservationEntry(index.toInt, kind, suffix))
    case _ => None
  }

  private def signalName(operand: SlpOperand): Option[String] = operand match {
    case SlpSignal(name, _) => Some(name)
    case _                  => None
  }

  private def isOr(operation: SlpOperation): Boolean =
    operation.opcode == SlpOr && operation.resultWidth == 1 && operation.operands.size == 2

  private def operationKey(operation: SlpOperation): PriorOperationKey =
    PriorOperationKey(
      opcode = operation.opcode.name,
      resultWidth = operation.resultWidth,
      storageWidth = operation.storageWidth,
      operandWidths = operation.operandWidths,
      parameters = operation.opcode.packSemanticParameters(operation.parameters)
    )

  /** Keep only one candidate per lane index, then split the remaining lanes
    * into maximal continuous index runs.  A duplicate index is ambiguous: it
    * cannot prove a one-to-one lane correspondence, so it is intentionally
    * excluded rather than chosen arbitrarily.
    */
  private def continuousRuns(members: Vector[(Int, Int)]): Vector[Vector[(Int, Int)]] = {
    val uniqueMembers = members.groupBy(_._1).valuesIterator.collect {
      case Vector(member) => member
    }.toVector.sortBy(_._1)

    uniqueMembers.foldLeft(Vector.empty[Vector[(Int, Int)]]) {
      case (Vector(), member) => Vector(Vector(member))
      case (completed, member) =>
        val current = completed.last
        if (member._1 == current.last._1 + 1) completed.dropRight(1) :+ (current :+ member)
        else completed :+ Vector(member)
    }
  }

  private def seedsForRuns(
    members:        Vector[(Int, Int)],
    discoveryPhase: String
  ): Vector[ICTPriorSeed] =
    continuousRuns(members).collect {
      case run if run.size >= 2 => ICTPriorSeed(run.map(_._2), discoveryPhase)
    }

  /** Verify the previous stage of one reduction lane recursively. */
  private def isPrefix(
    signal:       String,
    index:        Int,
    kind:         String,
    stage:        Int,
    operations:   Map[Int, SlpOperation],
    nameToNodeId: Map[String, Int]
  ): Boolean = {
    if (stage == 0) {
      entryDependency(signal).contains(EntryDependency(index, kind, 0))
    } else {
      nameToNodeId.get(signal).flatMap(operations.get).exists { operation =>
        if (!isOr(operation)) false
        else {
          val signals = operation.operands.flatMap(signalName)
          signals.size == 2 && signals.indices.exists { entryOperand =>
            entryDependency(signals(entryOperand)).contains(EntryDependency(index, kind, stage)) &&
              isPrefix(signals(1 - entryOperand), index, kind, stage - 1, operations, nameToNodeId)
          }
        }
      }
    }
  }

  private def dependencyReductionSeeds(
    candidateNodeIds: Vector[Int],
    operations:       Map[Int, SlpOperation],
    nodeLevel:        Int => Int,
    nodeLocation:     Int => Option[SlpModuleLocation],
    nameToNodeId:     Map[String, Int]
  ): Vector[ICTPriorSeed] = {
    val anchors = candidateNodeIds.flatMap { nodeId =>
      for {
        operation <- operations.get(nodeId)
        location <- nodeLocation(nodeId)
        if isOr(operation)
        signals = operation.operands.flatMap(signalName)
        if signals.size == 2
        entryOperand <- signals.indices.collectFirst {
          case operandIndex if entryDependency(signals(operandIndex)).exists(_.stage == 2) => operandIndex
        }
        entry <- entryDependency(signals(entryOperand))
        if isPrefix(signals(1 - entryOperand), entry.index, entry.kind, entry.stage - 1,
          operations, nameToNodeId)
      } yield SeedKey(location, nodeLevel(nodeId), entry.kind, entry.stage) -> (entry.index -> nodeId)
    }

    anchors.groupBy(_._1).toVector.sortBy { case (key, _) =>
      (key.location.instancePath, key.location.moduleName, key.level, key.kind, key.stage)
    }.flatMap { case (_, members) =>
      seedsForRuns(members.map(_._2), "prior:gemmini-reservation-station")
    }
  }

  /** Seed consumers of corresponding `entries_{ld,st}_<index><suffix>` state
    * fields.  The register fields themselves are state leaves, not SLP
    * operations; treating the consuming operation as the seed root lets the
    * normal ICT fanout expansion discover the remaining combinational cone.
    */
  private def indexedReservationEntrySeeds(
    candidateNodeIds: Vector[Int],
    operations:       Map[Int, SlpOperation],
    nodeLevel:        Int => Int,
    nodeLocation:     Int => Option[SlpModuleLocation]
  ): Vector[ICTPriorSeed] = {
    val uses = candidateNodeIds.flatMap { nodeId =>
      for {
        operation <- operations.get(nodeId).toVector
        location <- nodeLocation(nodeId).toVector
        (signal, argumentIndex) <- operation.operands.zipWithIndex.collect {
          case (signal: SlpSignal, index) => signal -> index
        }
        entry <- indexedReservationEntry(signal.name).toVector
      } yield {
        IndexedReservationUseKey(
          location = location,
          level = nodeLevel(nodeId),
          kind = entry.kind,
          suffix = entry.suffix,
          argumentIndex = argumentIndex,
          operation = operationKey(operation)
        ) -> (entry.index -> nodeId)
      }
    }

    uses.groupBy(_._1).toVector.sortBy(_._1.sortKey).flatMap { case (_, members) =>
      val kind = members.head._1.kind
      seedsForRuns(members.map(_._2), s"prior:gemmini-reservation-station:entries-$kind")
    }
  }

  /** Return dependency-reduction and indexed reservation-entry seed runs. */
  def discover(
    candidateNodeIds: Vector[Int],
    operations:       Map[Int, SlpOperation],
    nodeLevel:        Int => Int,
    nodeLocation:     Int => Option[SlpModuleLocation],
    nameToNodeId:     Map[String, Int]
  ): Vector[ICTPriorSeed] =
    (dependencyReductionSeeds(
      candidateNodeIds, operations, nodeLevel, nodeLocation, nameToNodeId
    ) ++ indexedReservationEntrySeeds(
      candidateNodeIds, operations, nodeLevel, nodeLocation
    )).distinct.sortBy(seed => (seed.nodeIds.mkString(","), seed.discoveryPhase))
}
