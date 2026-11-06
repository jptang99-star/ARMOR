package armor.slp

import essent.ir.RegUpdate
import firrtl.ir.{Expression, IntWidth, Reference, SubField, SubIndex, UIntType}

import scala.collection.mutable

final case class SlpStateTransitionPhase3Stats(
  proposals:                  Int,
  consumerLayouts:            Int,
  acceptedPacks:              Int,
  acceptedNodes:              Int,
  rejectedNoConsumerLayout:   Int,
  rejectedNoDirectInput:      Int,
  rejectedOverlap:            Int
)

final case class SlpStateTransitionPhase3Result(
  result: SlpPackingResult,
  stats:  SlpStateTransitionPhase3Stats
)

/** Select deferred self-feedback state transitions after ordinary ICT
  * discovery has established the retained combinational layouts.
  *
  * The phase deliberately derives every selected lane order from an existing
  * packed consumer of the state value.  It therefore never creates a maximal
  * family-wide state pack (for example 30 one-bit lanes) merely because all
  * corresponding next-state Muxes are structurally similar.
  */
final class SlpStateTransitionPhase3(context: SlpAnalysisContext) {
  private val view = context.graph
  private val operations = context.classifications.collect {
    case (nodeId, SlpSupported(operation)) => nodeId -> operation
  }.toMap

  private final case class UpdateInfo(
    nextNodeId:   Int,
    updateNodeId: Int,
    registerName: String,
    width:        Int,
    selfArm:      Int
  )

  /** A retained packed consumer reads a vector of scalar state registers.
    * The vector order is the canonical layout phase 3 must preserve when it
    * materializes the corresponding previous-state and next-state packs.
    */
  private final case class BackwardStateCandidate(
    consumerPackId: Int,
    argumentIndex: Int,
    updates:        Vector[UpdateInfo]
  ) {
    require(updates.nonEmpty)
  }

  private def referenceName(expression: Expression): Option[String] = expression match {
    case Reference(name, _, _, _)       => Some(name)
    case SubField(base, name, _, _)     => referenceName(base).map(prefix => s"$prefix.$name")
    case SubIndex(base, index, _, _)    => referenceName(base).map(prefix => s"${prefix}_$index")
    case _                              => None
  }

  private def uintWidth(expression: Expression): Option[Int] = expression.tpe match {
    case UIntType(IntWidth(width)) if width > 0 && width.isValidInt => Some(width.toInt)
    case _                                                         => None
  }

  private def operationOf(nodeId: Int, result: SlpPackingResult): Option[SlpOperation] =
    result.operationOverrides.get(nodeId).orElse(operations.get(nodeId))

  private def updateByRegister(result: SlpPackingResult): Map[String, UpdateInfo] = {
    val updates = view.validNodeIds.flatMap { updateNodeId =>
      view.node(updateNodeId).statement match {
        case update: RegUpdate =>
          for {
            registerName <- referenceName(update.regRef)
            registerWidth <- uintWidth(update.regRef)
            nextName <- referenceName(update.expr)
            nextNodeId <- view.graph.nameToID.get(nextName)
            mux <- operationOf(nextNodeId, result).filter(_.opcode == SlpMux)
            selfArms = mux.operands.zipWithIndex.collect {
              case (SlpSignal(name, width), arm)
                  if arm > 0 && name == registerName && width == registerWidth => arm
            }
            if selfArms.size == 1 && mux.operands.size == 3
          } yield UpdateInfo(nextNodeId, updateNodeId, registerName, registerWidth, selfArms.head)
        case _ => None
      }
    }
    updates.groupBy(_.registerName).collect {
      case (registerName, Vector(update)) => registerName -> update
    }
  }

  /** Traverse a retained packed consumer backwards across a state read.  The
    * consumer's operand order is the only legal layout order for the new
    * state pack: this is what makes the read exact rather than an unpack and
    * re-pack boundary.
    */
  private def backwardCandidates(result: SlpPackingResult): Vector[BackwardStateCandidate] = {
    val updates = updateByRegister(result)
    result.packs.flatMap { consumerPack =>
      val laneOperations = consumerPack.nodeIds.map(nodeId => operationOf(nodeId, result))
      if (laneOperations.exists(_.isEmpty)) Vector.empty
      else laneOperations.head.get.operands.indices.flatMap { argumentIndex =>
        val operands = laneOperations.map(_.get.operands(argumentIndex))
        val signals = operands.collect { case signal: SlpSignal => signal }
        val resolved = signals.flatMap(signal => updates.get(signal.name))
        val sameWidth = signals.map(_.width) == resolved.map(_.width)
        val sameShape = resolved.headOption.exists { first =>
          resolved.forall { update =>
            update.selfArm == first.selfArm &&
              operationOf(update.nextNodeId, result).exists(operation =>
                SlpPackShape.from(operation) == SlpPackShape.from(operationOf(first.nextNodeId, result).get)
              )
          }
        }
        if (signals.size == operands.size &&
            resolved.size == operands.size &&
            resolved.map(_.registerName).distinct.size == resolved.size &&
            sameWidth && sameShape &&
            resolved.size >= context.config.minParallelDegree &&
            resolved.map(_.width).sum <= context.config.machineWidth) {
          Some(BackwardStateCandidate(consumerPack.id, argumentIndex, resolved))
        } else None
      }
    }.groupBy(candidate => candidate.updates.map(_.updateNodeId)).values.map(_.head).toVector
      .sortBy(candidate => (candidate.consumerPackId, candidate.argumentIndex))
  }

  private def makePack(
    id: Int,
    nodeIds: Vector[Int],
    result: SlpPackingResult
  ): SlpPack = {
    val firstOperation = operationOf(nodeIds.head, result).get
    val locations = nodeIds.map(nodeId => view.node(nodeId).module)
    val commonLocation = locations.flatten.distinct match {
      case Vector(location) if locations.forall(_.contains(location)) => Some(location)
      case _                                                          => None
    }
    SlpPack(
      id = id,
      shape = SlpPackShape.from(firstOperation),
      lanes = nodeIds.map { nodeId =>
        val operation = operationOf(nodeId, result).get
        SlpLane(nodeId, operation.resultWidth, operation.storageWidth)
      },
      level = view.levels.toOption.get.levelOf(nodeIds.head).get,
      module = commonLocation,
      laneLocations = locations,
      discoveryPhase = Some("phase3-backward-state")
    )
  }

  def run(provisional: SlpPackingResult): SlpStateTransitionPhase3Result = {
    val occupiedCombinational = provisional.packs.iterator.flatMap(_.nodeIds).toSet
    val occupiedUpdates = provisional.regUpdateLayouts.iterator.flatMap(_.updateNodeIds).toSet
    val claimedCombinational = mutable.HashSet.empty[Int]
    val claimedUpdates = mutable.HashSet.empty[Int]
    val acceptedPacks = Vector.newBuilder[SlpPack]
    val acceptedLayouts = Vector.newBuilder[SlpRegUpdateLayout]
    var layoutCount = 0
    var rejectedNoConsumerLayout = 0
    var rejectedNoDirectInput = 0
    var rejectedOverlap = 0
    var nextPackId = provisional.packs.size

    val candidates = backwardCandidates(provisional)
    layoutCount = candidates.size
    if (candidates.isEmpty) rejectedNoConsumerLayout += 1
    candidates.foreach { candidate =>
      val nextNodeIds = candidate.updates.map(_.nextNodeId)
      val updateNodeIds = candidate.updates.map(_.updateNodeId)
      val overlap =
        nextNodeIds.exists(occupiedCombinational) ||
          updateNodeIds.exists(occupiedUpdates) ||
          nextNodeIds.exists(claimedCombinational) ||
          updateNodeIds.exists(claimedUpdates)

      if (overlap) rejectedOverlap += 1
      else {
        val pack = makePack(nextPackId, nextNodeIds, provisional)
        nextPackId += 1
        acceptedPacks += pack
        acceptedLayouts += SlpRegUpdateLayout(
          updateNodeIds,
          nextNodeIds,
          "phase3-backward-state"
        )
        claimedCombinational ++= nextNodeIds
        claimedUpdates ++= updateNodeIds
      }
    }

    val newPacks = acceptedPacks.result()
    val densePacks = (provisional.packs ++ newPacks).zipWithIndex.map {
      case (pack, id) => pack.copy(id = id)
    }
    val layouts = acceptedLayouts.result()
    val result = provisional.copy(
      packs = densePacks,
      regUpdateLayouts = provisional.regUpdateLayouts ++ layouts
    )
    SlpStateTransitionPhase3Result(
      result,
      SlpStateTransitionPhase3Stats(
        proposals = candidates.size,
        consumerLayouts = layoutCount,
        acceptedPacks = newPacks.size,
        acceptedNodes = newPacks.map(_.parallelDegree).sum,
        rejectedNoConsumerLayout = rejectedNoConsumerLayout,
        rejectedNoDirectInput = rejectedNoDirectInput,
        rejectedOverlap = rejectedOverlap
      )
    )
  }
}
