package armor.slp

import armor.{ArmorAnd, ArmorBitSelect, ArmorIdentity}
import essent.ir.RegUpdate
import firrtl.PrimOps.{And, Eq, Not, Or, Xor}
import firrtl.ir.{Connect, DefNode, DoPrim, Expression, IntWidth, Mux, Reference, SubField, SubIndex, UIntType}

import scala.collection.mutable

final case class ICTPackerConfig(
  enablePhase2: Boolean = true,
  allowCrossModulePipeline: Boolean = true,
  allowDefUsePackSizeMismatch: Boolean = true,
  allowMultiSuccessorExpansion: Boolean = true,
  enableExactConcatMerge: Boolean = false,
  enableIndexedBoundaryExpansion: Boolean = false,
  enableGemminiReservationStationPrior: Boolean = true,
  enableRegUpdateReadSeedDiscovery: Boolean = false,
  enableLocalInstanceEquivalence: Boolean = false
)

/** Discovery compatibility is intentionally independent of operand kind.
  *
  * This is the shape used by the original ICTPacker: operation identity and
  * widths determine whether lanes correspond. A signal lane and a literal
  * lane therefore remain discoverable together and the lowering decides how
  * to materialize their individual operands.
  */
private final case class ICTStmtShape(
  opType: String,
  resultWidth: Int,
  storageWidth: Int,
  resultType: String,
  operandWidths: Vector[Int]
) {
  def sortKey: (String, Int, Int, String, String) =
    (opType, resultWidth, storageWidth, resultType, operandWidths.mkString(":"))
}

/** Complete discovery identity.  Operation parameters are semantic metadata,
  * not operand lanes, and therefore must agree across a pack. */
private final case class ICTPackKey(
  shape: ICTStmtShape,
  parameters: Vector[BigInt]
) {
  def sortKey: (String, Int, Int, String, String, String) =
    (shape.opType, shape.resultWidth, shape.storageWidth, shape.resultType,
      shape.operandWidths.mkString(":"), parameters.mkString(":"))
}

private sealed trait ICTDiscoveryKind
private final case class ICTCombinational(operation: SlpOperation) extends ICTDiscoveryKind
private final case class ICTRegisterUpdate(registerName: String) extends ICTDiscoveryKind

private final case class ICTNodeMetadata(
  nodeId: Int,
  kind: ICTDiscoveryKind,
  shape: ICTStmtShape,
  resultName: String,
  operands: Vector[SlpOperand],
  resultWidth: Int,
  storageWidth: Int
)

private final case class ICTConsumerKey(
  packKey: ICTPackKey,
  argumentIndex: Int,
  level: Int
) {
  def sortKey = (packKey.sortKey, argumentIndex, level)
}

private sealed trait ICTLocalEquivKey {
  def sortKey: String
}

private final case class ICTNamedLocalKey(localNetName: String) extends ICTLocalEquivKey {
  def sortKey: String = s"name:$localNetName"
}

private final case class ICTTempExprKey(
  opcode: String,
  resultWidth: Int,
  storageWidth: Int,
  parameters: Vector[BigInt],
  operands: Vector[ICTOperandEquivKey]
) extends ICTLocalEquivKey {
  def sortKey: String =
    s"expr:$opcode:$resultWidth:$storageWidth:${parameters.mkString(",")}:" +
      operands.map(_.sortKey).mkString("[", ",", "]")
}

private sealed trait ICTOperandEquivKey {
  def sortKey: String
}

private final case class ICTConstOperandKey(width: Int, value: BigInt)
    extends ICTOperandEquivKey {
  def sortKey: String = s"const:$width:$value"
}

private final case class ICTLocalSignalOperandKey(width: Int, localName: String)
    extends ICTOperandEquivKey {
  def sortKey: String = s"local:$width:$localName"
}

private final case class ICTExternalSignalOperandKey(width: Int, fullName: String)
    extends ICTOperandEquivKey {
  def sortKey: String = s"external:$width:$fullName"
}

private final case class ICTInlineTempOperandKey(expr: ICTTempExprKey)
    extends ICTOperandEquivKey {
  def sortKey: String = s"inline:${expr.sortKey}"
}

/** Phase-1.5 seed key for generated module families which FIRRTL cannot dedup.
  *
  * The normal phase-1 key requires an exact module name.  This key preserves
  * the same local identity, but canonicalizes only the generated numeric
  * module suffix (for example `Foo_3` -> `Foo`).  Real local names remain
  * part of the key.  ExpressionDecompose-generated `_armor_expr*` temporaries
  * are keyed by their local expression shape instead, so per-module fresh-name
  * skew does not break discovery.
  */
private final case class ICTLocalInstanceEquivKey(
  moduleFamily: String,
  localKey: ICTLocalEquivKey,
  packKey: ICTPackKey,
  level: Int
) {
  def sortKey: (String, String, (String, Int, Int, String, String, String), Int) =
    (moduleFamily, localKey.sortKey, packKey.sortKey, level)
}

private final case class ICTIndexedNameKey(value: String, indexed: Boolean)

private sealed trait ICTIndexedOperandKey {
  def sortKey: String
  def hasIndexedComponent: Boolean
}

private final case class ICTIndexedConstOperandKey(width: Int, value: BigInt)
    extends ICTIndexedOperandKey {
  def sortKey: String = s"const:$width:$value"
  def hasIndexedComponent: Boolean = false
}

private final case class ICTIndexedLocalSignalOperandKey(
  width: Int,
  family: String,
  indexed: Boolean
) extends ICTIndexedOperandKey {
  def sortKey: String = s"local:$width:$family"
  def hasIndexedComponent: Boolean = indexed
}

private final case class ICTIndexedExternalSignalOperandKey(width: Int, fullName: String)
    extends ICTIndexedOperandKey {
  def sortKey: String = s"external:$width:$fullName"
  def hasIndexedComponent: Boolean = false
}

private final case class ICTIndexedInlineTempOperandKey(expr: ICTIndexedExprKey)
    extends ICTIndexedOperandKey {
  def sortKey: String = s"inline:${expr.sortKey}"
  def hasIndexedComponent: Boolean = expr.hasIndexedComponent
}

private final case class ICTIndexedExprKey(
  opcode: String,
  resultWidth: Int,
  storageWidth: Int,
  parameters: Vector[BigInt],
  operands: Vector[ICTIndexedOperandKey]
) {
  def sortKey: String =
    s"expr:$opcode:$resultWidth:$storageWidth:${parameters.mkString(",")}:" +
      operands.map(_.sortKey).mkString("[", ",", "]")
  def hasIndexedComponent: Boolean = operands.exists(_.hasIndexedComponent)
}

private final case class ICTIndexedBoundaryKey(
  instancePath: String,
  moduleName: String,
  level: Int,
  packKey: ICTPackKey,
  resultFamily: String,
  resultIndexed: Boolean,
  operands: Vector[ICTIndexedOperandKey]
) {
  def sortKey: (String, String, Int, (String, Int, Int, String, String, String), String, String) =
    (instancePath, moduleName, level, packKey.sortKey, resultFamily,
      operands.map(_.sortKey).mkString("[", ",", "]"))
  def hasIndexedComponent: Boolean =
    resultIndexed || operands.exists(_.hasIndexedComponent)
}

/** A materializable phase-1 seed layout, recorded before greedy discovery
  * starts.  It is deliberately operation-agnostic: any narrower use-def or
  * def-use expansion must not consume all of the lanes of a wider direct
  * layout which is still available.
  */
private final case class ICTBoundaryGroup(
  nodeIds: Vector[Int],
  hasUnpackedFanin: Boolean,
  hasUnpackedFanout: Boolean
)

/** One lane-preserving traversal of the state boundary. The next-expression
  * group and its update group must be committed together; otherwise a packed
  * next expression would merely introduce scalar write-back overhead.
  */
private final case class ICTStateTransitionCandidate(
  nextNodeIds: Vector[Int],
  updateNodeIds: Vector[Int]
)

/** Current-state register lane used as a virtual phase-2 source.
  *
  * A register read is a temporal state leaf rather than a combinational
  * PackGraph node.  Phase-2 may nevertheless use an already packed
  * combinational consumer of these reads to prove a lane layout and discover
  * other same-layout fanout consumers.
  */
private final case class ICTRegisterReadLane(
  updateNodeId:  Int,
  registerName: String,
  width:        Int
)

private final case class ICTRegisterReadConsumer(
  consumerNodeId: Int,
  argumentIndex:  Int
)

private final class MutableICTStats {
  var phase1Packs = 0
  var phase2Packs = 0
  var boundaryPacks = 0
  var indexedBoundaryCandidates = 0
  var indexedBoundaryPacks = 0
  var indexedBoundaryNodes = 0
  var useDefCandidates = 0
  var defUseCandidates = 0
  var exactConcatMerges = 0
  var dataflowReuseRejects = 0
  var stoppedNarrowPackExpansions = 0
  var stateTransitionCandidates = 0
  var stateTransitionPacks = 0
  var priorSeedCandidates = 0
  var priorSeedPacks = 0
  var priorSeedNodes = 0
  var localInstanceEquivCandidates = 0
  var localInstanceEquivPacks = 0
  var localInstanceEquivNodes = 0
  var seedCandidates = 0
  var rejectSingleton = 0
  var rejectDuplicate = 0
  var rejectShape = 0
  var rejectLevel = 0
  var rejectModuleNet = 0
  var rejectWidth = 0
  var rejectDependency = 0
  var rejectAlreadyPacked = 0
}

private sealed trait ICTNormalizeRejectReason
private object ICTNormalizeRejectReason {
  case object Singleton extends ICTNormalizeRejectReason
  case object Unsupported extends ICTNormalizeRejectReason
  case object Duplicate extends ICTNormalizeRejectReason
  case object AlreadyPacked extends ICTNormalizeRejectReason
  case object Shape extends ICTNormalizeRejectReason
  case object Level extends ICTNormalizeRejectReason
  case object Module extends ICTNormalizeRejectReason
  case object Width extends ICTNormalizeRejectReason
  case object Dependency extends ICTNormalizeRejectReason
}

/** Instance-correspondence-aware discovery matching the original ICTPacker.
  *
  * Combinational statements and RegUpdate statements share one candidate set,
  * one occupied-node set, and one use-def/def-use worklist. RegUpdate is split
  * into a state layout only after discovery; it never enters the current-cycle
  * combinational PackGraph.
  */
final class ICTPacker(
  context: SlpAnalysisContext,
  ictConfig: ICTPackerConfig = ICTPackerConfig()
) extends SlpPacker {
  override val name: String = "ict"

  private val config = context.config
  private val view = context.graph
  private val levels = view.levels.toOption.getOrElse(
    throw new IllegalArgumentException("ICTPacker requires an acyclic graph")
  )
  private val classifiedOperations = context.classifications.collect {
    case (nodeId, SlpSupported(operation)) => nodeId -> operation
  }.toMap
  private val regions = SlpRegionBuilder.build(context)
  private val operationOverrides = regions.iterator.map(region =>
    region.rootNodeId -> region.operation
  ).toMap
  private val absorbedNodeIds = regions.iterator.flatMap(_.internalNodeIds).toSet
  private val operations = (classifiedOperations ++ operationOverrides) -- absorbedNodeIds
  private val stats = new MutableICTStats
  private val packed = mutable.BitSet.empty
  private val phase1 = mutable.ArrayBuffer.empty[SlpPack]
  private val phase2 = mutable.ArrayBuffer.empty[SlpPack]
  private val phase1Groups = mutable.ArrayBuffer.empty[Vector[Int]]
  private val phase2Groups = mutable.ArrayBuffer.empty[Vector[Int]]
  private val regUpdateLayouts = mutable.ArrayBuffer.empty[SlpRegUpdateLayout]
  private val stateTransitionProposals = mutable.ArrayBuffer.empty[SlpStateTransitionProposal]

  private def referenceName(expression: Expression): Option[String] = expression match {
    case Reference(name, _, _, _)   => Some(name)
    case SubField(base, name, _, _) => referenceName(base).map(prefix => s"$prefix.$name")
    case SubIndex(base, index, _, _) => referenceName(base).map(prefix => s"${prefix}_$index")
    case _                          => None
  }

  private def uintWidth(expression: Expression): Option[Int] = expression.tpe match {
    case UIntType(IntWidth(width)) if width > 0 && width.isValidInt => Some(width.toInt)
    case _                                                         => None
  }

  private def legacyOpType(operation: SlpOperation): String = operation.statement match {
    case _ if operation.opcode == SlpTruncatingAdd => "TruncatingAdd"
    case _ if operation.opcode == SlpTruncatingSub => "TruncatingSub"
    case _: Connect => "Connect"
    case DefNode(_, _, _: Mux) => "Mux"
    case DefNode(_, _, DoPrim(op, _, _, _)) => op match {
      case And            => "And"
      case Or             => "Or"
      case Xor            => "Xor"
      case Not            => "Not"
      case Eq             => "Eq"
      case ArmorBitSelect => "BitSelect"
      case ArmorIdentity  => "SelfAssign"
      case ArmorAnd =>
        if (operation.resultWidth > operation.operands.head.width) "Pad2And" else "And2"
      case _ => operation.opcode.name
    }
    case _: DefNode => "Assign"
    case _          => operation.opcode.name
  }

  private def combinationalMetadata(nodeId: Int, operation: SlpOperation): ICTNodeMetadata = {
    val discoveryStorageWidth = operation.storageWidth
    ICTNodeMetadata(
      nodeId,
      ICTCombinational(operation),
      ICTStmtShape(
        legacyOpType(operation),
        operation.resultWidth,
        // Every backend stage shares the classifier's one-word lane footprint:
        // max(result width, runtime signal operand widths). Constants do not
        // occupy a packed runtime word.
        discoveryStorageWidth,
        "UIntType",
        operation.operandWidths
      ),
      view.node(nodeId).name,
      operation.operands,
      operation.resultWidth,
      discoveryStorageWidth
    )
  }

  private def regUpdateMetadata(nodeId: Int, update: RegUpdate): Option[ICTNodeMetadata] =
    for {
      registerName <- referenceName(update.regRef)
      sourceName <- referenceName(update.expr)
      resultWidth <- uintWidth(update.regRef)
      sourceWidth <- uintWidth(update.expr)
      if resultWidth <= config.machineWidth
    } yield ICTNodeMetadata(
      nodeId,
      ICTRegisterUpdate(registerName),
      ICTStmtShape("RegUpdate", resultWidth, resultWidth, "UIntType", Vector(sourceWidth)),
      // The old metadata result is the register name, while the graph node is
      // named register$final. Keep that distinction for def-use discovery.
      registerName,
      Vector(SlpSignal(sourceName, sourceWidth)),
      resultWidth,
      resultWidth
    )

  private val metadataByNodeId: Map[Int, ICTNodeMetadata] = view.validNodeIds.flatMap { nodeId =>
    operations.get(nodeId).map(operation => combinationalMetadata(nodeId, operation)).orElse {
      view.node(nodeId).statement match {
        case update: RegUpdate => regUpdateMetadata(nodeId, update)
        case _                 => None
      }
    }.map(nodeId -> _)
  }.toMap

  private val candidateNodeIds: Vector[Int] = view.validNodeIds.filter { nodeId =>
    metadataByNodeId.contains(nodeId) && view.node(nodeId).module.nonEmpty
  }

  /** A RegUpdate is a temporal edge, rather than a current-cycle graph edge.
    * Keep this index separate from fanin/fanout so phase-2 only crosses it by
    * the explicit, lane-preserving rule in stateTransitionCandidates.
    */
  private val regUpdatesByRegisterName: Map[String, Vector[Int]] =
    metadataByNodeId.iterator.collect {
      case (nodeId, ICTNodeMetadata(_, _: ICTRegisterUpdate, _, registerName, _, _, _)) =>
        registerName -> nodeId
    }.toVector.groupMap(_._1)(_._2).view.mapValues(_.sorted).toMap

  private def registerReadLane(signal: SlpSignal): Option[ICTRegisterReadLane] =
    regUpdatesByRegisterName.get(signal.name).collect {
      case Vector(updateNodeId)
          if metadataByNodeId.get(updateNodeId).exists(_.resultWidth == signal.width) &&
            view.node(updateNodeId).module.nonEmpty =>
        ICTRegisterReadLane(updateNodeId, signal.name, signal.width)
    }

  private val registerReadConsumersByName: Map[String, Vector[ICTRegisterReadConsumer]] =
    candidateNodeIds.flatMap { consumerId =>
      operations.get(consumerId).toVector.flatMap { operation =>
        operation.operands.zipWithIndex.collect {
          case (signal: SlpSignal, argumentIndex) if registerReadLane(signal).nonEmpty =>
            signal.name -> ICTRegisterReadConsumer(consumerId, argumentIndex)
        }
      }
    }.groupMap(_._1)(_._2).view.mapValues(_.distinct.sortBy(consumer =>
      (levelOf(consumer.consumerNodeId), consumer.argumentIndex, consumer.consumerNodeId)
    )).toMap

  private val debugRegReadSeedRegex =
    Option(System.getenv("ARMOR_SLP_DEBUG_REG_READ_SEED"))
      .filter(_.nonEmpty)
      .flatMap(pattern => scala.util.Try(pattern.r).toOption)

  private def debugRegReadSeedEnabled(text: String): Boolean =
    debugRegReadSeedRegex.exists(_.findFirstIn(text).nonEmpty)

  private def debugRegReadSeed(message: => String): Unit =
    if (debugRegReadSeedRegex.nonEmpty) Console.err.println(message)

  private def isCandidate(nodeId: Int): Boolean = metadataByNodeId.contains(nodeId) &&
    view.node(nodeId).valid && view.node(nodeId).module.nonEmpty
  private def metadata(nodeId: Int): ICTNodeMetadata = metadataByNodeId(nodeId)
  private def levelOf(nodeId: Int): Int = levels.levelOf(nodeId).get
  private def shapeOf(nodeId: Int): ICTStmtShape = metadata(nodeId).shape
  private def packKeyOf(nodeId: Int): ICTPackKey = metadata(nodeId).kind match {
    case ICTCombinational(operation) =>
      ICTPackKey(shapeOf(nodeId), operation.opcode.packSemanticParameters(operation.parameters))
    case _: ICTRegisterUpdate        => ICTPackKey(shapeOf(nodeId), Vector.empty)
  }
  private def moduleNetOf(nodeId: Int): Option[SlpModuleNet] =
    view.node(nodeId).module.map(location =>
      SlpModuleNet(location.moduleName, view.node(nodeId).localNetName)
    )
  private def instancePathOf(nodeId: Int): String =
    view.node(nodeId).module.map(_.instancePath).getOrElse("")

  private def localInstanceFamilyName(moduleName: String): String =
    moduleName.replaceFirst("_[0-9]+$", "")

  private val armorExprTempPattern = "^_armor_expr(_[0-9]+)?$".r
  private val maxLocalTempInlineDepth = 8

  private def isArmorExprTemp(localName: String): Boolean =
    armorExprTempPattern.pattern.matcher(localName).matches()

  private val localIndexPattern = "\\d+".r

  private def indexedNameKey(localName: String): ICTIndexedNameKey = {
    val canonical = localIndexPattern.replaceAllIn(localName, "#")
    ICTIndexedNameKey(canonical, canonical != localName)
  }

  private def relativeToInstance(fullName: String, instancePath: String): Option[String] = {
    if (instancePath.nonEmpty && fullName.startsWith(instancePath + "."))
      Some(fullName.stripPrefix(instancePath + "."))
    else if (instancePath.isEmpty)
      Some(fullName)
    else
      None
  }

  private def sameInstance(nodeId: Int, instancePath: String): Boolean =
    view.node(nodeId).module.exists(_.instancePath == instancePath)

  private def operandEquivKey(
    operand: SlpOperand,
    currentInstancePath: String,
    depth: Int
  ): ICTOperandEquivKey = operand match {
    case SlpUIntConstant(value, width) =>
      ICTConstOperandKey(width, value)

    case signal @ SlpSignal(name, width) =>
      relativeToInstance(name, currentInstancePath) match {
        case Some(localName) if isArmorExprTemp(localName) && depth < maxLocalTempInlineDepth =>
          signalProducer(signal) match {
            case Some(producerId)
                if operations.contains(producerId) &&
                  sameInstance(producerId, currentInstancePath) &&
                  view.node(producerId).isPure =>
              tempExprEquivKey(producerId, currentInstancePath, depth + 1)
                .map(ICTInlineTempOperandKey)
                .getOrElse(ICTLocalSignalOperandKey(width, localName))
            case _ =>
              ICTLocalSignalOperandKey(width, localName)
          }

        case Some(localName) =>
          ICTLocalSignalOperandKey(width, localName)

        case None =>
          ICTExternalSignalOperandKey(width, name)
      }
  }

  private def tempExprEquivKey(
    nodeId: Int,
    currentInstancePath: String,
    depth: Int
  ): Option[ICTTempExprKey] = {
    if (depth > maxLocalTempInlineDepth) return None
    if (!operations.contains(nodeId)) return None
    if (!sameInstance(nodeId, currentInstancePath)) return None
    if (!view.node(nodeId).isPure) return None

    val operation = operations(nodeId)
    Some(ICTTempExprKey(
      opcode = operation.opcode.name,
      resultWidth = operation.resultWidth,
      storageWidth = operation.storageWidth,
      parameters = operation.opcode.packSemanticParameters(operation.parameters),
      operands = operation.operands.map(operand =>
        operandEquivKey(operand, currentInstancePath, depth + 1)
      )
    ))
  }

  private def localEquivKeyOf(nodeId: Int): Option[ICTLocalEquivKey] = {
    val node = view.node(nodeId)
    if (isArmorExprTemp(node.localNetName)) {
      node.module.flatMap(location =>
        tempExprEquivKey(nodeId, location.instancePath, depth = 0)
      )
    } else {
      Some(ICTNamedLocalKey(node.localNetName))
    }
  }

  private def localInstanceEquivKeyOf(nodeId: Int): Option[ICTLocalInstanceEquivKey] =
    for {
      location <- view.node(nodeId).module
      localKey <- localEquivKeyOf(nodeId)
    } yield ICTLocalInstanceEquivKey(
      moduleFamily = localInstanceFamilyName(location.moduleName),
      localKey = localKey,
      packKey = packKeyOf(nodeId),
      level = levelOf(nodeId)
    )

  private def indexedOperandKey(
    operand: SlpOperand,
    currentInstancePath: String,
    depth: Int
  ): ICTIndexedOperandKey = operand match {
    case SlpUIntConstant(value, width) =>
      ICTIndexedConstOperandKey(width, value)

    case signal @ SlpSignal(name, width) =>
      relativeToInstance(name, currentInstancePath) match {
        case Some(localName) if isArmorExprTemp(localName) && depth < maxLocalTempInlineDepth =>
          signalProducer(signal) match {
            case Some(producerId)
                if operations.contains(producerId) &&
                  sameInstance(producerId, currentInstancePath) &&
                  view.node(producerId).isPure =>
              indexedTempExprKey(producerId, currentInstancePath, depth + 1)
                .map(ICTIndexedInlineTempOperandKey)
                .getOrElse {
                  val key = indexedNameKey(localName)
                  ICTIndexedLocalSignalOperandKey(width, key.value, key.indexed)
                }
            case _ =>
              val key = indexedNameKey(localName)
              ICTIndexedLocalSignalOperandKey(width, key.value, key.indexed)
          }

        case Some(localName) =>
          val key = indexedNameKey(localName)
          ICTIndexedLocalSignalOperandKey(width, key.value, key.indexed)

        case None =>
          ICTIndexedExternalSignalOperandKey(width, name)
      }
  }

  private def indexedTempExprKey(
    nodeId: Int,
    currentInstancePath: String,
    depth: Int
  ): Option[ICTIndexedExprKey] = {
    if (depth > maxLocalTempInlineDepth) return None
    if (!operations.contains(nodeId)) return None
    if (!sameInstance(nodeId, currentInstancePath)) return None
    if (!view.node(nodeId).isPure) return None

    val operation = operations(nodeId)
    Some(ICTIndexedExprKey(
      opcode = operation.opcode.name,
      resultWidth = operation.resultWidth,
      storageWidth = operation.storageWidth,
      parameters = operation.opcode.packSemanticParameters(operation.parameters),
      operands = operation.operands.map(operand =>
        indexedOperandKey(operand, currentInstancePath, depth + 1)
      )
    ))
  }

  private def indexedBoundaryKeyOf(nodeId: Int): Option[ICTIndexedBoundaryKey] =
    for {
      location <- view.node(nodeId).module
      operation <- operations.get(nodeId)
    } yield {
      val result = indexedNameKey(view.node(nodeId).localNetName)
      val operands = operation.operands.map(operand =>
        indexedOperandKey(operand, location.instancePath, depth = 0)
      )
      ICTIndexedBoundaryKey(
        instancePath = location.instancePath,
        moduleName = location.moduleName,
        level = levelOf(nodeId),
        packKey = packKeyOf(nodeId),
        resultFamily = result.value,
        resultIndexed = result.indexed,
        operands = operands
      )
    }

  private def sameIndexedBoundaryFamily(nodeIds: Vector[Int]): Boolean = {
    val keys = nodeIds.flatMap(indexedBoundaryKeyOf)
    keys.size == nodeIds.size &&
      keys.nonEmpty &&
      keys.head.hasIndexedComponent &&
      keys.map(_.sortKey).distinct.size == 1
  }

  /** OptSLP.orderPack sorts only by instance. The subsequent seed reorder is
    * by the complete statement name and must happen after width splitting.
    */
  private def orderPack(nodeIds: Vector[Int]): Vector[Int] =
    nodeIds.distinct.sortBy(nodeId => (instancePathOf(nodeId), nodeId))

  private def reorderByStmtName(nodeIds: Vector[Int]): Vector[Int] =
    nodeIds.sortBy(nodeId => (view.node(nodeId).name, nodeId))

  private def signalProducer(signal: SlpSignal): Option[Int] =
    view.graph.nameToID.get(signal.name).filter(isCandidate)

  private def operandProducer(operand: SlpOperand): Option[Int] = operand match {
    case signal: SlpSignal  => signalProducer(signal)
    case _: SlpUIntConstant => None
  }

  private def consumerOperandProducer(consumerId: Int, argumentIndex: Int): Option[Int] =
    metadata(consumerId).operands.lift(argumentIndex).flatMap(operandProducer)

  private def operandMatchesProducer(
    consumerId: Int,
    argumentIndex: Int,
    producerId: Int
  ): Boolean = {
    view.faninIds(consumerId).contains(producerId) &&
      consumerOperandProducer(consumerId, argumentIndex).contains(producerId)
  }

  private def hasInternalDependency(nodeIds: Vector[Int]): Boolean = {
    val members = nodeIds.toSet
    nodeIds.exists(nodeId =>
      view.faninIds(nodeId).exists(members) || view.fanoutIds(nodeId).exists(members)
    )
  }

  /** Capacity is checked independently at every materialized boundary. This
    * avoids using one opcode-dependent width as a proxy for input, transient
    * computation, and output layouts.
    */
  private def fitsPackedBoundaries(nodeIds: Vector[Int]): Boolean = {
    if (nodeIds.isEmpty) return true
    val nodeMetadata = nodeIds.map(metadata)
    val outputFits = nodeMetadata.map(_.resultWidth).sum <= config.machineWidth
    val argumentCount = nodeMetadata.map(_.operands.size).distinct match {
      case Vector(count) => count
      case _             => return false
    }
    val inputsFit = (0 until argumentCount).forall { argumentIndex =>
      val operands = nodeMetadata.map(_.operands(argumentIndex))
      !operands.exists(_.isInstanceOf[SlpSignal]) ||
        operands.map(_.width).sum <= config.machineWidth
    }
    outputFits && inputsFit
  }

  /**
    * Phase-1 seed partitioning must account for the degree that the later
    * retention filter requires, preferring a complete degree-aware partition.
    */
  private def splitByWidthAndDegree(nodeIds: Vector[Int]): Vector[Vector[Int]] = {
    val minDegree = config.minParallelDegree
    SlpWidthDegreePartitioner
      .partition(nodeIds, minDegree, fitsPackedBoundaries)
      .chunks
  }

  private def balancedSplit(nodeIds: Vector[Int], parts: Int): Vector[Vector[Int]] = {
    require(parts > 0)
    val size = nodeIds.size
    (0 until parts).map { index =>
      val begin = (index * size) / parts
      val end = ((index + 1) * size) / parts
      nodeIds.slice(begin, end)
    }.toVector
  }

  private def averageWidthSplitCandidate(
    candidate: Vector[Int],
    source: Vector[Int],
    globalPacked: mutable.BitSet,
    localUsed: Option[mutable.BitSet],
    requireModuleNet: Boolean
  ): Option[Vector[Vector[Int]]] = {
    val minDegree = config.minParallelDegree
    val maxParts = candidate.size / minDegree
    if (maxParts < 2) None
    else {
      (2 to maxParts).iterator.flatMap { parts =>
        val chunks = balancedSplit(candidate, parts)
        if (chunks.exists(_.size < minDegree)) None
        else {
          val normalized = chunks.map(chunk =>
            normalizeCandidateWithReason(
              chunk,
              source,
              globalPacked,
              localUsed,
              requireModuleNet,
              countStats = false
            )
          )
          Option.when(normalized.forall(_.isRight))(
            normalized.collect { case Right(chunk) => chunk }
          )
        }
      }.toSeq.headOption
    }
  }

  private def sameExpansionRegion(source: Vector[Int], candidate: Vector[Int]): Boolean = {
    if (ictConfig.allowCrossModulePipeline || source.isEmpty) return true
    val sourceModule = moduleNetOf(source.head).map(_.moduleName)
    sourceModule.nonEmpty && candidate.forall(nodeId =>
      moduleNetOf(nodeId).map(_.moduleName) == sourceModule
    )
  }

  private def recordNormalizeReject(reason: ICTNormalizeRejectReason): Unit = reason match {
    case ICTNormalizeRejectReason.Singleton     => stats.rejectSingleton += 1
    case ICTNormalizeRejectReason.Duplicate     => stats.rejectDuplicate += 1
    case ICTNormalizeRejectReason.AlreadyPacked => stats.rejectAlreadyPacked += 1
    case ICTNormalizeRejectReason.Shape         => stats.rejectShape += 1
    case ICTNormalizeRejectReason.Level         => stats.rejectLevel += 1
    case ICTNormalizeRejectReason.Module        => stats.rejectModuleNet += 1
    case ICTNormalizeRejectReason.Width         => stats.rejectWidth += 1
    case ICTNormalizeRejectReason.Dependency    => stats.rejectDependency += 1
    case ICTNormalizeRejectReason.Unsupported   =>
  }

  private def normalizeReject(
    reason: ICTNormalizeRejectReason,
    countStats: Boolean
  ): Left[ICTNormalizeRejectReason, Vector[Int]] = {
    if (countStats) recordNormalizeReject(reason)
    Left(reason)
  }

  private def normalizeCandidateWithReason(
    rawNodeIds: Vector[Int],
    source: Vector[Int],
    globalPacked: mutable.BitSet,
    localUsed: Option[mutable.BitSet],
    requireModuleNet: Boolean,
    countStats: Boolean = true
  ): Either[ICTNormalizeRejectReason, Vector[Int]] = {
    if (rawNodeIds.size < config.minParallelDegree)
      return normalizeReject(ICTNormalizeRejectReason.Singleton, countStats)
    if (rawNodeIds.exists(nodeId => !isCandidate(nodeId)))
      return normalizeReject(ICTNormalizeRejectReason.Unsupported, countStats)
    if (rawNodeIds.distinct.size != rawNodeIds.size)
      return normalizeReject(ICTNormalizeRejectReason.Duplicate, countStats)
    if (rawNodeIds.exists(globalPacked))
      return normalizeReject(ICTNormalizeRejectReason.AlreadyPacked, countStats)
    if (localUsed.exists(used => rawNodeIds.exists(used)))
      return normalizeReject(ICTNormalizeRejectReason.AlreadyPacked, countStats)
    if (rawNodeIds.map(packKeyOf).distinct.size != 1)
      return normalizeReject(ICTNormalizeRejectReason.Shape, countStats)
    if (rawNodeIds.map(levelOf).distinct.size != 1)
      return normalizeReject(ICTNormalizeRejectReason.Level, countStats)
    val moduleNets = rawNodeIds.flatMap(moduleNetOf)
    if (requireModuleNet &&
        (moduleNets.size != rawNodeIds.size || moduleNets.distinct.size != 1))
      return normalizeReject(ICTNormalizeRejectReason.Module, countStats)
    if (!sameExpansionRegion(source, rawNodeIds))
      return normalizeReject(ICTNormalizeRejectReason.Module, countStats)
    if (!fitsPackedBoundaries(rawNodeIds))
      return normalizeReject(ICTNormalizeRejectReason.Width, countStats)
    if (hasInternalDependency(rawNodeIds))
      return normalizeReject(ICTNormalizeRejectReason.Dependency, countStats)
    Right(rawNodeIds)
  }

  /** This is the original ICT normalizeCandidate contract. It does not mutate
    * either occupied set; the caller commits a whole phase-1 region at once.
    */
  private def normalizeCandidate(
    rawNodeIds: Vector[Int],
    source: Vector[Int],
    globalPacked: mutable.BitSet,
    localUsed: Option[mutable.BitSet],
    requireModuleNet: Boolean
  ): Option[Vector[Int]] =
    normalizeCandidateWithReason(
      rawNodeIds, source, globalPacked, localUsed, requireModuleNet
    ).toOption

  private def useDefCandidates(source: Vector[Int]): Vector[Vector[Int]] = {
    val sourceMetadata = source.map(metadata)
    val argumentCount = sourceMetadata.map(_.operands.size).minOption.getOrElse(0)
    (0 until argumentCount).flatMap { argumentIndex =>
      val laneProducers = sourceMetadata.zipWithIndex.flatMap { case (nodeMetadata, laneIndex) =>
        operandProducer(nodeMetadata.operands(argumentIndex)).map(laneIndex -> _)
      }
      laneProducers.groupBy { case (_, producerId) =>
        (packKeyOf(producerId), levelOf(producerId))
      }.values.toVector.flatMap {
        members =>
          val laneCount = members.map(_._1).distinct.size
          val ordered = members.sortBy(_._1).map(_._2).distinct.toVector
          if (ordered.size >= config.minParallelDegree && ordered.size == laneCount &&
              (ictConfig.allowDefUsePackSizeMismatch || ordered.size == source.size)) Some(ordered)
          else None
      }
    }.toVector
  }

  private def defUseCandidates(source: Vector[Int]): Vector[Vector[Int]] = {
    val grouped = mutable.HashMap.empty[ICTConsumerKey, mutable.HashMap[Int, Vector[Int]]]
    source.zipWithIndex.foreach { case (producerId, laneIndex) =>
      view.validFanoutIds(producerId).filter(isCandidate).foreach { consumerId =>
        metadata(consumerId).operands.zipWithIndex.foreach {
          case (_: SlpSignal, argumentIndex) if operandMatchesProducer(consumerId, argumentIndex, producerId) =>
            val key = ICTConsumerKey(packKeyOf(consumerId), argumentIndex, levelOf(consumerId))
            val lanes = grouped.getOrElseUpdate(key, mutable.HashMap.empty)
            lanes.update(
              laneIndex,
              (lanes.getOrElse(laneIndex, Vector.empty) :+ consumerId).distinct.sorted
            )
          case _ =>
        }
      }
    }
    val result = grouped.values.toVector.flatMap { laneMap =>
      val laneIndices = laneMap.keys.toVector.sorted
      val fullSize = laneIndices.size == source.size
      if (laneIndices.size < config.minParallelDegree ||
          (!ictConfig.allowDefUsePackSizeMismatch && !fullSize)) Vector.empty
      else if (!ictConfig.allowMultiSuccessorExpansion &&
          laneIndices.exists(index => laneMap(index).size > 1)) Vector.empty
      else {
        val ordinalCount = laneIndices.map(index => laneMap(index).size).minOption.getOrElse(0)
        (0 until ordinalCount).flatMap { ordinal =>
          val candidate = laneIndices.map(index => laneMap(index)(ordinal))
          if (candidate.distinct.size == candidate.size) Some(candidate) else None
        }.toVector
      }
    }
    result
  }

  private def registerReadConsumerCandidates(
    regLanes: Vector[ICTRegisterReadLane]
  ): Vector[Vector[Int]] = {
    if (regLanes.isEmpty ||
        regLanes.map(_.updateNodeId).distinct.size != regLanes.size ||
        regLanes.map(_.registerName).distinct.size != regLanes.size ||
        regLanes.map(_.width).sum > config.machineWidth) return Vector.empty

    val debugThisSeed =
      debugRegReadSeedRegex.exists { regex =>
        regLanes.exists(lane => regex.findFirstIn(lane.registerName).nonEmpty)
      }
    if (debugThisSeed) {
      debugRegReadSeed(
        s"[armor-slp-debug-reg-read-seed] seed lanes=${regLanes.size} " +
          s"width=${regLanes.map(_.width).sum} " +
          s"registers=${regLanes.map(_.registerName).mkString(";")}"
      )
    }

    val grouped = mutable.HashMap.empty[ICTConsumerKey, mutable.HashMap[Int, Vector[Int]]]
    regLanes.zipWithIndex.foreach { case (regLane, laneIndex) =>
      val consumers = registerReadConsumersByName.getOrElse(regLane.registerName, Vector.empty)
      if (debugThisSeed) {
        debugRegReadSeed(
          s"[armor-slp-debug-reg-read-seed]   lane=$laneIndex " +
            s"reg=${regLane.registerName} width=${regLane.width} consumers=${consumers.size}"
        )
      }
      consumers.foreach {
        consumer =>
          val consumerId = consumer.consumerNodeId
          val consumerName = view.node(consumerId).name
          if (debugThisSeed || debugRegReadSeedEnabled(consumerName)) {
            debugRegReadSeed(
              s"[armor-slp-debug-reg-read-seed]     consumer node=$consumerId " +
                s"arg=${consumer.argumentIndex} level=${levelOf(consumerId)} " +
                s"name=$consumerName key=${packKeyOf(consumerId).sortKey}"
            )
          }
          if (!packed(consumerId)) {
            val operands = metadata(consumerId).operands
            operands.lift(consumer.argumentIndex) match {
              case Some(SlpSignal(name, width))
                  if name == regLane.registerName && width == regLane.width =>
                val key = ICTConsumerKey(
                  packKeyOf(consumerId),
                  consumer.argumentIndex,
                  levelOf(consumerId)
                )
                val byLane = grouped.getOrElseUpdate(key, mutable.HashMap.empty)
                byLane.update(
                  laneIndex,
                  (byLane.getOrElse(laneIndex, Vector.empty) :+ consumerId).distinct.sorted
                )
              case _ =>
            }
          }
      }
    }

    if (debugThisSeed) {
      grouped.toVector.sortBy { case (key, _) => key.sortKey }.foreach { case (key, laneMap) =>
        debugRegReadSeed(
          s"[armor-slp-debug-reg-read-seed]   group lanes=${laneMap.keys.toVector.sorted.mkString(",")} " +
            s"arg=${key.argumentIndex} level=${key.level} key=${key.packKey.sortKey}"
        )
      }
    }

    grouped.toVector.sortBy { case (key, _) => key.sortKey }.flatMap { case (_, laneMap) =>
      val laneIndices = laneMap.keys.toVector.sorted
      val fullSize = laneIndices.size == regLanes.size
      if (laneIndices.size < config.minParallelDegree ||
          !fullSize ||
          (!ictConfig.allowMultiSuccessorExpansion &&
            laneIndices.exists(index => laneMap(index).size > 1))) Vector.empty
      else {
        val ordinalCount = laneIndices.map(index => laneMap(index).size).minOption.getOrElse(0)
        (0 until ordinalCount).flatMap { ordinal =>
          val candidate = laneIndices.map(index => laneMap(index)(ordinal))
          if (candidate.distinct.size == candidate.size) Some(candidate) else None
        }.toVector
      }
    }
  }

  /** Treat a discovered RegUpdate layout as a current-state register-read
    * layout witness.
    *
    * RegUpdate nodes are not current-cycle PackGraph producers, but their
    * register names and widths define the exact packed state lanes that later
    * register materialization will use.  Converting them to ICTRegisterReadLane
    * lets ordinary phase-2 consumer discovery reuse the same validation and
    * grouping logic as combinational pack expansion.
    */
  private def regReadLanesFromRegUpdateLayout(
    layout: SlpRegUpdateLayout
  ): Option[Vector[ICTRegisterReadLane]] = {
    val lanes = layout.updateNodeIds.map { updateNodeId =>
      metadataByNodeId.get(updateNodeId).collect {
        case ICTNodeMetadata(
              _,
              ICTRegisterUpdate(registerName),
              _,
              _,
              _,
              registerWidth,
              _
            ) =>
          ICTRegisterReadLane(updateNodeId, registerName, registerWidth)
      }
    }

    if (!lanes.forall(_.nonEmpty)) None
    else {
      val resolved = lanes.flatten
      val valid =
        resolved.map(_.updateNodeId).distinct.size == resolved.size &&
        resolved.map(_.registerName).distinct.size == resolved.size &&
        resolved.map(_.width).sum <= config.machineWidth
      Option.when(valid)(resolved)
    }
  }

  /** Cross one strictly controlled sequential boundary.
    *
    * Given a packed combinational consumer with an argument consisting of
    * corresponding current-state registers, find the unique RegUpdate for
    * every lane and offer its next-expression producers as a phase-2 group.
    * This does not add a graph edge between r and r$next: the candidate is
    * discovered only after every lane proves the same state-transition shape.
    */
  private def stateTransitionCandidates(source: Vector[Int]): Vector[ICTStateTransitionCandidate] = {
    if (source.isEmpty || !source.forall(nodeId =>
      metadata(nodeId).kind.isInstanceOf[ICTCombinational]
    )) return Vector.empty

    val sourceMetadata = source.map(metadata)
    val argumentCount = sourceMetadata.map(_.operands.size).distinct match {
      case Vector(count) => count
      case _             => return Vector.empty
    }

    (0 until argumentCount).flatMap { argumentIndex =>
      val transitions = sourceMetadata.map(_.operands(argumentIndex)).map {
        case SlpSignal(registerName, registerWidth) =>
          regUpdatesByRegisterName.get(registerName).collect {
            case Vector(updateNodeId)
                if metadata(updateNodeId).resultWidth == registerWidth =>
              view.node(updateNodeId).statement match {
                case update: RegUpdate =>
                  referenceName(update.expr)
                    .flatMap(view.graph.nameToID.get)
                    .filter(isCandidate)
                    .map(nextNodeId => updateNodeId -> nextNodeId)
                case _ => None
              }
          }.flatten
        case _ => None
      }
      if (transitions.forall(_.nonEmpty)) {
        val pairs = transitions.flatten
        val updateNodeIds = pairs.map(_._1)
        val nextNodeIds = pairs.map(_._2)
        if (updateNodeIds.distinct.size == updateNodeIds.size &&
            nextNodeIds.distinct.size == nextNodeIds.size) {
          Some(ICTStateTransitionCandidate(nextNodeIds, updateNodeIds))
        } else None
      } else None
    }.toVector
  }

  /** Seed phase 2 directly from a register's next-state Mux when normal
    * combinational use-def traversal has stopped at the current-state read.
    *
    * A candidate must be a self-feedback Mux: one value arm is precisely the
    * register updated by this RegUpdate.  The register read remains a state
    * leaf; this method never introduces a current-cycle graph edge through
    * the sequential boundary.  Once a group is accepted,
    * addStateTransitionCandidate atomically records both the Mux pack and
    * its exact RegUpdate layout, so scalar reassembly is never introduced.
    */
  private def stateTransitionSeedCandidates(): Vector[ICTStateTransitionCandidate] = {
    final case class SeedKey(
      nextShape: ICTStmtShape,
      nextLevel: Int,
      updateLevel: Int,
      registerFamily: String,
      conditionFamily: String,
      incomingFamily: String,
      selfArm: Int
    )
    final case class SeedLane(updateNodeId: Int, nextNodeId: Int, key: SeedKey)

    // Array indices in flattened Gemmini nets are represented as decimal
    // runs.  Removing only those runs gives a stable family key without
    // treating every local net in a parent module as a singleton.
    def signalFamily(name: String): String = name.replaceAll("\\d+", "#")
    def operandFamily(operand: SlpOperand): String = operand match {
      case SlpSignal(name, width)       => s"signal:$width:${signalFamily(name)}"
      case SlpUIntConstant(value, width) => s"constant:$width:$value"
    }

    val lanes = metadataByNodeId.iterator.flatMap {
      case (updateNodeId, ICTNodeMetadata(
            _, ICTRegisterUpdate(registerName), _, _, _, registerWidth, _
          )) =>
        view.node(updateNodeId).statement match {
          case update: RegUpdate =>
            referenceName(update.expr).flatMap(view.graph.nameToID.get)
              .filter(isCandidate).flatMap { nextNodeId =>
                operations.get(nextNodeId).filter(_.opcode == SlpMux).flatMap { mux =>
                  val selfArms = mux.operands.zipWithIndex.collect {
                    case (SlpSignal(name, width), arm)
                        if arm > 0 && name == registerName && width == registerWidth => arm
                  }
                  if (selfArms.size == 1 && mux.operands.size == 3) {
                    val selfArm = selfArms.head
                    val incomingArm = if (selfArm == 1) 2 else 1
                    Some(SeedLane(
                      updateNodeId,
                      nextNodeId,
                      SeedKey(
                        shapeOf(nextNodeId),
                        levelOf(nextNodeId),
                        levelOf(updateNodeId),
                        signalFamily(registerName),
                        operandFamily(mux.operands.head),
                        operandFamily(mux.operands(incomingArm)),
                        selfArm
                      )
                    ))
                  } else None
                }
              }
          case _ => None
        }
      case _ => None
    }.toVector

    lanes.groupBy(_.key).values.toVector.flatMap { group =>
      val byNextNodeId = group.map(lane => lane.nextNodeId -> lane).toMap
      val available = orderPack(group.map(_.nextNodeId).distinct.toVector).filterNot(packed)
      splitByWidthAndDegree(available).flatMap { nextNodeIds =>
        val updateNodeIds = nextNodeIds.map(byNextNodeId(_).updateNodeId)
        Option.when(
          nextNodeIds.size >= config.minParallelDegree &&
            updateNodeIds.distinct.size == updateNodeIds.size
        )(ICTStateTransitionCandidate(nextNodeIds, updateNodeIds))
      }
    }.sortBy(candidate => candidate.nextNodeIds.map(nodeId => view.node(nodeId).name).mkString("\\u0000"))
  }

  private def appendDiscoveredGroup(
    nodeIds: Vector[Int],
    target: mutable.ArrayBuffer[SlpPack],
    groups: mutable.ArrayBuffer[Vector[Int]],
    discoveryPhase: String
  ): Unit = {
    groups += nodeIds
    metadata(nodeIds.head).kind match {
      case _: ICTCombinational =>
        require(nodeIds.forall(id => metadata(id).kind.isInstanceOf[ICTCombinational]))
        val firstOperation = operations(nodeIds.head)
        val locations = nodeIds.map(nodeId => view.node(nodeId).module)
        val commonLocation = locations.flatten.distinct match {
          case Vector(location) if locations.forall(_.contains(location)) => Some(location)
          case _                                                          => None
        }
        val moduleNets = nodeIds.flatMap(moduleNetOf).distinct
        target += SlpPack(
          id = phase1.size + phase2.size,
          shape = SlpPackShape.from(firstOperation),
          lanes = nodeIds.map { nodeId =>
            val operation = operations(nodeId)
            SlpLane(nodeId, operation.resultWidth, operation.storageWidth)
          },
          level = levelOf(nodeIds.head),
          module = commonLocation,
          laneLocations = locations,
          moduleNet = if (moduleNets.size == 1) moduleNets.headOption else None,
          discoveryPhase = Some(discoveryPhase)
        )
      case _: ICTRegisterUpdate =>
        require(nodeIds.forall(id => metadata(id).kind.isInstanceOf[ICTRegisterUpdate]))
        val sourceNodeIds = nodeIds.map { nodeId =>
          metadata(nodeId).operands.head match {
            case SlpSignal(sourceName, _) => view.graph.nameToID.getOrElse(sourceName, nodeId)
            case _ => nodeId
          }
        }
        regUpdateLayouts += SlpRegUpdateLayout(nodeIds, sourceNodeIds, discoveryPhase)
    }
  }

  /** The original phase-1 grows a local region, then commits every node in the
    * region to the global occupied set. This ordering affects later seeds.
    */
  private def growPhase1Region(seed: Vector[Int]): Vector[Vector[Int]] = {
    val localUsed = mutable.BitSet.empty
    val result = mutable.ArrayBuffer.empty[Vector[Int]]
    val queue = mutable.Queue.empty[Vector[Int]]
    val visited = mutable.HashSet.empty[Vector[Int]]

    def addCandidate(
      candidate: Vector[Int],
      source: Vector[Int],
      phaseName: String = "phase2"
    ): Unit = {
      normalizeCandidate(candidate, source, packed, Some(localUsed), requireModuleNet = true).foreach {
        normalized =>
          val signature = normalized.sorted
          if (!visited(signature)) {
            visited += signature
            queue.enqueue(normalized)
            result += normalized
            localUsed ++= normalized
          }
      }
    }

    addCandidate(seed, seed)
    while (queue.nonEmpty) {
      val source = queue.dequeue()
      if (source.size >= config.minParallelDegree) {
        useDefCandidates(source).foreach { candidate =>
          stats.useDefCandidates += 1
          addCandidate(candidate, source)
        }
        defUseCandidates(source).foreach { candidate =>
          stats.defUseCandidates += 1
          addCandidate(candidate, source)
        }
      } else {
        stats.stoppedNarrowPackExpansions += 1
      }
    }
    result.toVector
  }

  private def buildPhase1(): Unit = {
    val statementsByLevel = candidateNodeIds.groupBy(levelOf)
    statementsByLevel.foreach { case (_, statements) =>
      val groups = statements.groupBy { nodeId =>
        val moduleNet = moduleNetOf(nodeId).get
        ((moduleNet.moduleName, moduleNet.localNetName), packKeyOf(nodeId))
      }.values
      groups.foreach { statementsInGroup =>
        val available = orderPack(statementsInGroup).filterNot(packed)
        splitByWidthAndDegree(available).foreach { basePack =>
          stats.seedCandidates += 1
          if (basePack.size < config.minParallelDegree) stats.rejectSingleton += 1
          else {
            val region = growPhase1Region(reorderByStmtName(basePack))
            if (region.nonEmpty) {
              region.foreach { group =>
                require(!group.exists(packed), "ICT phase1 region overlaps a committed pack")
                packed ++= group
                appendDiscoveredGroup(group, phase1, phase1Groups, "phase1")
              }
            }
          }
        }
      }
    }
    stats.phase1Packs = phase1Groups.size
  }

  private def buildLocalInstanceEquivSeeds(): Unit = {
    if (!ictConfig.enableLocalInstanceEquivalence) return

    def hasMultipleConcreteModules(nodeIds: Vector[Int]): Boolean =
      nodeIds.flatMap(nodeId => view.node(nodeId).module.map(_.moduleName)).distinct.size >= 2

    def splitByInstanceOccurrence(nodeIds: Vector[Int]): Vector[Vector[Int]] = {
      val byInstance = orderPack(nodeIds).groupBy(instancePathOf).toVector.map {
        case (instancePath, ids) => instancePath -> ids.sortBy(nodeId => (view.node(nodeId).name, nodeId))
      }.sortBy(_._1)
      val maxOccurrences = byInstance.map(_._2.size).maxOption.getOrElse(0)
      (0 until maxOccurrences).map { occurrence =>
        byInstance.flatMap { case (_, ids) => ids.lift(occurrence) }.toVector
      }.toVector
    }

    val groups = candidateNodeIds
      .filterNot(packed)
      .filter(operations.contains)
      .flatMap { nodeId =>
        localInstanceEquivKeyOf(nodeId).map(_ -> nodeId)
      }
      .groupBy(_._1)
      .toVector
      .sortBy { case (key, _) => key.sortKey }

    groups.foreach { case (_, entries) =>
      val available = entries.map(_._2).toVector.filterNot(packed)
      splitByInstanceOccurrence(available).foreach { occurrenceGroup =>
        val ordered = orderPack(occurrenceGroup).filterNot(packed)
        if (hasMultipleConcreteModules(ordered)) {
          splitByWidthAndDegree(ordered).foreach { basePack =>
          stats.localInstanceEquivCandidates += 1
            if (basePack.size < config.minParallelDegree || !hasMultipleConcreteModules(basePack)) {
              stats.rejectSingleton += 1
            } else {
              normalizeCandidate(
                basePack,
                Vector.empty,
                packed,
                None,
                requireModuleNet = false
              ).foreach { normalized =>
                packed ++= normalized
                appendDiscoveredGroup(
                  normalized,
                  phase1,
                  phase1Groups,
                  "local_instance_equiv"
                )
                stats.localInstanceEquivPacks += 1
                stats.localInstanceEquivNodes += normalized.size
              }
            }
          }
        }
      }
    }
    stats.phase1Packs = phase1Groups.size
  }

  /** Seed intra-instance bit-slice families which the normal ICT phase-1 key
    * cannot see.  Generic phase-1 deliberately groups identical local nets
    * across replicated instances; here `_T_24 ... _T_31` are distinct local
    * nets in one instance, but are equivalent unary operations over distinct
    * bits of the same source word.
    *
    * Keep this restricted to Not(bit_select(source, bit)) so it is a
    * structural fact rather than a name-based heuristic.  Phase-2 can then
    * grow ordinary corresponding consumers from the accepted Not pack.
    */
  private def buildBitSliceSeeds(): Unit = {
    final case class BitSliceSeedKey(
      instancePath: String,
      sourceName: String,
      sourceWidth: Int,
      shape: ICTStmtShape,
      level: Int
    )
    final case class BitSliceLane(nodeId: Int, bitPosition: Int)

    val candidates = candidateNodeIds.filterNot(packed).flatMap { nodeId =>
      operations.get(nodeId).collect {
        case operation @ SlpOperation(
              SlpNot, 1, _, Vector(SlpSignal(bitName, 1)), _, _
            ) =>
          view.graph.nameToID.get(bitName).flatMap(operations.get).collect {
            case SlpOperation(
                  SlpBitSelect, 1, _, Vector(SlpSignal(sourceName, sourceWidth)),
                  Vector(bitPosition), _
                )
                if sourceWidth <= config.machineWidth &&
                  bitPosition >= 0 && bitPosition < sourceWidth =>
              BitSliceSeedKey(
                instancePathOf(nodeId), sourceName, sourceWidth, shapeOf(nodeId), levelOf(nodeId)
              ) -> BitSliceLane(nodeId, bitPosition.toInt)
          }
      }.flatten
    }

    candidates.groupBy(_._1).toVector.sortBy { case (key, _) =>
      (key.instancePath, key.sourceName, key.level, key.shape.sortKey)
    }.foreach { case (_, keyedLanes) =>
      val lanes = keyedLanes.map(_._2).sortBy(lane => (lane.bitPosition, view.node(lane.nodeId).name))
      // Multiple Not nodes selecting one source bit are not a lane family:
      // accepting them would duplicate a lane in the packed result.
      if (lanes.map(_.bitPosition).distinct.size == lanes.size) {
        splitByWidthAndDegree(lanes.map(_.nodeId)).foreach { nodeIds =>
          if (nodeIds.size >= config.minParallelDegree) {
            normalizeCandidate(
              nodeIds, Vector.empty, packed, None, requireModuleNet = false
            ).foreach { normalized =>
              packed ++= normalized
              appendDiscoveredGroup(normalized, phase1, phase1Groups, "bit_slice")
            }
          }
        }
      }
    }
    stats.phase1Packs = phase1Groups.size
  }

  /** Insert trusted domain seeds after generic Phase-1 ownership has been
    * established and before Phase-2 boundary expansion starts. */
  private def buildPriorSeeds(): Unit = {
    if (!ictConfig.enableGemminiReservationStationPrior) return

    val seeds = GemminiReservationStationPrior.discover(
      candidateNodeIds.filterNot(packed),
      operations,
      levelOf,
      nodeId => view.node(nodeId).module,
      view.graph.nameToID.toMap
    )
    seeds.foreach { seed =>
      stats.priorSeedCandidates += 1
      // Local `_issue_valids_T_*` names intentionally differ lane-to-lane;
      // the prior has already proved a common ReservationStation instance.
      normalizeCandidate(seed.nodeIds, Vector.empty, packed, None, requireModuleNet = false).foreach {
        normalized =>
          packed ++= normalized
          appendDiscoveredGroup(normalized, phase1, phase1Groups, seed.discoveryPhase)
          stats.priorSeedPacks += 1
          stats.priorSeedNodes += normalized.size
      }
    }
    stats.phase1Packs = phase1Groups.size
  }

  /** Discover consumers of an already-packed producer as ordinary packs.
    *
    * Phase-1 ownership can legitimately pack a producer before the scalar
    * shape seeding reaches its fanout.  Constant comparisons are then left as
    * unpack -> scalar compare -> pack even though every lane has an exact
    * source correspondence.  This forward pass restores that correspondence
    * without introducing an opcode-specific plan: the discovered consumer is
    * a normal compare pack and AlignPlanner resolves the signal operand as
    * SlpDirectPackInput.
    */
  private def buildForwardConstantCompareConsumers(): Unit = {
    final case class ForwardCompareKey(
      opcode:         SlpOpcode,
      signalArgument: Int,
      signalWidth:    Int,
      constantWidth:  Int,
      constantValue:  BigInt
    )

    val sourcePacks = phase1.toVector.filter(pack =>
      pack.parallelDegree >= config.minParallelDegree
    )
    sourcePacks.foreach { sourcePack =>
      val candidatesByKey = sourcePack.nodeIds.zipWithIndex.flatMap { case (sourceNodeId, laneIndex) =>
        view.validFanoutIds(sourceNodeId).flatMap { consumerNodeId =>
          if (packed(consumerNodeId)) None
          else operations.get(consumerNodeId).collect {
            case operation @ SlpOperation(
                SlpEqConst, 1, _,
                Vector(SlpSignal(signalName, signalWidth), SlpUIntConstant(constant, constantWidth)),
                _, _
              ) if view.graph.nameToID.get(signalName).contains(sourceNodeId) &&
                  signalWidth == constantWidth &&
                  signalWidth == sourcePack.lanes(laneIndex).resultWidth &&
                  constant < (BigInt(1) << signalWidth) =>
              val key = ForwardCompareKey(SlpEqConst, 0, signalWidth, constantWidth, constant)
              Some(key, laneIndex, consumerNodeId)

            case operation @ SlpOperation(
                SlpGeq, 1, _,
                Vector(SlpSignal(signalName, signalWidth), SlpUIntConstant(constant, constantWidth)),
                _, _
              ) if view.graph.nameToID.get(signalName).contains(sourceNodeId) &&
                  signalWidth == constantWidth &&
                  signalWidth == sourcePack.lanes(laneIndex).resultWidth &&
                  constant < (BigInt(1) << signalWidth) =>
              val key = ForwardCompareKey(SlpGeq, 0, signalWidth, constantWidth, constant)
              Some(key, laneIndex, consumerNodeId)

            case operation @ SlpOperation(
                SlpGeq, 1, _,
                Vector(SlpUIntConstant(constant, constantWidth), SlpSignal(signalName, signalWidth)),
                _, _
              ) if view.graph.nameToID.get(signalName).contains(sourceNodeId) &&
                  signalWidth == constantWidth &&
                  signalWidth == sourcePack.lanes(laneIndex).resultWidth &&
                  constant < (BigInt(1) << signalWidth) =>
              val key = ForwardCompareKey(SlpGeq, 1, signalWidth, constantWidth, constant)
              Some(key, laneIndex, consumerNodeId)

            case operation @ SlpOperation(
                SlpLt, 1, _,
                Vector(SlpSignal(signalName, signalWidth), SlpUIntConstant(constant, constantWidth)),
                _, _
              ) if view.graph.nameToID.get(signalName).contains(sourceNodeId) &&
                  signalWidth == constantWidth &&
                  signalWidth == sourcePack.lanes(laneIndex).resultWidth &&
                  constant < (BigInt(1) << signalWidth) =>
              val key = ForwardCompareKey(SlpLt, 0, signalWidth, constantWidth, constant)
              Some(key, laneIndex, consumerNodeId)

            case operation @ SlpOperation(
                SlpLt, 1, _,
                Vector(SlpUIntConstant(constant, constantWidth), SlpSignal(signalName, signalWidth)),
                _, _
              ) if view.graph.nameToID.get(signalName).contains(sourceNodeId) &&
                  signalWidth == constantWidth &&
                  signalWidth == sourcePack.lanes(laneIndex).resultWidth &&
                  constant < (BigInt(1) << signalWidth) =>
              val key = ForwardCompareKey(SlpLt, 1, signalWidth, constantWidth, constant)
              Some(key, laneIndex, consumerNodeId)

            case operation @ SlpOperation(
                SlpNeq, 1, _,
                Vector(SlpSignal(signalName, signalWidth), SlpUIntConstant(constant, constantWidth)),
                _, _
              ) if view.graph.nameToID.get(signalName).contains(sourceNodeId) &&
                  signalWidth == constantWidth &&
                  signalWidth == sourcePack.lanes(laneIndex).resultWidth &&
                  constant < (BigInt(1) << signalWidth) =>
              val key = ForwardCompareKey(SlpNeq, 0, signalWidth, constantWidth, constant)
              Some(key, laneIndex, consumerNodeId)

            case operation @ SlpOperation(
                SlpNeq, 1, _,
                Vector(SlpUIntConstant(constant, constantWidth), SlpSignal(signalName, signalWidth)),
                _, _
              ) if view.graph.nameToID.get(signalName).contains(sourceNodeId) &&
                  signalWidth == constantWidth &&
                  signalWidth == sourcePack.lanes(laneIndex).resultWidth &&
                  constant < (BigInt(1) << signalWidth) =>
              val key = ForwardCompareKey(SlpNeq, 1, signalWidth, constantWidth, constant)
              Some(key, laneIndex, consumerNodeId)
          }
        }
      }.flatten.groupBy(_._1)

      candidatesByKey.toVector.sortBy { case (key, _) =>
        (key.opcode.name, key.signalArgument, key.signalWidth, key.constantWidth, key.constantValue)
      }.foreach { case (key, candidates) =>
        val byLane = candidates.groupBy(_._2)
        val complete = sourcePack.lanes.indices.forall(index => byLane.get(index).exists(_.size == 1))
        if (complete) {
          val consumers = sourcePack.lanes.indices.map(index => byLane(index).head._3).toVector
          // A forward consumer must remain an independent lane family. This
          // prevents one compare node shared by multiple source lanes from being
          // consumed twice and preserves the direct source order exactly.
          if (consumers.distinct.size == consumers.size) {
            // Preserve the producer's lane order.  Re-sorting by instance here
            // would still create a compare pack, but would sever the exact
            // source-pack layout required by SlpDirectPackInput.
            normalizeCandidate(
              consumers,
              sourcePack.nodeIds,
              packed,
              None,
              requireModuleNet = false
            ).foreach { normalized =>
              packed ++= normalized
              appendDiscoveredGroup(normalized, phase1, phase1Groups, s"forward_${key.opcode.name}_const")
            }
          }
        }
      }
    }
    stats.phase1Packs = phase1Groups.size
  }

  /** Boundary-driven indexed-local discovery.
    *
    * Generic phase-1 proves real dataflow boundaries first.  This stage only
    * inspects the ordinary use-def / def-use candidates reachable from those
    * boundaries, and accepts a candidate when exact local-name equality is the
    * only missing correspondence: local numeric runs are canonicalized to a
    * family marker (`idle_7` -> `idle_#`, `beatsLeft_7` -> `beatsLeft_#`).
    *
    * This deliberately is not a global name-family scan.  Every accepted pack
    * remains anchored to an existing phase-1 boundary and then goes through
    * the normal normalize, width, ownership, and dependency checks.
    */
  private def buildIndexedBoundaryExpansion(): Unit = {
    if (!ictConfig.enableIndexedBoundaryExpansion) return

    val boundaries = findBoundaryGroups()
    val queue = mutable.Queue.empty[(Vector[Int], Boolean, Boolean)]
    val visited = mutable.HashSet.empty[Vector[Int]]

    boundaries.foreach { boundary =>
      val signature = boundary.nodeIds.sorted
      if (!visited(signature)) {
        visited += signature
        queue.enqueue((boundary.nodeIds, boundary.hasUnpackedFanin, boundary.hasUnpackedFanout))
      }
    }

    def commit(normalized: Vector[Int], phaseName: String): Unit = {
      val signature = normalized.sorted
      if (!visited(signature)) {
        visited += signature
        packed ++= normalized
        appendDiscoveredGroup(normalized, phase1, phase1Groups, phaseName)
        queue.enqueue((normalized, true, true))
        stats.indexedBoundaryPacks += 1
        stats.indexedBoundaryNodes += normalized.size
      }
    }

    def tryAccept(
      candidate: Vector[Int],
      source: Vector[Int],
      phaseName: String
    ): Unit = {
      stats.indexedBoundaryCandidates += 1
      normalizeCandidateWithReason(
        candidate,
        source,
        packed,
        None,
        requireModuleNet = false
      ) match {
        case Right(normalized) if sameIndexedBoundaryFamily(normalized) =>
          commit(normalized, phaseName)

        case Right(_) =>

        case Left(ICTNormalizeRejectReason.Width) =>
          averageWidthSplitCandidate(
            candidate,
            source,
            packed,
            None,
            requireModuleNet = false
          ).foreach { chunks =>
            chunks.foreach { chunk =>
              if (sameIndexedBoundaryFamily(chunk)) commit(chunk, s"${phaseName}_split")
            }
          }

        case Left(_) =>
      }
    }

    while (queue.nonEmpty) {
      val (source, hasUnpackedFanin, hasUnpackedFanout) = queue.dequeue()
      if (source.size >= config.minParallelDegree) {
        if (hasUnpackedFanin) {
          useDefCandidates(source).foreach { candidate =>
            tryAccept(candidate, source, "indexed_boundary_use_def")
          }
        }
        if (hasUnpackedFanout) {
          defUseCandidates(source).foreach { candidate =>
            tryAccept(candidate, source, "indexed_boundary_def_use")
          }
        }
      }
    }
    stats.phase1Packs = phase1Groups.size
  }

  private def isOutsideCandidate(nodeId: Int): Boolean = isCandidate(nodeId) && !packed(nodeId)

  private def findBoundaryGroups(): Vector[ICTBoundaryGroup] = {
    val boundaries = phase1Groups.flatMap { group =>
      val hasUnpackedFanin = group.exists(nodeId =>
        view.validFaninIds(nodeId).exists(isOutsideCandidate)
      )
      val hasUnpackedFanout = group.exists(nodeId =>
        view.validFanoutIds(nodeId).exists(isOutsideCandidate)
      )
      if (hasUnpackedFanin || hasUnpackedFanout)
        Some(ICTBoundaryGroup(group, hasUnpackedFanin, hasUnpackedFanout))
      else None
    }.toVector
    stats.boundaryPacks = boundaries.size
    boundaries
  }

  /** Phase 2 uses one queue seeded with every phase-1 boundary, exactly like
    * the original implementation. Newly accepted groups occupy nodes at once.
    */
  private def buildPhase2(): Unit = {
    val boundaries = findBoundaryGroups()
    if (!ictConfig.enablePhase2) return
    val queue = mutable.Queue.empty[(Vector[Int], Boolean, Boolean)]
    val visited = mutable.HashSet.empty[Vector[Int]]
    boundaries.foreach { boundary =>
      val signature = boundary.nodeIds.sorted
      if (!visited(signature)) {
        visited += signature
        queue.enqueue((boundary.nodeIds, boundary.hasUnpackedFanin, boundary.hasUnpackedFanout))
      }
    }

    def acceptPhase2Candidate(normalized: Vector[Int], phaseName: String): Unit = {
      val signature = normalized.sorted
      if (!visited(signature)) {
        if (normalized.exists(nodeId => debugRegReadSeedEnabled(view.node(nodeId).name))) {
          debugRegReadSeed(
            s"[armor-slp-debug-reg-read-seed] accept phase=$phaseName " +
              s"nodes=${normalized.map(nodeId => s"${nodeId}:${view.node(nodeId).name}").mkString(";")}"
          )
        }
        visited += signature
        packed ++= normalized
        appendDiscoveredGroup(normalized, phase2, phase2Groups, phaseName)
        queue.enqueue((normalized, true, true))
      } else if (normalized.exists(nodeId => debugRegReadSeedEnabled(view.node(nodeId).name))) {
        debugRegReadSeed(
          s"[armor-slp-debug-reg-read-seed] skip-visited phase=$phaseName " +
            s"nodes=${normalized.map(nodeId => s"${nodeId}:${view.node(nodeId).name}").mkString(";")}"
        )
      }
    }

    def addCandidate(
      candidate: Vector[Int],
      source: Vector[Int],
      phaseName: String = "phase2"
    ): Unit = {
      val debugThisCandidate =
        candidate.exists(nodeId => debugRegReadSeedEnabled(view.node(nodeId).name))
      // Phase-2 first preserves the complete discovered correspondence.  If
      // the only rejection is that the full boundary is wider than one machine
      // word, fall back to average contiguous chunks.  All chunks are validated
      // before any chunk is committed, so discovery never observes a
      // half-split candidate.
      normalizeCandidateWithReason(
        candidate, source, packed, None, requireModuleNet = false, countStats = false
      ) match {
        case Right(normalized) =>
          if (debugThisCandidate) {
            debugRegReadSeed(
              s"[armor-slp-debug-reg-read-seed] normalize-ok phase=$phaseName " +
                s"raw=${candidate.map(nodeId => s"${nodeId}:${view.node(nodeId).name}").mkString(";")} " +
                s"normalized=${normalized.map(nodeId => s"${nodeId}:${view.node(nodeId).name}").mkString(";")}"
            )
          }
          acceptPhase2Candidate(normalized, phaseName)
        case Left(ICTNormalizeRejectReason.Width) =>
          averageWidthSplitCandidate(
            candidate, source, packed, None, requireModuleNet = false
          ) match {
            case Some(chunks) if chunks.forall(chunk => !visited(chunk.sorted)) =>
              if (debugThisCandidate) {
                debugRegReadSeed(
                  s"[armor-slp-debug-reg-read-seed] normalize-width-split phase=$phaseName " +
                    s"chunks=${chunks.map(chunk => chunk.map(nodeId => s"${nodeId}:${view.node(nodeId).name}").mkString("[", ";", "]")).mkString(";")}"
                )
              }
              chunks.foreach(chunk => acceptPhase2Candidate(chunk, s"${phaseName}_split"))
            case _ =>
              if (debugThisCandidate) {
                debugRegReadSeed(
                  s"[armor-slp-debug-reg-read-seed] reject phase=$phaseName reason=Width " +
                    s"nodes=${candidate.map(nodeId => s"${nodeId}:${view.node(nodeId).name}").mkString(";")}"
                )
              }
              recordNormalizeReject(ICTNormalizeRejectReason.Width)
          }
        case Left(reason) =>
          if (debugThisCandidate) {
            debugRegReadSeed(
              s"[armor-slp-debug-reg-read-seed] reject phase=$phaseName reason=$reason " +
                s"nodes=${candidate.map(nodeId => s"${nodeId}:${view.node(nodeId).name}").mkString(";")}"
            )
          }
          recordNormalizeReject(reason)
      }
    }

    var processedRegUpdateReadSeedLayouts = 0
    def seedFromRegUpdateReadLayouts(): Unit = {
      if (!ictConfig.enableRegUpdateReadSeedDiscovery) return

      while (processedRegUpdateReadSeedLayouts < regUpdateLayouts.size) {
        val layout = regUpdateLayouts(processedRegUpdateReadSeedLayouts)
        processedRegUpdateReadSeedLayouts += 1

        regReadLanesFromRegUpdateLayout(layout).foreach { regLanes =>
          registerReadConsumerCandidates(regLanes).foreach { candidate =>
            stats.defUseCandidates += 1
            addCandidate(candidate, Vector.empty, "phase2_reg_update_read_seed")
          }
        }
      }
    }

    /** Commit next expressions and their terminal RegUpdate layout as one
      * state-aware phase-2 step. RegUpdate is deliberately not a PackGraph
      * node, but appendDiscoveredGroup records it for SlpRegUpdatePacker.
      */
    def addStateTransitionCandidate(candidate: ICTStateTransitionCandidate, source: Vector[Int]): Unit = {
      val next = normalizeCandidate(
        candidate.nextNodeIds, source, packed, None, requireModuleNet = false
      )
      val updates = normalizeCandidate(
        candidate.updateNodeIds, source, packed, None, requireModuleNet = false
      )
      for {
        normalizedNext <- next
        normalizedUpdates <- updates
        if !visited(normalizedNext.sorted)
      } {
        visited += normalizedNext.sorted
        packed ++= normalizedNext
        appendDiscoveredGroup(normalizedNext, phase2, phase2Groups, "phase2")
        packed ++= normalizedUpdates
        appendDiscoveredGroup(normalizedUpdates, phase2, phase2Groups, "phase2")
        stats.stateTransitionPacks += 1
        queue.enqueue((normalizedNext, true, true))
      }
    }

    // Preserve self-feedback state Muxes as phase-3 proposals.  Committing
    // them here would reserve their nodes before normal ICT discovery and can
    // force a wide state layout that is incompatible with retained consumers.
    stateTransitionSeedCandidates().foreach { candidate =>
      stats.stateTransitionCandidates += 1
      stateTransitionProposals += SlpStateTransitionProposal(
        candidate.nextNodeIds,
        candidate.updateNodeIds
      )
    }

    seedFromRegUpdateReadLayouts()

    while (queue.nonEmpty) {
      val (source, expandUseDef, expandDefUse) = queue.dequeue()
      if (source.size >= config.minParallelDegree) {
        stateTransitionCandidates(source).foreach { candidate =>
          stats.stateTransitionCandidates += 1
          addStateTransitionCandidate(candidate, source)
        }
        if (expandUseDef) useDefCandidates(source).foreach { candidate =>
          stats.useDefCandidates += 1
          addCandidate(candidate, source)
        }
        if (expandDefUse) defUseCandidates(source).foreach { candidate =>
          stats.defUseCandidates += 1
          addCandidate(candidate, source)
        }
      } else {
        stats.stoppedNarrowPackExpansions += 1
      }
      seedFromRegUpdateReadLayouts()
    }
    stats.phase2Packs = phase2Groups.size
  }

  private def alignCost(source: SlpPack, destination: SlpPack): Int = {
    val sourceNames = source.nodeIds.map(nodeId => view.node(nodeId).name)
    val destinationOps = destination.nodeIds.map(operations)
    destinationOps.head.operands.indices.count { argumentIndex =>
      val operands = destinationOps.map(_.operands(argumentIndex)).collect {
        case SlpSignal(name, _) => name
      }
      operands.exists(sourceNames.contains) && operands != sourceNames
    }
  }

  private def mergeExactConcat(rawPacks: Vector[SlpPack]): Vector[SlpPack] = {
    if (!ictConfig.enableExactConcatMerge) return rawPacks
    var active = rawPacks
    var changed = true
    while (changed) {
      changed = false
      val packByNode = active.flatMap(pack => pack.nodeIds.map(_ -> pack.id)).toMap
      val edges = active.flatMap { source =>
        source.nodeIds.flatMap(view.validFanoutIds).flatMap(packByNode.get)
          .filter(_ != source.id).distinct.map(source.id -> _)
      }.distinct
      val groups = active.groupBy(pack => (pack.level, pack.moduleNet, pack.shape)).values
      val candidate = groups.toVector.flatMap(_.sortBy(_.id).combinations(2)).collectFirst {
        case Vector(left, right)
            if fitsPackedBoundaries(left.nodeIds ++ right.nodeIds) &&
              !hasInternalDependency(left.nodeIds ++ right.nodeIds) =>
          val pairIds = Set(left.id, right.id)
          val before = edges.filter(edge => pairIds(edge._1) || pairIds(edge._2))
            .map { case (src, dst) =>
              alignCost(active.find(_.id == src).get, active.find(_.id == dst).get)
            }.sum
          val merged = left.copy(
            lanes = left.lanes ++ right.lanes,
            laneLocations = left.laneLocations ++ right.laneLocations
          )
          val afterNeighbors = edges.flatMap { case (src, dst) =>
            val newSrc = if (pairIds(src)) left.id else src
            val newDst = if (pairIds(dst)) left.id else dst
            if (newSrc == newDst) None else Some(newSrc -> newDst)
          }.distinct
          val temporary = active.filterNot(_.id == right.id).map {
            case pack if pack.id == left.id => merged
            case pack                       => pack
          }
          val afterById = temporary.map(pack => pack.id -> pack).toMap
          val after = afterNeighbors.filter(edge => edge._1 == left.id || edge._2 == left.id)
            .map { case (src, dst) => alignCost(afterById(src), afterById(dst)) }.sum
          if (after <= before + 1) Some(left.id, right.id, merged)
          else {
            stats.dataflowReuseRejects += 1
            None
          }
      }.flatten
      candidate.foreach { case (leftId, rightId, merged) =>
        active = active.filterNot(_.id == rightId).map {
          case pack if pack.id == leftId => merged
          case pack                      => pack
        }.sortBy(_.id).zipWithIndex.map { case (pack, id) => pack.copy(id = id) }
        stats.exactConcatMerges += 1
        changed = true
      }
    }
    active
  }

  private def makeStats(packs: Vector[SlpPack]): SlpPackStats = {
    val resultBits = packs.map(_.totalResultWidth).sum
    val storageBits = packs.map(_.totalStorageWidth).sum
    val capacity = packs.size * config.machineWidth
    SlpPackStats(
      graphNodes = view.graph.numNodes(),
      validNodes = context.stats.validNodes,
      supportedNodes = context.stats.supportedNodes,
      // SlpPackStats describes materializable combinational packs. RegUpdate
      // participates in ICT discovery but is reported by SlpRegPackStats.
      candidateNodes = candidateNodeIds.count(operations.contains),
      seedCandidates = stats.seedCandidates,
      acceptedPacks = packs.size,
      pipelinePacks = phase2.size,
      packedNodes = packs.map(_.parallelDegree).sum,
      useDefCandidates = stats.useDefCandidates,
      defUseCandidates = stats.defUseCandidates,
      rejectedSingleton = stats.rejectSingleton,
      rejectedDuplicate = stats.rejectDuplicate,
      rejectedUnsupported = context.stats.unsupportedNodes,
      rejectedShape = stats.rejectShape,
      rejectedLevel = stats.rejectLevel,
      rejectedModule = stats.rejectModuleNet,
      rejectedWidth = stats.rejectWidth,
      rejectedDependency = stats.rejectDependency,
      rejectedAlreadyPacked = stats.rejectAlreadyPacked,
      opcodeHistogram = packs.groupBy(_.shape.opcode.name).toVector.map {
        case (opcode, values) => opcode -> values.size
      }.sortBy(_._1),
      parallelDegreeHistogram = packs.groupBy(_.parallelDegree).toVector.map {
        case (degree, values) => degree -> values.size
      }.sortBy(_._1),
      resultUtilization = if (capacity == 0) 0.0 else resultBits.toDouble / capacity,
      storageUtilization = if (capacity == 0) 0.0 else storageBits.toDouble / capacity
    )
  }

  override def run(): SlpPackingResult = {
    buildPhase1()
    buildIndexedBoundaryExpansion()
    buildLocalInstanceEquivSeeds()
    buildBitSliceSeeds()
    buildPriorSeeds()
    buildForwardConstantCompareConsumers()
    buildPhase2()
    val raw = (phase1 ++ phase2).toVector.sortBy(_.id).zipWithIndex.map {
      case (pack, id) => pack.copy(id = id)
    }
    val packs = mergeExactConcat(raw)
    if (debugRegReadSeedRegex.nonEmpty) {
      val debugNodeIds = view.validNodeIds.filter(nodeId =>
        debugRegReadSeedEnabled(view.node(nodeId).name)
      ).toSet
      if (debugNodeIds.nonEmpty) {
        def describe(label: String, values: Vector[SlpPack]): Unit = {
          val hits = values.filter(pack => pack.nodeIds.exists(debugNodeIds))
          debugRegReadSeed(
            s"[armor-slp-debug-reg-read-seed] $label hits=${hits.size} " +
              hits.map(pack =>
                s"id=${pack.id},phase=${pack.discoveryPhase.getOrElse("")},opcode=${pack.shape.opcode.name}," +
                  s"nodes=${pack.nodeIds.map(nodeId => s"${nodeId}:${view.node(nodeId).name}").mkString("[", ";", "]")}"
              ).mkString(" ")
          )
        }
        describe("phase1-final", phase1.toVector)
        describe("phase2-final", phase2.toVector)
        describe("raw-final", raw)
        describe("merged-final", packs)
      }
    }
    SlpPackingResult(
      name,
      packs,
      makeStats(packs),
      ICTDiagnostics(
        stats.phase1Packs,
        stats.phase2Packs,
        stats.boundaryPacks,
        stats.indexedBoundaryCandidates,
        stats.indexedBoundaryPacks,
        stats.indexedBoundaryNodes,
        stats.useDefCandidates,
        stats.defUseCandidates,
        stats.exactConcatMerges,
        stats.dataflowReuseRejects,
        stats.stoppedNarrowPackExpansions,
        stats.stateTransitionCandidates,
        stats.stateTransitionPacks,
        stats.priorSeedCandidates,
        stats.priorSeedPacks,
        stats.priorSeedNodes,
        stats.localInstanceEquivCandidates,
        stats.localInstanceEquivPacks,
        stats.localInstanceEquivNodes
      ),
      regUpdateLayouts.toVector,
      stateTransitionProposals.toVector,
      regions
    )
  }
}
