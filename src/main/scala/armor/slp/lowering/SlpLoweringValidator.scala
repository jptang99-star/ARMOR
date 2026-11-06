package armor.slp

final case class SlpLoweringRejection(originalPackId: Int, reason: String) {
  require(originalPackId >= 0)
  require(reason.nonEmpty)
}

final case class SlpLoweringValidation(
  result:     SlpPackingResult,
  rejections: Vector[SlpLoweringRejection]
) {
  require(result.packs.map(_.id) == result.packs.indices.toVector)
  require(rejections == rejections.sortBy(_.originalPackId))
}

/** Pre-emission validation for the portable Phase-4 lowering.
  *
  * A rejected pack is removed as a whole. Its original statements therefore
  * remain scalar fallback nodes when PackGraph and SlpPlan are rebuilt.
  */
object SlpLoweringValidator {
  private val supportedOpcodes: Set[SlpOpcode] =
    Set(SlpAdd, SlpTruncatingAdd, SlpTruncatingSub, SlpAnd, SlpOr, SlpXor, SlpNot, SlpMove, SlpCat,
      SlpMaskedAnd, SlpBitSelect, SlpBits, SlpBitGather, SlpEq, SlpEqConst, SlpGeq, SlpLt, SlpNeq, SlpMux, SlpOrr, SlpAndr, SlpLeqLowMask,
      SlpLeqConst, SlpOneHot)

  private def isSupportedOpcode(opcode: SlpOpcode): Boolean = opcode match {
    case SlpShlConst(_) | SlpShrConst(_) | SlpDshrSmall(_, _) | SlpDshlSmall(_, _, _) => true
    case other          => supportedOpcodes(other)
  }

  private def bitCount(value: BigInt, width: Int): Int =
    (0 until width).count(bit => ((value >> bit) & 1) == 1)

  private def argumentOffsets(laneOperations: Vector[SlpOperation], argumentIndex: Int): Vector[Int] =
    laneOperations.map(_.operands(argumentIndex).width).scanLeft(0)(_ + _).dropRight(1)

  def validate(context: SlpAnalysisContext, discovered: SlpPackingResult): SlpLoweringValidation = {
    val classifiedOperations = context.classifications.collect {
      case (nodeId, SlpSupported(operation)) => nodeId -> operation
    }.toMap
    val operations = classifiedOperations ++ discovered.operationOverrides

    def validTruncatingSub(operation: SlpOperation): Boolean = operation match {
      case SlpOperation(SlpTruncatingSub, resultWidth, storageWidth, operands, parameters, _) =>
        resultWidth > 0 && resultWidth <= 63 && storageWidth == resultWidth &&
          parameters == Vector(BigInt(resultWidth + 1)) &&
          operands.size == 2 &&
          operands.exists(_.isInstanceOf[SlpSignal]) &&
          operands.forall {
            case SlpSignal(_, width) => width <= resultWidth
            case SlpUIntConstant(value, width) => value >= 0 && width <= resultWidth
          }
      case _ => false
    }

    def rejection(pack: SlpPack): Option[String] = {
      val laneOperations = pack.nodeIds.flatMap(operations.get)
      if (laneOperations.size != pack.parallelDegree)
        Some("one or more lanes have no supported operation")
      else if (!isSupportedOpcode(pack.shape.opcode))
        Some(s"unsupported opcode ${pack.shape.opcode.name}")
      else if (pack.totalStorageWidth > context.config.machineWidth)
        Some(s"storage width ${pack.totalStorageWidth} exceeds ${context.config.machineWidth}")
      else if (pack.totalResultWidth > context.config.machineWidth)
        Some(s"result width ${pack.totalResultWidth} exceeds ${context.config.machineWidth}")
      else if (laneOperations.exists(operation =>
        operation.opcode != pack.shape.opcode ||
          operation.resultWidth != pack.shape.resultWidth ||
          operation.storageWidth != pack.shape.storageWidth ||
          operation.operandWidths != pack.shape.operandWidths))
        Some("lane operation no longer matches its pack shape")
      else if (laneOperations.exists(_.operands.exists(_.width > 64)))
        Some("operand wider than portable uint64_t lowering")
      else if (pack.shape.operandWidths.indices.exists { argumentIndex =>
        val operands = laneOperations.map(_.operands(argumentIndex))
        operands.exists(_.isInstanceOf[SlpSignal]) &&
          operands.map(_.width).sum > context.config.machineWidth
      })
        Some("packed operand layout exceeds machine width")
      else pack.shape.opcode match {
        case SlpAdd if laneOperations.exists {
          case SlpOperation(SlpAdd, resultWidth, storageWidth,
              operands, parameters, _) =>
            operands.size != 2 || parameters.nonEmpty ||
              !operands.exists(_.isInstanceOf[SlpSignal]) ||
              resultWidth != operands.map(_.width).max + 1 ||
              storageWidth != resultWidth
          case _ => true
        } =>
          Some("Add requires two UInt operands, at least one signal, and a full-carry result")
        case SlpTruncatingAdd if laneOperations.exists {
          case SlpOperation(SlpTruncatingAdd, 16, 16,
              Vector(SlpSignal(_, 16), SlpUIntConstant(value, width)), parameters, _) =>
            value != 1 || width > 16 || parameters != Vector(BigInt(17))
          case _ => true
        } =>
          Some("truncating Add region requires UInt<16> + literal 1 with a low-16 result")
        case SlpTruncatingSub if laneOperations.exists(operation => !validTruncatingSub(operation)) =>
          Some("truncating Sub requires two low-width operands, at least one signal, and a low-width result")
        case SlpAnd | SlpOr | SlpXor if laneOperations.exists(_.operands.size != 2) =>
          Some("binary bit operation has invalid arity")
        case SlpCat if laneOperations.exists {
          case SlpOperation(SlpCat, resultWidth, storageWidth, Vector(high, low), parameters, _) =>
            parameters.nonEmpty || resultWidth != high.width + low.width || storageWidth != resultWidth
          case _ => true
        } =>
          Some("Cat requires two operands and a result width equal to hiWidth + loWidth")
        case SlpNot | SlpMove if laneOperations.exists(_.operands.size != 1) =>
          Some("unary bit operation has invalid arity")
        case SlpOrr if laneOperations.exists {
          case SlpOperation(SlpOrr, 1, storageWidth, Vector(SlpSignal(_, inputWidth)), parameters, _) =>
            inputWidth <= 1 || storageWidth != inputWidth || parameters.nonEmpty ||
              inputWidth > 64
          case _ => true
        } =>
          Some("Orr requires one UInt<2..64> signal and a UInt<1> result")
        case SlpAndr if laneOperations.exists {
          case SlpOperation(SlpAndr, 1, storageWidth, Vector(SlpSignal(_, inputWidth)), parameters, _) =>
            inputWidth <= 1 || storageWidth != inputWidth || parameters.nonEmpty ||
              inputWidth > 64
          case _ => true
        } =>
          Some("Andr requires one UInt<2..64> signal and a UInt<1> result")
        case SlpLeqLowMask if laneOperations.exists {
          case SlpOperation(SlpLeqLowMask, 1, storageWidth,
              Vector(SlpSignal(_, inputWidth)), Vector(allowedLowBits), _) =>
            storageWidth != inputWidth || allowedLowBits < 0 || allowedLowBits >= inputWidth
          case _ => true
        } =>
          Some("ArmorLeqLowMask requires one UInt signal, a UInt<1> result, and 0 <= K < input width")
        case SlpLeqConst if laneOperations.exists {
          case SlpOperation(SlpLeqConst, 1, storageWidth,
              Vector(SlpSignal(_, inputWidth)), Vector(constant), _) =>
            storageWidth != inputWidth || inputWidth < 2 || inputWidth > 17 ||
              constant < 0 || constant >= (BigInt(1) << inputWidth)
          case _ => true
        } || laneOperations.map(_.parameters).distinct.size != 1 =>
          Some("ArmorLeqConst requires same UInt<2..17> input width and constant across every lane")
        case SlpMaskedAnd if laneOperations.exists(_.operands.size != 2) =>
          Some("ArmorAnd has invalid arity")
        case SlpBitSelect if laneOperations.exists(operation =>
          operation.operands.size != 1 || operation.parameters.size != 1 ||
            operation.parameters.head < 0 || operation.parameters.head >= operation.operands.head.width) =>
          Some("ArmorBitSelect has an invalid bit position")
        case SlpBits if laneOperations.exists {
          case SlpOperation(SlpBits, resultWidth, storageWidth,
              Vector(SlpSignal(_, inputWidth)), Vector(hi, lo), _) =>
            lo < 0 || hi < lo || hi >= inputWidth ||
              resultWidth != hi - lo + 1 ||
              storageWidth != inputWidth ||
              inputWidth > 64 || resultWidth > 64
          case _ => true
        } || laneOperations.map(_.parameters).distinct.size != 1 =>
          Some("Bits requires same hi/lo across lanes, one UInt signal, and a UInt slice result")
        case SlpBitGather if laneOperations.exists {
          case SlpOperation(SlpBitGather, resultWidth, storageWidth,
              Vector(SlpSignal(_, inputWidth)), Vector(mask), _) =>
            mask <= 0 ||
              inputWidth <= 0 || inputWidth > 64 ||
              resultWidth <= 0 || resultWidth > 64 ||
              storageWidth != inputWidth ||
              (mask & ~((BigInt(1) << inputWidth) - 1)) != 0 ||
              bitCount(mask, inputWidth) != resultWidth
          case _ => true
        } || laneOperations.map(_.parameters).distinct.size != 1 =>
          Some("ArmorBitGather requires same mask across lanes, one UInt signal, and popcount(mask)=result width")
        case SlpShlConst(amount) if laneOperations.exists { operation =>
          operation.operands match {
            case Vector(SlpSignal(_, inputWidth)) =>
              operation.resultWidth != inputWidth + amount ||
                operation.storageWidth != operation.resultWidth ||
                operation.parameters != Vector(BigInt(amount))
            case _ => true
          }
        } =>
          Some("Shl requires one UInt signal and result width inputWidth + shiftAmount")
        case SlpShrConst(amount) if laneOperations.exists { operation =>
          operation.operands match {
            case Vector(SlpSignal(_, inputWidth)) =>
              amount <= 0 || amount >= inputWidth ||
                operation.resultWidth != inputWidth - amount ||
                operation.storageWidth != inputWidth ||
                operation.parameters != Vector(BigInt(amount))
            case _ => true
          }
            } =>
          Some("Shr requires one UInt signal, 0 < shiftAmount < inputWidth, and result width inputWidth - shiftAmount")
        case SlpDshrSmall(valueWidth, shiftWidth) if (shiftWidth < 1 || shiftWidth > 3) ||
            laneOperations.exists {
          case SlpOperation(SlpDshrSmall(opValueWidth, opShiftWidth), resultWidth, storageWidth,
              Vector(SlpSignal(_, inputWidth), shiftOperand), parameters, _) =>
            opValueWidth != valueWidth || opShiftWidth != shiftWidth ||
              inputWidth != valueWidth ||
              shiftOperand.width != shiftWidth ||
              resultWidth != valueWidth ||
              storageWidth != valueWidth ||
              parameters.nonEmpty
          case _ => true
        } ||
            pack.outputOffsets != laneOperations.indices.map(_ * valueWidth).toVector ||
            (0 until 2).exists { argumentIndex =>
              argumentOffsets(laneOperations, argumentIndex) !=
                laneOperations.indices.map(_ * laneOperations.head.operands(argumentIndex).width).toVector
            } =>
          Some("DshrSmall requires dense UInt<2..8> value lanes, dense UInt<1..3> shift lanes, and dense same-width result lanes")
        case SlpDshlSmall(valueWidth, shiftWidth, resultWidth)
            if (shiftWidth != 1 && shiftWidth != 2) ||
              resultWidth != valueWidth + ((1 << shiftWidth) - 1) ||
              laneOperations.exists {
                case SlpOperation(SlpDshlSmall(opValueWidth, opShiftWidth, opResultWidth),
                    laneResultWidth, storageWidth, Vector(valueOperand, SlpSignal(_, shiftOperandWidth)),
                    parameters, _) =>
                  opValueWidth != valueWidth ||
                    opShiftWidth != shiftWidth ||
                    opResultWidth != resultWidth ||
                    valueOperand.width != valueWidth ||
                    shiftOperandWidth != shiftWidth ||
                    laneResultWidth != resultWidth ||
                    storageWidth != resultWidth ||
                    parameters.nonEmpty
                case _ => true
              } ||
              pack.outputOffsets != laneOperations.indices.map(_ * resultWidth).toVector ||
              argumentOffsets(laneOperations, 0) != laneOperations.indices.map(_ * valueWidth).toVector ||
              argumentOffsets(laneOperations, 1) != laneOperations.indices.map(_ * shiftWidth).toVector =>
          Some("DshlSmall requires dense value lanes, dense UInt<1..2> shift signal lanes, and dense dynamic-left-shift result lanes")
        case SlpEqConst if laneOperations.exists {
          case SlpOperation(SlpEqConst, 1, storageWidth,
              Vector(SlpSignal(_, signalWidth), SlpUIntConstant(value, literalWidth)), _, _) =>
            !(storageWidth >= 2 && storageWidth <= 17 && signalWidth == storageWidth &&
              literalWidth == storageWidth && value >= 0 &&
              value < (BigInt(1) << storageWidth))
          case _ => true
        } =>
          Some("EqConst requires a UInt<2..17> literal, with a UInt<1> result")
        case SlpEq if laneOperations.exists {
          case SlpOperation(SlpEq, 1, storageWidth,
              Vector(SlpSignal(_, leftWidth), SlpSignal(_, rightWidth)), parameters, _) =>
            parameters.nonEmpty || leftWidth <= 0 || rightWidth <= 0 ||
              leftWidth > 63 || rightWidth > 63 || storageWidth != leftWidth.max(rightWidth)
          case _ => true
        } =>
          Some("Eq requires two UInt<1..63> signal inputs and a UInt<1> result")
        case SlpGeq if !SlpGeqLowering.canLower(pack, laneOperations) =>
          Some("ArmorGeq requires dense same-width UInt<1..63> inputs, at least one signal operand, and one-bit output lanes")
        case SlpLt if !SlpLtLowering.canLower(pack, laneOperations) =>
          Some("ArmorLt requires dense same-width UInt<1..63> inputs, at least one signal operand, and one-bit output lanes")
        case SlpNeq if !SlpNeqLowering.canLower(pack, laneOperations) =>
          Some("ArmorNeq requires dense same-width UInt<2..63> inputs, at least one signal operand, and one-bit output lanes")
        case SlpOneHot if laneOperations.exists {
          case SlpOperation(SlpOneHot, resultWidth, storageWidth,
              Vector(SlpSignal(_, inputWidth)), parameters, _) =>
            parameters.nonEmpty || inputWidth < 1 || inputWidth > 3 ||
              resultWidth != (1 << inputWidth) || storageWidth != resultWidth
          case _ => true
        } || pack.outputOffsets != laneOperations.indices.map(_ * pack.shape.resultWidth).toVector =>
          Some("ArmorOneHot requires dense UInt<1..3> input lanes and dense UInt<2|4|8> result lanes")
        case SlpMux if laneOperations.exists(operation =>
          operation.operands.size != 3 || operation.operands.head.width != 1 ||
            operation.operands(1).width != operation.resultWidth ||
            operation.operands(2).width != operation.resultWidth) =>
          Some("Mux requires UInt<1> conditions and result-width data operands")
        case _ => None
      }
    }

    val checked = discovered.packs.sortBy(_.id).map(pack => pack -> rejection(pack))
    val safePacks = checked.collect { case (pack, None) => pack }
      .zipWithIndex.map { case (pack, newId) => pack.copy(id = newId) }
    val safeRootNodeIds = safePacks.iterator.flatMap(_.nodeIds).toSet
    val safeRegions = discovered.regions.filter(region => safeRootNodeIds(region.rootNodeId))
    val rejections = checked.collect {
      case (pack, Some(reason)) => SlpLoweringRejection(pack.id, reason)
    }
    SlpLoweringValidation(discovered.copy(packs = safePacks, regions = safeRegions), rejections)
  }
}
