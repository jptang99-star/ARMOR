package armor.slp

import armor.{ArmorAnd, ArmorBitExtract, ArmorBitGather, ArmorBitSelect, ArmorGeq, ArmorIdentity, ArmorLeqConst, ArmorLeqLowMask, ArmorLt, ArmorNeq, ArmorOneHot}
import essent.ir.{MemWrite, RegUpdate}
import firrtl.PrimOps.{Add, And, Andr, Bits, Cat, Dshr, Eq, Not, Or, Orr, Shl, Shr, Sub, Xor}
import firrtl._
import firrtl.ir._

object SlpOpClassifier {
  private val recognizedOpcodes: Set[PrimOp] =
    Set(Add, Sub, And, Or, Orr, Andr, Xor, Not, Cat, Bits, Eq, Shl, Shr, Dshr, ArmorIdentity, ArmorAnd, ArmorBitSelect,
      ArmorBitExtract, ArmorBitGather,
      ArmorLeqLowMask, ArmorLeqConst, ArmorGeq, ArmorLt, ArmorNeq, ArmorOneHot)

  private def bitCount(value: BigInt, width: Int): Int =
    (0 until width).count(bit => ((value >> bit) & 1) == 1)

  private def knownUIntWidth(tpe: Type): Either[SlpUnsupported, Int] = tpe match {
    case UIntType(IntWidth(width)) if width > 0 && width.isValidInt => Right(width.toInt)
    case UIntType(_: IntWidth) => Left(SlpUnsupported(SlpUnknownWidth, s"invalid UInt width: $tpe"))
    case UIntType(_)           => Left(SlpUnsupported(SlpUnknownWidth, s"unknown UInt width: $tpe"))
    case _                     => Left(SlpUnsupported(SlpNonUIntResult, s"SLP v1 only supports UInt, got $tpe"))
  }

  private def referenceName(expression: Expression): Option[String] = expression match {
    case Reference(name, _, _, _)       => Some(name)
    case SubField(base, name, _, _)     => referenceName(base).map(prefix => s"$prefix.$name")
    case SubIndex(base, index, _, _)    => referenceName(base).map(prefix => s"${prefix}_$index")
    case _                              => None
  }

  private val debugOperandRegex =
    Option(System.getenv("ARMOR_SLP_DEBUG_OPERANDS"))
      .filter(_.nonEmpty)
      .flatMap(pattern => scala.util.Try(pattern.r).toOption)

  private def statementName(statement: Statement): String = statement match {
    case DefNode(_, name, _) => name
    case Connect(_, loc, _)  => referenceName(loc).getOrElse(loc.serialize)
    case other               => other.serialize
  }

  private def debugOperandEnabled(statement: Statement, expression: Expression): Boolean =
    debugOperandRegex.exists { regex =>
      val haystack = s"${statementName(statement)} ${statement.serialize} ${expression.serialize}"
      regex.findFirstIn(haystack).nonEmpty
    }

  private def debugOperandText(expression: Expression): String = {
    val reference = referenceName(expression).getOrElse("<none>")
    val width = knownUIntWidth(expression.tpe).fold(_ => "unknown", width => s"UInt<$width>")
    val classified = operand(expression).fold(_.toString, _.toString)
    s"raw=${expression.serialize} type=${expression.tpe} width=$width reference=$reference operand=$classified"
  }

  private def debugOperands(expression: Expression, statement: Statement): Unit = {
    if (debugOperandEnabled(statement, expression)) {
      expression match {
        case DoPrim(op, args, params, _) =>
          Console.err.println(
            s"[armor-slp-debug-operands] stmt=${statementName(statement)} op=$op " +
              s"params=[${params.mkString(",")}] resultType=${expression.tpe} expr=${expression.serialize}"
          )
          args.zipWithIndex.foreach { case (arg, index) =>
            Console.err.println(s"[armor-slp-debug-operands]   arg$index ${debugOperandText(arg)}")
          }
        case Mux(cond, trueValue, falseValue, _) =>
          Console.err.println(
            s"[armor-slp-debug-operands] stmt=${statementName(statement)} op=Mux " +
              s"resultType=${expression.tpe} expr=${expression.serialize}"
          )
          Seq(cond, trueValue, falseValue).zipWithIndex.foreach { case (arg, index) =>
            Console.err.println(s"[armor-slp-debug-operands]   arg$index ${debugOperandText(arg)}")
          }
        case other =>
          Console.err.println(
            s"[armor-slp-debug-operands] stmt=${statementName(statement)} op=leaf " +
              s"resultType=${other.tpe} expr=${other.serialize} ${debugOperandText(other)}"
          )
      }
    }
  }

  private def debugClassification(
    expression:      Expression,
    statement:       Statement,
    classification:  SlpClassification
  ): SlpClassification = {
    if (debugOperandEnabled(statement, expression)) {
      Console.err.println(
        s"[armor-slp-debug-operands]   classification=${classification.toString}"
      )
    }
    classification
  }

  private def operand(expression: Expression): Either[SlpUnsupported, SlpOperand] = expression match {
    case literal @ UIntLiteral(value, _) =>
      knownUIntWidth(literal.tpe).map(width => SlpUIntConstant(value, width))
    case refLike if referenceName(refLike).nonEmpty =>
      knownUIntWidth(refLike.tpe).map(width => SlpSignal(referenceName(refLike).get, width))
    case other =>
      Left(SlpUnsupported(SlpUnsupportedExpression, s"unsupported SLP operand: ${other.serialize}"))
  }

  private def operands(expressions: Seq[Expression]): Either[SlpUnsupported, Vector[SlpOperand]] = {
    expressions.foldLeft[Either[SlpUnsupported, Vector[SlpOperand]]](Right(Vector.empty)) {
      case (Right(acc), expression) => operand(expression).map(acc :+ _)
      case (left @ Left(_), _)       => left
    }
  }

  private def build(
    opcode:     SlpOpcode,
    expressions: Seq[Expression],
    parameters: Seq[BigInt],
    resultType: Type,
    statement:  Statement
  ): SlpClassification = {
    (knownUIntWidth(resultType), operands(expressions)) match {
      case (Right(resultWidth), Right(opOperands)) =>
        val runtimeInputWidths = opOperands.collect { case signal: SlpSignal => signal.width }
        val storageWidth = (runtimeInputWidths :+ resultWidth).max
        SlpSupported(SlpOperation(
          opcode = opcode,
          resultWidth = resultWidth,
          storageWidth = storageWidth,
          operands = opOperands,
          parameters = parameters.toVector,
          statement = statement
        ))
      case (Left(unsupported), _) => unsupported
      case (_, Left(unsupported)) => unsupported
    }
  }

  private def classifyBitsLike(
    opName: String,
    prim:   DoPrim,
    arg:    Expression,
    hi:     BigInt,
    lo:     BigInt,
    resultType: Type,
    statement:  Statement
  ): SlpClassification = {
    (knownUIntWidth(resultType), operand(arg)) match {
      case (Right(resultWidth), Right(signal: SlpSignal))
          if lo >= 0 && hi >= lo && hi < signal.width &&
            resultWidth == hi - lo + 1 =>
        build(SlpBits, Seq(arg), Seq(hi, lo), resultType, statement)
      case (Right(resultWidth), Right(signal: SlpSignal)) =>
        SlpUnsupported(SlpInvalidOperand,
          s"$opName requires 0 <= lo <= hi < inputWidth and resultWidth=hi-lo+1, got " +
            s"UInt<${signal.width}> bits<$hi,$lo> -> UInt<$resultWidth>: ${prim.serialize}")
      case (Right(_), Right(_: SlpUIntConstant)) =>
        SlpUnsupported(SlpInvalidOperand, s"$opName input must be a UInt signal")
      case (Left(unsupported), _) => unsupported
      case (_, Left(unsupported)) => unsupported
    }
  }

  private def classifyExpression(
    expression: Expression,
    resultType: Type,
    statement:  Statement
  ): SlpClassification = {
    debugOperands(expression, statement)
    val classification = expression match {
    case m @ Mux(cond, trueValue, falseValue, _) =>
      (knownUIntWidth(cond.tpe), knownUIntWidth(trueValue.tpe),
        knownUIntWidth(falseValue.tpe), knownUIntWidth(resultType)) match {
        case (Right(1), Right(trueWidth), Right(falseWidth), Right(resultWidth))
            if trueWidth == falseWidth && trueWidth == resultWidth =>
          build(SlpMux, Seq(cond, trueValue, falseValue), Seq.empty, resultType, statement)
        case (Right(condWidth), _, _, _) if condWidth != 1 =>
          SlpUnsupported(SlpInvalidOperand,
            s"Mux condition must be UInt<1>, got UInt<$condWidth>: ${m.serialize}")
        case (Right(_), Right(trueWidth), Right(falseWidth), Right(resultWidth)) =>
          SlpUnsupported(SlpInvalidOperand,
            s"Mux branch/result widths must match, got true=$trueWidth false=$falseWidth result=$resultWidth")
        case (Left(unsupported), _, _, _) => unsupported
        case (_, Left(unsupported), _, _) => unsupported
        case (_, _, Left(unsupported), _) => unsupported
        case (_, _, _, Left(unsupported)) => unsupported
      }
    case p @ DoPrim(Add, args, Seq(), _) if args.size == 2 =>
      // Add is commutative. Keep a literal on the right when exactly one
      // operand is constant so old AddOne packs and general signal-signal
      // packs share one canonical opcode without changing ICT discovery.
      val normalized = args match {
        case Seq(literal: UIntLiteral, signal) if !signal.isInstanceOf[UIntLiteral] =>
          Seq(signal, literal)
        case _ => args
      }
      (knownUIntWidth(resultType), operands(normalized)) match {
        case (Right(resultWidth), Right(opOperands))
            if opOperands.exists(_.isInstanceOf[SlpSignal]) &&
              resultWidth == opOperands.map(_.width).max + 1 =>
          build(SlpAdd, normalized, Seq.empty, resultType, statement)
        case (Right(_), Right(opOperands)) if !opOperands.exists(_.isInstanceOf[SlpSignal]) =>
          SlpUnsupported(SlpInvalidOperand,
            s"packed Add requires at least one UInt signal: ${p.serialize}")
        case (Right(resultWidth), Right(opOperands)) =>
          SlpUnsupported(SlpInvalidOperand,
            s"packed Add must retain the full carry: max operand width " +
              s"${opOperands.map(_.width).max} requires UInt<${opOperands.map(_.width).max + 1}>, " +
              s"got UInt<$resultWidth>: ${p.serialize}")
        case (Left(unsupported), _) => unsupported
        case (_, Left(unsupported)) => unsupported
      }
    case p @ DoPrim(Sub, args, Seq(), _) if args.size == 2 =>
      (knownUIntWidth(resultType), operands(args)) match {
        case (Right(resultWidth), Right(opOperands))
            if opOperands.exists(_.isInstanceOf[SlpSignal]) &&
              resultWidth == opOperands.map(_.width).max + 1 =>
          build(SlpSub, args, Seq.empty, resultType, statement)
        case (Right(_), Right(opOperands)) if !opOperands.exists(_.isInstanceOf[SlpSignal]) =>
          SlpUnsupported(SlpInvalidOperand,
            s"packed Sub requires at least one UInt signal: ${p.serialize}")
        case (Right(resultWidth), Right(opOperands)) =>
          SlpUnsupported(SlpInvalidOperand,
            s"packed Sub must retain the full borrow: max operand width " +
              s"${opOperands.map(_.width).max} requires UInt<${opOperands.map(_.width).max + 1}>, " +
              s"got UInt<$resultWidth>: ${p.serialize}")
        case (Left(unsupported), _) => unsupported
        case (_, Left(unsupported)) => unsupported
      }
    case p @ DoPrim(And, args, Seq(), _) if args.size == 2 =>
      build(SlpAnd, args, Seq.empty, resultType, statement)
    case p @ DoPrim(Or, args, Seq(), _) if args.size == 2 =>
      build(SlpOr, args, Seq.empty, resultType, statement)
    case p @ DoPrim(Orr, Seq(arg), Seq(), _) =>
      (knownUIntWidth(resultType), operand(arg)) match {
        case (Right(1), Right(signal: SlpSignal)) =>
          build(SlpOrr, Seq(arg), Seq.empty, resultType, statement)
        case (Right(resultWidth), _) if resultWidth != 1 =>
          SlpUnsupported(SlpInvalidOperand,
            s"Orr result must be UInt<1>, got UInt<$resultWidth>: ${p.serialize}")
        case (_, Right(_: SlpUIntConstant)) =>
          SlpUnsupported(SlpInvalidOperand, "Orr input must be a UInt signal")
        case (Left(unsupported), _) => unsupported
        case (_, Left(unsupported)) => unsupported
      }
    case p @ DoPrim(Andr, Seq(arg), Seq(), _) =>
      (knownUIntWidth(resultType), operand(arg)) match {
        case (Right(1), Right(signal: SlpSignal)) =>
          build(SlpAndr, Seq(arg), Seq.empty, resultType, statement)
        case (Right(resultWidth), _) if resultWidth != 1 =>
          SlpUnsupported(SlpInvalidOperand,
            s"Andr result must be UInt<1>, got UInt<$resultWidth>: ${p.serialize}")
        case (_, Right(_: SlpUIntConstant)) =>
          SlpUnsupported(SlpInvalidOperand, "Andr input must be a UInt signal")
        case (Left(unsupported), _) => unsupported
        case (_, Left(unsupported)) => unsupported
      }
    case p @ DoPrim(Xor, args, Seq(), _) if args.size == 2 =>
      build(SlpXor, args, Seq.empty, resultType, statement)
    case p @ DoPrim(Not, args, Seq(), _) if args.size == 1 =>
      build(SlpNot, args, Seq.empty, resultType, statement)
    case p @ DoPrim(Cat, Seq(high, low), Seq(), _) =>
      (knownUIntWidth(resultType), operand(high), operand(low)) match {
        case (Right(resultWidth), Right(highOperand), Right(lowOperand))
            if (highOperand.isInstanceOf[SlpSignal] || lowOperand.isInstanceOf[SlpSignal]) &&
              resultWidth == highOperand.width + lowOperand.width =>
          build(SlpCat, Seq(high, low), Seq.empty, resultType, statement)
        case (Right(_), Right(highOperand), Right(lowOperand))
            if !highOperand.isInstanceOf[SlpSignal] && !lowOperand.isInstanceOf[SlpSignal] =>
          SlpUnsupported(SlpInvalidOperand,
            s"packed Cat requires at least one UInt signal: ${p.serialize}")
        case (Right(resultWidth), Right(highOperand), Right(lowOperand)) =>
          SlpUnsupported(SlpInvalidOperand,
            s"Cat result must be UInt<${highOperand.width + lowOperand.width}>, got " +
              s"UInt<$resultWidth>: ${p.serialize}")
        case (Left(unsupported), _, _) => unsupported
        case (_, Left(unsupported), _) => unsupported
        case (_, _, Left(unsupported)) => unsupported
      }
    case p @ DoPrim(Bits, Seq(arg), Seq(hi, lo), _) =>
      classifyBitsLike("Bits", p, arg, hi, lo, resultType, statement)
    case p @ DoPrim(ArmorBitExtract, Seq(arg), Seq(hi, lo), _) =>
      classifyBitsLike("ArmorBitExtract", p, arg, hi, lo, resultType, statement)
    case p @ DoPrim(Shl, Seq(arg), Seq(amount), _)
        if amount >= 0 && amount.isValidInt =>
      (operand(arg), knownUIntWidth(resultType)) match {
        case (Right(signal: SlpSignal), Right(resultWidth))
            if resultWidth == signal.width + amount.toInt =>
          build(
            SlpShlConst(amount.toInt),
            Seq(arg),
            Seq(amount),
            resultType,
            statement
          )
        case (Right(signal: SlpSignal), Right(resultWidth)) =>
          SlpUnsupported(SlpInvalidOperand,
            s"Shl result width must be input width + amount, got " +
              s"UInt<${signal.width}> shl $amount -> UInt<$resultWidth>: ${p.serialize}")
        case (Right(_), _) =>
          SlpUnsupported(SlpInvalidOperand, "Shl input must be a UInt signal")
        case (Left(unsupported), _) => unsupported
        case (_, Left(unsupported)) => unsupported
      }
    case p @ DoPrim(Shr, Seq(arg), Seq(amount), _)
        if amount > 0 && amount.isValidInt =>
      (operand(arg), knownUIntWidth(resultType)) match {
        case (Right(signal: SlpSignal), Right(resultWidth))
            if amount < signal.width && resultWidth == signal.width - amount.toInt =>
          build(
            SlpShrConst(amount.toInt),
            Seq(arg),
            Seq(amount),
            resultType,
            statement
          )
        case (Right(signal: SlpSignal), Right(resultWidth)) =>
          SlpUnsupported(SlpInvalidOperand,
            s"Shr result width must be input width - amount, got " +
              s"UInt<${signal.width}> shr $amount -> UInt<$resultWidth>: ${p.serialize}")
        case (Right(_), _) =>
          SlpUnsupported(SlpInvalidOperand, "Shr input must be a UInt signal")
        case (Left(unsupported), _) => unsupported
        case (_, Left(unsupported)) => unsupported
      }
    case p @ DoPrim(Dshr, Seq(value, shift), Seq(), _) =>
      (knownUIntWidth(resultType), operand(value), operand(shift)) match {
        case (Right(resultWidth), Right(valueSignal: SlpSignal), Right(shiftOperand))
            if valueSignal.width >= 2 && valueSignal.width <= 8 &&
              shiftOperand.width >= 1 && shiftOperand.width <= 3 &&
              resultWidth == valueSignal.width =>
          build(
            SlpDshrSmall(valueSignal.width, shiftOperand.width),
            Seq(value, shift),
            Seq.empty,
            resultType,
            statement
          )
        case (Right(resultWidth), Right(valueSignal: SlpSignal), Right(shiftOperand)) =>
          SlpUnsupported(SlpInvalidOperand,
            s"DshrSmall requires UInt<2..8> value, UInt<1..3> shift, and same-width result; got " +
              s"UInt<${valueSignal.width}> >> UInt<${shiftOperand.width}> -> UInt<$resultWidth>: ${p.serialize}")
        case (_, Right(_: SlpUIntConstant), _) =>
          SlpUnsupported(SlpInvalidOperand, "DshrSmall value input must be a UInt signal")
        case (Left(unsupported), _, _) => unsupported
        case (_, Left(unsupported), _) => unsupported
        case (_, _, Left(unsupported)) => unsupported
      }
    case p @ DoPrim(Eq, args, Seq(), _) if args.size == 2 =>
      val normalized = args match {
        case Seq(literal: UIntLiteral, signal) => Some(signal -> literal)
        case Seq(signal, literal: UIntLiteral) => Some(signal -> literal)
        case _                                  => None
      }
      normalized match {
        case Some((signalExpression, literal)) =>
          (knownUIntWidth(resultType), operand(signalExpression), operand(literal)) match {
            case (Right(1), Right(signal: SlpSignal), Right(constant: SlpUIntConstant))
                if signal.width >= 2 && signal.width <= 17 &&
                  constant.width == signal.width &&
                  constant.value < (BigInt(1) << signal.width) =>
              build(
                SlpEqConst,
                Seq(signalExpression, literal),
                Seq.empty,
                resultType,
                statement
              )
            case (Right(1), Right(_: SlpSignal), Right(_: SlpUIntConstant)) =>
              SlpUnsupported(SlpInvalidOperand,
                s"packed EqConst supports UInt<2..17> literals: ${p.serialize}")
            case (Right(resultWidth), _, _) if resultWidth != 1 =>
              SlpUnsupported(SlpInvalidOperand,
                s"packed EqConst result must be UInt<1>, got UInt<$resultWidth>")
            case (Left(unsupported), _, _) => unsupported
            case (_, Left(unsupported), _) => unsupported
            case (_, _, Left(unsupported)) => unsupported
            case _ => SlpUnsupported(SlpInvalidOperand,
              s"packed EqConst requires one UInt<2..17> signal/literal: ${p.serialize}")
          }
        case None =>
          (knownUIntWidth(resultType), operands(args)) match {
            case (Right(1), Right(Vector(_: SlpSignal, _: SlpSignal))) =>
              build(SlpEq, args, Seq.empty, resultType, statement)
            case (Right(resultWidth), _) if resultWidth != 1 =>
              SlpUnsupported(SlpInvalidOperand,
                s"packed Eq result must be UInt<1>, got UInt<$resultWidth>")
            case (Left(unsupported), _) => unsupported
            case (_, Left(unsupported)) => unsupported
            case _ => SlpUnsupported(SlpInvalidOperand,
              s"packed Eq requires two UInt signals or one supported UInt literal: ${p.serialize}")
          }
      }
    case p @ DoPrim(ArmorIdentity, args, Seq(), _) if args.size == 1 =>
      build(SlpMove, args, Seq.empty, resultType, statement)
    case p @ DoPrim(ArmorAnd, args, Seq(), _) if args.size == 2 =>
      args match {
        case Seq(value, maskLiteral @ UIntLiteral(mask, _)) =>
          (operand(value), knownUIntWidth(maskLiteral.tpe)) match {
            case (Right(signal: SlpSignal), Right(maskWidth))
                if signal.width <= 64 && mask == (BigInt(1) << maskWidth) - 1 =>
              build(SlpMaskedAnd, args, Seq.empty, resultType, statement)
            case (Right(signal: SlpSignal), _) if signal.width > 64 =>
              SlpUnsupported(SlpInvalidOperand,
                s"ArmorAnd source width ${signal.width} exceeds its 64-bit lowering contract")
            case (Right(_: SlpSignal), Right(maskWidth)) =>
              SlpUnsupported(SlpInvalidOperand,
                s"ArmorAnd mask must be $maskWidth low one bits, got 0x${mask.toString(16)}")
            case (Right(_), _) =>
              SlpUnsupported(SlpInvalidOperand, "ArmorAnd value must be a signal")
            case (Left(unsupported), _) => unsupported
            case (_, Left(unsupported)) => unsupported
          }
        case _ => SlpUnsupported(SlpInvalidOperand, s"ArmorAnd requires (value, UIntLiteral): ${p.serialize}")
      }
    case p @ DoPrim(ArmorBitSelect, args, Seq(bitPosition), _) if args.size == 1 =>
      (knownUIntWidth(resultType), operand(args.head)) match {
        case (Right(1), Right(signal: SlpSignal))
            if bitPosition >= 0 && bitPosition < signal.width =>
          build(SlpBitSelect, args, Seq(bitPosition), resultType, statement)
        case (Right(resultWidth), _) if resultWidth != 1 =>
          SlpUnsupported(SlpInvalidOperand,
            s"ArmorBitSelect result must be UInt<1>, got UInt<$resultWidth>")
        case (_, Right(_: SlpSignal)) =>
          SlpUnsupported(SlpInvalidOperand, s"ArmorBitSelect position $bitPosition is out of range")
        case (_, Right(_)) =>
          SlpUnsupported(SlpInvalidOperand, "ArmorBitSelect input must be a signal")
        case (Left(unsupported), _) => unsupported
        case (_, Left(unsupported)) => unsupported
      }
    case p @ DoPrim(op @ ArmorBitGather, args, Seq(mask), _) if args.size == 1 =>
      (knownUIntWidth(resultType), operand(args.head)) match {
        case (Right(resultWidth), Right(signal: SlpSignal))
            if mask > 0 && signal.width <= 64 &&
              (mask & ~((BigInt(1) << signal.width) - 1)) == 0 &&
              bitCount(mask, signal.width) == resultWidth =>
          build(SlpBitGather, args, Seq(mask), resultType, statement)
        case (Right(resultWidth), Right(signal: SlpSignal)) =>
          SlpUnsupported(SlpInvalidOperand,
            s"$op requires a non-zero mask within UInt<${signal.width}> with popcount=resultWidth; " +
              s"mask=0x${mask.toString(16)} result=UInt<$resultWidth>")
        case (_, Right(_)) =>
          SlpUnsupported(SlpInvalidOperand, s"$op input must be a signal")
        case (Left(unsupported), _) => unsupported
        case (_, Left(unsupported)) => unsupported
      }
    case p @ DoPrim(ArmorLeqLowMask, Seq(arg), Seq(allowedLowBits), _) =>
      (knownUIntWidth(resultType), operand(arg)) match {
        case (Right(1), Right(signal: SlpSignal))
            if allowedLowBits >= 0 && allowedLowBits < signal.width =>
          build(SlpLeqLowMask, Seq(arg), Seq(allowedLowBits), resultType, statement)
        case (Right(1), Right(signal: SlpSignal)) =>
          SlpUnsupported(SlpInvalidOperand,
            s"ArmorLeqLowMask allowed-low-bit count $allowedLowBits is invalid for UInt<${signal.width}>")
        case (Right(resultWidth), _) if resultWidth != 1 =>
          SlpUnsupported(SlpInvalidOperand,
            s"ArmorLeqLowMask result must be UInt<1>, got UInt<$resultWidth>")
        case (_, Right(_: SlpUIntConstant)) =>
          SlpUnsupported(SlpInvalidOperand, "ArmorLeqLowMask input must be a UInt signal")
        case (Left(unsupported), _) => unsupported
        case (_, Left(unsupported)) => unsupported
      }
    case p @ DoPrim(ArmorLeqConst, Seq(arg), Seq(constant), _) =>
      (knownUIntWidth(resultType), operand(arg)) match {
        case (Right(1), Right(signal: SlpSignal))
            if signal.width >= 2 && signal.width <= 17 && constant >= 0 &&
              constant < (BigInt(1) << signal.width) =>
          build(SlpLeqConst, Seq(arg), Seq(constant), resultType, statement)
        case (Right(1), Right(signal: SlpSignal)) =>
          SlpUnsupported(SlpInvalidOperand,
            s"ArmorLeqConst constant $constant is invalid for UInt<${signal.width}>")
        case (Right(resultWidth), _) if resultWidth != 1 =>
          SlpUnsupported(SlpInvalidOperand,
            s"ArmorLeqConst result must be UInt<1>, got UInt<$resultWidth>")
        case (_, Right(_: SlpUIntConstant)) =>
          SlpUnsupported(SlpInvalidOperand, "ArmorLeqConst input must be a UInt signal")
        case (Left(unsupported), _) => unsupported
        case (_, Left(unsupported)) => unsupported
      }
    case p @ DoPrim(ArmorGeq, Seq(left, right), Seq(), _) =>
      (knownUIntWidth(resultType), operand(left), operand(right)) match {
        case (Right(1), Right(leftOperand), Right(rightOperand))
            if (leftOperand.isInstanceOf[SlpSignal] || rightOperand.isInstanceOf[SlpSignal]) &&
              leftOperand.width == rightOperand.width && leftOperand.width <= 63 =>
          build(SlpGeq, Seq(left, right), Seq.empty, resultType, statement)
        case (Right(1), Right(leftOperand), Right(rightOperand))
            if !leftOperand.isInstanceOf[SlpSignal] && !rightOperand.isInstanceOf[SlpSignal] =>
          SlpUnsupported(SlpInvalidOperand, "ArmorGeq packed lowering requires at least one signal operand")
        case (Right(1), Right(leftOperand), Right(rightOperand)) =>
          SlpUnsupported(SlpInvalidOperand,
            s"ArmorGeq requires same-width UInt<1..63> signals, got " +
              s"UInt<${leftOperand.width}> and UInt<${rightOperand.width}>")
        case (Right(resultWidth), _, _) if resultWidth != 1 =>
          SlpUnsupported(SlpInvalidOperand,
            s"ArmorGeq result must be UInt<1>, got UInt<$resultWidth>")
        case (Left(unsupported), _, _) => unsupported
        case (_, Left(unsupported), _) => unsupported
        case (_, _, Left(unsupported)) => unsupported
      }
    case p @ DoPrim(ArmorLt, Seq(left, right), Seq(), _) =>
      (knownUIntWidth(resultType), operand(left), operand(right)) match {
        case (Right(1), Right(leftOperand), Right(rightOperand))
            if (leftOperand.isInstanceOf[SlpSignal] || rightOperand.isInstanceOf[SlpSignal]) &&
              leftOperand.width == rightOperand.width && leftOperand.width <= 63 =>
          build(SlpLt, Seq(left, right), Seq.empty, resultType, statement)
        case (Right(1), Right(leftOperand), Right(rightOperand))
            if !leftOperand.isInstanceOf[SlpSignal] && !rightOperand.isInstanceOf[SlpSignal] =>
          SlpUnsupported(SlpInvalidOperand, "ArmorLt packed lowering requires at least one signal operand")
        case (Right(1), Right(leftOperand), Right(rightOperand)) =>
          SlpUnsupported(SlpInvalidOperand,
            s"ArmorLt requires same-width UInt<1..63> operands, got " +
              s"UInt<${leftOperand.width}> and UInt<${rightOperand.width}>")
        case (Right(resultWidth), _, _) if resultWidth != 1 =>
          SlpUnsupported(SlpInvalidOperand,
            s"ArmorLt result must be UInt<1>, got UInt<$resultWidth>")
        case (Left(unsupported), _, _) => unsupported
        case (_, Left(unsupported), _) => unsupported
        case (_, _, Left(unsupported)) => unsupported
      }
    case p @ DoPrim(ArmorNeq, Seq(left, right), Seq(), _) =>
      (knownUIntWidth(resultType), operand(left), operand(right)) match {
        case (Right(1), Right(leftOperand), Right(rightOperand))
            if (leftOperand.isInstanceOf[SlpSignal] || rightOperand.isInstanceOf[SlpSignal]) &&
              leftOperand.width == rightOperand.width && leftOperand.width > 1 &&
              leftOperand.width <= 63 =>
          build(SlpNeq, Seq(left, right), Seq.empty, resultType, statement)
        case (Right(1), Right(leftOperand), Right(rightOperand))
            if !leftOperand.isInstanceOf[SlpSignal] && !rightOperand.isInstanceOf[SlpSignal] =>
          SlpUnsupported(SlpInvalidOperand, "ArmorNeq packed lowering requires at least one signal operand")
        case (Right(1), Right(leftOperand), Right(rightOperand)) =>
          SlpUnsupported(SlpInvalidOperand,
            s"ArmorNeq requires same-width UInt<2..63> operands, got " +
              s"UInt<${leftOperand.width}> and UInt<${rightOperand.width}>")
        case (Right(resultWidth), _, _) if resultWidth != 1 =>
          SlpUnsupported(SlpInvalidOperand,
            s"ArmorNeq result must be UInt<1>, got UInt<$resultWidth>")
        case (Left(unsupported), _, _) => unsupported
        case (_, Left(unsupported), _) => unsupported
        case (_, _, Left(unsupported)) => unsupported
      }
    case p @ DoPrim(ArmorOneHot, Seq(index), Seq(), _) =>
      (knownUIntWidth(resultType), operand(index)) match {
        case (Right(resultWidth), Right(signal: SlpSignal))
            if signal.width >= 1 && signal.width <= 3 &&
              resultWidth == (1 << signal.width) =>
          build(SlpOneHot, Seq(index), Seq.empty, resultType, statement)
        case (Right(resultWidth), Right(signal: SlpSignal)) =>
          SlpUnsupported(SlpInvalidOperand,
            s"ArmorOneHot requires UInt<1..3> -> UInt<(1 << width)>, " +
              s"got UInt<${signal.width}> -> UInt<$resultWidth>: ${p.serialize}")
        case (_, Right(_: SlpUIntConstant)) =>
          SlpUnsupported(SlpInvalidOperand, "ArmorOneHot input must be a UInt signal")
        case (Left(unsupported), _) => unsupported
        case (_, Left(unsupported)) => unsupported
      }
    case p @ DoPrim(op, _, _, _) if recognizedOpcodes.contains(op) =>
      SlpUnsupported(SlpInvalidArity, s"invalid arguments for ${p.op}: ${p.serialize}")
    case p: DoPrim =>
      SlpUnsupported(SlpUnsupportedOpcode, s"unsupported SLP primitive: ${p.op}")
    case _: ValidIf | _: SubAccess =>
      SlpUnsupported(SlpUnsupportedExpression, s"unsupported SLP expression: ${expression.serialize}")
    case leaf =>
      build(SlpMove, Seq(leaf), Seq.empty, resultType, statement)
    }
    debugClassification(expression, statement, classification)
  }

  def classify(node: SlpNode): SlpClassification = {
    if (!node.valid) {
      SlpUnsupported(SlpInvalidNode, s"node ${node.id} is not an emission node")
    } else {
      node.statement match {
        case d: DefNode => classifyExpression(d.value, d.value.tpe, d)
        case c: Connect => classifyExpression(c.expr, c.loc.tpe, c)
        case _: RegUpdate | _: MemWrite | _: DefRegister | _: DefMemory =>
          SlpUnsupported(SlpStatefulOperation, s"stateful statement: ${node.statement.serialize}")
        case _: Print | _: Stop =>
          SlpUnsupported(SlpUnsupportedStatement, s"side-effect statement: ${node.statement.serialize}")
        case other =>
          SlpUnsupported(SlpUnsupportedStatement, s"unsupported statement: ${other.serialize}")
      }
    }
  }
}
