package armor.slp

import firrtl.ir.Statement

sealed trait SlpOpcode {
  def name: String

  /** Parameters that are semantic invariants of one packed operation.
    *
    * Most opcode parameters are lane-local lowering data: for example a
    * BitSelect pack may intentionally use different bit positions.  Only an
    * opcode which requires one group-wide value exposes it here.
    */
  def packSemanticParameters(parameters: Vector[BigInt]): Vector[BigInt] = Vector.empty
}

case object SlpAnd extends SlpOpcode { val name = "and" }
case object SlpAdd extends SlpOpcode { val name = "add" }
case object SlpSub extends SlpOpcode { val name = "sub" }
case object SlpTruncatingAdd extends SlpOpcode { val name = "truncating_add" }
case object SlpTruncatingSub extends SlpOpcode { val name = "truncating_sub" }
case object SlpOr extends SlpOpcode { val name = "or" }
case object SlpOrr extends SlpOpcode { val name = "orr" }
case object SlpAndr extends SlpOpcode { val name = "andr" }
case object SlpXor extends SlpOpcode { val name = "xor" }
case object SlpNot extends SlpOpcode { val name = "not" }
case object SlpMove extends SlpOpcode { val name = "move" }
case object SlpCat extends SlpOpcode { val name = "cat" }
case object SlpMaskedAnd extends SlpOpcode { val name = "masked_and" }
case object SlpBitSelect extends SlpOpcode { val name = "bit_select" }
case object SlpBits extends SlpOpcode {
  val name = "bits"
  override def packSemanticParameters(parameters: Vector[BigInt]): Vector[BigInt] = parameters
}
case object SlpBitGather extends SlpOpcode {
  val name = "bit_gather"
  override def packSemanticParameters(parameters: Vector[BigInt]): Vector[BigInt] = parameters
}
final case class SlpShlConst(amount: Int) extends SlpOpcode {
  require(amount >= 0, "SLP constant left-shift amount must be non-negative")
  val name = s"shl_$amount"
}
final case class SlpShrConst(amount: Int) extends SlpOpcode {
  require(amount > 0, "SLP constant right-shift amount must be positive")
  val name = s"shr_$amount"
}
final case class SlpDshrSmall(valueWidth: Int, shiftWidth: Int) extends SlpOpcode {
  require(valueWidth >= 2 && valueWidth <= 8,
    s"SLP small dynamic right-shift value width must be in [2,8], got $valueWidth")
  require(shiftWidth >= 1 && shiftWidth <= 3,
    s"SLP small dynamic right-shift currently supports UInt<1..3> shift amounts, got $shiftWidth")
  val name = s"dshr_w${valueWidth}_s${shiftWidth}"
}
final case class SlpDshlSmall(valueWidth: Int, shiftWidth: Int, resultWidth: Int) extends SlpOpcode {
  require(valueWidth > 0 && valueWidth <= 64,
    s"SLP small dynamic left-shift value width must be in [1,64], got $valueWidth")
  require(shiftWidth == 1 || shiftWidth == 2,
    s"SLP small dynamic left-shift currently supports UInt<1> or UInt<2> shift amounts, got $shiftWidth")
  require(resultWidth == valueWidth + ((1 << shiftWidth) - 1),
    s"SLP dynamic left-shift result width must be valueWidth + maxShift, got value=$valueWidth shift=$shiftWidth result=$resultWidth")
  require(resultWidth <= 64,
    s"SLP small dynamic left-shift result width must fit uint64_t lane, got $resultWidth")
  val name = s"dshl_w${valueWidth}_s${shiftWidth}_r${resultWidth}"
}
case object SlpEq extends SlpOpcode { val name = "eq" }
case object SlpEqConst extends SlpOpcode { val name = "eq_const" }
case object SlpGeq extends SlpOpcode { val name = "geq" }
case object SlpLt extends SlpOpcode { val name = "lt" }
case object SlpNeq extends SlpOpcode { val name = "neq" }
case object SlpOneHot extends SlpOpcode { val name = "one_hot" }
case object SlpLeqLowMask extends SlpOpcode {
  val name = "leq_low_mask"
  override def packSemanticParameters(parameters: Vector[BigInt]): Vector[BigInt] = parameters
}
case object SlpLeqConst extends SlpOpcode {
  val name = "leq_const"
  override def packSemanticParameters(parameters: Vector[BigInt]): Vector[BigInt] = parameters
}
case object SlpMux extends SlpOpcode { val name = "mux" }

sealed trait SlpOperand {
  def width: Int
}

final case class SlpSignal(name: String, width: Int) extends SlpOperand {
  require(name.nonEmpty, "SLP signal name cannot be empty")
  require(width > 0, "SLP signal width must be positive")
}

final case class SlpUIntConstant(value: BigInt, width: Int) extends SlpOperand {
  require(value >= 0, "SLP UInt constant cannot be negative")
  require(width > 0, "SLP UInt constant width must be positive")
}

/** Typed description consumed by the future packer.
  *
  * storageWidth is the widest runtime signal or result which a lane needs to
  * carry. Compile-time constants do not occupy packed runtime storage. It can
  * be wider than resultWidth, notably for ArmorBitSelect and truncation.
  */
final case class SlpOperation(
  opcode:       SlpOpcode,
  resultWidth:  Int,
  storageWidth: Int,
  operands:     Vector[SlpOperand],
  parameters:   Vector[BigInt],
  statement:    Statement
) {
  require(resultWidth > 0, "SLP result width must be positive")
  require(storageWidth >= resultWidth, "SLP storage width cannot be narrower than its result")
  require(operands.nonEmpty, "SLP operation must have at least one operand")

  def operandWidths: Vector[Int] = operands.map(_.width)
}

sealed trait SlpRejectReason {
  def code: String
}

case object SlpInvalidNode extends SlpRejectReason { val code = "invalid_node" }
case object SlpUnsupportedStatement extends SlpRejectReason { val code = "unsupported_statement" }
case object SlpUnsupportedOpcode extends SlpRejectReason { val code = "unsupported_opcode" }
case object SlpUnsupportedExpression extends SlpRejectReason { val code = "unsupported_expression" }
case object SlpStatefulOperation extends SlpRejectReason { val code = "stateful_operation" }
case object SlpNonUIntResult extends SlpRejectReason { val code = "non_uint_result" }
case object SlpUnknownWidth extends SlpRejectReason { val code = "unknown_width" }
case object SlpInvalidArity extends SlpRejectReason { val code = "invalid_arity" }
case object SlpInvalidOperand extends SlpRejectReason { val code = "invalid_operand" }

sealed trait SlpClassification
final case class SlpSupported(operation: SlpOperation) extends SlpClassification
final case class SlpUnsupported(reason: SlpRejectReason, detail: String) extends SlpClassification
