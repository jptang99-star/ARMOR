package armor

import firrtl.ir.PrimOp

/** Internal primitive operations used after FIRRTL has reached LowForm.
  *
  * They deliberately carry the original FIRRTL result type.  This makes the
  * rewrite type-preserving and lets the C++ emitter lower them without having
  * to infer widths again.
  */
case object ArmorBitSelect extends PrimOp {
  override def toString: String = "armor_bit_select"
}

case object ArmorBitExtract extends PrimOp {
  override def toString: String = "armor_bit_extract"
}

/** Gather the selected bits of a UInt into consecutive low-order bits.
  *
  * The sole argument is the source and the sole constant is its selection
  * mask.  The result width is therefore popcount(mask).  This is the IR
  * representation of BMI2 PEXT, but intentionally records its bit-level
  * semantics rather than a target-specific instruction.
  */
case object ArmorBitGather extends PrimOp {
  override def toString: String = "armor_bit_gather"
}

/** UInt low-bit mask operation used for <= 64-bit scalar lowering.
  *
  * Arguments are (value, lowOnesMask), and the result type determines the
  * truncation width.  BitOpNormalizePass only creates this operation when the
  * value and result can be represented by one uint64_t.
  */
case object ArmorAnd extends PrimOp {
  override def toString: String = "armor_and"
}

case object ArmorZeroExtend extends PrimOp {
  override def toString: String = "armor_zero_extend"
}

case object ArmorIdentity extends PrimOp {
  override def toString: String = "armor_identity"
}

/** Unsigned x <= (2^allowedLowBits - 1).  Equivalently, every bit at or
  * above allowedLowBits is zero.  This has a dedicated packed lowering.
  */
case object ArmorLeqLowMask extends PrimOp {
  override def toString: String = "armor_leq_low_mask"
}

/** Unsigned x <= C, where C is carried in DoPrim.consts.
  *
  * This is deliberately a unary primitive: normalization has already
  * canonicalized both `x <= C` and `C >= x`, and the literal is a semantic
  * parameter rather than a second data-flow operand.  That lets SLP require
  * one constant for every lane in a packed comparison.
  */
case object ArmorLeqConst extends PrimOp {
  override def toString: String = "armor_leq_const"
}

/** Unsigned lhs >= rhs after normalization.
  *
  * Dynamic <= is canonicalized by swapping operands.  Keeping one semantic
  * primitive lets SLP discover and lower lane-wise unsigned comparisons
  * without depending on source spelling.
  */
case object ArmorGeq extends PrimOp {
  override def toString: String = "armor_geq"
}

/** Unsigned lhs < rhs after normalization.
  *
  * Keeping Lt as a first-class semantic primitive makes SLP discovery,
  * statistics, comments, and lowering explicit instead of encoding it as
  * Not(Geq) in a later emitter-only rewrite.
  */
case object ArmorLt extends PrimOp {
  override def toString: String = "armor_lt"
}

/** Unsigned same-width lhs != rhs after normalization.
  *
  * The UInt<1> case remains Xor and non-zero tests remain Orr; this primitive
  * captures only multi-bit dynamic inequality so SLP can lower it without
  * scalar unpack/repack boundaries.
  */
case object ArmorNeq extends PrimOp {
  override def toString: String = "armor_neq"
}

/** UInt one-hot decode, equivalent to UInt<1>(1) << index.
  *
  * This primitive is created only when the index width and result width are
  * statically known.  SLP can then lower a pack of one-hot decodes directly
  * from packed index lanes instead of unpacking each dynamic shift.
  */
case object ArmorOneHot extends PrimOp {
  override def toString: String = "armor_one_hot"
}

/** Read one element from a power-of-two UInt vector using a UInt index.
  *
  * The first argument is the index; remaining arguments are elements in
  * ascending index order.  It is a target-neutral representation of a
  * priority-Mux decoder and permits SLP lowering to read an already packed
  * register vector with one variable shift.
  */
case object ArmorIndexedMux extends PrimOp {
  override def toString: String = "armor_indexed_mux"
}

object ArmorPrimOps {
  def contains(op: PrimOp): Boolean = op match {
    case ArmorBitSelect | ArmorBitExtract | ArmorBitGather |
        ArmorAnd | ArmorZeroExtend | ArmorIdentity |
        ArmorLeqLowMask | ArmorLeqConst | ArmorGeq | ArmorLt | ArmorNeq | ArmorOneHot | ArmorIndexedMux => true
    case _ => false
  }
}
