package armor

object CppBitUtils {
  def uint64Constant(value: BigInt): String =
    s"UINT64_C(0x${value.toString(16)})"

  def isSingleBitMask(mask: BigInt): Boolean =
    mask > 0 && (mask & (mask - 1)) == 0

  def isLowContiguousMask(mask: BigInt): Boolean =
    mask > 0 && (mask & (mask + 1)) == 0

  def singleBitIndex(mask: BigInt): Int = {
    require(isSingleBitMask(mask))
    mask.bitLength - 1
  }

  def emitPext(input: String, mask: BigInt): String = {
    require(mask >= 0 && mask < (BigInt(1) << 64),
      s"PEXT mask must fit UInt<64>: 0x${mask.toString(16)}")

    val source = s"($input)"
    if (mask == 0) {
      "UINT64_C(0)"
    } else if (isSingleBitMask(mask)) {
      val bit = singleBitIndex(mask)
      if (bit == 0) s"($source & UINT64_C(0x1))"
      else s"(($source >> $bit) & UINT64_C(0x1))"
    } else if (isLowContiguousMask(mask)) {
      val fullMask = (BigInt(1) << 64) - 1
      if (mask == fullMask) source
      else s"($source & ${uint64Constant(mask)})"
    } else {
      s"_pext_u64($source, ${uint64Constant(mask)})"
    }
  }
}
