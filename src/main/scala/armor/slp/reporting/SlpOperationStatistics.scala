package armor.slp

import armor.{ArmorAnd, ArmorBitExtract, ArmorBitGather, ArmorBitSelect, ArmorGeq, ArmorIdentity, ArmorLeqConst, ArmorLeqLowMask, ArmorLt, ArmorNeq, ArmorOneHot, ArmorPrimOps, ArmorZeroExtend}
import essent.ir.{MemWrite, RegUpdate}
import firrtl.ir.{Connect, DefNode, DoPrim, Mux, Print, Statement, Stop}

/** Legacy-style operation accounting over the immutable SLP graph.
  *
  * `raw` counts every valid graph node. `packed` counts only nodes selected by
  * the final lowering plan (including packed RegUpdate nodes), so the report
  * describes the emitted SLP program rather than merely discovery candidates.
  */
object SlpOperationStatistics {
  final case class Row(opType: String, raw: Int, packed: Int) {
    require(raw >= packed, s"packed count exceeds raw count for $opType")

    def unpacked: Int = raw - packed
  }

  private val primitiveNames = Map(
    "add" -> "Add", "addw" -> "Addw", "sub" -> "Sub", "subw" -> "Subw",
    "mul" -> "Mul", "div" -> "Div", "rem" -> "Rem",
    "lt" -> "Lt", "leq" -> "Leq", "gt" -> "Gt", "geq" -> "Geq",
    "eq" -> "Eq", "neq" -> "Neq", "pad" -> "Pad",
    "shl" -> "Shl", "shlw" -> "Shlw", "shr" -> "Shr",
    "dshl" -> "Dshl", "dshlw" -> "Dshlw", "dshr" -> "Dshr",
    "cvt" -> "Cvt", "neg" -> "Neg", "not" -> "Not",
    "and" -> "And", "or" -> "Or", "xor" -> "Xor",
    "andr" -> "Andr", "orr" -> "Orr", "xorr" -> "Xorr",
    "cat" -> "Cat", "bits" -> "Bits", "head" -> "Head", "tail" -> "Tail",
    "asuint" -> "AsUInt", "assint" -> "AsSInt", "asclock" -> "AsClock",
    "asasyncreset" -> "AsAsyncReset"
  )

  private def armorOpName(op: firrtl.ir.PrimOp): String = op match {
    case ArmorAnd        => "ArmorAnd"
    case ArmorBitExtract => "ArmorBitExtract"
    case ArmorBitGather  => "ArmorBitGather"
    case ArmorBitSelect  => "ArmorBitSelect"
    case ArmorGeq        => "ArmorGeq"
    case ArmorIdentity   => "ArmorIdentity"
    case ArmorLeqConst   => "ArmorLeqConst"
    case ArmorLeqLowMask => "ArmorLeqLowMask"
    case ArmorLt         => "ArmorLt"
    case ArmorNeq        => "ArmorNeq"
    case ArmorOneHot     => "ArmorOneHot"
    case ArmorZeroExtend => "ArmorZeroExtend"
    case other           => other.toString
  }

  def opType(statement: Statement): String = statement match {
    case _: Connect  => "Connect"
    case _: MemWrite => "MemWrite"
    case _: RegUpdate => "RegUpdate"
    case _: Print    => "Print"
    case _: Stop     => "Stop"
    case DefNode(_, _, Mux(_, _, _, _)) => "Mux"
    case DefNode(_, _, DoPrim(op, _, _, _)) if ArmorPrimOps.contains(op) => armorOpName(op)
    case DefNode(_, _, DoPrim(op, _, _, _)) =>
      primitiveNames.getOrElse(op.toString.toLowerCase, op.toString.capitalize)
    case _: DefNode => "Assign"
    case _          => "Other"
  }

  def rows(context: SlpAnalysisContext, packedNodeIds: Set[Int]): Vector[Row] = {
    val raw = context.graph.validNodeIds.iterator
      .map(nodeId => opType(context.graph.node(nodeId).statement))
      .toVector
      .groupMapReduce(identity)(_ => 1)(_ + _)
    val packed = packedNodeIds.iterator
      .filter(context.graph.validNodeIds.contains)
      .map(nodeId => opType(context.graph.node(nodeId).statement))
      .toVector
      .groupMapReduce(identity)(_ => 1)(_ + _)

    raw.keys.toVector.sorted.map { opType =>
      Row(opType, raw(opType), packed.getOrElse(opType, 0))
    }
  }

  def format(rows: Vector[Row]): String = {
    val rawTotal = rows.map(_.raw).sum
    val packedTotal = rows.map(_.packed).sum
    require(rawTotal > 0, "operation statistics require at least one valid graph node")

    def percentage(count: Int): Double = count.toDouble * 100.0 / rawTotal
    def countAndPercentage(count: Int): String = f"$count%6d(${percentage(count)}%6.2f%%)"

    val header = f" ${"OpType"}%-20s ${"Raw"}%16s ${"Packed"}%16s ${"unPacked"}%16s"
    val separator = "-" * 71
    val body = rows.map { row =>
      f" ${row.opType}%-20s ${countAndPercentage(row.raw)}%16s ${countAndPercentage(row.packed)}%16s ${countAndPercentage(row.unpacked)}%16s"
    }
    val total = f" ${"TOTAL"}%-20s ${countAndPercentage(rawTotal)}%16s ${countAndPercentage(packedTotal)}%16s ${countAndPercentage(rawTotal - packedTotal)}%16s"
    (Vector(header, separator) ++ body ++ Vector(separator, total)).mkString(System.lineSeparator()) + System.lineSeparator()
  }
}
