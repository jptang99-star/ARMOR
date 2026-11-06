package armor

import essent.ir.{MemWrite, RegUpdate}
import firrtl._
import firrtl.PrimOps._
import firrtl.ir._
import firrtl.passes.Pass
import firrtl.options.Dependency
import logger.LazyLogging

import scala.collection.mutable

/** Canonicalizes selected UInt bit operations without changing result types.
  *
  * A rewrite is performed only when the input width is statically known and
  * all operation bounds are valid.  Signed operations, unknown widths, zero
  * width corner cases, and malformed bounds are intentionally left untouched.
  */
object BitOpNormalizePass extends Pass with LazyLogging {
  override def prerequisites = Seq(Dependency(ExpressionDecomposePass))
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform): Boolean = false

  private def knownUIntTypeWidth(tpe: Type): Option[BigInt] = tpe match {
    case UIntType(IntWidth(width)) if width > 0 => Some(width)
    case _                                      => None
  }

  private def knownUIntWidth(e: Expression): Option[BigInt] = knownUIntTypeWidth(e.tpe)

  private def slpUnsignedCompareWidth(width: BigInt): Boolean =
    width >= 1 && width <= 63

  private def isUIntLiteral(e: Expression): Boolean = e match {
    case UIntLiteral(_, _) => true
    case _                 => false
  }

  private def dynamicCompareOperands(left: Expression, right: Expression): Boolean =
    !isUIntLiteral(left) && !isUIntLiteral(right)

  /** For an unsigned W-bit value, x > (2^(W - 1) - 1) is exactly x[W - 1]. */
  private def unsignedTopBitThreshold(width: BigInt): BigInt =
    (BigInt(1) << (width.toInt - 1)) - 1

  private def lowOnesWidth(value: BigInt): Option[BigInt] =
    if (value >= 0 && (value & (value + 1)) == 0) Some(BigInt(value.bitLength))
    else None

  private def identity(p: DoPrim): DoPrim =
    DoPrim(ArmorIdentity, p.args, Seq.empty, p.tpe)

  private def extract(p: DoPrim, hi: BigInt, lo: BigInt): DoPrim = {
    val op = if (hi == lo) ArmorBitSelect else ArmorBitExtract
    val consts = if (hi == lo) Seq(hi) else Seq(hi, lo)
    DoPrim(op, p.args, consts, p.tpe)
  }

  private def lowMaskAnd(p: DoPrim, maskWidth: BigInt): DoPrim = {
    val mask = (BigInt(1) << maskWidth.toInt) - 1
    val maskLiteral = UIntLiteral(mask, IntWidth(maskWidth))
    DoPrim(ArmorAnd, Seq(p.args.head, maskLiteral), Seq.empty, p.tpe)
  }

  /** Compresses a constant according to the low-to-high source-bit order of
    * ArmorBitGather.  This is PEXT's value semantics, written here so the
    * normalizer remains independent of the eventual C++ lowering.
    */
  private def gatherConstant(value: BigInt, mask: BigInt, sourceWidth: Int): BigInt = {
    var result = BigInt(0)
    var destinationBit = 0
    var sourceBit = 0
    while (sourceBit < sourceWidth) {
      if (((mask >> sourceBit) & 1) == 1) {
        if (((value >> sourceBit) & 1) == 1)
          result |= BigInt(1) << destinationBit
        destinationBit += 1
      }
      sourceBit += 1
    }
    result
  }

  private def bitCount(value: BigInt, width: Int): Int =
    (0 until width).count(bit => ((value >> bit) & 1) == 1)

  private[armor] def normalizeExpr(e: Expression): Expression = {
    val children = e.mapExpr(normalizeExpr)
    children match {
      case p @ DoPrim(op, _, _, _) if ArmorPrimOps.contains(op) => p

      // UInt<1>(1) << x is a one-hot decode. Keep the canonical operation
      // width-derived: the SLP lowering supports the compact UInt<1..3>
      // forms, whose results are UInt<2>, UInt<4>, and UInt<8>.
      case p @ DoPrim(Dshl, Seq(UIntLiteral(value, literalWidth), amount), Seq(), _)
          if value == 1 && literalWidth == IntWidth(1) &&
            knownUIntWidth(amount).exists(indexWidth =>
              indexWidth >= 1 && indexWidth <= 3 &&
                knownUIntWidth(p).contains(BigInt(1) << indexWidth.toInt)) =>
        DoPrim(ArmorOneHot, Seq(amount), Seq.empty, p.tpe)

      case p @ DoPrim(Neq, Seq(left, right), Seq(), _)
          if knownUIntWidth(left).contains(BigInt(1)) &&
            knownUIntWidth(right).contains(BigInt(1)) &&
            knownUIntWidth(p).contains(BigInt(1)) =>
        DoPrim(Xor, p.args, Seq.empty, p.tpe)

      // A non-zero test is exactly FIRRTL's OR reduction. Keeping it as Orr
      // gives SLP a first-class reduction node instead of forcing a packed
      // producer through scalar unpack, Neq, and scalar-to-pack alignment.
      case p @ DoPrim(Neq, Seq(value, UIntLiteral(literal, _)), Seq(), _)
          if literal == 0 && knownUIntWidth(value).exists(_ > BigInt(1)) &&
            knownUIntWidth(p).contains(BigInt(1)) =>
        DoPrim(Orr, Seq(value), Seq.empty, p.tpe)

      case p @ DoPrim(Neq, Seq(UIntLiteral(literal, _), value), Seq(), _)
          if literal == 0 && knownUIntWidth(value).exists(_ > BigInt(1)) &&
            knownUIntWidth(p).contains(BigInt(1)) =>
        DoPrim(Orr, Seq(value), Seq.empty, p.tpe)

      case p @ DoPrim(Neq, Seq(left, right), Seq(), _)
          if knownUIntWidth(left).exists(width =>
            width > 1 && width <= 63 && knownUIntWidth(right).contains(width)
          ) && knownUIntWidth(p).contains(BigInt(1)) =>
        DoPrim(ArmorNeq, Seq(left, right), Seq.empty, p.tpe)

      // x <= (2^K - 1) iff all bits at and above K are zero.  Preserve this
      // as one primitive so ExpressionDecomposePass does not need to run a
      // second time to flatten Bits -> Orr -> Not before SLP sees it.
      case p @ DoPrim(Leq, Seq(value, UIntLiteral(threshold, _)), Seq(), _)
          if knownUIntWidth(value).exists { width =>
            width <= 64 && lowOnesWidth(threshold).exists(lowBits => lowBits < width)
          } && knownUIntWidth(p).contains(BigInt(1)) =>
        val allowedLowBits = lowOnesWidth(threshold).get
        DoPrim(ArmorLeqLowMask, Seq(value), Seq(allowedLowBits), p.tpe)

      // Keep a general unsigned comparison against a literal as a unary
      // semantic operation.  The SLP packer can consequently require a
      // single common constant for all lanes, independently of whether the
      // original FIRRTL wrote x <= C or C >= x.
      case p @ DoPrim(Leq, Seq(value, literal @ UIntLiteral(constant, _)), Seq(), _)
          if knownUIntWidth(value).exists { width =>
            width >= 2 && width <= 17 && knownUIntWidth(literal).contains(width) &&
              constant >= 0 && constant < (BigInt(1) << width.toInt)
          } && knownUIntWidth(p).contains(BigInt(1)) =>
        DoPrim(ArmorLeqConst, Seq(value), Seq(constant), p.tpe)

      case p @ DoPrim(Geq, Seq(literal @ UIntLiteral(constant, _), value), Seq(), _)
          if knownUIntWidth(value).exists { width =>
            width >= 2 && width <= 17 && knownUIntWidth(literal).contains(width) &&
              constant >= 0 && constant < (BigInt(1) << width.toInt)
          } && knownUIntWidth(p).contains(BigInt(1)) =>
        DoPrim(ArmorLeqConst, Seq(value), Seq(constant), p.tpe)

      // x < 0 is false; x < 1 is x == 0; and x < C is x <= C - 1.
      // Keep these literal cases before the dynamic ArmorLt rule so existing
      // EqConst/LeqConst packed lowerings handle them.
      case p @ DoPrim(Lt, Seq(_, UIntLiteral(constant, _)), Seq(), _)
          if constant == 0 && knownUIntWidth(p).contains(BigInt(1)) =>
        UIntLiteral(0, IntWidth(1))

      case p @ DoPrim(Lt, Seq(value, literal @ UIntLiteral(constant, literalWidth)), Seq(), _)
          if constant == 1 && knownUIntWidth(value).exists(width =>
            knownUIntWidth(literal).contains(width)
          ) && knownUIntWidth(p).contains(BigInt(1)) =>
        DoPrim(Eq, Seq(value, UIntLiteral(0, literalWidth)), Seq.empty, p.tpe)

      case p @ DoPrim(Lt, Seq(value, literal @ UIntLiteral(constant, _)), Seq(), _)
          if knownUIntWidth(value).exists { width =>
            width >= 2 && width <= 17 && knownUIntWidth(literal).contains(width) &&
              constant > 1 && constant < (BigInt(1) << width.toInt)
          } && knownUIntWidth(p).contains(BigInt(1)) =>
        DoPrim(ArmorLeqConst, Seq(value), Seq(constant - 1), p.tpe)

      case p @ DoPrim(Geq, Seq(left, right), Seq(), _)
          if knownUIntWidth(left).exists(width =>
            slpUnsignedCompareWidth(width) && knownUIntWidth(right).contains(width)
          ) &&
            knownUIntWidth(p).contains(BigInt(1)) =>
        DoPrim(ArmorGeq, Seq(left, right), Seq.empty, p.tpe)

      case p @ DoPrim(Leq, Seq(left, right), Seq(), _)
          if knownUIntWidth(left).exists(width =>
            slpUnsignedCompareWidth(width) && knownUIntWidth(right).contains(width)
          ) &&
            knownUIntWidth(p).contains(BigInt(1)) =>
        DoPrim(ArmorGeq, Seq(right, left), Seq.empty, p.tpe)

      case p @ DoPrim(Lt, Seq(left, right), Seq(), _)
          if dynamicCompareOperands(left, right) &&
            knownUIntWidth(left).exists(width =>
              slpUnsignedCompareWidth(width) && knownUIntWidth(right).contains(width)
            ) &&
            knownUIntWidth(p).contains(BigInt(1)) =>
        DoPrim(ArmorLt, Seq(left, right), Seq.empty, p.tpe)

      // Unsigned x > 0b011...1 is precisely the most-significant bit of x.
      // This avoids a lane-wise comparison and keeps the value in the SLP
      // dataflow as an ArmorBitSelect, which can be packed directly.
      case p @ DoPrim(Gt, Seq(left, UIntLiteral(threshold, _)), Seq(), _)
          if knownUIntWidth(left).exists { width =>
            threshold == unsignedTopBitThreshold(width)
          } && knownUIntWidth(p).contains(BigInt(1)) =>
        val width = knownUIntWidth(left).get
        DoPrim(ArmorBitSelect, Seq(left), Seq(width - 1), p.tpe)

      case p @ DoPrim(Gt, Seq(left, right), Seq(), _)
          if dynamicCompareOperands(left, right) &&
            knownUIntWidth(left).exists(width =>
              slpUnsignedCompareWidth(width) && knownUIntWidth(right).contains(width)
            ) &&
            knownUIntWidth(p).contains(BigInt(1)) =>
        DoPrim(ArmorLt, Seq(right, left), Seq.empty, p.tpe)

      case p @ DoPrim(Bits, Seq(arg), Seq(hi, lo), _)
          if knownUIntWidth(arg).exists(width => lo >= 0 && hi >= lo && hi < width) =>
        val resultWidth = hi - lo + 1
        if (hi == lo) extract(p, hi, lo)
        else if (lo == 0 && knownUIntWidth(arg).exists(_ <= 64) && resultWidth <= 64)
          lowMaskAnd(p, resultWidth)
        else extract(p, hi, lo)

      case p @ DoPrim(Head, Seq(arg), Seq(amount), _)
          if knownUIntWidth(arg).exists(width => amount > 0 && amount <= width) =>
        val width = knownUIntWidth(arg).get
        extract(p, width - 1, width - amount)

      case p @ DoPrim(Tail, Seq(arg), Seq(amount), _)
          if knownUIntWidth(arg).exists(width => amount >= 0 && amount < width) =>
        val width = knownUIntWidth(arg).get
        val resultWidth = width - amount
        if (width <= 64 && resultWidth <= 64) lowMaskAnd(p, resultWidth)
        else extract(p, resultWidth - 1, 0)

      case p @ DoPrim(Pad, Seq(arg), Seq(targetWidth), _)
          if knownUIntWidth(arg).exists(sourceWidth => targetWidth > 0 && targetWidth <= sourceWidth) =>
        identity(p)

      case p @ DoPrim(Pad, Seq(arg), Seq(targetWidth), _)
          if knownUIntWidth(arg).exists(sourceWidth => sourceWidth <= 64 && targetWidth > sourceWidth) =>
        val sourceWidth = knownUIntWidth(arg).get
        lowMaskAnd(p, sourceWidth)

      case p @ DoPrim(Pad, Seq(arg), Seq(targetWidth), _)
          if knownUIntWidth(arg).exists(sourceWidth => sourceWidth > 64 && targetWidth > sourceWidth) =>
        DoPrim(ArmorZeroExtend, p.args, Seq(targetWidth), p.tpe)

      case p @ DoPrim(Orr, Seq(arg), Seq(), _)
          if knownUIntWidth(arg).contains(BigInt(1)) =>
        identity(p)

      // A one-bit reduction AND is its input.  Keeping this as an identity
      // lets SLP retain direct pack reuse instead of treating the reduction
      // as a scalar boundary.
      case p @ DoPrim(Andr, Seq(arg), Seq(), _)
          if knownUIntWidth(arg).contains(BigInt(1)) &&
            knownUIntWidth(p).contains(BigInt(1)) =>
        identity(p)

      case other => other
    }
  }

  /** Normalize a module while remembering the original source of every
    * canonical low-bit mask node.
    *
    * ExpressionDecomposePass runs before this pass, so a chain such as
    *
    *   n16 = bits(x17, 15, 0)
    *   n8  = bits(n16, 7, 0)
    *
    * is represented by two DefNodes rather than one nested expression.  The
    * scalar rewrites above turn both operations into ArmorAnd.  This module
    * normalizer then forwards n8 to x17 directly.  The result type and the
    * final low-ones mask are kept unchanged, so this is also correct for a
    * truncate/zero-extend/truncate chain.
    */
  private final class ModuleNormalizer {
    private type LowMaskSources = Map[String, Expression]
    private type Definitions = Map[String, Expression]

    private val bypassedNodes = mutable.HashSet.empty[String]
    private var rewrittenLowBitAddSubCount = 0
    private var removedLowBitAddSubCount = 0

    def rewrittenLowBitAddSubs: Int = rewrittenLowBitAddSubCount
    def removedLowBitAddSubs: Int = removedLowBitAddSubCount

    private def isLowOnes(value: BigInt): Boolean =
      value > 0 && (value & (value + 1)) == 0

    private def lowMaskArgument(e: Expression): Option[Expression] = e match {
      case DoPrim(ArmorAnd, Seq(arg, UIntLiteral(mask, _)), Seq(), _)
          if isLowOnes(mask) =>
        Some(arg)
      case _ => None
    }

    private def referenceName(e: Expression): Option[String] = e match {
      case Reference(name, _, _, _) => Some(name)
      case _                        => None
    }

    private def collapseLowMaskChain(e: Expression, sources: LowMaskSources): Expression = e match {
      case p @ DoPrim(ArmorAnd, Seq(arg, mask: UIntLiteral), Seq(), _)
          if isLowOnes(mask.value) =>
        referenceName(arg).flatMap(name => sources.get(name).map(name -> _)) match {
          case Some((bypassedName, originalSource)) =>
            bypassedNodes += bypassedName
            p.copy(args = Seq(originalSource, mask))
          case None => p
        }
      case other => other
    }

    private def normalizeExpression(e: Expression, sources: LowMaskSources): Expression =
      collapseLowMaskChain(normalizeExpr(e), sources)

    /** The least-significant bit of either a one-bit addition or subtraction
      * is XOR.  ExpressionDecomposePass has already named the arithmetic
      * operation, so recognize the resulting two-node pattern here rather
      * than requiring nested expressions:
      *
      *   wide = add/sub(UInt<1>, UInt<1>) : UInt<2>
      *   low  = bits(wide, 0, 0)           : UInt<1>
      *
      * The rewrite leaves `wide` available when it has another consumer. If
      * the low-bit projection was its only consumer, the ordinary dead-node
      * removal below drops it.  This is deliberately restricted to position
      * zero and two UInt<1> operands: carries and borrows cannot affect that
      * bit, while wider arithmetic would not have the same property.
      */
    /** Normalize the two canonical representations of a one-bit low
      * projection.  `tail(wide, 1)` becomes `ArmorAnd(wide, 1)` earlier in
      * this pass, whereas `bits(wide, 0, 0)` becomes ArmorBitSelect.
      */
    private def lowBitProjectionSource(expression: Expression): Option[Expression] = expression match {
      case DoPrim(ArmorBitSelect, Seq(source), Seq(bitPosition), resultType)
          if bitPosition == 0 && knownUIntTypeWidth(resultType).contains(BigInt(1)) =>
        Some(source)
      case DoPrim(ArmorAnd, Seq(source, UIntLiteral(mask, _)), Seq(), resultType)
          if mask == 1 && knownUIntTypeWidth(resultType).contains(BigInt(1)) =>
        Some(source)
      case _ => None
    }

    private def rewriteLowBitAddSub(
      expression:  Expression,
      definitions: Definitions
    ): Expression = lowBitProjectionSource(expression) match {
      case Some(source) =>
        referenceName(source).flatMap(definitions.get) match {
          case Some(DoPrim(op @ (Add | Sub), Seq(left, right), Seq(), arithmeticType))
              if knownUIntWidth(left).contains(BigInt(1)) &&
                knownUIntWidth(right).contains(BigInt(1)) &&
                knownUIntTypeWidth(arithmeticType).contains(BigInt(2)) =>
            // `source` is no longer used by this projection.  It is removed
            // only if the complete module has no remaining direct consumers.
            bypassedNodes += referenceName(source).get
            rewrittenLowBitAddSubCount += 1
            DoPrim(Xor, Seq(left, right), Seq.empty, expression.tpe)
          case _ => expression
        }
      case None => expression
    }

    private def normalizeExpression(
      e:           Expression,
      sources:     LowMaskSources,
      definitions: Definitions
    ): Expression = rewriteLowBitAddSub(normalizeExpression(e, sources), definitions)

    /** The returned environment contains only definitions visible after the
      * returned statement.  Branch-local definitions are deliberately not
      * allowed to escape their branch.
      */
    def normalizeStatement(
      statement: Statement,
      sources:   LowMaskSources,
      definitions: Definitions = Map.empty
    ): (Statement, LowMaskSources, Definitions) = statement match {
      case Block(statements) =>
        val (normalized, finalSources, finalDefinitions) = statements.foldLeft(
          (Vector.empty[Statement], sources, definitions)
        ) { case ((result, currentSources, currentDefinitions), current) =>
          val (normalizedCurrent, nextSources, nextDefinitions) =
            normalizeStatement(current, currentSources, currentDefinitions)
          (result :+ normalizedCurrent, nextSources, nextDefinitions)
        }
        (Block(normalized), finalSources, finalDefinitions)

      case conditional: Conditionally =>
        val pred = normalizeExpression(conditional.pred, sources, definitions)
        val (conseq, _, _) = normalizeStatement(conditional.conseq, sources, definitions)
        val (alt, _, _) = normalizeStatement(conditional.alt, sources, definitions)
        (conditional.copy(pred = pred, conseq = conseq, alt = alt), sources, definitions)

      case node: DefNode =>
        val value = normalizeExpression(node.value, sources, definitions)
        val nextSources = lowMaskArgument(value) match {
          case Some(source) => sources.updated(node.name, source)
          case None         => sources - node.name
        }
        (node.copy(value = value), nextSources, definitions.updated(node.name, value))

      case other =>
        (other.mapExpr(expression => normalizeExpression(expression, sources, definitions)),
          sources, definitions)
    }

    private def countExpressionReferences(
      expression: Expression,
      counts:     mutable.Map[String, Int]
    ): Unit = expression match {
      case Reference(name, _, _, _) => counts.update(name, counts.getOrElse(name, 0) + 1)
      case other                    => other.foreachExpr(countExpressionReferences(_, counts))
    }

    private def countStatementReferences(
      statement: Statement,
      counts:    mutable.Map[String, Int]
    ): Unit = statement match {
      case Block(statements) => statements.foreach(countStatementReferences(_, counts))
      case conditional: Conditionally =>
        countExpressionReferences(conditional.pred, counts)
        countStatementReferences(conditional.conseq, counts)
        countStatementReferences(conditional.alt, counts)
      // ESSENT's custom statements intentionally leave foreachExpr
      // unimplemented, so visit their expressions explicitly.
      case update: RegUpdate =>
        countExpressionReferences(update.regRef, counts)
        countExpressionReferences(update.expr, counts)
      case write: MemWrite =>
        Seq(write.wrEn, write.wrMask, write.wrAddr, write.wrData)
          .foreach(countExpressionReferences(_, counts))
      case other => other.foreachExpr(countExpressionReferences(_, counts))
    }

    private def removeDeadBypassedNodes(
      statement: Statement,
      counts:    collection.Map[String, Int]
    ): Statement = statement match {
      case Block(statements) =>
        Block(statements.iterator
          .map(removeDeadBypassedNodes(_, counts))
          .filterNot(_ == EmptyStmt)
          .toSeq)
      case conditional: Conditionally =>
        conditional.copy(
          conseq = removeDeadBypassedNodes(conditional.conseq, counts),
          alt = removeDeadBypassedNodes(conditional.alt, counts)
        )
      case node: DefNode
          if bypassedNodes.contains(node.name) && counts.getOrElse(node.name, 0) == 0 =>
        removedLowBitAddSubCount += 1
        EmptyStmt
      case other => other
    }

    def finish(statement: Statement): Statement = {
      val counts = mutable.HashMap.empty[String, Int]
      countStatementReferences(statement, counts)
      removeDeadBypassedNodes(statement, counts)
    }
  }

  /** Def-use rewrite for a masked decode key.
    *
    * A decoder commonly materializes a W-bit masked temporary and then
    * compares it against a family of W-bit literals.  If every use is such a
    * comparison, the temporary may safely change type to UInt<popcount(mask)>
    * and each literal can be compressed by the same mask.  The all-uses rule
    * is essential: it makes this a type-changing rewrite without leaving an
    * old-width reference elsewhere in the module.
    */
  private object MaskedEqWidthReducer {
    private final case class Candidate(
      source: Expression,
      mask: BigInt,
      sourceWidth: Int,
      resultWidth: Int,
      keyWidth: Int
    )
    private final case class Uses(good: Int, bad: Int)
    final case class Stats(keys: Int, comparisons: Int) {
      def +(other: Stats): Stats = Stats(keys + other.keys, comparisons + other.comparisons)
    }

    private def uintWidth(expression: Expression): Option[Int] = expression.tpe match {
      case UIntType(IntWidth(width)) if width > 0 && width <= 64 && width.isValidInt => Some(width.toInt)
      case _ => None
    }

    private def uintTypeWidth(tpe: Type): Option[Int] = tpe match {
      case UIntType(IntWidth(width)) if width > 0 && width <= 64 && width.isValidInt => Some(width.toInt)
      case _ => None
    }

    private def candidate(node: DefNode): Option[Candidate] = node.value match {
      case DoPrim(And, Seq(source, UIntLiteral(mask, _)), Seq(), resultType) =>
        (uintWidth(source), uintTypeWidth(resultType)) match {
          case (Some(sourceWidth), Some(resultWidth))
              if sourceWidth == resultWidth && mask >= 0 =>
            val clippedMask = mask & ((BigInt(1) << sourceWidth) - 1)
            val keyWidth = bitCount(clippedMask, sourceWidth)
            if (keyWidth > 1 && keyWidth < sourceWidth)
              Some(Candidate(source, clippedMask, sourceWidth, resultWidth, keyWidth))
            else None
          case _ => None
        }
      case DoPrim(And, Seq(UIntLiteral(mask, _), source), Seq(), resultType) =>
        candidate(node.copy(value = DoPrim(And, Seq(source, UIntLiteral(mask, IntWidth(mask.bitLength.max(1)))), Seq.empty, resultType)))
      case _ => None
    }

    private def directEqUse(
      expression: Expression,
      candidates: Map[String, Candidate]
    ): Option[(String, UIntLiteral, Boolean)] = expression match {
      case DoPrim(Eq, Seq(reference: Reference, literal: UIntLiteral), Seq(), _) =>
        candidates.get(reference.name).map(_ => (reference.name, literal, false))
      case DoPrim(Eq, Seq(literal: UIntLiteral, reference: Reference), Seq(), _) =>
        candidates.get(reference.name).map(_ => (reference.name, literal, true))
      case _ => None
    }

    private def collectExprUses(
      expression: Expression,
      candidates: Map[String, Candidate],
      uses: mutable.Map[String, Uses]
    ): Unit = directEqUse(expression, candidates) match {
      case Some((name, literal, _)) =>
        val candidate = candidates(name)
        val literalFits = (literal.value & ~candidate.mask) == 0
        val previous = uses.getOrElse(name, Uses(0, 0))
        uses.update(name, if (literalFits) previous.copy(good = previous.good + 1)
          else previous.copy(bad = previous.bad + 1))
      case None => expression match {
        case Reference(name, _, _, _) if candidates.contains(name) =>
          val previous = uses.getOrElse(name, Uses(0, 0))
          uses.update(name, previous.copy(bad = previous.bad + 1))
        case other => other.foreachExpr(child => collectExprUses(child, candidates, uses))
      }
    }

    private def collectStatementUses(
      statement: Statement,
      candidates: Map[String, Candidate],
      uses: mutable.Map[String, Uses]
    ): Unit = statement match {
      case Block(statements) => statements.foreach(collectStatementUses(_, candidates, uses))
      case conditional: Conditionally =>
        collectExprUses(conditional.pred, candidates, uses)
        collectStatementUses(conditional.conseq, candidates, uses)
        collectStatementUses(conditional.alt, candidates, uses)
      case update: RegUpdate =>
        collectExprUses(update.regRef, candidates, uses)
        collectExprUses(update.expr, candidates, uses)
      case write: MemWrite =>
        Seq(write.wrEn, write.wrMask, write.wrAddr, write.wrData)
          .foreach(collectExprUses(_, candidates, uses))
      case node: DefNode => collectExprUses(node.value, candidates, uses)
      case other => other.foreachExpr(expression => collectExprUses(expression, candidates, uses))
    }

    private def rewriteExpression(
      expression: Expression,
      eligible: Map[String, Candidate]
    ): Expression = directEqUse(expression, eligible) match {
      case Some((name, literal, literalOnLeft)) =>
        val candidate = eligible(name)
        val keyType = UIntType(IntWidth(candidate.keyWidth))
        val compressed = UIntLiteral(
          gatherConstant(literal.value, candidate.mask, candidate.sourceWidth),
          IntWidth(candidate.keyWidth)
        )
        expression match {
          case p: DoPrim =>
            val reference = p.args.collectFirst { case ref: Reference => ref }.get
              .copy(tpe = keyType)
            val arguments = if (literalOnLeft) Seq(compressed, reference) else Seq(reference, compressed)
            p.copy(args = arguments)
          case _ => expression
        }
      case None => expression.mapExpr(rewriteExpression(_, eligible))
    }

    private def rewriteStatement(
      statement: Statement,
      localEligible: Map[String, Candidate],
      outerEligible: Map[String, Candidate]
    ): (Statement, Stats) = {
      val eligible = outerEligible ++ localEligible
      statement match {
        // The large generated modules contain deeply nested Blocks.  A
        // candidate is deliberately discovered only in the enclosing module
        // block: recursively discovering candidates here would rescan every
        // ancestor subtree and turn this otherwise linear def-use analysis
        // into a prohibitively expensive traversal.  Outer rewrites still
        // flow into nested scopes, so a top-level decoder key remains safe to
        // use in conditionals and nested blocks.
        case block: Block =>
          val (rewritten, stats) = block.stmts.foldLeft((Vector.empty[Statement], Stats(0, 0))) {
            case ((result, accumulated), child) =>
              val (next, nextStats) = rewriteStatement(child, Map.empty, eligible)
              (result :+ next, accumulated + nextStats)
          }
          (Block(rewritten), stats)
        case conditional: Conditionally =>
          val (conseq, conseqStats) = rewriteStatement(conditional.conseq, Map.empty, eligible)
          val (alt, altStats) = rewriteStatement(conditional.alt, Map.empty, eligible)
          (conditional.copy(
            pred = rewriteExpression(conditional.pred, eligible),
            conseq = conseq,
            alt = alt
          ), conseqStats + altStats)
        case node: DefNode if localEligible.contains(node.name) =>
          val candidate = localEligible(node.name)
          val keyType = UIntType(IntWidth(candidate.keyWidth))
          val gather = DoPrim(ArmorBitGather, Seq(candidate.source), Seq(candidate.mask), keyType)
          (node.copy(value = gather), Stats(1, 0))
        case node: DefNode =>
          val value = rewriteExpression(node.value, eligible)
          (node.copy(value = value), Stats(0, 0))
        case update: RegUpdate =>
          (update.copy(
            regRef = rewriteExpression(update.regRef, eligible),
            expr = rewriteExpression(update.expr, eligible)
          ), Stats(0, 0))
        case write: MemWrite =>
          (write.copy(
            wrEn = rewriteExpression(write.wrEn, eligible),
            wrMask = rewriteExpression(write.wrMask, eligible),
            wrAddr = rewriteExpression(write.wrAddr, eligible),
            wrData = rewriteExpression(write.wrData, eligible)
          ), Stats(0, 0))
        case other =>
          (other.mapExpr(expression => rewriteExpression(expression, eligible)), Stats(0, 0))
      }
    }

    private def countRewrittenComparisons(statement: Statement, eligible: Set[String]): Int = {
      var count = 0
      def visitExpr(expression: Expression): Unit = expression match {
        case DoPrim(Eq, Seq(Reference(name, _, _, _), _: UIntLiteral), Seq(), _)
            if eligible(name) => count += 1
        case DoPrim(Eq, Seq(_: UIntLiteral, Reference(name, _, _, _)), Seq(), _)
            if eligible(name) => count += 1
        case other => other.foreachExpr(visitExpr)
      }
      def visitStatement(s: Statement): Unit = s match {
        case Block(statements) => statements.foreach(visitStatement)
        case conditional: Conditionally => visitExpr(conditional.pred); visitStatement(conditional.conseq); visitStatement(conditional.alt)
        case update: RegUpdate => visitExpr(update.regRef); visitExpr(update.expr)
        case write: MemWrite => Seq(write.wrEn, write.wrMask, write.wrAddr, write.wrData).foreach(visitExpr)
        case node: DefNode => visitExpr(node.value)
        case other => other.foreachExpr(visitExpr)
      }
      visitStatement(statement)
      count
    }

    private def reduceBlock(block: Block, outerEligible: Map[String, Candidate]): (Statement, Stats) = {
      val localCandidates = block.stmts.collect { case node: DefNode =>
        candidate(node).map(node.name -> _)
      }.flatten.toMap
      val uses = mutable.HashMap.empty[String, Uses]
      collectStatementUses(block, localCandidates, uses)
      val localEligible = localCandidates.filter { case (name, _) =>
        val observed = uses.getOrElse(name, Uses(0, 0))
        observed.good > 0 && observed.bad == 0
      }
      val comparisonCount = countRewrittenComparisons(block, localEligible.keySet)
      val (rewritten, childStats) = block.stmts.foldLeft((Vector.empty[Statement], Stats(0, 0))) {
        case ((result, stats), statement) =>
          val (next, nextStats) = rewriteStatement(statement, localEligible, outerEligible)
          (result :+ next, stats + nextStats)
      }
      (Block(rewritten), childStats + Stats(0, comparisonCount))
    }

    def reduce(statement: Statement): (Statement, Stats) = statement match {
      case block: Block => reduceBlock(block, Map.empty)
      case other => rewriteStatement(other, Map.empty, Map.empty)
    }
  }

  override def run(circuit: Circuit): Circuit = {
    ArmorIndexedMuxOriginalTraceRegistry.clear()
    var rewrittenLowBitAddSubs = 0
    var removedLowBitAddSubs = 0
    var compressedMaskedEqKeys = 0
    var compressedMaskedEqComparisons = 0
    val modules = circuit.modules.map {
      case module: Module =>
        val normalizer = new ModuleNormalizer
        val (normalizedBody, _, _) = normalizer.normalizeStatement(module.body, Map.empty)
        val normalized = normalizer.finish(normalizedBody)
        val (body, maskedEqStats) = MaskedEqWidthReducer.reduce(normalized)
        rewrittenLowBitAddSubs += normalizer.rewrittenLowBitAddSubs
        removedLowBitAddSubs += normalizer.removedLowBitAddSubs
        compressedMaskedEqKeys += maskedEqStats.keys
        compressedMaskedEqComparisons += maskedEqStats.comparisons
        module.copy(body = body)
      case extModule: ExtModule => extModule
    }
    logger.info(
      s"Armor low-bit Add/Sub fusion rewrote $rewrittenLowBitAddSubs truncations " +
        s"and eliminated $removedLowBitAddSubs dead Add/Sub nodes"
    )
    logger.info(
      s"Armor masked-Eq compression rewrote $compressedMaskedEqKeys masked keys and " +
        s"$compressedMaskedEqComparisons constant comparisons"
    )
    logger.info("Armor indexed-Mux reduction deferred until SLP residual lowering")
    circuit.copy(modules = modules)
  }
}
