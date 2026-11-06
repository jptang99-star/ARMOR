package armor

import essent.ir.{MemWrite, RegUpdate}
import firrtl._
import firrtl.PrimOps._
import firrtl.ir._
import firrtl.options.Dependency
import firrtl.passes.Pass
import logger.LazyLogging

import scala.collection.mutable

/** Eliminates duplicate pure FIRRTL node expressions before SLP discovery.
  *
  * The pass is deliberately local to a module and statement-order based:
  * a duplicate node is replaced only with an earlier, dominating node in the
  * same lexical scope.  Conditional branches inherit expressions available
  * before the branch, but branch-local aliases never escape to following
  * statements.
  */
object IrCanonicalCsePass extends Pass with LazyLogging {
  override def prerequisites = Seq(Dependency(BitProjectionPromotionPass))
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform): Boolean = false

  private sealed trait ExprKey
  private final case class RefKey(name: String, tpe: String) extends ExprKey
  private final case class UIntLitKey(value: BigInt, width: String) extends ExprKey
  private final case class SIntLitKey(value: BigInt, width: String) extends ExprKey
  private final case class PrimKey(
    op:     String,
    args:   Vector[ExprKey],
    consts: Vector[BigInt],
    tpe:    String)
      extends ExprKey
  private final case class SubFieldKey(base: ExprKey, field: String, tpe: String) extends ExprKey
  private final case class SubIndexKey(base: ExprKey, index: Int, tpe: String) extends ExprKey
  private final case class SubAccessKey(base: ExprKey, index: ExprKey, tpe: String) extends ExprKey

  private final case class Stats(removedNodes: Int, rewrittenRefs: Int) {
    def +(that: Stats): Stats =
      Stats(removedNodes + that.removedNodes, rewrittenRefs + that.rewrittenRefs)
  }
  private object Stats {
    val Empty: Stats = Stats(0, 0)
  }

  private final class ModuleCse(
    initialAliases: Map[String, Expression] = Map.empty,
    initialSeen:    Map[ExprKey, Expression] = Map.empty) {
    private val aliases = mutable.Map.empty[String, Expression] ++ initialAliases
    private val seen = mutable.Map.empty[ExprKey, Expression] ++ initialSeen
    private var stats = Stats.Empty

    def resultStats: Stats = stats

    private def typeKey(tpe: Type): String = tpe.serialize
    private def widthKey(width: Width): String = width.serialize
    private def exprSortKey(key: ExprKey): String = key.toString

    private def isSupportedCsePrim(op: PrimOp): Boolean = op match {
      case And | Or | Xor | Not |
          Eq | Neq | Lt | Leq | Gt | Geq |
          Bits | Head | Tail | Cat |
          Pad | AsUInt | Shl | Shr |
          ArmorAnd | ArmorBitSelect | ArmorBitExtract | ArmorBitGather |
          ArmorIdentity | ArmorLeqLowMask | ArmorLeqConst | ArmorGeq | ArmorLt | ArmorNeq |
          ArmorOneHot =>
        true
      case _ => false
    }

    private def isCommutative(op: PrimOp): Boolean = op match {
      case And | Or | Xor | Eq | Neq | ArmorAnd | ArmorNeq => true
      case _ => false
    }

    private def canonicalRef(name: String, tpe: Type): Expression =
      Reference(name, tpe, NodeKind, SourceFlow)

    private def rewriteRef(ref: WRef): Expression =
      aliases.get(ref.name) match {
        case Some(replacement) if typeKey(replacement.tpe) == typeKey(ref.tpe) =>
          stats = stats.copy(rewrittenRefs = stats.rewrittenRefs + 1)
          replacement
        case _ => ref
      }

    private def rewriteExpression(expression: Expression): Expression = expression match {
      case ref: WRef => rewriteRef(ref)
      case sub: WSubField =>
        sub.copy(expr = rewriteExpression(sub.expr))
      case sub: WSubIndex =>
        sub.copy(expr = rewriteExpression(sub.expr))
      case sub: WSubAccess =>
        sub.copy(expr = rewriteExpression(sub.expr), index = rewriteExpression(sub.index))
      case prim: DoPrim =>
        prim.copy(args = prim.args.map(rewriteExpression))
      case mux: Mux =>
        mux.copy(
          cond = rewriteExpression(mux.cond),
          tval = rewriteExpression(mux.tval),
          fval = rewriteExpression(mux.fval)
        )
      case valid: ValidIf =>
        valid.copy(cond = rewriteExpression(valid.cond), value = rewriteExpression(valid.value))
      case other => other
    }

    /** Rewrites a sink expression without replacing the sink root itself.
      * SubAccess indices may still contain pure computation or aliases and are
      * therefore rewritten.
      */
    private def rewriteLocation(location: Expression): Expression = location match {
      case sub: WSubField =>
        sub.copy(expr = rewriteLocation(sub.expr))
      case sub: WSubIndex =>
        sub.copy(expr = rewriteLocation(sub.expr))
      case sub: WSubAccess =>
        sub.copy(expr = rewriteLocation(sub.expr), index = rewriteExpression(sub.index))
      case other => other
    }

    private def keyOf(expression: Expression): Option[ExprKey] = rewriteExpression(expression) match {
      case ref: WRef =>
        Some(RefKey(ref.name, typeKey(ref.tpe)))
      case UIntLiteral(value, width) =>
        Some(UIntLitKey(value, widthKey(width)))
      case SIntLiteral(value, width) =>
        Some(SIntLitKey(value, widthKey(width)))
      case prim @ DoPrim(op, args, consts, tpe) if isSupportedCsePrim(op) =>
        val argKeys = args.map(keyOf)
        if (argKeys.forall(_.isDefined)) {
          val keys = argKeys.flatten.toVector
          val ordered = if (isCommutative(op)) keys.sortBy(exprSortKey) else keys
          Some(PrimKey(op.toString, ordered, consts.toVector, typeKey(tpe)))
        } else None
      case _: DoPrim => None
      case sub: WSubField =>
        keyOf(sub.expr).map(SubFieldKey(_, sub.name, typeKey(sub.tpe)))
      case sub: WSubIndex =>
        keyOf(sub.expr).map(SubIndexKey(_, sub.value, typeKey(sub.tpe)))
      case sub: WSubAccess =>
        for {
          baseKey <- keyOf(sub.expr)
          indexKey <- keyOf(sub.index)
        } yield SubAccessKey(baseKey, indexKey, typeKey(sub.tpe))
      case _ => None
    }

    private def nodeValueKey(expression: Expression): Option[ExprKey] =
      expression match {
        case prim: DoPrim => keyOf(prim)
        case _            => None
      }

    private def rewriteStatement(statement: Statement): Vector[Statement] = statement match {
      case EmptyStmt => Vector.empty
      case Block(statements) =>
        Vector(Block(statements.toVector.flatMap(rewriteStatement)))
      case node @ DefNode(_, name, value) =>
        val rewrittenValue = rewriteExpression(value)
        nodeValueKey(rewrittenValue) match {
          case Some(key) =>
            seen.get(key) match {
              case Some(existing) if typeKey(existing.tpe) == typeKey(rewrittenValue.tpe) =>
                aliases(name) = existing
                stats = stats.copy(removedNodes = stats.removedNodes + 1)
                Vector.empty
              case _ =>
                seen(key) = canonicalRef(name, rewrittenValue.tpe)
                Vector(node.copy(value = rewrittenValue))
            }
          case None =>
            Vector(node.copy(value = rewrittenValue))
        }
      case conditional: Conditionally =>
        val rewrittenPred = rewriteExpression(conditional.pred)
        val rewrittenConseq = rewriteAliasesOnlyStatement(conditional.conseq)
        val rewrittenAlt = rewriteAliasesOnlyStatement(conditional.alt)
        Vector(conditional.copy(pred = rewrittenPred, conseq = rewrittenConseq, alt = rewrittenAlt))
      case connect: Connect =>
        Vector(connect.copy(loc = rewriteLocation(connect.loc), expr = rewriteExpression(connect.expr)))
      case connect: PartialConnect =>
        Vector(connect.copy(loc = rewriteLocation(connect.loc), expr = rewriteExpression(connect.expr)))
      case update: RegUpdate =>
        Vector(update.copy(regRef = rewriteLocation(update.regRef), expr = rewriteExpression(update.expr)))
      case write: MemWrite =>
        Vector(write.copy(
          wrEn = rewriteExpression(write.wrEn),
          wrMask = rewriteExpression(write.wrMask),
          wrAddr = rewriteExpression(write.wrAddr),
          wrData = rewriteExpression(write.wrData)
        ))
      case other =>
        Vector(other.mapExpr(rewriteExpression))
    }

    private def rewriteAliasesOnlyStatement(statement: Statement): Statement = statement match {
      case EmptyStmt => EmptyStmt
      case Block(statements) =>
        Block(statements.map(rewriteAliasesOnlyStatement))
      case node: DefNode =>
        node.copy(value = rewriteExpression(node.value))
      case conditional: Conditionally =>
        conditional.copy(
          pred = rewriteExpression(conditional.pred),
          conseq = rewriteAliasesOnlyStatement(conditional.conseq),
          alt = rewriteAliasesOnlyStatement(conditional.alt)
        )
      case connect: Connect =>
        connect.copy(loc = rewriteLocation(connect.loc), expr = rewriteExpression(connect.expr))
      case connect: PartialConnect =>
        connect.copy(loc = rewriteLocation(connect.loc), expr = rewriteExpression(connect.expr))
      case update: RegUpdate =>
        update.copy(regRef = rewriteLocation(update.regRef), expr = rewriteExpression(update.expr))
      case write: MemWrite =>
        write.copy(
          wrEn = rewriteExpression(write.wrEn),
          wrMask = rewriteExpression(write.wrMask),
          wrAddr = rewriteExpression(write.wrAddr),
          wrData = rewriteExpression(write.wrData)
        )
      case other =>
        other.mapExpr(rewriteExpression)
    }

    def rewriteRootStatement(statement: Statement): Statement = statement match {
      case Block(statements) =>
        Block(statements.toVector.flatMap(rewriteStatement))
      case other =>
        rewriteStatement(other) match {
          case Vector(single) => single
          case many          => Block(many)
        }
    }
  }

  override def run(circuit: Circuit): Circuit = {
    var removedNodes = 0
    var rewrittenRefs = 0
    val modules = circuit.modules.map {
      case module: Module =>
        val cse = new ModuleCse
        val body = cse.rewriteRootStatement(module.body)
        val stats = cse.resultStats
        removedNodes += stats.removedNodes
        rewrittenRefs += stats.rewrittenRefs
        module.copy(body = body)
      case extModule: ExtModule => extModule
    }
    logger.info(
      s"Armor IR canonical CSE removed $removedNodes duplicate nodes and rewrote $rewrittenRefs references"
    )
    circuit.copy(modules = modules)
  }
}
