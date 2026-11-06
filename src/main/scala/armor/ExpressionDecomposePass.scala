package armor

import essent.ir.{MemWrite, RegUpdate}
import firrtl._
import firrtl.ir._
import firrtl.passes.Pass

/** Converts nested scalar expressions to a local, A-normal form.
  *
  * Generated nodes are inserted immediately before the statement that uses
  * them.  Nodes inside a conditional remain inside that conditional, so this
  * pass never makes a branch-local computation unconditional.  A fresh
  * Namespace is used for every module; consequently the transform has no
  * global mutable state and is deterministic and idempotent.
  */
object ExpressionDecomposePass extends Pass {
  override def prerequisites = Seq.empty
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform): Boolean = false

  private final class ModuleLowerer(namespace: Namespace) {
    private type LoweredExpr = (Vector[Statement], Expression)

    private def nodeRef(name: String, tpe: Type): Reference =
      Reference(name, tpe, NodeKind, SourceFlow)

    /** Expressions which can be consumed without introducing another node.
      * Ref-like expressions are already names/paths; only a SubAccess index
      * can itself contain computation, and that index is lowered separately.
      */
    private def isLeaf(e: Expression): Boolean = e match {
      case _: Literal | _: Reference | _: SubField | _: SubIndex | _: SubAccess => true
      case _                                                                    => false
    }

    private def materialize(prefix: Vector[Statement], value: Expression): LoweredExpr = {
      if (isLeaf(value)) (prefix, value)
      else {
        val name = namespace.newName("_armor_expr")
        (prefix :+ DefNode(NoInfo, name, value), nodeRef(name, value.tpe))
      }
    }

    private def lowerAsLeaf(e: Expression): LoweredExpr = {
      val (prefix, value) = lowerExpr(e)
      materialize(prefix, value)
    }

    /** Rebuild a reference path without turning the path itself into a node. */
    private def lowerPath(e: Expression): LoweredExpr = e match {
      case sf: SubField =>
        val (prefix, base) = lowerPath(sf.expr)
        (prefix, sf.copy(expr = base))
      case si: SubIndex =>
        val (prefix, base) = lowerPath(si.expr)
        (prefix, si.copy(expr = base))
      case sa: SubAccess =>
        val (basePrefix, base) = lowerPath(sa.expr)
        val (indexPrefix, index) = lowerAsLeaf(sa.index)
        (basePrefix ++ indexPrefix, sa.copy(expr = base, index = index))
      case other => lowerExpr(other)
    }

    private def lowerExpr(e: Expression): LoweredExpr = e match {
      case m: Mux =>
        val (condPrefix, cond) = lowerAsLeaf(m.cond)
        val (truePrefix, tval) = lowerAsLeaf(m.tval)
        val (falsePrefix, fval) = lowerAsLeaf(m.fval)
        (condPrefix ++ truePrefix ++ falsePrefix, m.copy(cond = cond, tval = tval, fval = fval))

      case p: DoPrim =>
        val (prefix, args) = lowerMany(p.args, lowerAsLeaf)
        (prefix, p.copy(args = args))

      case v: ValidIf =>
        val (condPrefix, cond) = lowerAsLeaf(v.cond)
        val (valuePrefix, value) = lowerAsLeaf(v.value)
        (condPrefix ++ valuePrefix, v.copy(cond = cond, value = value))

      case path @ (_: SubField | _: SubIndex | _: SubAccess) => lowerPath(path)
      case other                                              => (Vector.empty, other)
    }

    private def lowerMany(
      expressions: Seq[Expression],
      lower:       Expression => LoweredExpr
    ): (Vector[Statement], Seq[Expression]) = {
      expressions.foldLeft((Vector.empty[Statement], Vector.empty[Expression])) {
        case ((allStatements, allExpressions), expression) =>
          val (statements, result) = lower(expression)
          (allStatements ++ statements, allExpressions :+ result)
      }
    }

    private def lowerRoot(e: Expression): LoweredExpr = lowerAsLeaf(e)

    def lowerStatement(s: Statement): Statement = s match {
      case b: Block =>
        Block(b.stmts.flatMap(statement => flatten(lowerStatement(statement))))

      case c: Conditionally =>
        val (predPrefix, pred) = lowerRoot(c.pred)
        Block(predPrefix :+ c.copy(
          pred = pred,
          conseq = lowerStatement(c.conseq),
          alt = lowerStatement(c.alt)
        ))

      case d: DefNode =>
        val (prefix, value) = lowerExpr(d.value)
        Block(prefix :+ d.copy(value = value))

      case c: Connect =>
        val (locPrefix, loc) = lowerPath(c.loc)
        val (exprPrefix, expr) = lowerRoot(c.expr)
        Block(locPrefix ++ exprPrefix :+ c.copy(loc = loc, expr = expr))

      case c: PartialConnect =>
        val (locPrefix, loc) = lowerPath(c.loc)
        val (exprPrefix, expr) = lowerRoot(c.expr)
        Block(locPrefix ++ exprPrefix :+ c.copy(loc = loc, expr = expr))

      case r: RegUpdate =>
        val (locPrefix, loc) = lowerPath(r.regRef)
        val (exprPrefix, expr) = lowerRoot(r.expr)
        Block(locPrefix ++ exprPrefix :+ r.copy(regRef = loc, expr = expr))

      case m: MemWrite =>
        val (enPrefix, en) = lowerRoot(m.wrEn)
        val (maskPrefix, mask) = lowerRoot(m.wrMask)
        val (addrPrefix, addr) = lowerRoot(m.wrAddr)
        val (dataPrefix, data) = lowerRoot(m.wrData)
        Block(enPrefix ++ maskPrefix ++ addrPrefix ++ dataPrefix :+
          m.copy(wrEn = en, wrMask = mask, wrAddr = addr, wrData = data))

      // Keep Print arguments scalar and lazily evaluated by the emitter, but
      // make the FIR enable a normal named combinational value.  This lets
      // repeated assertion/printf guards participate in SLP while the Print
      // statement itself remains a scalar side-effect boundary.
      case p: Print =>
        val (enPrefix, en) = lowerRoot(p.en)
        Block(enPrefix :+ p.copy(en = en))

      // Stop has the same pure FIR enable semantics as Print.  Extract only
      // that enable; its clock and return code are statement metadata, and
      // the Stop itself must remain scalar because it has a side effect.
      case st: Stop =>
        val (enPrefix, en) = lowerRoot(st.en)
        Block(enPrefix :+ st.copy(en = en))

      case other => other
    }

    private def flatten(s: Statement): Seq[Statement] = s match {
      case Block(stmts) => stmts.flatMap(flatten)
      case EmptyStmt    => Seq.empty
      case other        => Seq(other)
    }
  }

  override def run(circuit: Circuit): Circuit = {
    circuit.copy(modules = circuit.modules.map {
      case module: Module =>
        val lowerer = new ModuleLowerer(Namespace(module))
        module.copy(body = lowerer.lowerStatement(module.body))
      case extModule: ExtModule => extModule
    })
  }
}
