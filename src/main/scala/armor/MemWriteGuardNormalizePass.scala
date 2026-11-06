package armor

import essent.ir.MemWrite
import firrtl._
import firrtl.PrimOps.And
import firrtl.ir._
import firrtl.options.Dependency
import firrtl.passes.Pass
import logger.LazyLogging

/** Canonicalizes MemWrite side-effect guards.
  *
  * ESSENT emits a memory write as a side-effect statement guarded by both
  * wrEn and wrMask.  ExpressionDecomposePass already materializes both fields
  * independently, but the final side-effect guard still has two IR operands:
  *
  *   if (update_registers && wrEn && wrMask) mem[addr] = data
  *
  * This pass folds that pair into one explicit UInt<1> enable and rewrites the
  * mask to UInt<1>(1):
  *
  *   guard = wrEn & wrMask
  *   MemWrite(wrEn = guard, wrMask = 1, ...)
  *
  * Keeping this as an IR normalization lets normal SLP discovery see the guard
  * as a regular node, instead of adding MemWrite-specific matching in the C++
  * emitter.
  */
object MemWriteGuardNormalizePass extends Pass with LazyLogging {
  override def prerequisites = Seq(Dependency(BitOpNormalizePass))
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform): Boolean = false

  private val UInt1Type: UIntType = UIntType(IntWidth(1))
  private val UInt1One: UIntLiteral = UIntLiteral(1, IntWidth(1))
  private val UInt1Zero: UIntLiteral = UIntLiteral(0, IntWidth(1))

  private def isUInt1(expression: Expression): Boolean = expression.tpe match {
    case UIntType(IntWidth(width)) => width == 1
    case _                         => false
  }

  private def literalValue(expression: Expression): Option[BigInt] = expression match {
    case UIntLiteral(value, IntWidth(width)) if width == 1 => Some(value)
    case _                                                 => None
  }

  private def isUInt1One(expression: Expression): Boolean =
    literalValue(expression).contains(BigInt(1))

  private def isUInt1Zero(expression: Expression): Boolean =
    literalValue(expression).contains(BigInt(0))

  private def sameExpression(left: Expression, right: Expression): Boolean =
    left.serialize == right.serialize && left.tpe.serialize == right.tpe.serialize

  private final class ModuleNormalizer(namespace: Namespace) {
    private var normalizedWrites = 0
    private var insertedGuards = 0
    private var constantGuards = 0

    def stats: (Int, Int, Int) = (normalizedWrites, insertedGuards, constantGuards)

    private def guardRef(name: String): Reference =
      Reference(name, UInt1Type, NodeKind, SourceFlow)

    private def normalizeMemWrite(write: MemWrite): Vector[Statement] = {
      if (!isUInt1(write.wrEn) || !isUInt1(write.wrMask) || isUInt1One(write.wrMask)) {
        Vector(write)
      } else {
        normalizedWrites += 1
        if (isUInt1Zero(write.wrEn) || isUInt1Zero(write.wrMask)) {
          constantGuards += 1
          Vector(write.copy(wrEn = UInt1Zero, wrMask = UInt1One))
        } else if (isUInt1One(write.wrEn)) {
          Vector(write.copy(wrEn = write.wrMask, wrMask = UInt1One))
        } else if (sameExpression(write.wrEn, write.wrMask)) {
          Vector(write.copy(wrEn = write.wrEn, wrMask = UInt1One))
        } else {
          val name = namespace.newName("_armor_memwrite_guard")
          val guard = DoPrim(And, Seq(write.wrEn, write.wrMask), Seq.empty, UInt1Type)
          insertedGuards += 1
          Vector(
            DefNode(NoInfo, name, guard),
            write.copy(wrEn = guardRef(name), wrMask = UInt1One)
          )
        }
      }
    }

    private def normalizeStatement(statement: Statement): Vector[Statement] = statement match {
      case EmptyStmt => Vector.empty
      case Block(statements) =>
        Vector(Block(statements.toVector.flatMap(normalizeStatement)))
      case conditional: Conditionally =>
        Vector(conditional.copy(
          conseq = normalizeRoot(conditional.conseq),
          alt = normalizeRoot(conditional.alt)
        ))
      case write: MemWrite => normalizeMemWrite(write)
      case other           => Vector(other)
    }

    def normalizeRoot(statement: Statement): Statement = statement match {
      case Block(statements) =>
        Block(statements.toVector.flatMap(normalizeStatement))
      case other =>
        normalizeStatement(other) match {
          case Vector(single) => single
          case many          => Block(many)
        }
    }
  }

  override def run(circuit: Circuit): Circuit = {
    var normalizedWrites = 0
    var insertedGuards = 0
    var constantGuards = 0

    val modules = circuit.modules.map {
      case module: Module =>
        val normalizer = new ModuleNormalizer(Namespace(module))
        val body = normalizer.normalizeRoot(module.body)
        val (writes, inserted, constants) = normalizer.stats
        normalizedWrites += writes
        insertedGuards += inserted
        constantGuards += constants
        module.copy(body = body)
      case extModule: ExtModule => extModule
    }

    logger.info(
      s"Armor MemWrite guard normalize rewrote $normalizedWrites writes, " +
        s"inserted $insertedGuards guards, folded $constantGuards constant guards"
    )
    circuit.copy(modules = modules)
  }
}
