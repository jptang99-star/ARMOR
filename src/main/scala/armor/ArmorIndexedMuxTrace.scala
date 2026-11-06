package armor

import firrtl.ir.{Expression, Type}

import scala.collection.mutable

/** Trace-only metadata for ArmorIndexedMux.
  *
  * ArmorIndexedMux is a semantic compression of a priority-Mux decoder.
  * During lowering we sometimes emit a faster indexed read instead of the
  * original scalar chain.  These records preserve the original DefNode names
  * for comment-only lowering; they must not affect IR semantics.
  */
final case class ArmorIndexedMuxOriginalStep(
  targetName: String,
  resultType: Type,
  selector:   Expression,
  indexValue: Int,
  trueValue:  Expression,
  falseValue: Expression
)

final case class ArmorIndexedMuxOriginalTrace(
  moduleName: String,
  rootName:   String,
  steps:      Vector[ArmorIndexedMuxOriginalStep]
)

object ArmorIndexedMuxOriginalTraceRegistry {
  private val byModuleAndRoot =
    mutable.HashMap.empty[(String, String), ArmorIndexedMuxOriginalTrace]

  def clear(): Unit = byModuleAndRoot.clear()

  def register(trace: ArmorIndexedMuxOriginalTrace): Unit =
    if (trace.steps.nonEmpty)
      byModuleAndRoot.update((trace.moduleName, trace.rootName), trace)

  def get(moduleName: String, rootName: String): Option[ArmorIndexedMuxOriginalTrace] =
    byModuleAndRoot.get((moduleName, rootName))

  def get(rootName: String): Option[ArmorIndexedMuxOriginalTrace] =
    byModuleAndRoot.collectFirst { case ((_, `rootName`), trace) => trace }
}
