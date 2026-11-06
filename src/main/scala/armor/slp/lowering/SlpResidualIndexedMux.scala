package armor.slp

import armor.{ArmorIndexedMuxOriginalStep, ArmorIndexedMuxOriginalTrace}
import essent.ir.{MemWrite, RegUpdate}
import firrtl.PrimOps.Eq
import firrtl.ir._

import scala.collection.mutable

/** Indexed-mux lowering left over after ordinary SLP packing has had first
  * refusal.  This is intentionally a lowering overlay, not a FIRRTL rewrite:
  * it keeps StatementGraph stable while letting the final emitter compress
  * only decoder chains which were not claimed by SLP packs.
  */
final case class SlpResidualIndexedMux(
  rootNodeId:     Int,
  selector:       Expression,
  values:         Vector[Expression],
  resultType:     Type,
  absorbedNodeIds: Set[Int],
  inputNodeIds:   Set[Int],
  trace:          ArmorIndexedMuxOriginalTrace
) {
  val selectorWidth: Int = selector.tpe match {
    case UIntType(IntWidth(width)) if width > 0 && width.isValidInt => width.toInt
    case other => throw new IllegalArgumentException(s"invalid indexed-mux selector type: $other")
  }

  require(rootNodeId >= 0)
  require(values.nonEmpty)
  require(values.size == 1 << selectorWidth)
  require(absorbedNodeIds.forall(_ >= 0))
  require(!absorbedNodeIds(rootNodeId))
  require(inputNodeIds.forall(_ >= 0))

  val scalarUses: Set[(Int, Int)] =
    inputNodeIds.iterator.filter(_ != rootNodeId).map(_ -> rootNodeId).toSet
}

final case class SlpResidualIndexedMuxPlan(muxes: Vector[SlpResidualIndexedMux]) {
  require(muxes.map(_.rootNodeId) == muxes.map(_.rootNodeId).distinct.sorted)

  val byRootNodeId: Map[Int, SlpResidualIndexedMux] =
    muxes.iterator.map(mux => mux.rootNodeId -> mux).toMap
  val absorbedNodeIds: Set[Int] =
    muxes.iterator.flatMap(_.absorbedNodeIds).toSet
  val scalarUses: Set[(Int, Int)] =
    muxes.iterator.flatMap(_.scalarUses).toSet
}

object SlpResidualIndexedMuxPlan {
  val Empty: SlpResidualIndexedMuxPlan = SlpResidualIndexedMuxPlan(Vector.empty)
}

object SlpResidualIndexedMuxPlanner {
  private final case class EqTest(selector: Expression, value: Int, nodeId: Option[Int])

  private final case class Candidate(
    rootNodeId:   Int,
    rootName:     String,
    selector:     Expression,
    values:       Vector[Expression],
    resultType:   Type,
    absorbedMuxes: Set[Int],
    absorbedEqs:  Set[Int],
    inputNodeIds: Set[Int],
    trace:        ArmorIndexedMuxOriginalTrace
  ) {
    val absorbedNodeIds: Set[Int] = absorbedMuxes ++ absorbedEqs
    val chainNodeIds: Set[Int] = absorbedNodeIds + rootNodeId
  }

  private final case class Definition(nodeId: Int, node: DefNode)

  private def uintWidth(expression: Expression): Option[Int] = expression.tpe match {
    case UIntType(IntWidth(width)) if width > 0 && width.isValidInt => Some(width.toInt)
    case _                                                          => None
  }

  private def expressionName(expression: Expression): Option[String] = expression match {
    case Reference(name, _, _, _)   => Some(name)
    case SubField(base, name, _, _) => expressionName(base).map(prefix => s"$prefix.$name")
    case _                          => None
  }

  private def expressionReferences(expression: Expression): Set[String] = expressionName(expression) match {
    case Some(name) => Set(name)
    case None =>
      val names = mutable.HashSet.empty[String]
      expression.foreachExpr(child => names ++= expressionReferences(child))
      names.toSet
  }

  private def sameExpression(left: Expression, right: Expression): Boolean =
    left.serialize == right.serialize && left.tpe == right.tpe

  private def decodeEq(
    expression: Expression,
    definitions: Map[String, Definition]
  ): Option[EqTest] = {
    val candidate = expression match {
      case Reference(name, _, _, _) => definitions.get(name).map(definition =>
        (definition.node.value, Some(definition.nodeId))
      )
      case other => Some((other, None))
    }
    candidate.flatMap {
      case (DoPrim(Eq, Seq(left, right), Seq(), _), nodeId) =>
        (left, right) match {
          case (UIntLiteral(value, _), selector) if value >= 0 && value.isValidInt =>
            Some(EqTest(selector, value.toInt, nodeId))
          case (selector, UIntLiteral(value, _)) if value >= 0 && value.isValidInt =>
            Some(EqTest(selector, value.toInt, nodeId))
          case _ => None
        }
      case _ => None
    }
  }

  private def statementReferences(statement: Statement): Set[String] = statement match {
    case Block(statements) => statements.iterator.flatMap(statementReferences).toSet
    case conditional: Conditionally =>
      expressionReferences(conditional.pred) ++ statementReferences(conditional.conseq) ++
        statementReferences(conditional.alt)
    case node: DefNode => expressionReferences(node.value)
    case update: RegUpdate => expressionReferences(update.regRef) ++ expressionReferences(update.expr)
    case write: MemWrite => expressionReferences(write.wrEn) ++ expressionReferences(write.wrMask) ++
      expressionReferences(write.wrAddr) ++ expressionReferences(write.wrData)
    case connect: Connect => expressionReferences(connect.loc) ++ expressionReferences(connect.expr)
    case print: Print => expressionReferences(print.en) ++ print.args.flatMap(expressionReferences)
    case stop: Stop => expressionReferences(stop.en)
    case other =>
      val result = mutable.HashSet.empty[String]
      other.foreachExpr(expression => result ++= expressionReferences(expression))
      result.toSet
  }

  private def decodeChain(
    context: SlpAnalysisContext,
    rootNodeId: Int,
    definitions: Map[String, Definition]
  ): Option[Candidate] = {
    val view = context.graph
    val root = view.node(rootNodeId).statement match {
      case node: DefNode => node
      case _             => return None
    }
    val values = mutable.HashMap.empty[Int, Expression]
    val muxes = mutable.HashSet.empty[Int]
    val eqs = mutable.HashSet.empty[Int]
    val steps = mutable.ArrayBuffer.empty[ArmorIndexedMuxOriginalStep]
    var selector: Option[Expression] = None
    var current = root.value
    var currentNodeId = rootNodeId
    var currentName = root.name
    var continue = true

    while (continue) current match {
      case Mux(condition, trueValue, falseValue, resultType) =>
        decodeEq(condition, definitions) match {
          case Some(test) if test.value > 0 &&
              selector.forall(sameExpression(_, test.selector)) && !values.contains(test.value) =>
            selector = Some(test.selector)
            values.update(test.value, trueValue)
            steps += ArmorIndexedMuxOriginalStep(
              targetName = currentName,
              resultType = resultType,
              selector = test.selector,
              indexValue = test.value,
              trueValue = trueValue,
              falseValue = falseValue
            )
            test.nodeId.foreach(eqs += _)
            falseValue match {
              case Reference(nextName, _, _, _) if definitions.get(nextName).exists { definition =>
                  definition.node.value.isInstanceOf[Mux]
                } =>
                val next = definitions(nextName)
                muxes += next.nodeId
                currentNodeId = next.nodeId
                currentName = next.node.name
                current = next.node.value
              case base =>
                values.update(0, base)
                continue = false
            }
          case _ => return None
        }
      case _ => return None
    }

    for {
      selected <- selector
      indexWidth <- uintWidth(selected)
      resultWidth <- uintWidth(root.value)
      if resultWidth > 0 && resultWidth <= 64 && indexWidth > 0 && indexWidth <= 6
      laneCount = 1 << indexWidth
      if values.keySet == (0 until laneCount).toSet
      ordered = (0 until laneCount).map(values).toVector
      if ordered.forall(uintWidth(_).contains(resultWidth))
    } yield {
      val moduleName = view.node(rootNodeId).module.map(_.moduleName).getOrElse("")
      val inputNames = (expressionReferences(selected) ++ ordered.flatMap(expressionReferences)).toSet
      val inputNodeIds = inputNames.flatMap(view.graph.nameToID.get)
      Candidate(
        rootNodeId = rootNodeId,
        rootName = root.name,
        selector = selected,
        values = ordered,
        resultType = root.value.tpe,
        absorbedMuxes = muxes.toSet,
        absorbedEqs = eqs.toSet,
        inputNodeIds = inputNodeIds,
        trace = ArmorIndexedMuxOriginalTrace(moduleName, root.name, steps.reverse.toVector)
      )
    }
  }

  /** Returns absorbed nodes which remain live through uses outside chosen
    * residual roots.  Such nodes are not suppressed; keeping them may duplicate
    * a suffix for an external user, but preserves semantics.
    */
  private def retainedAbsorbedNodes(
    context: SlpAnalysisContext,
    candidates: Vector[Candidate]
  ): Set[Int] = {
    val view = context.graph
    val chosenRoots = candidates.iterator.map(_.rootNodeId).toSet
    val absorbed = candidates.iterator.flatMap(_.absorbedNodeIds).toSet
    val retained = mutable.HashSet.empty[Int]

    view.validNodeIds.foreach { nodeId =>
      if (!chosenRoots(nodeId) && !absorbed(nodeId)) {
        statementReferences(view.node(nodeId).statement).foreach { name =>
          view.graph.nameToID.get(name).filter(absorbed).foreach(retained += _)
        }
      }
    }

    var changed = true
    while (changed) {
      changed = false
      retained.toVector.foreach { nodeId =>
        statementReferences(view.node(nodeId).statement).foreach { name =>
          view.graph.nameToID.get(name).filter(absorbed).foreach { dependency =>
            val before = retained.size
            retained += dependency
            changed = changed || retained.size != before
          }
        }
      }
    }
    retained.toSet
  }

  def build(
    context: SlpAnalysisContext,
    packGraph: SlpPackGraph,
    regPacking: Option[SlpRegPackingResult] = None
  ): SlpResidualIndexedMuxPlan = {
    val view = context.graph
    val blockedNodeIds =
      packGraph.nodeToPackId.keySet ++
        packGraph.absorbedNodeIds ++
        regPacking.toVector.flatMap(_.packs).flatMap(_.nodeIds).toSet

    val definitions = view.validNodeIds.flatMap { nodeId =>
      view.node(nodeId).statement match {
        case node: DefNode => Some(node.name -> Definition(nodeId, node))
        case _             => None
      }
    }.toMap
    val falseBranchNodeIds = definitions.valuesIterator.collect {
      case Definition(_, DefNode(_, _, Mux(_, _, Reference(name, _, _, _), _)))
          if definitions.contains(name) =>
        definitions(name).nodeId
    }.toSet

    val candidates = view.validNodeIds
      .filterNot(falseBranchNodeIds)
      .filterNot(blockedNodeIds)
      .flatMap(nodeId => decodeChain(context, nodeId, definitions))
      .filter(candidate => candidate.chainNodeIds.intersect(blockedNodeIds).isEmpty)
      .sortBy(_.rootNodeId)

    val chosenByRoot = candidates.map(candidate => candidate.rootNodeId -> candidate).toMap
    val retained = retainedAbsorbedNodes(context, chosenByRoot.values.toVector)
    val muxes = chosenByRoot.values.toVector.sortBy(_.rootNodeId).map { candidate =>
      SlpResidualIndexedMux(
        rootNodeId = candidate.rootNodeId,
        selector = candidate.selector,
        values = candidate.values,
        resultType = candidate.resultType,
        absorbedNodeIds = candidate.absorbedNodeIds -- retained,
        inputNodeIds = candidate.inputNodeIds,
        trace = candidate.trace
      )
    }

    SlpResidualIndexedMuxPlan(muxes)
  }
}
