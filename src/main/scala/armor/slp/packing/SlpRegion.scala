package armor.slp

import essent.ir.{MemWrite, RegUpdate}
import firrtl.ir.{Connect, DefNode, Expression, Reference, SubField, SubIndex}

/** A packed operation whose externally visible input/output boundaries differ
  * from an internal scalar expression chain.
  *
  * The root remains the node represented by the SlpPack. Internal nodes are
  * semantically absorbed by the region and must not be scheduled separately.
  */
final case class SlpRegion(
  rootNodeId:      Int,
  operation:       SlpOperation,
  internalNodeIds: Vector[Int]
) {
  require(rootNodeId >= 0)
  require(internalNodeIds.nonEmpty)
  require(!internalNodeIds.contains(rootNodeId))
  require(internalNodeIds.distinct.size == internalNodeIds.size)
}

object SlpRegionBuilder {
  private def lowMask(width: Int): BigInt = (BigInt(1) << width) - 1

  private def referenceName(expression: Expression): Option[String] = expression match {
    case Reference(name, _, _, _)   => Some(name)
    case SubField(base, name, _, _) => referenceName(base).map(prefix => s"$prefix.$name")
    case SubIndex(base, index, _, _) => referenceName(base).map(prefix => s"${prefix}_$index")
    case _                          => None
  }

  /** Build the first boundary-aware region: UInt<16> + 1 -> UInt<17>, followed
    * by a low-16 projection. The transient carry bit remains inside the region;
    * both materialized boundaries are four-packable UInt<16> vectors.
    */
  def build(context: SlpAnalysisContext): Vector[SlpRegion] = {
    val view = context.graph
    val classified = context.classifications.collect {
      case (nodeId, SlpSupported(operation)) => nodeId -> operation
    }.toMap

    /** StatementGraph fanout intentionally crosses eliminated Connect nodes.
      * Region ownership instead needs the direct IR consumers of a value.
      */
    val directConsumerIdsBySignal = view.validNodeIds.flatMap { nodeId =>
      val inputNames = classified.get(nodeId).map(_.operands.collect {
        case SlpSignal(name, _) => name
      }).getOrElse(view.node(nodeId).statement match {
        case DefNode(_, _, value) => referenceName(value).toVector
        case Connect(_, _, expr)  => referenceName(expr).toVector
        case update: RegUpdate    => referenceName(update.expr).toVector
        case write: MemWrite      =>
          Vector(write.wrEn, write.wrMask, write.wrAddr, write.wrData).flatMap(referenceName)
        case _ => Vector.empty
      })
      inputNames.distinct.map(_ -> nodeId)
    }.groupMap(_._1)(_._2).view.mapValues(_.distinct.sorted).toMap

    def directConsumers(signalName: String): Vector[Int] =
      directConsumerIdsBySignal.getOrElse(signalName, Vector.empty)

    def validTruncatingSubOperands(resultWidth: Int, operands: Vector[SlpOperand]): Boolean =
      operands.size == 2 &&
        operands.exists(_.isInstanceOf[SlpSignal]) &&
        operands.forall {
          case SlpSignal(_, width) => width <= resultWidth
          case SlpUIntConstant(value, width) => value >= 0 && width <= resultWidth
        }

    val candidates = classified.toVector.flatMap { case (rootNodeId, rootOperation) =>
      rootOperation match {
        case SlpOperation(
            SlpMaskedAnd,
            16,
            _,
            Vector(SlpSignal(sourceName, 17), SlpUIntConstant(mask, 16)),
            _,
            rootStatement
          ) if mask == lowMask(16) =>
          view.graph.nameToID.get(sourceName).flatMap { addNodeId =>
            classified.get(addNodeId).flatMap {
              case addOperation @ SlpOperation(
                  SlpAdd,
                  17,
                  _,
                  Vector(SlpSignal(_, 16), SlpUIntConstant(constantValue, constantWidth)),
                  _,
                  _
                ) if constantValue == 1 && constantWidth <= 16 &&
                    directConsumers(sourceName) == Vector(rootNodeId) &&
                    view.node(addNodeId).module == view.node(rootNodeId).module =>
                Some(SlpRegion(
                  rootNodeId,
                  SlpOperation(
                    opcode = SlpTruncatingAdd,
                    resultWidth = 16,
                    storageWidth = 16,
                    operands = addOperation.operands,
                    parameters = Vector(BigInt(17)),
                    statement = rootStatement
                  ),
                  Vector(addNodeId)
                ))
              case _ => None
            }
          }
        case SlpOperation(
            SlpMaskedAnd,
            resultWidth,
            _,
            Vector(SlpSignal(sourceName, sourceWidth), SlpUIntConstant(mask, maskWidth)),
            _,
            rootStatement
          ) if resultWidth > 0 && sourceWidth == resultWidth + 1 &&
              maskWidth == resultWidth && mask == lowMask(resultWidth) =>
          view.graph.nameToID.get(sourceName).flatMap { subNodeId =>
            classified.get(subNodeId).flatMap {
              case subOperation @ SlpOperation(
                  SlpSub,
                  subResultWidth,
                  _,
                  operands,
                  _,
                  _
                ) if subResultWidth == resultWidth + 1 &&
                    validTruncatingSubOperands(resultWidth, operands) &&
                    directConsumers(sourceName) == Vector(rootNodeId) &&
                    view.node(subNodeId).module == view.node(rootNodeId).module =>
                Some(SlpRegion(
                  rootNodeId,
                  SlpOperation(
                    opcode = SlpTruncatingSub,
                    resultWidth = resultWidth,
                    storageWidth = resultWidth,
                    operands = subOperation.operands,
                    parameters = Vector(BigInt(resultWidth + 1)),
                    statement = rootStatement
                  ),
                  Vector(subNodeId)
                ))
              case _ => None
            }
          }
        case _ => None
      }
    }.sortBy(_.rootNodeId)

    val internalNodes = candidates.flatMap(_.internalNodeIds)
    require(internalNodes.distinct.size == internalNodes.size,
      "an SLP internal node cannot be absorbed by multiple regions")
    candidates
  }
}
