package armor.slp

/**
  * Partitions one ordered SLP lane family without splitting an individual
  * lane.  Unlike the legacy greedy splitter, the primary path treats the
  * retained parallel degree as a constraint: it only accepts a complete
  * partition when every chunk both fits one machine word and has enough
  * lanes to survive pack retention.
  *
  * The caller owns statement-graph validation and commit.  This component is
  * deliberately pure: it only reasons about ordered lane indices and an
  * externally supplied materialized-boundary predicate.
  */
private[slp] object SlpWidthDegreePartitioner {

  sealed trait Strategy {
    def name: String
  }

  case object WholeGroup extends Strategy {
    override val name: String = "whole"
  }

  case object DegreeAwareFullCover extends Strategy {
    override val name: String = "degree_aware_full_cover"
  }

  case object GreedyPartialFallback extends Strategy {
    override val name: String = "greedy_partial_fallback"
  }

  case object NoRetainedChunk extends Strategy {
    override val name: String = "none"
  }

  final case class Result[A](
    chunks:       Vector[Vector[A]],
    fullyCovered: Boolean,
    strategy:     Strategy
  ) {
    require(chunks.forall(_.nonEmpty))
  }

  private final case class Range(begin: Int, end: Int) {
    require(begin >= 0 && end > begin)

    def size: Int = end - begin
  }

  /**
    * Return the best partition for an ordered family.
    *
    * Preference order for a complete cover is deliberately deterministic:
    * fewer pack boundaries, then a larger weakest pack, then a more balanced
    * degree distribution, then lexicographically earlier chunk sizes.
    */
  def partition[A](
    ordered: Vector[A],
    minDegree: Int,
    segmentFits: Vector[A] => Boolean
  ): Result[A] = {
    require(minDegree > 0, s"minimum retained degree must be positive, got $minDegree")

    if (ordered.size < minDegree) {
      Result(Vector.empty, fullyCovered = false, NoRetainedChunk)
    } else if (segmentFits(ordered)) {
      Result(Vector(ordered), fullyCovered = true, WholeGroup)
    } else {
      // Most groups have uniform lane widths.  Preserve the old linear
      // capacity scan first, then rebalance its minimum number of chunks.  In
      // the common 5 + 3 case this immediately yields 4 + 4, without probing
      // every possible range of a large replicated family.
      val greedyPartition = greedyRanges(ordered, segmentFits)
      val greedyCoversAll = greedyPartition.nonEmpty &&
        greedyPartition.forall(range =>
          range.size >= minDegree && segmentFits(ordered.slice(range.begin, range.end))
        )
      if (greedyCoversAll) {
        Result(
          greedyPartition.map(range => ordered.slice(range.begin, range.end)),
          fullyCovered = true,
          DegreeAwareFullCover
        )
      } else {
        val balanced = balancedRanges(ordered.size, greedyPartition.size)
        val balancedCoversAll = balanced.nonEmpty &&
          balanced.forall(range =>
            range.size >= minDegree && segmentFits(ordered.slice(range.begin, range.end))
          )
        if (balancedCoversAll) {
          Result(
            balanced.map(range => ordered.slice(range.begin, range.end)),
            fullyCovered = true,
            DegreeAwareFullCover
          )
        } else {
          val chunks = greedyPartition.collect {
            case range if range.size >= minDegree &&
                segmentFits(ordered.slice(range.begin, range.end)) =>
              ordered.slice(range.begin, range.end)
          }
          Result(
            chunks,
            fullyCovered = false,
            if (chunks.nonEmpty) GreedyPartialFallback else NoRetainedChunk
          )
        }
      }
    }
  }

  private def greedyRanges[A](
    ordered: Vector[A],
    segmentFits: Vector[A] => Boolean
  ): Vector[Range] = {
    val ranges = Vector.newBuilder[Range]
    var begin = 0
    var end = 0
    while (end < ordered.size) {
      val nextEnd = end + 1
      if (end > begin && !segmentFits(ordered.slice(begin, nextEnd))) {
        ranges += Range(begin, end)
        begin = end
      }
      end += 1
    }
    if (end > begin) ranges += Range(begin, end)
    ranges.result()
  }

  private def balancedRanges(laneCount: Int, parts: Int): Vector[Range] =
    if (parts <= 0 || parts > laneCount) Vector.empty
    else (0 until parts).map { part =>
      Range(
        begin = (part * laneCount) / parts,
        end = ((part + 1) * laneCount) / parts
      )
    }.toVector


}
