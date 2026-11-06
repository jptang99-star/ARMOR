package armor.slp

final case class SlpProjectionCseKey(
  source:           SlpProjectionSource,
  sourceWidth:      Int,
  destinationWidth: Int,
  transfers:        Vector[SlpBitTransfer],
  epoch:            Option[Int]
) {
  require(sourceWidth > 0 && sourceWidth <= 64)
  require(destinationWidth > 0 && destinationWidth <= 64)
  require(transfers.nonEmpty)
}

sealed trait SlpProjectionCseUser {
  def scheduleIndex: Int
}

final case class SlpAlignmentProjectionCseUser(
  alignmentId:   Int,
  termIndex:     Int,
  scheduleIndex: Int
) extends SlpProjectionCseUser {
  require(alignmentId >= 0)
  require(termIndex >= 0)
  require(scheduleIndex >= 0)
}

final case class SlpPackProjectionCseUser(
  packId:        Int,
  argumentIndex: Int,
  scheduleIndex: Int
) extends SlpProjectionCseUser {
  require(packId >= 0)
  require(argumentIndex >= 0)
  require(scheduleIndex >= 0)
}

final case class SlpProjectionCseEntry(
  id:        Int,
  key:       SlpProjectionCseKey,
  firstUser: SlpProjectionCseUser,
  users:     Vector[SlpProjectionCseUser]
) {
  require(id >= 0)
  require(users.size >= 2)
  require(users.contains(firstUser))
}

final case class SlpProjectionCsePlan(entries: Vector[SlpProjectionCseEntry]) {
  require(entries.map(_.id).distinct.size == entries.size)
  require(entries == entries.sortBy(_.id))
  require(entries.map(_.key).distinct.size == entries.size)

  val byKey: Map[SlpProjectionCseKey, SlpProjectionCseEntry] =
    entries.map(entry => entry.key -> entry).toMap

  val firstAlignmentUsers: Map[Int, Vector[SlpProjectionCseEntry]] =
    entries.collect {
      case entry @ SlpProjectionCseEntry(_, _, user: SlpAlignmentProjectionCseUser, _) =>
        user.alignmentId -> entry
    }.groupBy(_._1).view.mapValues(_.map(_._2).sortBy(_.id)).toMap

  val firstPackUsers: Map[Int, Vector[SlpProjectionCseEntry]] =
    entries.collect {
      case entry @ SlpProjectionCseEntry(_, _, user: SlpPackProjectionCseUser, _) =>
        user.packId -> entry
    }.groupBy(_._1).view.mapValues(_.map(_._2).sortBy(_.id)).toMap

  val alignmentUsers: Map[(Int, Int), SlpProjectionCseEntry] =
    entries.flatMap { entry =>
      entry.users.collect {
        case user: SlpAlignmentProjectionCseUser =>
          (user.alignmentId -> user.termIndex) -> entry
      }
    }.toMap

  val packUsers: Map[(Int, Int), SlpProjectionCseEntry] =
    entries.flatMap { entry =>
      entry.users.collect {
        case user: SlpPackProjectionCseUser =>
          (user.packId -> user.argumentIndex) -> entry
      }
    }.toMap
}

object SlpProjectionCsePlanner {
  final case class AlignmentUse(
    alignmentId:   Int,
    termIndex:     Int,
    scheduleIndex: Int,
    key:           SlpProjectionCseKey
  ) {
    require(alignmentId >= 0)
    require(termIndex >= 0)
    require(scheduleIndex >= 0)

    def user: SlpAlignmentProjectionCseUser =
      SlpAlignmentProjectionCseUser(alignmentId, termIndex, scheduleIndex)
  }

  final case class PackUse(
    packId:        Int,
    argumentIndex: Int,
    scheduleIndex: Int,
    key:           SlpProjectionCseKey
  ) {
    require(packId >= 0)
    require(argumentIndex >= 0)
    require(scheduleIndex >= 0)

    def user: SlpPackProjectionCseUser =
      SlpPackProjectionCseUser(packId, argumentIndex, scheduleIndex)
  }

  def build(
    alignmentUses: Vector[AlignmentUse],
    packUses:      Vector[PackUse]
  ): SlpProjectionCsePlan = {
    val keyedUsers =
      alignmentUses.map(use => use.key -> use.user) ++
        packUses.map(use => use.key -> use.user)

    val duplicatedUses = keyedUsers
      .groupBy(_._1)
      .toVector
      .flatMap { case (key, uses) =>
        val sortedUsers = uses.map(_._2).sortBy(userSortKey)
        Option.when(sortedUsers.size >= 2)(key -> sortedUsers)
      }
      .sortBy { case (key, users) =>
        val firstUser = users.head
        (firstUser.scheduleIndex, firstUseSortKey(firstUser), sortKey(key))
      }

    val entries = duplicatedUses.zipWithIndex.map { case ((key, users), id) =>
      SlpProjectionCseEntry(
        id = id,
        key = key,
        firstUser = users.head,
        users = users
      )
    }
    SlpProjectionCsePlan(entries)
  }

  def sortKey(key: SlpProjectionCseKey): String =
    Seq(
      key.source.toString,
      key.sourceWidth.toString,
      key.destinationWidth.toString,
      key.transfers.map(transfer =>
        s"${transfer.sourceOffset}:${transfer.destinationOffset}:${transfer.width}"
      ).mkString(";"),
      key.epoch.fold("")(_.toString)
    ).mkString("|")

  private def firstUseSortKey(user: SlpProjectionCseUser): String = user match {
    case SlpAlignmentProjectionCseUser(alignmentId, termIndex, _) =>
      s"alignment:$alignmentId:$termIndex"
    case SlpPackProjectionCseUser(packId, argumentIndex, _) =>
      s"pack:$packId:$argumentIndex"
  }

  private def userSortKey(user: SlpProjectionCseUser): (Int, String) =
    user.scheduleIndex -> firstUseSortKey(user)
}
