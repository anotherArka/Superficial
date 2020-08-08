package superficial

object Helper {
  def random[T](s: Set[T]): T = {
    val n = util.Random.nextInt(s.size)
      s.iterator.drop(n).next
  }
}