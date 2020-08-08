package superficial

import Object._

trait Morphism { morph =>
  val domain : Object
  val range  : Object

  def is_composable_with(next : Morphism) : Boolean = {
    morph.range == next.domain
  }

  def +(before : Morphism) : Morphism = Morphism.Compose(morph, before)
}

object Morphism {
  class Atomic(from : Object, to : Object) extends Morphism {
    val domain = from
    val range  = to
  }

  case class Compose(after : Morphism, before : Morphism) extends Morphism {
    require(before.is_composable_with(after), s"$before can not be composed with $after")
    val domain = before.domain
    val range = after.range
  }
}