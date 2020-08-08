package superficial

import Object._

trait Morphism { morph =>
  val domain : Object
  val range  : Object

  def is_composable_with(before : Morphism) : Boolean = {
    morph.domain == before.range
  }

  def +(before : Morphism) : Morphism = Morphism.Compose(morph, before)
}

object Morphism {
  class Atomic(from : Object, to : Object) extends Morphism {
    val domain = from
    val range  = to
  }

  case class Compose(after : Morphism, before : Morphism) extends Morphism {
    require(after.is_composable_with(before), s"$after can not be composed with $before")
    val domain = before.domain
    val range = after.range
  } 
}