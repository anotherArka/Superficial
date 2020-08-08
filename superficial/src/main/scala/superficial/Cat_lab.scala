package superficial

import Morphism._
import Equality_of_morphisms._
import Category._

object Cat_lab {
  val a : Object = new Object()
  val b : Object = new Object()
  val c : Object = new Object()
  val d : Object = new Object()
  val e : Object = new Object()

  val f : Morphism = new Atomic(a, b)
  val g : Morphism = new Atomic(b, c)
  val h : Morphism = new Atomic(c, d)
  val k : Morphism = new Atomic(d, e)

  val Eq_C : Equality_of_morphisms = Equality_of_morphisms.apply(Set(Set(f), Set(g), Set(h), Set(k)))
  val C : Category = Category.apply(Eq_C)
}