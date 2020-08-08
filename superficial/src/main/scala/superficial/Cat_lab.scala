package superficial

import Morphism._
import Equality_of_morphisms._
import Category._

object Cat_lab {
  val a : Object = new Object()
  val b : Object = new Object()
  val f : Morphism = new Atomic(a, b)

  val Eq_C : Equality_of_morphisms = Equality_of_morphisms.apply(Set(Set(f)))
  val C : Category = Category.apply(Eq_C)
}