package superficial

import Morphism._
import Equivalence_class._
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

  var C = new Category {
    var objects   : Set[Object]   = Set(a, b, c, d, e)
    var morphisms : Set[Morphism] = Set(f, g, h, k)
    var equality_of_morphisms : Equivalence_class[Morphism] = Equivalence_class.apply(List())
  }
}
