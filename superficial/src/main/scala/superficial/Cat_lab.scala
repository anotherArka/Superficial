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

/*
object Exp_lemma_1 {
  val u : Object = new Object()
  val x : Object = new Object()
  val v : Object = new Object()
  val y : Object = new Object()

  val alpha : Morphism = new Atomic(u, x)
  val p     : Morphism = new Atomic(x, y)
  val beta  : Morphism = new Atomic(v, y)
  val i     : Morphism = new Atomic(u, v)

  val C = new Category 
}
*/