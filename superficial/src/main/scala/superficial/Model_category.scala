package superficial

import Morphism._
import Category._

trait Model extends Category { model =>

  var fib       : Set[Morphism]
  var cofib     : Set[Morphism]
  var weak_eqv  : Set[Morphism]

  /**        a
   *     u ----> x
   *   i |       | p
   *     \/     \/
   *     v ----> y
   *         b
   */
  def axiom_4(a : Morphism, b : Morphism, i : Morphism, p : Morphism) : Unit = {

    require(model.are_equal(p.+(a), b.+(i)), s"The diagram does not commute")
    require(model.cofib.contains(i), s"$i is not a cofibration")
    require(model.fib.contains(p),   s"$p is not a fibration")
    require(model.weak_eqv.intersect(Set(i,p)).nonEmpty, s"Neither $i not $p is an weak equivalence")

    val t : Morphism = new Atomic(b.domain, a.range)
    model.morphisms += t
    model.morphisms += p.+(t)
    model.morphisms += t.+(i)
    model.equality_of_morphisms.add(Set(p.+(t), b))
    model.equality_of_morphisms.add(Set(t.+(i), a))
  }
}

object Model {
  def apply(equality : Set[Set[Morphism]],
    fibrations : Set[Morphism], cofibrations : Set[Morphism], weq : Set[Morphism])
    : Model = {
    val new_morphisms : Set[Morphism] =
      equality.flatMap(el => el).++(fibrations).++(cofibrations).++(weq)
    val new_domains   : Set[Object]   = new_morphisms.map(f => f.domain)
    val new_ranges    : Set[Object]   = new_morphisms.map(f => f.range)
    val new_equality  : Equivalence_class[Morphism] = Equivalence_class.apply(equality.toList)
    new Model {
      var objects   = new_domains.++(new_ranges)
      var morphisms = new_morphisms
      var fib       = fibrations
      var cofib     = cofibrations
      var weak_eqv  = weq
      var equality_of_morphisms = new_equality
    }
  }
}

