package superficial

import Morphism._
import Equality_of_morphisms._

// we have to define methods to make sure that if f is inside weak_equiv/fibrations/cofibrations and
// f ~ g according to morphisms then g is also inside weak_equiv/fibrations/cofibrations
trait Model_category { model_cat =>
  // should we use var instead of val so we can update the values rather than creating
  // a new data each time we apply an axiom

  val morphisms    : Equality_of_morphisms
  val weak_equiv   : Set[Morphism]
  val fibrations   : Set[Morphism]
  val cofibrations : Set[Morphism]

  def axiom_2_1(f : Morphism, g : Morphism) : Model_category = {
    val new_morphisms  : Equality_of_morphisms = morphisms
    val new_fibrations   : Set[Morphism] = fibrations
    val new_cofibrations : Set[Morphism] = cofibrations
    val new_weak_equiv   : Set[Morphism] =
      if (f.is_composable_with(g) && (weak_equiv.contains(f)) && (weak_equiv.contains(g))) {
        weak_equiv.+(g.+(f))
      }
      else weak_equiv
    Model_category.apply(new_morphisms, new_fibrations, new_cofibrations, new_weak_equiv)
  }

  def axiom_2_2(f : Morphism, g : Morphism) : Model_category = {
    val new_morphisms  : Equality_of_morphisms = morphisms
    val new_fibrations   : Set[Morphism] = fibrations
    val new_cofibrations : Set[Morphism] = cofibrations
    val new_weak_equiv   : Set[Morphism] =
      if (f.is_composable_with(g) && (weak_equiv.contains(f)) && (weak_equiv.contains(g.+(f)))) {
        weak_equiv.+(g)
      }
      else weak_equiv
    Model_category.apply(new_morphisms, new_fibrations, new_cofibrations, new_weak_equiv)
  }

  def axiom_2_3(f : Morphism, g : Morphism) : Model_category = {
    val new_morphisms  : Equality_of_morphisms = morphisms
    val new_fibrations   : Set[Morphism] = fibrations
    val new_cofibrations : Set[Morphism] = cofibrations
    val new_weak_equiv   : Set[Morphism] =
      if (f.is_composable_with(g) && (weak_equiv.contains(g)) && (weak_equiv.contains(g.+(f)))) {
        weak_equiv.+(f)
      }
      else weak_equiv
    Model_category.apply(new_morphisms, new_fibrations, new_cofibrations, new_weak_equiv)
  } 

}

object Model_category {
  def apply(cat : Equality_of_morphisms, weq : Set[Morphism], fib : Set[Morphism], cofib : Set[Morphism]) =
    new Model_category {
      val morphisms    = cat
      val weak_equiv   = weq
      val fibrations   = fib
      val cofibrations = cofib
  }
}
