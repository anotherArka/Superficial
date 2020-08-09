package superficial

import Object._
import Morphism._
import Helper._
import Equivalence_class._

trait Category {cat =>
  
  var objects   : Set[Object]
  var morphisms : Set[Morphism]
  var equality_of_morphisms : Equivalence_class[Morphism]

  def are_equal (f : Morphism, g : Morphism) : Boolean = equality_of_morphisms.are_equal(f,g)

  def add_id(ob : Object) : Unit = {
    objects   += ob
    morphisms += Category.id_morph(ob)
  }

  def add_id_all : Unit = objects.map(add_id)
  
  def id_axiom(f : Morphism) : Unit = {
    cat.add_id(f.domain)
    cat.add_id(f.range)
    val i1 : Morphism = Category.id_morph(f.domain)
    val i2 : Morphism = Category.id_morph(f.range)
    val f1 : Morphism = f.+(i1)
    val f2 : Morphism = i2.+(f)
    morphisms += f1
    morphisms += f2
    equality_of_morphisms.add_list(List(Set(f, f1, f2))) 
  }

  def id_axiom_all : Unit = cat.morphisms.map(f => cat.id_axiom(f))

  def assoc_axiom (f : Morphism, g : Morphism, h : Morphism) : Unit = {
    require(h.is_composable_with(g), s"$h is not composable with $g")
    require(g.is_composable_with(f), s"$g is not composable with $f")
    val f1 : Morphism = h.+(g.+(f))
    val f2 : Morphism = (h.+(g)).+(f)
    morphisms += f1
    morphisms += f2
    equality_of_morphisms.add(Set(f1, f2))
  }

   def complete_with_assoc_helper(first : List[Morphism], second : List[Morphism], third : List[Morphism],
    full_list : List[Morphism]) : Unit = {
    first match {
      case Nil => {}
      case (f :: fs) => {
        second match {
          case Nil => cat.complete_with_assoc_helper(fs, full_list, full_list, full_list)
          case (g :: gs) => {
            third match {
              case Nil => cat.complete_with_assoc_helper((f :: fs), gs, full_list, full_list)
              case (h :: hs) => {
                if (g.is_composable_with(f) && h.is_composable_with(g)) {
                  cat.assoc_axiom(f, g, h)
                  cat.complete_with_assoc_helper(f :: fs, g :: gs, hs, full_list)
                }
                else cat.complete_with_assoc_helper(f :: fs, g :: gs, hs, full_list)
              }
            }
          }
        }
      }
    }
  }

  def complete_with_assoc(n : Int) : Unit = {
    if (n > 0) {
      val morph_list : List[Morphism] = cat.morphisms.toList
      cat.complete_with_assoc_helper(morph_list, morph_list, morph_list, morph_list)
      cat.complete_with_assoc(n-1)
    }
    else {}
  }
}

object Category {
  def apply(equality : Set[Set[Morphism]]) : Category = {
    val new_morphisms : Set[Morphism] = equality.flatMap(el => el)
    val new_domains   : Set[Object]   = new_morphisms.map(f => f.domain)
    val new_ranges    : Set[Object]   = new_morphisms.map(f => f.range)
    val new_equality  : Equivalence_class[Morphism] = Equivalence_class.apply(equality.toList)
    new Category {
      var objects   = new_domains.++(new_ranges)
      var morphisms = new_morphisms
      var equality_of_morphisms = new_equality
    }
  }

  case class id_morph(ob : Object) extends Morphism{
    val domain = ob
    val range  = ob
  } 
}

