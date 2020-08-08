package superficial

import Object._
import Morphism._
import Helper._

trait Morphism_class { morph_class =>
   val domain : Object
   val range  : Object
   val morphisms : Set[Morphism]
}

trait Equality_of_morphisms { equality =>

  val morphisms : Set[Set[Morphism]]
 
  /**
   * Given a set newSet of Morphisms expands the Equivalence class with newSet.
   * First it adds it to the collection of morphisms, and then uses makeWellDefined 
   * method to merge morphisms inside the equivalence class until there are no 
   * intersecting pair of morphisms.
   */
  def expandWith(newSet : Set[Morphism]) : Equality_of_morphisms = {
    val destination = equality.morphisms.find(ss => ss.intersect(newSet).nonEmpty)
    val intermediate = destination match {
      case None => Equality_of_morphisms.apply(equality.morphisms.+(newSet))
      case Some(element) => {
        val newElement = element.++(newSet)
        Equality_of_morphisms.dumbApply(equality.morphisms.-(element).+(newElement))
      }
    }
    val result = intermediate.makeWellDefined
    assert(result.isWellDefined, 
      s"The result $result of expanding the equality $equality with $newSet" ++ 
       "is not well defined as a equivalence class")
    result 
  }
  /**
   * Checks if the collection of morphisms in the equivalence class are mutually disjoint.
   * We do not use the findIntersectingPair method to check so that we
   * can check methods where findIntersectingPairs are used
   */
  def isWellDefined = {
    val allElements : Set[Morphism] = equality.morphisms.flatMap(e => e)
    (allElements.filter(el => 
      (equality.morphisms.filter(_.contains(el)).size != 1)).size == 0)
  }

  def findIntersectingPair : Option[(Set[Morphism], Set[Morphism])] = {
    val setList : List[Set[Morphism]] = equality.morphisms.toList
    def helper(oneList : List[Set[Morphism]], anotherList : List[Set[Morphism]]) : Option[(Set[Morphism], Set[Morphism])] = {
      oneList match {
        case Nil => None
        case el :: els => {
          anotherList match {
            case Nil => helper(els, els)
            case fl :: fls => {
              if ((el.intersect(fl).nonEmpty) && (el != fl)) Some((el, fl))
              else helper(el :: els, fls)
            }
          }
        }
      }
    }
    helper(setList, setList)
  }

  /** 
   * If the equivalence class is not well defined makes it well defined. 
   * That is merges intersecting pairs of morphisms.
   */
  def makeWellDefined : Equality_of_morphisms = {
    val result = equality.findIntersectingPair match {
      case None => equality
      case Some((a, b)) => {
        val newmorphisms : Set[Set[Morphism]] = equality.morphisms.-(a).-(b).+(a.++(b))
        Equality_of_morphisms.dumbApply(newmorphisms).makeWellDefined
      }
    }
    assert(result.isWellDefined, s"The result $result of makeWellDefined is not a collection of" ++ 
      "mutually disjoint collection of morphisms")
    result  
  }

  def merge (anotherClass : Equality_of_morphisms) : Equality_of_morphisms = {
    val newClass : Set[Set[Morphism]] = equality.morphisms.++(anotherClass.morphisms)
    Equality_of_morphisms.apply(newClass)
  }

  def are_equal (f : Morphism, g : Morphism) : Boolean = {
    val result : Boolean = morphisms.find(el => (el.contains(f) && el.contains(g))) match {
      case None => false
      case Some(el) => true
    }
    result  
  }

  def isInside (f : Morphism) : Boolean = equality.are_equal(f,f)
}

object Equality_of_morphisms {
  
  def dumbApply (newmorphisms : Set[Set[Morphism]]) : Equality_of_morphisms = new Equality_of_morphisms {
    val morphisms = newmorphisms
  }

  def apply (newmorphisms : Set[Set[Morphism]]) : Equality_of_morphisms = {
    val intermediate : Equality_of_morphisms = Equality_of_morphisms.dumbApply(newmorphisms)
    val result : Equality_of_morphisms = intermediate.makeWellDefined
    assert(result.isWellDefined, s"The result $result of makeWellDefined is not a collection of" ++ 
      "mutually disjoint collection of morphisms")
    result
  }
}

trait Category {cat =>

  val objects   : Set[Object]
  val morphisms : Set[Morphism]
  val equality_of_morphism : Equality_of_morphisms

  def id_axiom (f : Morphism) : Category = {
    val i1 : Morphism = Category.id_morph(f.domain)
    val i2 : Morphism = Category.id_morph(f.range)
    val f1 : Morphism = f.+(i1)
    val f2 : Morphism = (i2).+(f)
    new Category {
      val objects   = cat.objects
      val morphisms = cat.morphisms.++(Set(f, f1, f2))
      val equality_of_morphism = cat.equality_of_morphism.merge(
        Equality_of_morphisms.apply(Set(Set(f, f1, f2), Set(i1), Set(i2))))
    }
  }

  def assoc_axiom (f : Morphism, g : Morphism, h : Morphism) : Category = {
    require(h.is_composable_with(g), s"$h is not composable with $g")
    require(g.is_composable_with(f), s"$g is not composable with $f")
    val f1 : Morphism = h.+(g.+(f))
    val f2 : Morphism = (h.+(g)).+(f)
    new Category {
      val objects   = cat.objects
      val morphisms = cat.morphisms.++(Set(f1, f2))
      val equality_of_morphism = cat.equality_of_morphism.expandWith(Set(f1, f2))
    }
  }

  def random_extend : Category = {
    val f : Morphism = Helper.random(cat.morphisms)
    val intermediate = cat.id_axiom(f)

    val g : Morphism = Helper.random(cat.morphisms.filter(k => k.is_composable_with(f)))
    val h : Morphism = Helper.random(cat.morphisms.filter(k => k.is_composable_with(g)))
    
    intermediate.assoc_axiom(f, g, h)
  }

  def complete_with_id_helper(remaining: List[Morphism]) : Category = {
    remaining match {
      case Nil => cat
      case (f :: fs) => cat.id_axiom(f).complete_with_id_helper(fs)
    }
  }

  def complete_with_id(n : Int) : Category = {
    if (n > 0) cat.complete_with_id_helper(cat.morphisms.toList).complete_with_id(n-1)
    else cat
  }

  def complete_with_assoc_helper(first : List[Morphism], second : List[Morphism], third : List[Morphism],
    full_list : List[Morphism]) : Category = {
    first match {
      case Nil => cat
      case (f :: fs) => {
        second match {
          case Nil => cat.complete_with_assoc_helper(fs, full_list, full_list, full_list)
          case (g :: gs) => {
            third match {
              case Nil => cat.complete_with_assoc_helper((f :: fs), gs, full_list, full_list)
              case (h :: hs) => {
                if (g.is_composable_with(f) && h.is_composable_with(g)) {
                  cat.assoc_axiom(f, g, h).complete_with_assoc_helper(f :: fs, g :: gs, hs, full_list)
                }
                else cat.complete_with_assoc_helper(f :: fs, g :: gs, hs, full_list)
              }
            }
          }
        }
      }
    }
  }

  def complete_with_assoc(n : Int) : Category = {
    if (n > 0) {
      val morph_list : List[Morphism] = cat.morphisms.toList
      cat.complete_with_assoc_helper(morph_list, morph_list, morph_list, morph_list).complete_with_assoc(n-1)
    }
    else cat
  }

  def random_extend_times(n : Integer) : Category = {
    if (n > 1) (cat.random_extend).random_extend_times(n - 1)
    else cat
  }

}

object Category {

  def apply(equality : Equality_of_morphisms) : Category = {
    val new_morphisms : Set[Morphism] = equality.morphisms.flatMap(el => el)
    val domains       : Set[Object]   = new_morphisms.map(_.domain)
    val ranges        : Set[Object]   = new_morphisms.map(_.range)
    val new_objects   : Set[Object]   = domains.++(ranges)
    val new_id        : Set[Morphism] = new_objects.map(a => id_morph(a))
    
    new Category {
      val objects   : Set[Object]   = new_objects
      val morphisms : Set[Morphism] = new_morphisms.++(new_id)
      val equality_of_morphism : Equality_of_morphisms = equality
    }
  }

  case class id_morph (obj : Object) extends Morphism {
    val domain : Object = obj
    val range  : Object = obj
  }
}