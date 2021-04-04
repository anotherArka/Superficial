package superficial

import Morphism._
import Category._

trait Model extends Category { model =>

  var fib       : Set[Morphism]
  var cofib     : Set[Morphism]
  var weak_eqv  : Set[Morphism]

  /**
   * Axiom CM2 from Goerss and Jardin
   */
  def axiom_2(f : Morphism, g : Morphism, h : Morphism) : Unit = {  

    require(model.morphisms.contains(f), s"$f is not a morphism in the category $model")
    require(model.morphisms.contains(g), s"$g is not a morphism in the category $model")
    require(model.morphisms.contains(h), s"$h is not a morphism in the category $model")
    
    require(model.are_equal(f.+(g), h) , s"$f composed with $g is not equal to $h")
    
    require(model.weak_eqv.intersect(Set(f, g, h)).size >= 2,
      s"No two of $f, $g and $h are weak equivalences")

    model.weak_eqv += f
    model.weak_eqv += g
    model.weak_eqv += h   
  }

  /**
   *  Axiom CM3 from Goerss and Jardin
   *
   *          i           r
   *      X -------> X' -------> X
   *      |          |           |
   *    f |        g |         f |
   *      |          |           |
   *      \/         \/          \/
   *      Y -------> Y' -------> Y
   *           i           r
   *      
   *      r . i = id
   */
  def axiom_3_weak_eqv(f : Morphism, g : Morphism, r : Morphism, i : Morphism) : Unit = {
    require(model.morphisms.contains(f), s"$f is not a morphism in the category $model")
    require(model.morphisms.contains(g), s"$g is not a morphism in the category $model")
    require(model.morphisms.contains(i), s"$i is not a morphism in the category $model")
    require(model.morphisms.contains(r), s"$r is not a morphism in the category $model")

    require(model.are_equal(r.+(i), id_morph(f.domain)), s"$r composed with $i is not identity")
    require(model.are_equal(i.+(f), g.+(i)), s"$g composed with $i is not same as $i composed with $f")
    require(model.are_equal(r.+(g), f.+(r)), s"$r composed with $g is not same as $f composed with $r")

    require(model.weak_eqv.contains(g), s"$g is not a weak equivalence in the category $model")

    model.weak_eqv += f
  }

  def axiom_3_fib(f : Morphism, g : Morphism, r : Morphism, i : Morphism) : Unit = {
    require(model.morphisms.contains(f), s"$f is not a morphism in the category $model")
    require(model.morphisms.contains(g), s"$g is not a morphism in the category $model")
    require(model.morphisms.contains(i), s"$i is not a morphism in the category $model")
    require(model.morphisms.contains(r), s"$r is not a morphism in the category $model")

    require(model.are_equal(r.+(i), id_morph(f.domain)), s"$r composed with $i is not identity")
    require(model.are_equal(i.+(f), g.+(i)), s"$g composed with $i is not same as $i composed with $f")
    require(model.are_equal(r.+(g), f.+(r)), s"$r composed with $g is not same as $f composed with $r")

    require(model.fib.contains(g), s"$g is not a fibration in the category $model")

    model.fib += f
  }

  def axiom_3_cofib(f : Morphism, g : Morphism, r : Morphism, i : Morphism) : Unit = {
    require(model.morphisms.contains(f), s"$f is not a morphism in the category $model")
    require(model.morphisms.contains(g), s"$g is not a morphism in the category $model")
    require(model.morphisms.contains(i), s"$i is not a morphism in the category $model")
    require(model.morphisms.contains(r), s"$r is not a morphism in the category $model")

    require(model.are_equal(r.+(i), id_morph(f.domain)), s"$r composed with $i is not identity")
    require(model.are_equal(i.+(f), g.+(i)), s"$g composed with $i is not same as $i composed with $f")
    require(model.are_equal(r.+(g), f.+(r)), s"$r composed with $g is not same as $f composed with $r")

    require(model.cofib.contains(g), s"$g is not a fibration in the category $model")

    model.cofib += f
  } 

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

  def axiom_5_1(f : Morphism) : Unit = {
    require(model.morphisms.contains(f), s"$f is not a morphism in $model")
    val c : Object   = new Object() 
    val i : Morphism = new Atomic(f.domain, c)
    val p : Morphism = new Atomic(c, f.range)
    
    model.morphisms += p
    model.morphisms += i
    model.fib       += p
    model.cofib     += i
    model.weak_eqv  += i
    model.equality_of_morphisms.add(Set(p.+(i), f))
  }

  /**
   *    f.domain
   *       |
   *     j |
   *       |
   *       \/
   *       c --------> f.range
   *             q
   */
  def axiom_5_2(f : Morphism) : Unit = {
    require(model.morphisms.contains(f), s"$f is not a morphism in $model")
    val c : Object   = new Object() 
    val j : Morphism = new Atomic(f.domain, c)
    val q : Morphism = new Atomic(c, f.range)
    
    model.morphisms += q
    model.morphisms += j
    model.fib       += q
    model.cofib     += j
    model.weak_eqv  += q
    model.equality_of_morphisms.add(Set(q.+(j), f))
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

  /**
   *    f.domain
   *       |
   *     i |
   *       |
   *       \/
   *       c --------> f.range
   *             p
   */
  
}

