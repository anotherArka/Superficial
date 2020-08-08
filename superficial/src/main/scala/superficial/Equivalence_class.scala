package superficial

trait Equivalence_class[T] {eq_class =>
  var partition : Set[Set[T]] = Set()

  /** 
   * Checks if the sets in the equivalence class are mutually disjoint.
   * We do not use the findIntersectingPair method to check so that we
   * can check methods where findIntersectingPairs are used
   */
  def is_well_defined : Boolean = {
    val all_elements : Set[T] = eq_class.partition.flatMap(e => e)
    (all_elements.filter(el => 
      (eq_class.partition.filter(_.contains(el)).size != 1)).size == 0)
  }

  def delete(to_delete : List[Set[T]]) : Unit = {
    to_delete match {
      case Nil => {}
      case (d :: ds) => {
        eq_class.partition.-=(d)
        eq_class.delete(ds)        
      }
    }
  } 

    def add(new_set : Set[T]) : Unit = {
      val inter : Set[Set[T]] = eq_class.partition.filter(cl => (cl.intersect(new_set).nonEmpty)).+(new_set)
      eq_class.delete(inter.toList)
      eq_class.partition.+=(inter.flatMap(x => x))      
    }

    def add_list(full_set : List[Set[T]]) : Unit = {
      full_set match {
        case Nil => {}
        case (r :: rs) => {
          eq_class.add(r)
          eq_class.add_list(rs)
        }
      }  
    }

    def make_well_defined : Unit = {
      val full_list : List[Set[T]] = eq_class.partition.toList
      eq_class.add_list(full_list)
      require(eq_class.is_well_defined, s"$eq_class is not well defined")
    }
}
