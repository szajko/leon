import leon.Utils._
import leon.Annotations._

object QuickSort {
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case object Nil extends List

  def size(lst : List) : Int = (lst match {
    case Nil => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def cont(lst : List) : Set[Int] = (lst match {
    case Nil => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ cont(xs)
  })

  def splitWithPivot(lst : List, pivot : Int) : (List,List) = swp0(lst, pivot, Nil, Nil)

  def allLE(s : Set[Int], i : Int) : Boolean = { s == Set.empty[Int] || s.max <= i }
  def allGT(s : Set[Int], i : Int) : Boolean = { s == Set.empty[Int] || s.min > i }

  def swp0(lst : List, pivot : Int, a1 : List, a2 : List) : (List,List) = {
    require(allLE(cont(a1), pivot) && allGT(cont(a2), pivot))
    lst match {
      case Nil => (a1, a2)

      case Cons(x, xs) if x <= pivot =>
        swp0(xs, pivot, Cons(x, a1), a2)

      case Cons(x, xs) =>
        swp0(xs, pivot, a1, Cons(x, a2))
    }
  } ensuring(res => (cont(res._1) ++ cont(res._2)) == (cont(lst) ++ cont(a1) ++ cont(a2)))

  /*
  def isSorted(lst : List) : Int = (lst match {
    case Nil => true
    case Cons(_, Nil) => true
    case Cons(x, xs @ Cons(y, ys)) => (x <= y) && isSorted(xs)
  })

  def sort(lst : List) : List = (lst match {
    case Nil => Nil
    case Cons(_, Nil) => lst
    case other =>
      val pivot = pickPivot(lst)
      val (l1, l2) = splitWithPivot(lst, pivot)
      
  
  }) ensuring(isSorted(_))
  */
}
