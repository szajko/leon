import scala.collection.immutable.Set
import leon.Annotations._
import leon.Utils._

object InsertionSort {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def size(l: List): Int = (l match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring (_ >= 0)

  def contents(l: List): Set[Int] = l match {
    case Nil() => Set.empty
    case Cons(x, xs) => contents(xs) ++ Set(x)
  }

  def isSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, Cons(y, ys)) => x <= y && isSorted(Cons(y, ys))
  }

  /* Inserting element 'e' into a sorted list 'l' produces a sorted list with
   * the expected content and size */
  def insert(e: Int, l: List): List = {
    require(isSorted(l))
    choose { (res: List) =>
      (
        contents(res) == contents(l) ++ Set(e) &&
        isSorted(res) &&
        size(res) == size(l) + 1)
    }
    //    l match {
    //      case Nil() => Cons(e, Nil())
    //      case Cons(x, xs) =>
    //        if (x <= e) Cons(x, sortedIns(e, xs))
    //        else Cons(e, l)
    //    }
  }

  /* Insertion sort yields a sorted list of same size and content as the input
   * list */
  def sort(l: List): List = (l match {
    case Nil() => Nil()
    case Cons(x, xs) => insert(x, sort(xs))
  }) ensuring (res => contents(res) == contents(l)
    && isSorted(res)
    && size(res) == size(l))

}
