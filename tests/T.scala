import leon.Utils._
import leon.Annotations._

object T {
  def sizeOfEmpty(A : Set[Int]) : Boolean = {
    (A == Set.empty[Int]) == (A.size == 0)
  }.holds

  def hasModel1(A : Set[Int], m : Int, M : Int) : Boolean = {
    !(A != Set.empty[Int] && A.min == m && A.max == M && m != M)
  }.holds

  def setLess(a : Set[Int], b : Set[Int]) : Boolean = {
    require(a.size > 0 && b.size > 0)
    (a.max < b.min)
  }

  def setLessDef(s1 : Set[Int], s2 : Set[Int], x1 : Int, x2 : Int) : Boolean = {
    require(s1.size > 0 && s2.size > 0)

    if (setLess(s1,s2) && s1.contains(x1) && s2.contains(x2)) x1 < x2  
    else true
  }.holds
}
