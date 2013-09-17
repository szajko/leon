import leon.Utils._
import leon.Annotations._

object T {
  def sizeOfEmpty(A : Set[Int]) : Boolean = {
    (A == Set.empty[Int]) == (A.size == 0)
  }.holds

  def hasModel1(A : Set[Int], m : Int, M : Int) : Boolean = {
    !(A != Set.empty[Int] && A.min == m && A.max == M && m != M)
  }.holds
}
