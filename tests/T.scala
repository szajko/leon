import leon.Utils._
import leon.Annotations._

object T {
  def sizeOfEmpty(A : Set[Int]) : Boolean = {
    (A == Set.empty[Int]) == (A.size == 0)
  }.holds
}
