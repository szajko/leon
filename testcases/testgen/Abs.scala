import leon.Utils._
import leon.Annotations._

object Abs {

  @main
  def abs(x: Int): Int = {
    if(x < 0) -x else x
  } ensuring(_ >= 0)

}
