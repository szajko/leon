/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers
package combinators

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

class UnrollingSolverFactory[S <: Solver](val sf : SolverFactory[S]) extends SolverFactory[Solver] {
  val description = "Unrolling loop around a base solver."
  val name = "U[" + sf.name + "]"

  val context = sf.context
  val program = sf.program

  override def free() {
    sf.free()
  }

  override def recoverInterrupt() {
    sf.recoverInterrupt()
  }

  def getNewSolver() : Solver = {
    new Solver {
      private val underlying : Solver = sf.getNewSolver()

      private var theConstraint : Option[Expr] = None

      private def fail(because : String) : Nothing = {
        throw new Exception("Not supported in UnrollingSolvers : " + because)
      }

      def push() : Unit = fail("push()")
      def pop(lvl : Int = 1) : Unit = fail("pop(lvl)")
      
      def assertCnstr(expression : Expr) {
        if(!theConstraint.isEmpty) {
          fail("Multiple assertCnstr")
        }
        theConstraint = Some(expression)
      }

      def interrupt() {
        underlying.interrupt()
      }

      def recoverInterrupt() {
        underlying.recoverInterrupt()
      }

      def check : Option[Boolean] = theConstraint.map { expr =>
        underlying.assertCnstr(expr)
        underlying.check
      } getOrElse {
        Some(true)
      }

      def checkAssumptions(assumptions : Set[Expr]) : Option[Boolean] = {
        fail("checkAssumptions(assumptions)")
      }

      def getModel : Map[Identifier,Expr] = {
        underlying.getModel
      }

      def getUnsatCore : Set[Expr] = {
        fail("getUnsatCore")
      }
    }
  }
}
