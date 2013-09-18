/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers
package combinators

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._

import scala.collection.mutable.{Map=>MutableMap}

class DNFSolverFactory[S <: Solver](val sf : SolverFactory[S]) extends SolverFactory[Solver] {
  val description = "DNF around a base solver"
  val name = sf.name + "!"

  val context = sf.context
  val program = sf.program

  private val thisFactory = this

  override def free() {
    sf.free()
  }

  override def recoverInterrupt() {
    sf.recoverInterrupt()
  }

  def getNewSolver() : Solver = {
    new Solver {
      private var theConstraint : Option[Expr] = None
      private var theModel : Option[Map[Identifier,Expr]] = None

      private def fail(because : String) : Nothing = { throw new Exception("Not supported in DNFSolvers : " + because) }

      def push() : Unit = fail("push()")
      def pop(lvl : Int = 1) : Unit = fail("pop(lvl)")
      
      def assertCnstr(expression : Expr) {
        if(!theConstraint.isEmpty) { fail("Multiple assertCnstr(...).") }
        theConstraint = Some(expression)
      }

      def interrupt() { fail("interrupt()") }

      def recoverInterrupt() { fail("recoverInterrupt()") }

      def check : Option[Boolean] = theConstraint.map { expr =>
        import context.reporter

        val simpleSolver = SimpleSolverAPI(sf)

        var result : Option[Boolean] = None

        def info(msg : String) { reporter.info("In " + thisFactory.name + ": " + msg) }
        
        info("Before NNF:\n" + expr)

        val nnfed = nnf(expr, false)

        info("After NNF:\n" + nnfed)

        simpleSolver.solveSAT(nnfed) match {
          case (Some(false), _) =>
            result = Some(false)

          case (Some(true), m) =>
            result = Some(true)
            theModel = Some(m)

          case (None, m) =>
            result = None
            theModel = Some(m)
         }
         result 
      } getOrElse {
        Some(true)
      }

      def checkAssumptions(assumptions : Set[Expr]) : Option[Boolean] = {
        fail("checkAssumptions(assumptions)")
      }

      def getModel : Map[Identifier,Expr] = {
        val vs : Set[Identifier] = theConstraint.map(variablesOf(_)).getOrElse(Set.empty)
        theModel.getOrElse(Map.empty).filter(p => vs(p._1))
      }

      def getUnsatCore : Set[Expr] = { fail("getUnsatCore") }
    }
  }

  private def nnf(expr : Expr, flip : Boolean) : Expr = expr match {
    case _ : Let | _ : IfExpr => throw new Exception("Can't NNF *everything*, sorry.")
    case Not(Implies(l,r)) => nnf(And(l, Not(r)), flip)
    case Implies(l, r)     => nnf(Or(Not(l), r), flip)
    case Not(Iff(l, r))    => nnf(Or(And(l, Not(r)), And(Not(l), r)), flip)
    case Iff(l, r)         => nnf(Or(And(l, r), And(Not(l), Not(r))), flip)
    case And(es) if flip   => Or(es.map(e => nnf(e, true)))
    case And(es)           => And(es.map(e => nnf(e, false)))
    case Or(es)  if flip   => And(es.map(e => nnf(e, true)))
    case Or(es)            => Or(es.map(e => nnf(e, false)))
    case Not(e) if flip    => nnf(e, false)
    case Not(e)            => nnf(e, true)
    case LessThan(l,r)      if flip => GreaterEquals(l,r)
    case GreaterThan(l,r)   if flip => LessEquals(l,r)
    case LessEquals(l,r)    if flip => GreaterThan(l,r)
    case GreaterEquals(l,r) if flip => LessThan(l,r)
    case elze if flip      => Not(elze)
    case elze              => elze
  }
}
