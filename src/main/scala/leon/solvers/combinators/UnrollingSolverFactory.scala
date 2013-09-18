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

class UnrollingSolverFactory[S <: Solver](val sf : SolverFactory[S]) extends SolverFactory[Solver] {
  val description = "Unrolling loop around a base solver."
  val name = sf.name + "*"

  val context = sf.context
  val program = sf.program

  // Yes, a hardcoded constant. Sue me.
  val MAXUNROLLINGS : Int = 3

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

      private def fail(because : String) : Nothing = {
        throw new Exception("Not supported in UnrollingSolvers : " + because)
      }

      def push() : Unit = fail("push()")
      def pop(lvl : Int = 1) : Unit = fail("pop(lvl)")
      
      def assertCnstr(expression : Expr) {
        if(!theConstraint.isEmpty) {
          fail("Multiple assertCnstr(...).")
        }
        theConstraint = Some(expression)
      }

      def interrupt() { fail("interrupt()") }

      def recoverInterrupt() { fail("recoverInterrupt()") }

      def check : Option[Boolean] = theConstraint.map { expr =>
        import context.reporter

        val simpleSolver = SimpleSolverAPI(sf)

        def info(msg : String) { reporter.info("In " + thisFactory.name + ": " + msg) }

        info("Check called on " + expr + "...")

        val template = getTemplate(expr)

        val aVar : Identifier = template.activatingBool
        var allClauses : Seq[Expr] = Nil
        var allBlockers : Map[Identifier,Set[FunctionInvocation]] = Map.empty

        def fullOpenExpr : Expr = {
          And(Variable(aVar), And(allClauses.reverse))
        }

        def fullClosedExpr : Expr = {
          And(fullOpenExpr, And(allBlockers.toSeq.map(p => Not(Variable(p._1)))))
        }

        val (nc, nb) = template.instantiate(aVar, template.funDef.args.map(a => Variable(a.id)))

        allClauses = nc.reverse
        allBlockers = nb

        var unrollingCount : Int = 0
        var done : Boolean = false
        var result : Option[Boolean] = None

        // We're now past the initial step.
        while(!done && unrollingCount < MAXUNROLLINGS) {
          val closed : Expr = fullClosedExpr
          simpleSolver.solveSAT(closed) match {
            case (Some(false), _) =>
              simpleSolver.solveSAT(fullOpenExpr) match {
                case (Some(false), _) =>
                  done = true
                  result = Some(false)

                case _ =>
                  fail("must unroll")
              }

            case (Some(true), model) =>
              done = true
              result = Some(true)
              theModel = Some(model)

            case (None, _) =>
              fail("unknown in underlying")
          }
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

  private val funDefTemplateCache : MutableMap[FunDef, FunctionTemplate] = MutableMap.empty
  private val exprTemplateCache : MutableMap[Expr, FunctionTemplate] = MutableMap.empty

  private def getTemplate(funDef: FunDef): FunctionTemplate = {
    funDefTemplateCache.getOrElse(funDef, {
      val res = FunctionTemplate.mkTemplate(funDef, true)
      funDefTemplateCache += funDef -> res
      res
    })
  }

  private def getTemplate(body: Expr): FunctionTemplate = {
    exprTemplateCache.getOrElse(body, {
      val fakeFunDef = new FunDef(FreshIdentifier("fake", true), body.getType, variablesOf(body).toSeq.map(id => VarDecl(id, id.getType)))
      fakeFunDef.body = Some(body)

      val res = FunctionTemplate.mkTemplate(fakeFunDef, false)
      exprTemplateCache += body -> res
      res
    })
  }
}
