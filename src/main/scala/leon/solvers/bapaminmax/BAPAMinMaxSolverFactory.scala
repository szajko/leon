/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers
package bapaminmax

import solvers.combinators._

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

class BAPAMinMaxSolverFactory[S <: Solver](sf : SolverFactory[S]) extends RewritingSolverFactory[S,EncodingInformation](sf) {
  val description : String = "QFBAPA< Rewriting Solver"
  val name : String = "BAPA<"
  
  def rewriteCnstr(expression : Expr) : (Expr,EncodingInformation) = {
    val (newExpression, meta) = Transformations.rewriteVC(expression)
    (newExpression, meta)
  }

  def reconstructModel(model : Map[Identifier,Expr], meta : EncodingInformation) : Map[Identifier,Expr] = {
    // FIXME : REMOVE
    ProceedSetOperators.getCounterExample(model)(meta)
    model
  }
}
