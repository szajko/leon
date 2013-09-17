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
    val modelForSomeSets : Map[Expr,Set[Int]] = ProceedSetOperators.getCounterExample(model)(meta)
    val asExprModel : Map[Expr,Expr] = modelForSomeSets.mapValues { is =>
      FiniteSet(is.map(IntLiteral(_)).toSeq).setType(SetType(Int32Type))
    }

    val originalVars : Set[Identifier] = meta.originalFreeVariables

    val withModel : Set[(Identifier,Option[Expr])] = originalVars.map { id =>
      val fromRealModel : Option[Expr] = asExprModel.get(Variable(id))
      val fromEncModel : Option[Expr]  = model.get(id)
      val best : Option[Expr] = fromRealModel orElse fromEncModel
      (id -> best)
    }

    withModel.filter(_._2.isDefined).toMap.mapValues(_.get)
  }
}
