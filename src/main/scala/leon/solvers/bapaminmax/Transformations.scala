/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers
package bapaminmax

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

object Transformations {
  import ProceedSetOperators._

  def rewriteVC(expression : Expr) : (Expr,EncodingInformation) = {
    var vc = expression

    //eliminating lets operators
    var collected : List[(Identifier, Expr)] = Nil

    def letCollector(e : Expr) : Expr = e match {
      case Let(i, e, b) => collected = (i, e) :: collected; b
      case other => other
    }

    val withoutLets : Expr = simplePostTransform(letCollector)(vc)

    val asEqualities : List[Expr] = collected.map {
      case (i, e) => Equals(Variable(i), e)
    }

    val woletvc =  And(withoutLets :: asEqualities)
         
    //collect the expression on sets      
    var setConstraints : Set[Expr]= Set.empty 
    
    def collectSetOperator(t: Expr)  = t  match {
      case SetEquals(l,r) => {
        //println("A SetEquals operator is found.")
        //println(l.getType)
        setConstraints += t; IntLiteral(0)
      }
      case ElementOfSet(_, _) => setConstraints += t; IntLiteral(0)
      case SubsetOf(_, _) => setConstraints += t; IntLiteral(0)
      case SetIntersection(_,_)=> setConstraints += t; IntLiteral(0)
      case SetMin(_) => setConstraints += t; IntLiteral(0)
      case SetMax(_) => setConstraints += t; IntLiteral(0)
      case SetCardinality(_) => setConstraints += t; IntLiteral(0)
      case SetUnion(_,_)=> setConstraints += t; IntLiteral(0)
      case SetDifference(_, _) => setConstraints += t; IntLiteral(0)
      case FiniteSet(_) => setConstraints += t; IntLiteral(0)
      case _ => t
    }
    
    val myPrinter : Expr=>Expr = simplePreTransform(e => { collectSetOperator(e) })
    
    val s = myPrinter(woletvc)
    
    var setCnsrt: Expr = BooleanLiteral(true)
    
    // This carries all the mutable state that comes from
    // the encoding into new variables etc.
    val meta = new EncodingInformation()

    if (! setConstraints.isEmpty){
      //println(woletvc)
    
      // println("----------------------The collected set expresssiona are:----------------------")
      // println(setConstraints)

      setCnsrt = proceedSets(setConstraints)(meta)
      //println("All added constraints------------------------" + setCnsrt)
    }
    
    vc = And(setCnsrt, vc)
    
    meta.originalFreeVariables = variablesOf(expression)
    (vc, meta)
  }
}
