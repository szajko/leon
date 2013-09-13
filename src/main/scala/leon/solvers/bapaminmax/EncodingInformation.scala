/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers
package bapaminmax

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

class EncodingInformation() {
    //contains all "in" operators, all of them starts with in
    var elementsOf : Set[Expr] = Set.empty
    //contains all constant sets
    var constantSets : Set[Expr] = Set.empty
    var sideConstraints : Set[Expr] = Set.empty
    var globalSideConstraints : Set[Expr] = Set.empty
    // Boolean variables
    var isEmptySet: Boolean = false
    val myEmptySet = Variable(FreshIdentifier("EmptySet", true).setType(SetType(Int32Type)))
    var inf : Expr = IntLiteral(0)
    var mInf: Expr = IntLiteral(0)
    var isMinMax: Boolean = false
    
    //collect Dependencies
    var cDep: Set[Set[Expr]] = Set.empty
    var mDep: Set[Set[Expr]] = Set.empty
    //and the original formula
    var cOrig: Set[Expr] = Set.empty
    var mOrig: Set[Expr] = Set.empty
    var MOrig: Set[Expr] = Set.empty
    //containts the elements of constantSets and right sides of element
    var sngSet: Set[Expr] = Set.empty
    var sngArray: Array[Expr] = Array.empty
    //mapping all variables that are defined as Expr
    var stringToExpr : Map[String, Expr] = Map.empty
    var finalClusters: Array[Array[Expr]] = Array.empty
    var globalClusts: Array[Set[Expr]] = Array.empty
    var globalMinMaxIndicies : Set[Int] = Set.empty
    //fo handling the singletons
    var componentToXMap: Map[Set[Expr], Set[Int]] = Map.empty
    var alfaToRegion: Map[String, (Set[Expr],Set[Expr])] = Map.empty
    var alfaToVarMap: Map[String, Int] = Map.empty
    //min-max cluster -> (Set(m...), Set(M...)) 
    var mClustToM: Map[Set[Expr], (Set[String],Set[String])] = Map.empty
    //m.. or M.. -> (set containing, set not conctaining)
    var mToRegion: Map[String, (Set[Expr],Set[Expr])] = Map.empty
    var regionToBMap: Map[(Set[Expr],Set[Expr]), Set[String]] = Map.empty
    var serialNumberToNumOsMap : Map[Int, Int] = Map.empty
    var setCollecor : Set[Expr] = Set.empty

    
    //HyperGraph
    var G = new HyperGraph
}
