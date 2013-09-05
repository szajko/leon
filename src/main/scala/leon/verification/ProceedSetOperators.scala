/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package verification

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

//my things
import HyperGraph._

import solvers.{Solver,TrivialSolver,TimeoutSolver}
import solvers.z3.FairZ3Solver

import scala.collection.mutable.{Set => MutableSet}

object ProceedSetOperators {

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

    
    //HyperGraph
    var G = new HyperGraph

    def proceedSets(e: Set[Expr]) : Expr = {
      //initialization
      elementsOf = Set.empty
      constantSets = Set.empty
      sideConstraints = Set.empty
      globalSideConstraints = Set.empty
      isEmptySet = false
      isMinMax = false
    
      //cardinality and min-max dependencies
      cDep = Set.empty
      mDep = Set.empty
      cOrig = Set.empty
      mOrig = Set.empty
      MOrig = Set.empty
      sngSet = Set.empty
      sngArray = Array.empty
      //maps
      stringToExpr = Map.empty
      finalClusters = Array.empty
      globalClusts = Array.empty
      globalMinMaxIndicies = Set.empty
      componentToXMap = Map.empty
      alfaToRegion = Map.empty
      alfaToVarMap = Map.empty
      mClustToM = Map.empty
      mToRegion = Map.empty
      regionToBMap = Map.empty
      inf = getVar("inf")
      mInf= getVar("mInf")

      //lift all constant sets that are not variables
      //and eliminate the following operators:
      //seteq, subset, in, constantSets
      e.foreach(tp => eliminateOperators(tp))
      println("-- sideConstraints -- " + sideConstraints)
      sngArray = sngSet.toArray
      val  newE : Set[Expr] = e | sideConstraints
      
      //apply DeMorgan + meanwhile collect Dependencies
      //only card, min and max operators are remained on diff, intersec, union, compl of some sets
      newE.foreach(tp => deMorganCollectDep(tp))
      if (mDep != Set.empty) isMinMax = true
      println("-- cDep -- " + cDep)
      println("-- mDep -- " + mDep)
      
      //creating clusters
      val clusters: (Array[Set[Expr]], Set[Int]) = createClusters(cDep, mDep)
      globalClusts = clusters._1
      println("--- clusters----" + globalClusts.toSet)
      globalMinMaxIndicies = clusters._2
      println("Min-max indeces of the clusters: " + globalMinMaxIndicies)
      //produces finalClusters
      clsToArray(clusters._1)
      println("Singletons Array:" + sngArray.toSet)
      
      val cardCnstrs: Expr = G.getEqualities("k#", Set.empty)
      println("Cardinality constraints:\n" + cardCnstrs )
      val substituteCnstr : Expr = subsAbsMinMax()
      
      val sngCnstr : Expr = getTheSevenTypeCnstr()
      
      //println("This should not be empty: mClustToM " +       mClustToM)
      //println("This should not be empty: mToRegion " +       mToRegion)
      
      //collect sngs-s
      //var sngs : Set[Expr] = Set.empty
      //bridges.foreach{a => sngs += a._2}
      
      //println("sngCnstr: " + sngCnstr)
      println("substituteCnstr: " + substituteCnstr)
      println("cardCnstr: " + cardCnstrs)
      //println("And(sideConstraints.toSeq: " + And(sideConstraints.toSeq))
      
      val infCnstr : Expr = And(GreaterEquals(inf, IntLiteral(1000)),LessEquals(mInf, IntLiteral(-1000)))
      
      val allcnsrt : Set[Expr] = Set(sngCnstr, substituteCnstr, cardCnstrs, And(sideConstraints.toSeq), infCnstr)
 
      And(allcnsrt.toSeq)
     }

     
    def eliminateOperators(formula : Expr) : Unit = {
      //do not define local variables as this function is called multiple times
    
      def rec(t : Expr) : Unit = t match {
        case SetEquals(l, r) => { //will it recognise that it is not a simple equal 
	  val tmp1: Expr = Equals(SetCardinality(SetIntersection(l, SetComplement(r))),IntLiteral(0))
	  val tmp2: Expr = Equals(SetCardinality(SetIntersection(r, SetComplement(l))),IntLiteral(0))	  
	  sideConstraints += Iff(SetEquals(l,r), And(tmp1, tmp2))
        }
        case SubsetOf(l, r) =>{
	  val tmp: Expr = Equals(SetCardinality(SetIntersection(l, SetComplement(r))),IntLiteral(0))
	  sideConstraints += Iff(SubsetOf(l,r), tmp)
        }
        //it should be done in applyDeMorgan
        /*case SetDifference(l, r) =>{
	  val tmp: Expr = Equals(SetCardinality(SetIntersection(l, SetComplement(r))),IntLiteral(0))
	  sideConstraints += Iff(SetDifference(l,r), tmp)
        }*/
        case ElementOfSet(l, r) => {
	  elementsOf += ElementOfSet(l, r)
	  sngSet += l
	}
	case fs @ FiniteSet(s) => { // s : Seq[Expr] (Expr = int type)
	  if (s.isEmpty) {
	    isEmptySet = true
	    sideConstraints += Equals(SetCardinality(fs), IntLiteral(0))
	  }
	  else {
	    constantSets += fs
	    //cDep += Set(t)
	  }
	  cDep += Set(t)
	  sngSet ++= s.toSet
	}
	case _ =>{ }
      }
      
     val afterRec : Expr=>Expr = simplePreTransform(e => { rec(e);  e})
     val s = afterRec(formula)
     //if(isEmptySet == true){
     //	sideConstraints += Equals(SetCardinality(myEmptySet),IntLiteral(0))
     //}
     //sngArray = sngSet.toArray
     //end of liftConstantSets 
  }
  
   def deMorganCollectDep(formula : Expr) : Unit = {
      
      //applyDeMorgan
     def rec(t : Expr) : Expr = t match {	
       case SetUnion(l, r) => SetUnion(rec(l), rec(r))
       case SetIntersection(l, r) => SetIntersection(rec(l), rec(r))
       case SetDifference(l, r) => rec(SetIntersection(l, SetComplement(r)))
       case SetComplement(SetComplement(l)) => rec(l)
       case SetComplement(SetUnion(l,r)) => rec(SetIntersection(SetComplement(l),SetComplement(r)))
       case SetComplement(SetIntersection(l,r)) => rec(SetUnion(SetComplement(l),SetComplement(r)))
       case SetComplement(SetDifference(l,r)) => rec(SetComplement(SetIntersection(l, SetComplement(r))))
       case _ => t
     }
     //three relevant operators: card, min, max
     def findOps(et: Expr): Unit = et match {
       case SetCardinality(l) =>{
         val tmp = rec(l)
         if (tmp != l)
           sideConstraints += Equals(SetCardinality(l), SetCardinality(tmp))
         cOrig += tmp
         cDep += addSets(tmp, Set.empty)
       }
       case SetMin(l) => {
         val tmp = rec(l)
         if (l != tmp)
           sideConstraints += Equals(SetMin(l), SetMin(tmp))
         mOrig += tmp
         mDep += addSets(tmp, Set.empty)
       }
       case SetMax(l) => {
         val tmp = rec(l)
         if (l != tmp)
           sideConstraints += Equals(SetMax(l), SetMax(tmp))
         MOrig += tmp
         mDep += addSets(tmp, Set.empty)
       }
       case ElementOfSet(l, r) => {
         //val tmp1 = rec(l)
         val tmp2 = rec(r)
         cDep += addSets(tmp2, Set.empty)
       }
       case _ =>{ }
     }
     // computes a set of sets of related sets (ahem).
     // E.g. if you have | A U B | != | C \ B |, the result should be:
     // { { A, B }, { B, C } }
     //the input is a region in a card / min-max constraint
     def addSets(ut: Expr, clusters: Set[Expr]) : Set[Expr] = ut match {
       case SetUnion(l, r) => addSets(l, Set.empty) | addSets(r, clusters)
       case SetIntersection(l, r) => addSets(l, Set.empty) | addSets(r, clusters)
       case SetComplement(l) => addSets(l, clusters)
       //it might only be a set
       case _ => clusters + ut
     }
      
     val afterRec : Expr=>Expr = simplePreTransform(e => { findOps(e);  e})
     val s = afterRec(formula)
 
     //end of deMorganCollectDep
  }
  
  //select dependencies, which contains all dependencies
  def filterNecessaryDep(dep: Set[Set[Expr]]) : Set[Set[Expr]] = {
      dep.filter(s1 => !dep.exists(s2 => (s1!=s2 && s1.subsetOf(s2))))
  }
  
  //creating the hyperGraph
  //(cardinality dependencies + singleton set, min-max dependencies)
  def createClusters(cardDep: Set[Set[Expr]],  minMaxDep: Set[Set[Expr]] ) : (Array[Set[Expr]], Set[Int])  ={ 
    G = new HyperGraph
    G.createHyperGraph(filterNecessaryDep(cardDep))
    //createMinMaxClusters should be called first, as it can modify the cardClusters
    G.createMinMaxClusters(filterNecessaryDep(minMaxDep))
    G.getClustsArrays()
  }
  
  //write constraints for cl1 and cl2
  def writeCnstrsForClusters(st: String, cl1: Set[Expr], cl2: Set[Expr]): Set[Expr] ={
    var additionalConstr : Set[Expr] = Set.empty
    //find the clusters, if not found-> return -1 -> it should never be the case
    def findCluster(cls1: Set[Expr]): Int = {
      var found: Boolean = false
      var jj: Int = -1
      for(ii<- 0 to globalClusts.length-1 if !found) {
        if(globalClusts(ii) == cls1){
          jj = ii
          found = true
        }
      }
      jj
    }    

    
    //comVars is not empty!
    def getAST(st: String, comVars: Set[Expr], clustNum1: Int, clustNum2: Int){
      val cls1 : Set[Expr] = globalClusts(clustNum1)
      var cls2 : Set[Expr] = globalClusts(clustNum2)
      var comRegions : Set[(Set[Expr],Set[Expr])]= Set.empty 
      val str: Expr = comVars.head
      comRegions += Pair(Set.empty,Set(str)) 
      comRegions += Pair(Set(str),Set.empty) 
      for (ii<-comVars){
        for(comReg<-comRegions if(!comReg._1.contains(ii) && !comReg._2.contains(ii))){
          comRegions -= comReg
          comRegions += Pair(comReg._1 + ii, comReg._2)
          comRegions += Pair(comReg._1, comReg._2 + ii)
        }
      }      
      //eliminate the case, where every set variable is negated 
      // == the complement of all variables is considered
      for(comReg<-comRegions if(comReg._1 == Set.empty)){
        comRegions -= comReg
      }
      
      for(comReg<-comRegions){
        val leftSide: Set[String] = getRegName(st, comReg._1, comReg._2, clustNum1, cls1)
        val rightSide: Set[String] = getRegName(st, comReg._1, comReg._2, clustNum2, cls2)
        //stat.cardConstr += 1
        if (st.startsWith("k"))
          additionalConstr += Equals(addStringsAsVars(leftSide),addStringsAsVars(rightSide))
        else
          //sys.error("WriteCnstrsForClusters is called with a wrong prefix: st!")
          additionalConstr += Equals(orStringsAsVars(leftSide),orStringsAsVars(rightSide))          
      }
            
    }
    
    val n1 = findCluster(cl1)
    val n2 = findCluster(cl2)
    if (!(cl1 & cl2).isEmpty){
      getAST(st, cl1 & cl2, n1, n2)
    }
    additionalConstr    
  }
  
  //returns the modified AST and the set of constant set (their cardinality is needed later)
  def subsAbsMinMax() : Expr ={
    var siConstraints: Set[Expr] = Set.empty
    
    cOrig.foreach(a=> {
      val resRegion: (Set[String],Set[Expr]) = getRegionAST("k#" ,a, -1)
      //siConstraints ++= resRegion._2
      siConstraints += Equals(SetCardinality(a), addStringsAsVars(resRegion._1)) 
    })
    mOrig.foreach(a=> {
      val resRegion: (Set[String],Set[Expr]) = getRegionAST("m#" ,a, -1)
      //siConstraints ++= resRegion._2
      var toOr : Set[Expr] = Set.empty
      resRegion._1.foreach(b=> {
        siConstraints += LessEquals(SetMin(a), getVar(b))
        toOr += Equals(SetMin(a), getVar(b))
      })
      siConstraints += Or(toOr.toSeq)
    })
    MOrig.foreach(a=> {
      val resRegion: (Set[String],Set[Expr]) = getRegionAST("M#" ,a, -1)
      //siConstraints ++= resRegion._2
      var toOr: Set[Expr] = Set.empty
      resRegion._1.foreach(b=> {
        siConstraints += GreaterEquals(SetMax(a), getVar(b))
        toOr += Equals(SetMax(a), getVar(b))
      })
      siConstraints += Or(toOr.toSeq)
    })
    
    elementsOf.foreach(a => 
      a match {
	case ElementOfSet(l, r) => {
	  val ind : Int = getIndex(l)
	  val resRegion: (Set[String],Set[Expr]) = getRegionAST(("A#" +ind+"#") ,r, ind)
	  siConstraints += Iff(ElementOfSet(l, r),Or(resRegion._1.map(b=>getVar(b)).toSeq)) 
	}
	case _ => {
	  sys.error("Error in elementsOf variable.")
	}
      }
    )
    
    constantSets.foreach(a => 
      a match {
	case fs @ FiniteSet(r) => {
	  var toAnd: Set[Expr] = Set.empty
	  r.foreach(b=>{
	    val ind: Int = getIndex(b)
            val resRegion: (Set[String],Set[Expr]) = getRegionAST(("A#" +ind+"#") ,fs, ind)
	    toAnd += Or(resRegion._1.map(b=>getVar(b)).toSeq) 
	  })	    
	  siConstraints += And(toAnd.toSeq)
	}
	case _ => {
	  sys.error("Error in constantSets variable.")
	}
      }
    )
   /*case Eleme(l, r) =>{ 
        //meanwhile alfaToRegion should be updated
        var xName: String =""
        l match{
          case Var(s) => xName = s
          case _ => sys.error("In the right side of Eleme(l,r), a Var(s) should be.")
        }
        val resRegion: (Set[String],Set[AST[Boolean]]) = getRegionAST(("A#"+xName+"_#") ,r, xName)
        siConstraints ++= resRegion._2
        makeOrVars(resRegion._1)
      }*/
    //this for the constantSets
    And(siConstraints.toSeq)
  }
      
    
  
   //return an AST[Int] substituting a cardinality or min-max values of a region
  //if bothe isCard and isMin are true, it returns cardinality names for min/max constraints!
  def getRegionAST(st: String, region: Expr, xName: Int) :(Set[String],Set[Expr]) ={
    var res: Set[(Set[Expr],Set[Expr])] = Set.empty
    var sideCnstrs: Set[Expr] = Set.empty
    //the Union operator will be on the top of the tree
    //the applied rule is A^(B U C) = (A^B) U (A^C) and analogously (A U B)^C = (A^C) U (B^C) 
    def liftUnion(t: Expr ) : Expr = t match{
      case SetUnion(l, r) => SetUnion(liftUnion(l),liftUnion(r))
      case SetIntersection(SetUnion(l1,r1),r) => SetUnion(liftUnion(SetIntersection(l1,r)),liftUnion(SetIntersection(r1,r)))
      case SetIntersection(l,SetUnion(l2,r2)) => SetUnion(liftUnion(SetIntersection(l,l2)),liftUnion(SetIntersection(l,r2)))
      case SetIntersection(l, r) =>{ SetIntersection(liftUnion(l),liftUnion(r))
      }
      //case Setminus(l, r) => this is already eliminated
      case SetComplement(l) => SetComplement(l) //complement of more than one element is also eliminated
      case _ => t
    }
    
    //get the variables
    def traverseTree(t: Expr) : Unit = t match {
      case SetUnion(l, r) => traverseTree(l); traverseTree(r)
      case SetIntersection(l, r) => res += getVariables(t)
      //case Setminus(l, r) => this is already eliminated
      //case Compl(Setvar(l)) => res += Pair(Set.empty, Set(l)) 
      //complement of more than one element is also eliminated
      //case Compl(Myset(l)) => warn("UNDEFINED input format, 
      //it is not possible to have a region with only complements variables.")
      //case Compl(Setvar(s)) => warn("UNDEFINED input format, 
      //it is not possible to have a region with only complements variables.")
      case _ => res += Pair(Set(t), Set.empty)
    }
    
    def getVariables(t: Expr): (Set[Expr],Set[Expr]) = t match{
      //case Union(l, r) => getVariables(l) | getVariables(r)
      case SetIntersection(l, r) => (getVariables(l)._1 | getVariables(r)._1, getVariables(l)._2 | getVariables(r)._2)
      case SetComplement(l) => Pair(Set.empty, Set(l))
      case _ => Pair(Set(t), Set.empty)   
    }
    
    def getContainingVariables(t: Expr): Set[Expr] = t match{
      case SetUnion(l, r) => getContainingVariables(l) | getContainingVariables(r)
      case SetIntersection(l, r) => getContainingVariables(l) | getContainingVariables(r)
      //case Setminus(l, r) => getContainingVariables(l) |getContainingVariables(r)
      case SetComplement(l) => getContainingVariables(l)
      case _ => Set(t)     
    }
    //starts executing getRegionAST here
    //find the cluster, which contains the variables of this region
    val isThisMinMax: Boolean = st.startsWith("m#") || st.startsWith("M#")
    var found: Boolean = false
    var j : Int = 0
    for(i<-0 to globalClusts.length -1 if (!found && (globalMinMaxIndicies.contains(i) || !isThisMinMax))){
      if (getContainingVariables(region).subsetOf(globalClusts(i))) {found = true; j=i}
    }
    //println("this is the region: " + region)
    if (!found) sys.error("The containing cluster in getRegionAST was not found!!!")
    var unionLifted: Expr = liftUnion(region)
    while (unionLifted != liftUnion(unionLifted)){
      unionLifted = liftUnion(unionLifted)
    }
    traverseTree(unionLifted)
    
    var toSum: Set[String] = Set.empty
    //println("Res: " + res)

    for(ii<-res){
      //println("inGetRegionAST" + ii._1 + "  " + ii._2.toString + "  " + j.toString + " cluster:  " + clusters(j).toString +isCard.toString+isMin.toString )
      //this might be only the empty sets, ie.:B\B = B intersec B...
      //we should handle the empty region with additional constraints
      if ((ii._1 & ii._2) != Set.empty){
        //toSum += (st +"_empty")
        //if (st == "k#") sideCnstrs += Eq(Var(st +"_empty"),Const(0))
        //else if (st != "m#"&& st != "M#") sideCnstrs += Eqbool(VarBool(st +"_empty"),Bool(false))
        //else globalEmptyDefined = true
        sys.error("The program cannot handle the complement of the union of some sets," +
                  " each region should contain at least one set.")
      }
      else toSum ++= getRegName(st, ii._1, ii._2, j, globalClusts(j))
    }
    //toSum.map(a=> a + "_" +xName)
    //update componentToXMap
    if(xName != -1){
      val tmpComponent = G.components.find(a => globalClusts(j).subsetOf(a))
      tmpComponent match{
        case Some(a) =>{
          val tmpCompInMap = componentToXMap.find(b => b._1 == a)
          tmpCompInMap match{
            case Some(b) =>{
              val previous: Set[Int] = componentToXMap(a)
              componentToXMap -= a
              componentToXMap += (a->(previous+xName))
            }
            case None => componentToXMap += (a->Set(xName))
          }
        }
        case None => sys.error("The containing component in getRegionAST() was not found.")
      }
    }
    (toSum, sideCnstrs)

  }
// ---------------------------------------------------------------------  
//naming functions
  //if both isCard and isMin are true, it returns cardinality names for min/max constraints
  def getRegName(st: String, setContain: Set[Expr], setNotContain: Set[Expr], clstNum: Int, cluster: Set[Expr]) : Set[String] = { 
    //println("set contain: " + setContain + " not contain: " + setNotContain + " cluster: " + cluster)
    var res: Set[String] = Set.empty
    //if (setContain == Set.empty) sys.error("The setContain set cannot be empty in getRegionNames().")
    var allRegions : Set[(Set[Expr],Set[Expr])]= Set(Pair(setContain,setNotContain))
    //it can, because of noMultipleSngs...
    if(setContain == Set.empty){
      val oneElement: Expr = cluster.head
      allRegions += Pair(Set(oneElement),Set.empty)
      allRegions += Pair(Set.empty, Set(oneElement))
    }
   
     
    for (ii<-cluster){
      for(reg<-allRegions if(!reg._1.contains(ii) && !reg._2.contains(ii))){
        allRegions -= reg
        allRegions += Pair(reg._1 + ii, reg._2)
        allRegions += Pair(reg._1, reg._2 + ii)
      }
    }
    
    //but we have to substract the case, where there is no containing setContain
    for(allReg<-allRegions if(allReg._1 == Set.empty)){
        allRegions -= allReg
    }

    for(reg<-allRegions){
      res +=getName(st, reg._1, reg._2, clstNum)
    }
    res
    
  }
  
  //min-max cluster -> (Set(m...), Set(M...)) 
  //var mClustToM: Map[Set[String], (Set[String],Set[String])] = Map.empty
  //var mToRegion: Map[String, (Set[String],Set[String])] = Map.empty
  //name: k/m/M/mk_clusternumber_1010010
  //if both isCard and isMin are true, it returns cardinality names for min/max constraints
  //long_max = 2^63-1, thus the maximum number of Strings = 62 !! 
  def getName(st: String, setContaining: Set[Expr], setNotContaining: Set[Expr], clustNum: Int): String ={
  
    if ((setContaining & setNotContaining) != Set.empty)
      sys.error("The input sets in getName() shoud be disjoint.")
    if (setContaining.size + setNotContaining.size > 63)
      sys.error("The maximum number of input sets in getName is 63, as the greatest long is 2^63-1.")
    var orderedArray: Array[Expr] = finalClusters(clustNum)
    //findOrder(setContaining | setNotContaining)
    //in the old version scala.util.Sorting.quickSort(orderedArray)
    var seqNum: Long = 0
    for(i<-0 to orderedArray.length-1){
        if (setContaining.contains(orderedArray(i))) seqNum += pow2(i)       
    }
    var name: String = st + clustNum.toString + "#" + seqNum.toString
    
    if (st.startsWith("A#")){
      alfaToRegion +=(name->Pair(setContaining,setNotContaining))
      alfaToVarMap += (name->(st.drop(2).dropRight(1)).toInt)
    }
    else if(st == "m#" ){
      mToRegion += (name-> Pair(setContaining,setNotContaining))
      addTomClustToM((setContaining | setNotContaining), name, true)
    }
    else if (st == "M#"){
      mToRegion += (name-> Pair(setContaining,setNotContaining))
      addTomClustToM((setContaining | setNotContaining), name, false)
    }
    name

  }
  
  def addTomClustToM(clust: Set[Expr], m: String, isMin: Boolean){
    val c = mClustToM.find(a=> (a._1==clust))
    c match {
      case Some(x) => {
        mClustToM -=x._1
        if (isMin) mClustToM += (clust->(x._2._1 +m, x._2._2  ))
        else mClustToM += (clust->(x._2._1 , x._2._2 +m ))
      }
      case None => {
        if (isMin) mClustToM += (clust-> (Set(m),Set.empty ))
        else mClustToM += (clust-> (Set.empty, Set(m)))
      }
    }
  }
  
  //there is not built-in Math.pow function for long values
  def pow2(n: Int): Long = {
    if (n==0) 1
    else 2*pow2(n-1)
  }
  
  def addStringsAsVars(mySet: Set[String]) : Expr = {
    val first: String = mySet.head 
    var tree: Expr = getVar(first)
    for (toAdd<-mySet if toAdd!= first){
       tree = Plus(tree, getVar(toAdd))
    }
    tree  
  }
  
  def orStringsAsVars(mySet: Set[String]) : Expr = {
    Or(mySet.map(a=> getVar(a)).toSeq)
    //val first: String = mySet.head 
    //var tree: Expr = getVar(first)
    //for (toAdd<-mySet if toAdd!= first){
    //   tree = Or(tree, getVar(toAdd))
    //}
    //tree  
  }
  
  def makeNegAndStrings(mySet: Set[String]) : Expr = {
    And(mySet.map(a=> Not(getVar(a))).toSeq) 
  }
  
  def makeAddZ3AST(additional: Set[Expr]): Expr ={
//    else {
      val first: Expr = additional.head
      var res: Expr = first
      for(a<-additional if a!=first){
        res = Plus(res, a)
      }
      res
//    }
  }
  
  
  
  
//------------------------------------------------------------------------------------------------------
// auxiliary functions
   def getVar(str: String) : Expr = {
      //the crated variables may start with 
      //in case of integers: k#, M#, m#, E#
      //in case of booleans: A#, B#, G#
      val c = stringToExpr.find(a=> (a._1== str))
      c match {
	case Some(x) => {
	  x._2
	}
	case None => {
	  var typeOfVar : TypeTree = Int32Type
	  if (str.startsWith("A") || str.startsWith("B") || str.startsWith("G") )
	    typeOfVar = BooleanType	  
	  val mySetName = FreshIdentifier(str, true).setType(typeOfVar)
	  //BooleanType
	  val v : Expr= Variable(mySetName)
	  if (str.startsWith("k#"))
	    sideConstraints += GreaterEquals(v, IntLiteral(0)) 
	  stringToExpr += (str -> v)
	  //all k#.. >= 0 and M# and m# are between inf and -inf
	  v
	}
      }
    }
    
  def clsToArray(cls: Array[Set[Expr]]): Unit = {
    /*for(ii<- 0 to cls.length -1){
      finalClusters(ii) = cls(ii).toArray
    }*/
    finalClusters =cls.map(a=>{a.toArray})
  }

  // An object used to generate fresh variable names.
  object FreshName {
    private var used : Map[String,Int] = Map.empty

    def apply(prefix : String) : String = {
      val lastUsed = used.getOrElse(prefix, -1)
      val next = lastUsed + 1
      used = used.updated(prefix, next)
      prefix + next
    }
  }
  
  def getIndex(sn: Expr): Int = {
    var found: Boolean = false
    var jj: Int = -1
    for(ii<- 0 to sngArray.length-1 if !found) {
      if(sngArray(ii) == sn){
        jj = ii
        found = true
      }
    }
    jj
  }
//-----------------------------------------------------------------
//produce the seven type of constraints
//-----------------------------------------------------------------
  def getTheSevenTypeCnstr(): Expr = {
    var eArray : Array[Expr] = Array.empty
//nagyon fontos, hogy minden változó -inf és inf között legyen FIXME
    var componentESetMap: Map[Set[Expr], Set[String]] = Map.empty
    
    //orderES - generates the first type of constraints
    def get1st(compNum: Int, compInG: Set[Expr] ,eNums: Int): Expr= {
      var setEs : Set[String] = Set.empty
      var toAnd: Set[Expr] = Set.empty
      for(ii<-0 to sngArray.size -1 ){
        setEs += ("E#"+compNum + "#" + (ii))
        if (ii!= 0)
          toAnd += LessThan(getVar("E#"+compNum + "#" + (ii-1)), getVar("E#"+compNum + "#" + ii))
      }
      componentESetMap += (compInG -> setEs)
      And(toAnd.toSeq) 
    }
      
    //mapEqualities
    def get2nd(compNum: Int, compInG: Set[Expr], eNums: Int): Expr ={
      val filtered = componentToXMap.filter(a=>{ compInG.subsetOf(a._1)})
      var toAnd : Set[Expr] = Set.empty
      var toOrr : Set[Expr] = Set.empty
      filtered.foreach(a=>{//a.2 contains the indices of the proper singletons
        //x=e1 v x=e2 v..., only one a should be found
        for(v<-a._2){
          toOrr = Set.empty
          for(ii<-0 to eNums-1){
            val eqClass: Expr = getVar("E#"+compNum + "#" + ii)
            toOrr += Equals(sngArray(v), eqClass)
          }
          toAnd += Or(toOrr.toSeq)
        }
      })
      And(toAnd.toSeq) 
    }
      
    //ensureConsistency->5
    def get3rd(compNum: Int, compInG: Set[Expr], eNums: Int): Expr ={
      //B1 = B2 v B3....
      //we add constraints based on the hypergraph
      var toAnd: Set[Expr] = Set.empty
      for(ii<-0 to eNums-1){
        val st: String = "B#E#"+compNum + "#" + ii + "#"
        val cnstr: Expr = G.getEqualities(st, compInG)
        if (cnstr != IntLiteral(0)) {
          //println("Added third type constraints: " + cnstr
          toAnd += cnstr
        }
      }
      if (toAnd != Set.empty)
        And(toAnd.toSeq)
      else
        IntLiteral(0)
    }
      
      
    //noMultipleSngs
    def get4th(compNum: Int, compInG: Set[Expr], eNums: Int): Expr ={
      //summa B#E..-s <=1 in each cluster
      var toAnd: Set[Expr] = Set.empty
      for(ii<-0 to G.clusters.length-1){
        //if the cluster is in this cluster
        if (G.clusters(ii).subsetOf(compInG) && G.clusters(ii).size > 1){
           val nameSet : Set[String] = getRegName("#", Set.empty, Set.empty, ii, G.clusters(ii))
           var toOrr: Set[Expr] = Set.empty
           var modNameSet : Set[String] = Set.empty
           for(jj<- 0 to eNums-1){
             modNameSet = nameSet.map(a=> ("B#E#"+compNum + "#" + jj +a))
             //println(modNameSet)
             for (except<-modNameSet){
               toOrr += And(getVar(except),makeNegAndStrings(modNameSet-except))
             }
             toOrr += makeNegAndStrings(modNameSet)
             toAnd += Or(toOrr.toSeq)
           }        
        }
      }
      And(toAnd.toSeq)
    }
      
    //elementIsIn->3
    def get5th(compNum: Int, compInG: Set[Expr], eNums: Int): Expr ={
      val regions: Set[(Set[Expr],Set[Expr])] = alfaToRegion.values.toSet
      var toAnd : Set[Expr] = Set.empty
      for(reg<-regions if (reg._1 | reg._2).subsetOf(compInG)){
        //filter the alfa values defined for this region
        val alfaSet = (alfaToRegion.filter(a => a._2 == reg)).keySet
        for(ii<- 0 to eNums-1){
          var toOrr: Set[Expr] = Set.empty
          var toOrrb: Set[Expr] = Set.empty     
          alfaSet.foreach(b=>{
          //x=e ^ alfa   
          toOrr += And(Equals(sngArray(alfaToVarMap(b)), getVar("E#"+compNum + "#" + ii)), getVar(b)) 
          toOrrb += And(Equals(sngArray(alfaToVarMap(b)), getVar("E#"+compNum + "#" + ii)), Not(getVar(b))) 
          })
          val tmp: Expr = Or(toOrr.toSeq)
          val B: String = getName("B#E#"+compNum + "#" + ii + "#", reg._1, reg._2, findCluster(reg._1 | reg._2))
          toAnd += Or(Not(tmp),getVar(B))
          //x=e ^ ¬alfa ... => ¬B
          toAnd += Or(Not(Or(toOrrb.toSeq)), Not(getVar(B)))
          //z3.assertCnstr(createFormulaInZ3(Disj(Neg(makeOr(toOrrb)),Neg(VarBool(B)))))
        }    
      }
      And(toAnd.toSeq)
    }
      
    //cardMinSngs
    def get6th(compNum: Int, compInG: Set[Expr], eNums: Int): Expr ={
      //k>= summa B
      var toAnd: Set[Expr] = Set.empty
      //k>= summa B
      for(serialNumber<-0 to G.clusters.length-1 if G.clusters(serialNumber).subsetOf(compInG)){
        //set containing, and set not containing
        var allRegions : Set[(Set[Expr],Set[Expr])]= Set(Pair(Set.empty,Set.empty)) 
        for (ii<-G.clusters(serialNumber)){
          for(reg<-allRegions if(!reg._1.contains(ii) && !reg._2.contains(ii))){
            allRegions -= reg
            allRegions += Pair(reg._1 + ii, reg._2)
            allRegions += Pair(reg._1, reg._2 + ii)
          }
        }
        for(allReg<-allRegions if(allReg._1 == Set.empty)){
          allRegions -= allReg
        }
        //for each region
        for(reg<-allRegions){
          //for each equivalency class
          var setOfBs: Set[String] = Set.empty
          for(jj<-0 to eNums-1){
            val B: String = getName("B#E#"+compNum + "#" + jj + "#", reg._1, reg._2, serialNumber)
            setOfBs += B
          }
          val card: Expr = getVar(getName("k#", reg._1, reg._2, serialNumber))
          setOfBs.foreach(b=>{
            val ib: Expr = getVar("i"+b)
            toAnd += Implies(Equals(getVar(b),BooleanLiteral(true)),Equals(ib,IntLiteral(1)))
            toAnd += Implies(Equals(getVar(b),BooleanLiteral(false)),Equals(ib,IntLiteral(0)))
          })
          //this caused a mistake-> corrigated
          regionToBMap += (reg->setOfBs)
          toAnd += LessEquals(addStringsAsVars(setOfBs.map(b=>{"i"+b})),card)
        }
      }
      And(toAnd.toSeq)
      
    }
    
    //contOnlyThose
    def get7th(compNum: Int, compInG: Set[Expr], eNums: Int): Expr = {
      //B_e_r = e=x1 v e=x2 v...
      var toAnd: Set[Expr] = Set.empty
      for(cSet<-constantSets){
        val FiniteSet(elements) = cSet 
        //s is the name
        val s: Expr = cSet
        //strs contains the elements
        val strs: Set[Expr] = elements.toSet
        if (compInG.contains(s)){
        //find a cluster, in which there is this Constset
        val serialNumber: Int = findOneCluster(s)
        //set containing, and set not containing
        var allRegions : Set[(Set[Expr],Set[Expr])]= Set(Pair(Set(s),Set.empty)) 
        for (ii<-G.clusters(serialNumber)){
          for(reg<-allRegions if(!reg._1.contains(ii) && !reg._2.contains(ii))){
            allRegions -= reg
            allRegions += Pair(reg._1 + ii, reg._2)
            allRegions += Pair(reg._1, reg._2 + ii)
          }
        }
        //for each region
        for(reg<-allRegions){
          //for each equivalency class
          var setOfBs: Set[String] = Set.empty
          for(jj<-0 to eNums-1){
            var toOrSet: Set[Expr] = Set.empty
            //for each alfa in this region
            //println(alfaToRegion)
            val alfaSet = (alfaToRegion.filter(a => a._2 == (reg._1, reg._2))).keySet
            //println("alfaset" +alfaSet)
            alfaSet.foreach(b=>{
              //x=e ^ alfa
              if(strs.contains(sngArray(alfaToVarMap(b)))){
                toOrSet += And(Equals(sngArray(alfaToVarMap(b)), getVar("E#"+compNum + "#" + jj)), getVar(b))
              }
            })
            //println("toOrset: " + toOrSet)
            val tmp: Expr = Or(toOrSet.toSeq)
            val B: String = getName("B#E#"+compNum + "#" + jj + "#", reg._1, reg._2, serialNumber)
            setOfBs += B
            //println("7a: " + Eqbool(VarBool(B), tmp))
            toAnd += Equals(getVar(B), tmp)
          }
          val card: Expr = getVar(getName("k#", reg._1, reg._2, serialNumber))
          setOfBs.foreach(b=>{
            val ib: Expr = getVar("i"+b)
            //println("7b: " +z3.mkITE(z3.mkEq(z3bool,z3.mkTrue), z3.mkEq(z3int,one),z3.mkEq(z3int,zero) ) )
            toAnd += Implies(Equals(getVar(b),BooleanLiteral(true)), Equals(ib,IntLiteral(1)))
            toAnd += Implies(Equals(getVar(b),BooleanLiteral(false)), Equals(ib,IntLiteral(0)))
          })
          //println("7: " + Eq(card,makeAddVars(setOfBs.map(b=>{"i"+b}))))
          toAnd += Equals(card,addStringsAsVars(setOfBs.map(b=>{"i"+b})))
        }
        }
      }      
      And(toAnd.toSeq)
    }
      
    //some auxiliary functions
  
    def findOneCluster(cls1: Expr): Int = {
      var found: Boolean = false
      var jj: Int = -1
      for(ii<- 0 to G.clusters.length-1 if !found) {
        if(G.clusters(ii).contains(cls1)){
          jj = ii
          found = true
        }
      }
      if (jj== -1) sys.error("Cluster is not found in findOneCluster().")
      jj
    }
      
    def findCluster(cls1: Set[Expr]): Int = {
      var found: Boolean = false
      var jj: Int = -1
      for(ii<- 0 to G.clusters.length-1 if !found) {
        if(G.clusters(ii) == cls1){
          jj = ii
          found = true
        }
      }
      jj
    }
    //generateSMTforMinMax
//--------------------------------------------------    
    //second version of handling min-max constraints    
    def generateSMTforMinMax(): Expr = {
      //the sets of O-s Z3AST varibales
      var setOs: Set[Expr] = Set.empty
      //contains the defined c values for every interval
      var intToCs: Map[Int,Set[Expr]] = Map.empty
      var serialNumber: Int = 0
      
      var toAndo : Set[Expr] = Set.empty
      val zero: Expr = IntLiteral(0)
      val one: Expr = IntLiteral(1)
      val two: Expr = IntLiteral(2)

      
      //generate the set of O-s and the ordering constraints between them
      //the ordering constraints are automatically added to the SMT
      def generateOs(numOs: Int, setEs: Set[String]){
        setOs = Set.empty

        var previous: Expr = BooleanLiteral(true)
        for(ii<- 1 to numOs){
          val someO = getVar(("o#_"+ii+"_"+serialNumber))
          //adding ordering constraints for each o
          if (ii >1){
            toAndo += GreaterThan(someO,previous)
          }
          //for the first ordering, o_1 is greater than -inf
          else{
            toAndo += GreaterThan(someO,mInf)
          }
          previous = someO
          setOs += someO
        }
        //for the last O (O_n), we add that is is smaller, than inf
        toAndo += GreaterThan(inf,previous)
        
        var toAnd: Set[Expr] = Set.empty
        //add the constraints that the set of Es are in the O-s
        if (setEs != Set.empty) {
          for(e<-setEs){
            val eInZ3 :Expr = getVar(e)
            var toOr: Set[Expr] = Set.empty 
            for(o<-setOs){
              toOr += Equals(eInZ3, o)
            }
            toAnd += Or(toOr.toSeq)
          }
          toAndo += And(toAnd.toSeq)
        }
      }
      
      //the input is an m#_.. or M#_.. Expr variables
      //the output is an Expr, which ensures that the input is equal with one o in setOs
      def mIsSomeO(inputVar: Expr): Expr = {
        var toDisj : Set[Expr] = Set.empty
        for(ii<-setOs){
          toDisj += Equals(inputVar, ii)
        }
        Or(toDisj.toSeq)
      }
      
      //generates the set of c-s for a Venn region 
      //and the constraints, which c-s are zero
      def generateCs(inputVar: String, numOs: Int, Z3Min: Expr, Z3Max: Expr): (Set[Expr], Expr) = {
        var outputSet: Set[Expr] = Set.empty
        var outputCnstrs: Set[Expr] = Set.empty
        //m=>o_(j+1) => c_i^j=0
        //M<=o_j => c_i^j=0
        for(ii<-0 to numOs){
          val someC: Expr = getVar(("c"+inputVar+"_"+ii+"_"+serialNumber))
          toAndo += GreaterEquals(someC,zero)
          outputSet += someC
          //add constraints, when it is zero
          if (ii != 0 && ii!= numOs){
            val OGreater: Expr= getVar(("o#_"+(ii+1)+"_"+serialNumber))
            val OSmaller: Expr = getVar(("o#_"+ii+"_"+serialNumber))
            outputCnstrs += Implies(Or(GreaterEquals(Z3Min,OGreater),LessEquals(Z3Max,OSmaller)), Equals(someC,zero))
          }
          else if (ii == 0){
            val OGreater: Expr= getVar(("o#_"+(ii+1)+"_"+serialNumber))
            outputCnstrs += Implies(GreaterEquals(Z3Min,OGreater), Equals(someC,zero))
          }
          else if( ii == numOs){
            val OSmaller: Expr = getVar(("o#_"+ii+"_"+serialNumber))
            outputCnstrs += Implies(LessEquals(Z3Max,OSmaller), Equals(someC,zero))
          }
            
          //add this to the Map of c-s
          val tmp = intToCs.find(a=> a._1== ii)
          tmp match{
            case Some(x) => {
              intToCs -= x._1
              intToCs += (ii->(x._2 +someC ))
            }
            case None => {intToCs += (ii->Set(someC) )}
          }
        }
        (outputSet,And(outputCnstrs.toSeq))
      }
      
      //returns a Expr, which ensures that all input variables are zero
      def allCIsZero(inputVars: Set[Expr]) : Expr = {
        var toConj : Set[Expr] = Set.empty
        for(ii<-inputVars){
          toConj += Equals(ii, zero)
        }
        And(toConj.toSeq)
      }
      
      //summa c <= max-min-1
      def generateCnstrsForIntervals(){
        intToCs.foreach(a=>{
          if (a._1 != 0 && a._1 != intToCs.size-1){
            val MaxO = getVar(("o#_"+(a._1+1)+"_"+serialNumber))
            val MinO = getVar(("o#_"+a._1+"_"+serialNumber))
            toAndo += LessEquals(makeAddZ3AST(a._2),Minus(Minus(MaxO,MinO),one))
          }
        })
      
      }
      
      //returns an integer variable, which  = 0, if min/max = someB
      //sec. return value returns an AST which ensure, that the m<=E-s<=M, if the set is not empty
      def getIfEqualWithSomeB(setEs: Set[String], mM: Expr , mMstr: String) : (Expr, Expr) = {
        var toOr : Set[Expr] = Set.empty
        var toAnd: Set[Expr] = Set.empty
        for(e<-setEs){
          toOr += Equals(getVar(e), mM)
          //if mM= E => BE for that region is 1
          //"B#E#"+compNum + "_" + ii
          val B: Expr = getVar( "B#"+e + mMstr.tail)
          val bIs1: Expr = Equals(B,BooleanLiteral(true))
          //m<=E-s<=M
          if (mMstr.startsWith("m"))
            toAnd += Implies(Equals(B,BooleanLiteral(true)),LessEquals(mM,getVar(e)))
          else //it startsWith "M"
            toAnd += Implies(Equals(B,BooleanLiteral(true)),GreaterEquals(mM,getVar(e)))
          toAndo += Implies(Equals(getVar(e),mM),bIs1)
        }
        val newInt :Expr = getVar("i"+mM)
        //println("szerintem ez: " + newInt)
        toAndo += Implies(Or(toOr.toSeq),Equals(newInt,zero))
        toAndo += Implies(Not(Or(toOr.toSeq)),Equals(newInt,one))
        (newInt,And(toAnd.toSeq))
      }
      
      //---------------
      //Starts executing here
      //The satisfiability of all min-max cluster can be handeled separately, 
      //as there is no two min-max cluster in the same component of the hypergraph
      for(clust<-mClustToM){
        //set serialNumber to the index of the corresponding minMaxCluster
        globalMinMaxIndicies.foreach(minMaxIndex =>{ 
          if ((clust._1).subsetOf(globalClusts(minMaxIndex)))
            serialNumber = minMaxIndex
        })
        val minSet: Set[String] = clust._2._1
        val maxSet: Set[String] = clust._2._2
        val numMinMax: Int = (minSet | maxSet).size
        var setEs : Set[String] = Set.empty
        val tmpfound = componentESetMap.find(a=>{(clust._1).subsetOf(a._1)})
        tmpfound match{
          case Some(x) =>{
            setEs = x._2
          }
          case None => () //there is no defined ES for that set
        }
        //number of Os generated for this cluster
        val numOs : Int = numMinMax + setEs.size
        serialNumberToNumOsMap += (serialNumber -> numOs)
        
        setOs = Set.empty
        intToCs = Map.empty

        //the min-max values of non-emty regions are not allowed to be equal
        for(mM1<-minSet | maxSet){
          for(mM2<-minSet | maxSet if (mM1 != mM2)){
            if (mM1.tail != mM2.tail){
              val var1 : Expr = getVar(mM1)
              val var2 : Expr = getVar(mM2)
              val card1 : Expr = getVar("k"+mM1.tail)
              val card2 : Expr = getVar("k"+mM2.tail)
              toAndo += Implies(And(GreaterThan(card1,zero),GreaterThan(card2,zero)),Not(Equals(var1,var2)))
            }
          } 
        }
        generateOs(numOs, setEs)
        var usedMax: Set[String] = Set.empty
        for(min<-minSet){
          val Z3Card = getVar("k"+min.tail)
          //z3.assertCnstr(z3.mkGE(Z3Card, zero))
          val Z3Min = getVar(min)
          val max = maxSet.find(a=>(a.tail == min.tail))
          max match {
            //if both min and max are defined for a Venn region
            case Some(x) =>{
              usedMax += x
              val Z3Max = getVar(x)
              //every k>=0
              //println(z3.mkGE(Z3Card, zero))
              toAndo += GreaterEquals(Z3Card, zero)
              var setOfBs : Set[String] = Set.empty
              val foundAnyB = regionToBMap.find(tmp => tmp._1 == mToRegion(min))
              foundAnyB match{ 
                case Some(tmpfound) => setOfBs = tmpfound._2
                case None => ()
              }        
              //the set of C-s
              val cSet: (Set[Expr], Expr) = generateCs(min.tail, numOs, Z3Min, Z3Max)   
              //if k=0 m= inf, M=-inf, all c-s are zero 
              val Z3ifkIs0: Expr = And(And(Equals(Z3Min,inf), Equals(Z3Max,mInf)), allCIsZero(cSet._1))
              //if k= 1 -inf<min=max<inf, all c-s are zero, m=M=o_?
              val tASet: Set[Expr] = Set(GreaterThan(inf,Z3Max), Equals(Z3Max,Z3Min), GreaterThan(Z3Min,mInf), allCIsZero(cSet._1))
              var Z3ifkIs1: Expr = And(And(tASet.toSeq), mIsSomeO(Z3Min))
              //else -inf<min<max<inf, some c-s are zero, and k = 2 + Sum(c-s), m,M=o_?
              val tBSet: Set[Expr] = Set(GreaterThan(inf,Z3Max), GreaterThan(Z3Max,Z3Min), GreaterThan(Z3Min,mInf),cSet._2, Equals(Z3Card,Plus(makeAddZ3AST(cSet._1),two)) )  
              var Z3else : Expr = And(And(And(tBSet.toSeq) , mIsSomeO(Z3Min)), mIsSomeO(Z3Max))
              
              if (setEs != Set.empty){
                val z3SetOfBs: Set[Expr] = setOfBs.map(b=>getVar("i"+b))
                val isMinSomeE: (Expr, Expr) = getIfEqualWithSomeB(setEs, Z3Min, min)
                val isMaxSomeE: (Expr, Expr) = getIfEqualWithSomeB(setEs, Z3Max, x) //x=max, but max is optional 
                var andThisSet : Set[Expr] = Set(GreaterThan(inf,Z3Max), GreaterThan(Z3Max,Z3Min), GreaterThan(Z3Min,mInf))
                andThisSet ++= Set(cSet._2 ,isMinSomeE._2,isMaxSomeE._2)
                val tmpSum = Plus(Plus(makeAddZ3AST(cSet._1), isMinSomeE._1),isMaxSomeE._1)
                andThisSet += Equals(Z3Card,Plus(tmpSum, makeAddZ3AST(z3SetOfBs)))
                Z3else = And(And(And(andThisSet.toSeq), mIsSomeO(Z3Min)), mIsSomeO(Z3Max))
                Z3ifkIs1 = And(And(Z3ifkIs1,isMinSomeE._2),isMaxSomeE._2)
              }   
              //println(z3.mkITE(Equals(Z3Card,zero),Z3ifkIs0 ,z3.mkITE(Equals(Z3Card,one),Z3ifkIs1, Z3else)))
              toAndo += Implies(Equals(Z3Card,zero),Z3ifkIs0)
              toAndo += Implies(Equals(Z3Card,one),Z3ifkIs1)
              toAndo += Implies(GreaterEquals(Z3Card,two), Z3else)
            }
            //if there is no max defined for a Venn region
            case None => {
              toAndo += GreaterEquals(Z3Card, zero)
              var setOfBs : Set[String] = Set.empty
              val foundAnyB = regionToBMap.find(tmp => tmp._1 == mToRegion(min))
              foundAnyB match{ 
                case Some(tmpfound) => setOfBs = tmpfound._2
                case None => ()
              }
              val z3SetOfBs: Set[Expr] = setOfBs.map(b=>getVar("i"+b))
                
              var Z3ifNot0: Expr = GreaterThan(Z3Card,zero) 
              if (setEs != Set.empty) {
                val isMinSomeE = getIfEqualWithSomeB(setEs, Z3Min, min)
                val mytAnd = And(Z3ifNot0, isMinSomeE._2)
                Z3ifNot0 = And(mytAnd, GreaterEquals(Z3Card,Plus(isMinSomeE._1, makeAddZ3AST(z3SetOfBs))))
              }
              //if k= 0 => min = Inf, else: (m=o1 v m= o2...) && k>0 
              //in the second case (m=o1 v m= o2...) ensures, that -inf<m<inf
              //println(z3.mkITE(z3.mkEq(Z3Card, zero), z3.mkEq(Z3Min,inf), And(z3.mkGT(Z3Card,zero),mIsSomeO(Z3Min))))
              toAndo += Implies(Equals(Z3Card, zero), Equals(Z3Min,inf))
              toAndo += Implies(Not(Equals(Z3Card, zero)), And(Z3ifNot0,mIsSomeO(Z3Min))) 
            }
          }
        }
        //if only max is defined for a Venn region
        for(max<-maxSet if (!usedMax.contains(max))){
          val Z3Card = getVar(("k"+max.tail))
          val Z3Max = getVar(max)
          //println(z3.mkGE(Z3Card, zero))
          toAndo += GreaterEquals(Z3Card, zero)
          //e<= M
          
          var setOfBs : Set[String] = Set.empty
          val foundAnyB = regionToBMap.find(tmp => tmp._1 == mToRegion(max))
          foundAnyB match{ 
            case Some(tmpfound) => setOfBs = tmpfound._2
            case None => ()
          }
          val z3SetOfBs: Set[Expr] = setOfBs.map(b=>{
            getVar("i"+b)              
          })
          var Z3ifNot0: Expr = GreaterThan(Z3Card,zero)
          if (setEs != Set.empty){
            val isMaxSomeE = getIfEqualWithSomeB(setEs, Z3Max, max)
            Z3ifNot0 = And(And(Z3ifNot0,isMaxSomeE._2), GreaterEquals(Z3Card,Plus(isMaxSomeE._1, makeAddZ3AST(z3SetOfBs))))
          }      
            
          //if k= 0 => min = Inf, else: (m=o1 v m= o2...) && k>0 
          //in the second case (m=o1 v m= o2...) ensures, that -inf<m<inf
          //println(z3.mkITE(z3.mkEq(Z3Card, zero), z3.mkEq(Z3Max,mInf), And(z3.mkGT(Z3Card,zero),mIsSomeO(Z3Max))))
          toAndo += Implies(Equals(Z3Card, zero), Equals(Z3Max,mInf))
          toAndo += Implies(Not(Equals(Z3Card, zero)), And(Z3ifNot0,mIsSomeO(Z3Max)))
        }
        generateCnstrsForIntervals()
          
        serialNumber +=1
         
      }
      And(toAndo.toSeq)
    }
      
    
    
    
    //end of generateSMTforMinMax
    
    var compNum: Int = 0
    componentESetMap = Map.empty
    var cst: Set[Expr] = Set.empty
    //println("keyset: " + componentToXMap.keySet)
    for (compInG<-componentToXMap.keySet){
      //there is at least one sng in that component
      compNum +=1
      //IF WE NEED COMPNUMMAP
      //compNumMap += (compInG->compNum)
      //solveCompInG
      val eNums = componentToXMap(compInG).size
      //solveCompInG
      val c1st : Expr = get1st(compNum, compInG, eNums) //orderES
      val c2nd : Expr = get2nd(compNum, compInG, eNums) //mapEqualities
      //if nothing to be returned, then c3rd = IntLiteral(0)
      val c3rd : Expr = get3rd(compNum, compInG, eNums)  //ensureConsistency
      val c4th : Expr = get4th(compNum, compInG, eNums) //noMultipleSngs
      val c5th : Expr = get5th(compNum, compInG, eNums) //elementIsIn
      val c6th : Expr = get6th(compNum, compInG, eNums) //cardMinSngs
      val c7th : Expr = get7th(compNum, compInG, eNums) //contOnlyThose
      //if isMinMax false //we are ready:-)

      cst += c1st 
      cst += c2nd
      cst += c3rd
      cst += c4th
      cst += c5th
      cst += c6th
      cst += c7th
      
/*      println("orderEs: " + c1st)
      println("mapEqualities: " + c2nd)
      println("ensureConsistency: " + c3rd)
      println("noMultipleSngs: " + c4th)
      println("elementIsIn: " + c5th)
      println("cardMinSngs: " + c6th)
      println("contOnlyThose: " + c7th)
      println("intvals: " + intvals)*/
      
    }

    if (isMinMax == true) { 
      val intvals = generateSMTforMinMax()
      cst += intvals
    }
  

    And(cst.toSeq)
  }
  
  //-------------------------------------------------------------------
  //build sets as counterexample 
  def getCounterExample(counterexample : Map[Identifier,Expr]) {
    //build a map for the needed sets
    var solu : Map[Expr, Set[Int]] = Map.empty
    var usedElems : Set[Int] = Set.empty
    var readySets : Set[Expr] = Set.empty
    var readyClusterIndices: Set[Int] = Set.empty
    var globalSngSet : Set[Int] = Set.empty
    
    
    //insert singletons into the map
    def InsertSNGs() {
      //     var regionToBMap: Map[(Set[Expr],Set[Expr]), Set[String]] = Map.empty
      for (regToB <- regionToBMap) {
        for(b<- regToB._2){
          if (getValueBoolean(b) == true){
            //add this element to the containing sets
            regToB._1._1.foreach(set => {
              var eName : String = (b.tail).tail
              while ( ! eName.endsWith("#")){
                eName = eName.dropRight(1)
              }
              eName = eName.dropRight(1)
              while ( ! eName.endsWith("#")){
                eName = eName.dropRight(1)
              }
              eName = eName.dropRight(1)
              //println("addElement " + set + "   " + eName)
              val element : Int = getValueInt(eName)
              globalSngSet += element
              addElement(set, element)
            })
          }
          else{
            var eName : String = (b.tail).tail
            while ( ! eName.endsWith("#")){
              eName = eName.dropRight(1)
            }
            eName = eName.dropRight(1)
            while ( ! eName.endsWith("#")){
              eName = eName.dropRight(1)
            }
            eName = eName.dropRight(1)
            val element : Int = getValueInt(eName)
            //get the values of all sngs....
            globalSngSet += element
          }
        }
      }
    }
    
    //fill out the sets of min-max nodes
    def fillMinMaxNodes(){
      globalMinMaxIndicies.foreach(minMaxIndex =>{ 
        usedElems = Set.empty //initialize usedElems for this cluster
        //for all regions in this cluster
        //set containing, and set not containing
        var allRegions : Set[(Set[Expr],Set[Expr])]=  getAllComb(globalClusts(minMaxIndex))
        //for each region
        for(reg<-allRegions){
          //collect minMax values if there is any
          val filtered = mToRegion.filter(a => a._2 == reg)
          val mM : Set[String] = filtered.keySet
          if (!stringToExpr.contains(getName("k#", reg._1, reg._2, minMaxIndex))){
            if(mM != Set.empty)
              sys.error("A cardinality constraint should be defined for the min-max values!")
          }
          else{
          val card: Int = getValueInt(getName("k#", reg._1, reg._2, minMaxIndex))
          //if one minMax is defined
          if (mM.size == 1 && card > 0){
            mM.foreach(mMm => {
              (reg._1).foreach(a =>{ 
                addElement(a, getValueInt(mMm))
              })
              //cardinality of this region
              //println("this is the card of:" + card + " this " + reg)
              //println("this is the min-max index: " + minMaxIndex)
              //println("com elements " + getCommonCurrentElements(reg._1, reg._2))
              if (mMm.startsWith("m")){ //this is min value
                while( getCommonCurrentElements(reg._1, reg._2).size != card){
                  //println(getCommonCurrentElements(reg._1, reg._2))
                  //println("this is the card of:" + card + " this " + reg)
                  val freshE : Int = getGreatFreshElem(getValueInt("o#_" + serialNumberToNumOsMap(minMaxIndex) +"_" + minMaxIndex))
                  (reg._1).foreach(set => addElement(set, freshE))
                }
              }
              else{ //this is max value
                while( getCommonCurrentElements(reg._1, reg._2).size != card){
                  val freshE : Int = getSmallFreshElem(getValueInt("o#_1_" + minMaxIndex))
                  (reg._1).foreach(set => addElement(set, freshE))
                }
              }
            })
            
            // no c-s are defined
          }
          
          
          //if both min and max is defined
          else if (mM.size == 2 && card > 0){
            mM.foreach(mMm => {
              (reg._1).foreach(a =>{ 
              addElement(a, getValueInt(mMm))
              })
            })
            //it has c values
            for (ij<- 0 to serialNumberToNumOsMap(minMaxIndex)){
              val cValue : Int = getValueInt(getName("c#", reg._1, reg._2, minMaxIndex)+ "_" + ij + "_" + minMaxIndex)
              if (cValue != 0) 
                for (jji <- 1 to cValue ){
                  val lowerBound : String = "o#_" + ij +"_" + minMaxIndex
                  val upperBound : String = "o#_" + (ij+1) +"_" + minMaxIndex
                  val freshE : Int = getFreshElem(getValueInt(lowerBound), getValueInt(upperBound))
                  (reg._1).foreach(set => addElement(set, freshE))
                }
            }
          }
          
          
          //if neither min nor max is defined
          else if (mM.size == 0 && card > 0){
            //get the corresponding k value
            while( getCommonCurrentElements(reg._1, reg._2).size != card){
              val freshE : Int = getSmallFreshElem(getValueInt("o#_1_" + minMaxIndex))
              
              (reg._1).foreach(set => {
                addElement(set, freshE)})
              
            }
          }
          else if (mM.size > 2)
            sys.error("For this region the number of defined min-max-es is more than 2.")         
        }}
        readySets = readySets ++ globalClusts(minMaxIndex)
      })
      readyClusterIndices = globalMinMaxIndicies
    }
    
    //fill out the whole hyperGraph
    def fillHyperGraph(){
      G.initializeTraversion()
      //first fill out nodes, which are in contained some hyperEdge
      while(G.hyperEdgesLeft != Set.empty){
        val myEdge = G.getNextHyperEdge(readySets)
        //start with the hyperEdge's direct nodes
        fillOutCluster(myEdge._1)
        //continue with the nodes contained in the hyperEdge
        (myEdge._2).foreach(a=> fillOutCluster(a))
      }
      //fill out nodes, which are not contained in any hyperEdge
      var notReadySets : Set[Int] = Set.empty
      for(iijj <- 0 to globalClusts.length-1){
        notReadySets += iijj
      }
      notReadySets = notReadySets -- readyClusterIndices
      for(iijj<- notReadySets){
        fillOutCluster(globalClusts(iijj))
      }
    }
    
    def fillOutCluster(cls: Set[Expr]){
      //usedElems till now in this cluster
      usedElems = Set.empty
      cls.foreach(a=> usedElems ++= getCommonCurrentElements(Set(a), Set.empty))      
      val clustIndex : Int = findCluster(cls)
      readyClusterIndices += clustIndex
      val combReadies : Set[(Set[Expr],Set[Expr])] = getAllComb(cls & readySets)
      val combNonReadies : Set[(Set[Expr],Set[Expr])] = getAllComb(cls -- readySets)
      //var coReadies : (Set[Expr],Set[Expr]) = Pair(Set.empty, Set.empty)
      for (coReadies <- combReadies){
        var regionElements : Set[Int] = getCommonCurrentElements(coReadies._1, coReadies._2)
        for(coNonReadies <- combNonReadies){
          //get the cardinality of this region
          val containing : Set[Expr] = coReadies._1 ++ coNonReadies._1
          val nonContaining : Set[Expr] = coReadies._2 ++ coNonReadies._2
          val card: Int = getValueInt(getName("k#", containing, nonContaining, clustIndex))
          //count the sngs in this region
          val sngSet : Set[Int] = getCommonCurrentElements(containing, nonContaining)
          if (card-sngSet.size >0)
          //println("containing: " +containing + " nonContaining " + nonContaining)
          for(j<-1 to (card-sngSet.size)){
            //println("j : " + j + " card-sngSet.size " + (card - sngSet.size))
            //println("regionElements: " + regionElements)
            //println("globalSngSet: " + globalSngSet)
            //println("sngSet: " + sngSet)
            val elem : Int = (regionElements -- globalSngSet).head
            regionElements -= elem
            (coNonReadies._1).foreach(b=> addElement(b, elem))
          }
          
        }
      }
      for(coNonReadies <- combNonReadies){
        //get the cardinality of this region
        val containing : Set[Expr] = coNonReadies._1
        val nonContaining : Set[Expr] = coNonReadies._2 ++ (cls & readySets)
        if (stringToExpr.contains(getName("k#", containing, nonContaining, clustIndex))){
        val card: Int = getValueInt(getName("k#", containing, nonContaining, clustIndex))
        //count the sngs in this region
        val sngSet : Set[Int] = getCommonCurrentElements(containing, nonContaining)
        if (card-sngSet.size >0)
        for(j<-0 to (card-sngSet.size)){
          val elem : Int = getGreatFreshElem(0)
          (coNonReadies._1).foreach(b=> addElement(b, elem))
        }
        }
          
      }
      readySets ++= cls
      
    }
    
    //auxiliary functions ---------------------------------------------------------
    def addElement(set: Expr, elem: Int) {
      val c = solu.find(a=> a._1 == set)
      c match {
        case Some(x) => {
          solu -= x._1
          val tmmp : Set[Int] = x._2
          solu += (x._1 -> (tmmp ++ Set(elem)))
        }
        case None => {
          solu += (set -> Set(elem) )
        }
      }
    }    
     
    
    
    def getValueInt(name: String) : Int  = {
      var id : Identifier = FreshIdentifier("Nothing", true).setType(SetType(Int32Type))
      getVar(name) match{
        case Variable(i) => id = i
        case _ => sys.error(name + " is not variable in getValueInt!")
      }
      counterexample(id) match{
        case IntLiteral(v) => v
      }
    }
    
    def getValueBoolean(name: String) : Boolean = {
      var id : Identifier = FreshIdentifier("Nothing", true).setType(SetType(Int32Type))
      getVar(name) match{
        case Variable(i) => id = i
        case _ => sys.error(name + " is not variable in getValueInt!")
      }
      counterexample(id) match{
        case BooleanLiteral(true) => true
        case BooleanLiteral(false) => false
      }
    }
    

    def getFreshElem(smaller : Int, greater: Int) :Int = {
      var found : Boolean = false
      var jj : Int = 0
      var ii : Int = smaller + 1
      while(!found && ii < greater){
        if (! usedElems.contains(ii)){
          jj = ii
          usedElems += jj
          found = true
        }
        ii = ii+1
      }
      if (!found) 
        sys.error("Not possible to find fresh value between " + smaller + " and " + greater + "in getFreshElem!")
      jj
    }
    
    def getSmallFreshElem(smaller : Int) :Int = {
      var found : Boolean = false
      var jj : Int = 0
      var ii : Int = getValueInt("mInf") -1
      while(!found){
        if (! usedElems.contains(ii)){
          jj = ii
          usedElems += jj
          found = true
        }
        ii = ii-1
      }
      jj
    }
    
    def getGreatFreshElem(great : Int) :Int = {
      var found : Boolean = false
      var jj : Int = 0
      var ii : Int = getValueInt("inf") +1
      while(!found){
        if (! usedElems.contains(ii)){
          jj = ii
          usedElems += jj
          found = true
        }
        ii = ii+1
      }
      jj
    }
    
    
    def getCommonCurrentElements(sets: Set[Expr], notContaining: Set[Expr]) : Set[Int] = {
      (sets ++ notContaining).foreach(tmpSet =>{
        if (! (solu.keySet.contains(tmpSet)))
          solu += (tmpSet -> Set.empty)
      })
      var elms : Set[Int] = solu(sets.head)
      sets.foreach(a => elms = elms & solu(a))
      notContaining.foreach(b => elms = elms -- solu(b))
      elms
    }
    
    def getAllComb(sets: Set[Expr]) : Set[(Set[Expr],Set[Expr])]= {
      var allRegions : Set[(Set[Expr],Set[Expr])] = Set(Pair(Set.empty,Set.empty)) 
      for (ii<-sets){
        for(reg<-allRegions if(!reg._1.contains(ii) && !reg._2.contains(ii))){
          allRegions -= reg
          allRegions += Pair(reg._1 + ii, reg._2)
          allRegions += Pair(reg._1, reg._2 + ii)
        }
      }
      for(allReg<-allRegions if(allReg._1 == Set.empty)){
        allRegions -= allReg
      }
      allRegions
    }
    
    //find the clusters, if not found-> return -1 -> it should never be the case
    def findCluster(cls1: Set[Expr]): Int = {
      var found: Boolean = false
      var jj: Int = -1
      for(ii<- 0 to globalClusts.length-1 if !found) {
        if(globalClusts(ii) == cls1){
          jj = ii
          found = true
        }
      }
      jj
    }    

    
    

    
    //starts executing here ----------------------------------
    //println("CounterExample: " + counterexample)
    
    InsertSNGs()
    fillMinMaxNodes()
    fillHyperGraph()
    
    println("The solution is: " + solu)
    
  
  }
  
  
}