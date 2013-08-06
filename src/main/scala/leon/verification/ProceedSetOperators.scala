/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package verification

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

//what I wanted to add
//import 

import solvers.{Solver,TrivialSolver,TimeoutSolver}
import solvers.z3.FairZ3Solver

import scala.collection.mutable.{Set => MutableSet}

object ProceedSetOperators {

    var bridges : Map[Expr, Expr] = Map.empty
    var sideConstraints : Set[Expr] = Set.empty
    var isEmptySet: Boolean = false
    val myEmptySet = Variable(FreshIdentifier("EmptySet", true).setType(SetType(Int32Type)))
    
    //collect Dependencies
     var cDep: Set[Set[Expr]] = Set.empty
     var mDep: Set[Set[Expr]] = Set.empty

    def proceedSets(e: Set[Expr]) : Expr = {
      //initialization
      bridges = Map.empty
      sideConstraints   = Set.empty
      isEmptySet = false
      
      //lift all constant sets that are not variables
      //and eliminate the following operators:
      //seteq, subset, in, eleme
      println("elotte bridges")
      println(bridges)
      e.foreach(tp => eliminateOperators(tp))
      println("--bridges ---")
      println(bridges)
      println("-- sideConstraints -- ")
      println(sideConstraints)
      
      val  newE : Set[Expr] = e | sideConstraints
      
      
      //only card, min and max operators are remained on diff, intersec, union, compl of sets
      newE.foreach(tp => deMorganCollectDep(tp))
      
      //apply DeMorgan + meanwhile collect Dependencies
      
      //eliminate operators: eleme
      
    
       /*getSol = getSolution
       if(containsMinMax(formula)) { contMinMax = true; getSol = false}
       mClustToM = Map.empty
       mToRegion = Map.empty
      
       //"lifts" all sets that are not variables (formula, Set[BridgeSingleton...])
       //(modified formula without constant sets, set of singletons)
       val f0 : (AST[Boolean], Set[String], Set[AST[Boolean]]) = liftConstantSets(formula)
       //println("After liftConstantSets formula is\n" + f0._1 + "\nsingletions:" + f0._2)
       //eliminate some operations
       val f1: (AST[Boolean], Set[String]) = eliminateOperators(f0._1, f0._3) 
       //println("Operators are eliminated" + f1._1) 
       //set of additional singletons
       val singletonSet : Set[String] = f0._2 | f1._2
       //println("singletons: " + singletonSet)
       stat.singletonsVar = singletonSet.size
       //Apply De Morgan's law
       val f2: AST[Boolean] = applyDeMorgan(f1._1)
       //println("DeMorgan is used:" + f2)
      
       //FixMe :-> check wether everithing is used for bridges as well

       //creating the clusters 
       //(cardinality dependencies, min-max dependencies)
       val dependencies: (Set[Set[String]], Set[Set[String]]) = collectDependencies(f2) 
       //println("Cardinality dependencies: " + dependencies)
       val clusters: (Set[Set[String]], Set[Set[String]]) = createClusters(dependencies._1, singletonSet, dependencies._2)
       println("SingletonSet: " + singletonSet)
       val finalCardClustersSet: Set[Set[String]] = filterNecessaryDep(clusters._1)
       val finalMinMaxClustersSet: Set[Set[String]]= clusters._2  //makeMinMaxClusters(finalCardClustersSet: Set[Set[String]], dependencies._2)
       //------------------------
       val finalCardClusters: Array[Set[String]]= (finalCardClustersSet).toArray
       println("Cardinality and Briging Clusters: " + finalCardClusters.toSet)
       val finalMinMaxClusters: Array[Set[String]] =   finalMinMaxClustersSet.toArray
       println("Final min-max clusters: " + finalMinMaxClusters.toSet)
       stat.cardClust = finalCardClusters.length
       stat.minmaxClust = finalMinMaxClusters.length
      
       //writing constraints
       val additionalConstr: AST[Boolean] = getAdditionalConstraints(finalCardClusters) 
       //maybe it should be accelerated... optimize...
       //println("additional constraints:\n" + additionalConstr )
       val f3: AST[Boolean] =  substituteInTree(f2, finalCardClusters, finalMinMaxClusters)
       //println("Substitute in tree:\n" + f3)
       val additionalMinMaxConstr: AST[Boolean] = addCardConstrForMinMax(finalMinMaxClusters, finalCardClusters)
       //println("Additional min-max constraints: " + additionalMinMaxConstr)
       val briging: (Int, Set[String]) = findBridgeCluster(singletonSet, finalCardClusters)
       val finalFormula : AST[Boolean] = Conj(Conj(f3,additionalConstr),additionalMinMaxConstr)
       //println("Final formula: " + finalFormula)
       //println(mToRegion)
      

       val Z3Result: (Map[String,Int], Boolean) = solveFormula(finalFormula, briging._1, briging._2, getSolution, method)
       
       updateStat(finalMinMaxClustersSet ++ finalCardClustersSet)
      
       stat.solvable = false
       val finalResult = if(Z3Result._2 == true) {
         stat.solvable = true
         if (getSol == true){
           var solution = new GetSolut(finalCardClusters, Z3Result._1, f3 , formula)
           val env: Environment = solution.getMapping()
           Sat(env, stat)
         }
         else Sat(Environment(Map.empty, Map.empty), stat)
       } else {
         Unsat(stat)
       }
       val time1 = System.currentTimeMillis
      
       stat.solvingTime = time1 - time0
      
       stat.printStat()
       finalResult*/
       IntLiteral(0)
     }
     
    def addBridge(toAdd: Expr) : Expr = {
      val c = bridges.find(a=> (a._1== toAdd))
      c match {
	case Some(x) => {
	  x._2
	}
	case None => {
	  val setName : String = FreshName("SNG")
	  val mySetName = FreshIdentifier(setName, true).setType(SetType(Int32Type))
	  val v = Variable(mySetName)
	  bridges += (toAdd -> v)
	  v	  
	}
      }
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
     
    def eliminateOperators(formula : Expr) : Unit = {
    
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
	  val nameSng : Expr = addBridge(l)
	  //creater Side Constraint
	  sideConstraints += Iff(ElementOfSet(l,r), SubsetOf(nameSng , r))
	  rec(SubsetOf(nameSng , r))
	}
	case FiniteSet(s) => { // s : Seq[Expr] (Expr = int type)
	  if (s.isEmpty) {
	    isEmptySet = true
	    myEmptySet
	  }
	  else {
	    var elements : Set[Expr] = Set.empty  
	    s.foreach(tmp =>{ 
	      val nameSng : Expr = addBridge(tmp)
	      elements += nameSng} )
	      
	    //creater Side Constraint
	    val first: Expr = elements.head
	    var tree : Expr = first
	    for(ii<-elements if (ii!=first)){
	      tree  = SetUnion(tree, ii)
	    }          
	    rec(SetEquals(t , tree))
	  }
	}
	case _ =>{ }
      }
      
     val afterRec : Expr=>Expr = simplePreTransform(e => { rec(e);  e})
     val s = afterRec(formula)
     if(isEmptySet == true){
	sideConstraints += Equals(SetCardinality(myEmptySet),IntLiteral(0))
     }
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
       case _ => t
     }
     //three relevant operators: card, min, max
     def findOps(et: Expr): Unit = et match {
       case SetCardinality(l) =>{
         val tmp = rec(l)
         sideConstraints += Equals(SetCardinality(l), SetCardinality(tmp))
         cDep += addSets(l, Set.empty)
       }
       case SetMin(l) => {
         val tmp = rec(l)
         sideConstraints += Equals(SetMin(l), SetMin(tmp))
         mDep += addSets(l, Set.empty)
       }
       case SetMax(l) => {
         val tmp = rec(l)
         sideConstraints += Equals(SetMax(l), SetMax(tmp))
         mDep += addSets(l, Set.empty)
       }
       case _ =>{ }
     }
     // computes a set of sets of related sets (ahem).
     // E.g. if you have | A U B | != | C \ B |, the result should be:
     // { { A, B }, { B, C } }
     //the input is a region in a card / min-max constraint
     def addSets(ut: Expr, cluster: Set[Expr]) : Set[Expr] = ut match {
       case SetUnion(l, r) => addSets(l, Set.empty) | addSets(r, cluster)
       case SetIntersection(l, r) => addSets(l, Set.empty) | addSets(r, cluster)
       case SetComplement(l) => addSets(l, cluster)
       //it might only be a set
       case _ => cluster + ut
     }
      
     val afterRec : Expr=>Expr = simplePreTransform(e => { findOps(e);  e})
     val s = afterRec(formula)
 
     //end of deMorganCollectDep
  }
  
  
  //select dependencies, which contain all dependencies
  def filterNecessaryDep(dep: Set[Set[Expr]]) : Set[Set[Expr]] = {
      dep.filter(s1 => !dep.exists(s2 => (s1!=s2 && s1.subsetOf(s2))))
  }
  
  //(cardinality dependencies + singleton set, min-max dependencies)
  def createClusters(cardDep: Set[Set[Expr]], sngs: Set[Expr],  minMaxDep: Set[Set[Expr]] ) : (Set[Set[Expr]], Set[Set[Expr]])  ={
    class Hyper{
      type Node = Set[Expr]
      type Nodes = Set[Node]
      type CommonVars = Set[Expr]
      type Edge = (CommonVars, Nodes) //var this: Edge = (Set("MyName"), Set(Set("sdj")))
      type Edges = Set[Edge]

      var hyperNodes: Nodes = Set.empty
      var hyperEdges: Edges = Set.empty
      var foundCycle: Boolean = false
      var cycleEdges: Edges = Set.empty
      var components : Set[Set[Expr]] = Set.empty
      var minMaxComponents: Set[Set[Expr]] = Set.empty
      
      def createHyperGraph(dependecies: Set[Node]) {
	for(constraint<- dependecies){
	  //compare a new node with other nodes in the hypergraph and add necessary edges
	  for(node<-hyperNodes){
	    if ((constraint & node) != Set.empty){ 
	      hyperEdges += Pair((constraint & node) ,Set(node,constraint))
	      foundCycle = false
	      cycleEdges = Set.empty
	      //searching for possible cycle
	      findCycle(constraint, constraint, Set.empty, Set.empty, (Set.empty, Set.empty))
	      //contract the proper hyperedges if a cycle is found
	      hyperEdges = hyperEdges -- cycleEdges
	      var newCommonVars: CommonVars = Set.empty
	      var newNodes: Nodes = Set.empty
	      for(cEdge<-cycleEdges){
	        val (cCommonVars, cNodes) = cEdge
	        newCommonVars = newCommonVars | cCommonVars
	        newNodes = newNodes | cNodes
	      }
	      hyperEdges += Pair(newCommonVars, newNodes)
	    }
	    //println("***nodes: " + node + "size: " + hyperNodes.size + " \n\nEdges: " + hyperEdges + " size: " + hyperEdges.size)
	  }
	  //add this node to the set of hypernodes too
	  hyperNodes += constraint
	  //println("--------------Nodes: " + hyperNodes.size + " \n\nEdges: " + hyperEdges + " size: " + hyperEdges.size)
	}
	//the hypergraph is ready if there is no min-max constraints
	//println("Cardinality hypergrah is created: nodes: " + hyperNodes + "size: " + hyperNodes.size + " Edges: " + hyperEdges + " size: " + hyperEdges.size)   
	//for(edge<-hyperEdges)yield{
	//  var (commonVars, nodes) = edge
	//  commonVars
	//})

      }
      
      //it does not find cycles, where you have to go back in the same edge immediately 
      //for instance, if you have constraint over (s1, s2, s3) and (s1, s2, s4) 
      def findCycle(sNode: Node, cNode: Node, visitedNodes: Nodes, usedEdges: Edges, lastEdge: Edge): Unit = { //visitedNodes does not contain startNode
      //println("--findCycle:" + sNode + " cNode: " + cNode +"visited: " + visitedNodes + "used Edges" + usedEdges + "lastEdge:" + lastEdge)
      //println("input graph: Edges: " + hyperEdges + " size: " + hyperEdges.size)
      //Fixme: optimise this function
        val nextEdges: Edges = hyperEdges.filter(edge =>{var (commonVars, nodes) = edge
          (nodes.contains(cNode) && edge != lastEdge)})
        if (foundCycle == false) {
	  for(edge<-nextEdges){
	    var (commonVars, nodes) = edge
	    for (nextNode<-nodes if (!visitedNodes.contains(nextNode)|| nextNode == sNode)){
	      if (foundCycle == false){
		if(nextNode == sNode && usedEdges != Set.empty){ //cycle found
		  foundCycle = true
		  cycleEdges = usedEdges + edge
		  return
		}
		else{//if cycle is still not found, continue DFS
		  if(nextNode != sNode){
		    findCycle(sNode, nextNode, (visitedNodes+nextNode), (usedEdges + edge), edge)
		  }
		}
	      }
	    }
	  }
        
        }
	//visitedNodes += cNode
      }
      
      def getComponents()  {
        components = hyperNodes
        contractIfNecessary()
      }
      
      //if there is a two components to contract, it stops, uptades and starts itself recursively
      def contractIfNecessary() {
        var found : Boolean = false
        for(c1<-components if (!found)){
          for(c2<-components if (c1 != c2 && (!found))){
            if (!((c1 & c2).isEmpty)){
              found = true
              components -= c1
              components -= c2
              components += (c1++c2)
              contractIfNecessary()
            }
          }
        }
      }
      
      def contractIfNec(comp: Set[Expr]){
        var found : Boolean = false
        for(c1<-minMaxComponents if (!found)){
          for(c2<-minMaxComponents if (c1 != c2 && (!found))){
            if (((!(c1 & comp).isEmpty) && (!(c2 & comp).isEmpty)) || !(c1 & c2).isEmpty){
              found = true
              minMaxComponents -= c1
              minMaxComponents -= c2
              minMaxComponents += (c1++c2)
              contractIfNec(comp)
            }
          }
        }
      }
      
      def createMinMaxClusters(mDep: Set[Set[Expr]], sngs: Set[Expr]): Set[Set[Expr]] ={
        val saveNodes: Nodes = hyperNodes
        if( mDep == Set.empty) Set.empty
        else{
          getComponents()
          minMaxComponents = mDep
          //contract min-max components if they are not disjoint or has a common element in one component of the hypergraph
          for(c<-components){
            contractIfNec(c)
          }
          //find the component, which contains the singletons
          var sngsComponenet: Set[Expr] = Set.empty
          var found: Boolean = false
          for(c<-components if !(found)){
            if (!(c & sngs).isEmpty){
              sngsComponenet = c
            }
          }
          //add the singletons to the minMax component, which has any common elements with the component containing the singletons
          found = false
          for(c<-minMaxComponents if !(found)){
            if (!(c & sngsComponenet).isEmpty){
              minMaxComponents -= c
              minMaxComponents += (c++sngs)
            }
          }
          
          for(c<-minMaxComponents){
            //compare a new node with other nodes in the hypergraph and add necessary edges
            for(node<-hyperNodes){
              if ((c & node) != Set.empty){ 
	        hyperEdges += Pair((c & node) ,Set(node,c))
	      foundCycle = false
	      cycleEdges = Set.empty
	      //searching for possible cycle
	      findCycle(c, c, Set.empty, Set.empty, (Set.empty, Set.empty))
	      //contract the proper hyperedges if a cycle is found
	      hyperEdges = hyperEdges -- cycleEdges
	      var newCommonVars: CommonVars = Set.empty
	      var newNodes: Nodes = Set.empty
	      for(cEdge<-cycleEdges){
	        val (cCommonVars, cNodes) = cEdge
	        newCommonVars = newCommonVars | cCommonVars
	        newNodes = newNodes | cNodes
	      }
	      hyperEdges += Pair(newCommonVars, newNodes)
	    }
	    //println("***nodes: " + node + "size: " + hyperNodes.size + " \n\nEdges: " + hyperEdges + " size: " + hyperEdges.size)
	  }
	  //add this node to the set of hypernodes too
	  hyperNodes += c
	  //println("--------------Nodes: " + hyperNodes.size + " \n\nEdges: " + hyperEdges + " size: " + hyperEdges.size)
            
          }
          hyperNodes = saveNodes   
          minMaxComponents
        }
      }
      
      //only callable if the hypergraph is ready
      def getCardClust(): Nodes = {
        val nodesFromEdges = for (edge<-hyperEdges)yield{
	  var (commonVars, nodes) = edge
	  commonVars
	}
	//union of nodes and tha "name" (common variables) in the hypergraph
	val clusters: Nodes = hyperNodes | nodesFromEdges
	clusters
      }
    }
    //starts executing here
    val necDep = filterNecessaryDep(cardDep + sngs)
    val G = new Hyper
    G.createHyperGraph(necDep)
    //createMinMaxClusters should be called first, as it can modify the cardClusters
    val minMaxClusters: Set[Set[Expr]] = G.createMinMaxClusters(minMaxDep, sngs)
    val cardClusters: Set[Set[Expr]]= G.getCardClust()
    (cardClusters, minMaxClusters)
    
    //end of createClusters
  }

  
 

}