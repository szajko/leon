/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers
package bapaminmax

import purescala.Trees._
import ProceedSetOperators.writeCnstrsForClusters

object HyperGraph{
class HyperGraph{

      type Node = Set[Expr]
      type Nodes = Set[Node]
      type CommonVars = Set[Expr]
      type Edge = (CommonVars, Nodes) //var this: Edge = (Set("MyName"), Set(Set("sdj")))
      type Edges = Set[Edge]
      //initialization
      var hyperNodes: Nodes = Set.empty
      var hyperEdges: Edges = Set.empty
      var foundCycle: Boolean = false
      var cycleEdges: Edges = Set.empty
      var components : Nodes = Set.empty
      var minMaxComponents: Nodes = Set.empty
      var clusters : Array[Set[Expr]] = Array.empty
      var minMaxIndecies: Set[Int] = Set.empty
      
      //----------------------------------------
      var hyperEdgesLeft : Edges = Set.empty
      def initializeTraversion() {
        hyperEdgesLeft = hyperEdges
      }
      
      def getNextHyperEdge(readyVars: Set[Expr]) : Edge = {
        var foundEdge: Edge = hyperEdgesLeft.head
        var found: Boolean = false
        for(myEdge<- hyperEdgesLeft){
          if ((readyVars & myEdge._1) != Set.empty) {
            found = true
            foundEdge = myEdge
          }
        }
        if (!found)
          foundEdge = hyperEdgesLeft.head
        hyperEdgesLeft = hyperEdgesLeft - foundEdge
        foundEdge
      }
      
      //------------------------------------
      
      def createHyperGraph(dependecies: Nodes) {
        //println("input is: " + dependecies)
	for(constraint<- dependecies){
	  //compare a new node with other nodes in the hypergraph and add necessary edges
	  for(node<-hyperNodes){
	    if ((constraint & node) != Set.empty){ 
	      hyperEdges += Pair((constraint & node) ,Set(node,constraint))
	      foundCycle = false
	      cycleEdges = Set.empty
	      //searching for possible cycle, only modifies cycleEdges and foundCycle
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
      def findCycle(sNode: Node, cNode: Node, visitedNodes: Nodes, usedEdges: Edges, lastEdge: Edge): Unit = { 
      //visitedNodes does not contain startNode
      //cNode -> current Node, sNode -> startNode
      //println("--findCycle:" + sNode + " cNode: " + cNode +"visited: " + visitedNodes + "used Edges" + usedEdges + "lastEdge:" + lastEdge)
      //println("input graph: Edges: " + hyperEdges + " size: " + hyperEdges.size)
      //uses a DFS search on nodes
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
      
      //minMaxComponents stores the minMaxCusters
      def createMinMaxClusters(mDep: Nodes) {
        val saveNodes: Nodes = hyperNodes
        //if there is no min-max constraints at all, SNG-s are not added
         if(mDep == Set.empty) getComponents() 
        else{
          getComponents()
          minMaxComponents = mDep
          //contract min-max components if they are not disjoint or has a common element in one component of the hypergraph
          for(c<-components){
            contractIfNec(c)
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
          getComponents()
          //store the original Nodes of the HyperGraph
          hyperNodes = saveNodes 
          //minMaxClusters are the min-max components
        }
      }
      
      //only callable if the hypergraph is ready
      def getCardClust(): Nodes = {
        val nodesFromEdges = for (edge<-hyperEdges)yield{
	  var (commonVars, nodes) = edge
	  commonVars
	}
	//union of nodes and the "name" (common variables) in the hypergraph
	hyperNodes | nodesFromEdges
     }

      def getClustsArrays(): (Array[Set[Expr]], Set[Int]) = {
        clusters = (minMaxComponents ++ getCardClust()).toArray
        for(ii<- 0 to clusters.length -1){
          //minMaxComponents contains the min-max nodes
          //chech if this node is in the set of min-max nodes
          if (minMaxComponents.contains(clusters(ii))) 
            minMaxIndecies += ii
        }
        (clusters, minMaxIndecies)
      }
      
      //st is the pr-String
      //if containedSets == Set.empty, write constraints for the whole graph
      def getEqualities(st: String, containedSets: Set[Expr]): Expr = {
        var toAndConstr : Set[Expr] = Set.empty
        //find out, for which set variables should we write constraints
        var toUseVars: Set[Expr] = Set.empty
        if (containedSets != Set.empty){
          val comp = components.filter(a => !(a & containedSets).isEmpty)
          comp.foreach(a=> toUseVars ++= a)
        }
        //write constraints for the whole graph
        else{
          components.foreach(a=> toUseVars ++= a)
        }
        
        for(edge<-hyperEdges){
          //if it is in the comonents, for wich constraints should be written
          if (!(toUseVars & edge._1).isEmpty){
            for(c<-edge._2){
              if (edge._1 != c){ 
                toAndConstr ++= writeCnstrsForClusters(st,edge._1,c)
                //println("")
              }
            }
          }
        }
        
       //if (st == "k#") upStat(toAndConstr.size)
       
        if (toAndConstr != Set.empty)
          And(toAndConstr.toSeq)
        else BooleanLiteral(true)
      }

}
}
