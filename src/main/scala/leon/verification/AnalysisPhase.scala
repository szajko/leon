/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package verification

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import solvers._
import solvers.z3._

//what I added
import ProceedSetOperators._

import scala.collection.mutable.{Set => MutableSet}

object AnalysisPhase extends LeonPhase[Program,VerificationReport] {
  val name = "Analysis"
  val description = "Leon Verification"

  implicit val debugSection = DebugSectionVerification

  override val definedOptions : Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1,f2,..."),
    LeonValueOptionDef("timeout",   "--timeout=T",       "Timeout after T seconds when trying to prove a verification condition.")
  )

  def generateVerificationConditions(reporter: Reporter, program: Program, functionsToAnalyse: Set[String]): Map[FunDef, List[VerificationCondition]] = {
    val defaultTactic = new DefaultTactic(reporter)
    defaultTactic.setProgram(program)
    val inductionTactic = new InductionTactic(reporter)
    inductionTactic.setProgram(program)

    var allVCs = Map[FunDef, List[VerificationCondition]]()

    for(funDef <- program.definedFunctions.toList.sortWith((fd1, fd2) => fd1 < fd2) if (functionsToAnalyse.isEmpty || functionsToAnalyse.contains(funDef.id.name))) {

      val tactic: Tactic =
        if(funDef.annotations.contains("induct")) {
          inductionTactic
        } else {
          defaultTactic
        }

      if(funDef.body.isDefined) {
        val funVCs = tactic.generatePreconditions(funDef) ++
                     tactic.generatePatternMatchingExhaustivenessChecks(funDef) ++
                     tactic.generatePostconditions(funDef) ++
                     tactic.generateMiscCorrectnessConditions(funDef) ++
                     tactic.generateArrayAccessChecks(funDef)

        allVCs += funDef -> funVCs.toList
      }
    }

    val notFound = functionsToAnalyse -- allVCs.keys.map(_.id.name)
    notFound.foreach(fn => reporter.error("Did not find function \"" + fn + "\" though it was marked for analysis."))

    allVCs
  }

  def checkVerificationConditions(vctx: VerificationContext, vcs: Map[FunDef, List[VerificationCondition]]) : VerificationReport = {
    val reporter = vctx.reporter
    val solvers  = vctx.solvers

    val interruptManager = vctx.context.interruptManager

    for((funDef, vcs) <- vcs.toSeq.sortWith((a,b) => a._1 < b._1); vcInfo <- vcs if !interruptManager.isInterrupted()) {
      val funDef = vcInfo.funDef
      var vc = vcInfo.condition
      
      //handling the operators on sets
      //println(vc)
      
      
      
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
      
      //println(woletvc)
      
      //println("------------ez----------------------")
      
      
      //collect the expression on sets
      
      //val myPrinter : Expr=>Expr = simplePreTransform(e => { println(e); e })

      //val s = myPrinter(woletvc) // after this, s == someTree
      //println(s)
      
      //val someExpression : Expr = ...
      
      var setConstraints : Set[Expr]= Set.empty 
      
      def collectSetOperator(t: Expr)  = t  match {
        case SetEquals(l,r) => {
          println("this is what we are SEARCHING!!!!!!!!!!!!!!!!!!!!!!")
          println(t)
          println(l.getType)
          println(r.getType)
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
      
      //println(setConstraints)
      var setCnsrt: Expr = BooleanLiteral(true)
      if (! setConstraints.isEmpty){
        println(woletvc)
      
        println("------------collect set expr.----------------------")
	println(setConstraints)
	
      
      
      
	setCnsrt = proceedSets(setConstraints)
	println("---------")
	
//	println(setCnsrt)
      
	println("itt a vege")
      }
      
      vc = Implies(setCnsrt, vc)
      
      
      //I have all constraints on sets
      //let eliminate If then else operators and so on....
      //ERROR: it is missing right now
      
      //convert it to the formula, what I can process
      //Handling set operators !!! 
      
      //val setExprMatcher : PartialFunction[Expr,Expr] = { 
	//case e if e.getType == SetType(Int32Type) => e 
//	case e if e match {
//	  case SetMin(_) => e
//	  case _ =>
//	}
//      }

//      val allSetExpressions : List[Expr] = collect(setExprMatcher)(woletvc)
      
     // println(allSetExpressions)

      //println("------------create a tree myself----------------------")
      //Ez mukodik :-):-)
      //val aid = FreshIdentifier("envaltozom").setType(Int32Type)
      //val av = Variable(aid)

      //val laid = FreshIdentifier("en").setType(Int32Type)
      //val lav = Variable(aid)
      //val finExpr = LessThan(av, lav)
      
      //println(finExpr)
      
      //create a set
      
      //val intSetType : TypeTree = SetType(Int32Type)

      //val mySetName = FreshIdentifier("halmaz", true).setType(intSetType)   
      // the "true" means it will always print with unique id

      //val myset = FiniteSet(Seq(IntLiteral(0), IntLiteral(1)))
      //val av = Variable(mySetName)
      
      //println(myset)
      //constant set
      //FiniteSet(Seq(IntLiteral(0), IntLiteral(1)))
      
      //FiniteSet(Seq.empty).setType(Int32Type)

      
      //println(av)
      
      
      reporter.info("Now considering '" + vcInfo.kind + "' VC for " + funDef.id + "...")
      reporter.debug("Verification condition (" + vcInfo.kind + ") for ==== " + funDef.id + " ====")
      reporter.debug(simplifyLets(vc))

      // try all solvers until one returns a meaningful answer
      solvers.find(se => {
        reporter.debug("Trying with solver: " + se.name)
        val t1 = System.nanoTime
        val (satResult, counterexample) = SimpleSolverAPI(se).solveSAT(Not(vc))
        val solverResult = satResult.map(!_)

        val t2 = System.nanoTime
        val dt = ((t2 - t1) / 1000000) / 1000.0

        solverResult match {
          case _ if interruptManager.isInterrupted() =>
            reporter.info("=== CANCELLED ===")
            vcInfo.time = Some(dt)
            false

          case None =>
            vcInfo.time = Some(dt)
            false

          case Some(true) =>
            reporter.info("==== VALID ====")

            vcInfo.hasValue = true
            vcInfo.value = Some(true)
            vcInfo.solvedWith = Some(se)
            vcInfo.time = Some(dt)
            true

          case Some(false) =>
            reporter.error("Found counter-example : ")
            reporter.error(counterexample.toSeq.sortBy(_._1.name).map(p => p._1 + " -> " + p._2).mkString("\n"))
            reporter.error("==== INVALID ====")
            vcInfo.hasValue = true
            vcInfo.value = Some(false)
            vcInfo.solvedWith = Some(se)
            vcInfo.counterExample = Some(counterexample)
            vcInfo.time = Some(dt)
            true
        }
      }) match {
        case None => {
          vcInfo.hasValue = true
          reporter.warning("==== UNKNOWN ====")
        }
        case _ =>
      }
    }

    val report = new VerificationReport(vcs)
    report
  }

  def run(ctx: LeonContext)(program: Program) : VerificationReport = {
    var functionsToAnalyse   = Set[String]()
    var timeout: Option[Int] = None

    for(opt <- ctx.options) opt match {
      case LeonValueOption("functions", ListValue(fs)) =>
        functionsToAnalyse = Set() ++ fs

      case v @ LeonValueOption("timeout", _) =>
        timeout = v.asInt(ctx)

      case _ =>
    }

    val reporter = ctx.reporter

    val fairZ3 = new FairZ3SolverFactory(ctx, program)

    val baseSolvers : Seq[SolverFactory[Solver]] = fairZ3 :: Nil

    val solvers: Seq[SolverFactory[Solver]] = timeout match {
      case Some(t) =>
        baseSolvers.map(_.withTimeout(100L*t))

      case None =>
        baseSolvers
    }

    val vctx = VerificationContext(ctx, solvers, reporter)

    val report = if(solvers.size >= 1) {
      reporter.debug("Running verification condition generation...")
      val vcs = generateVerificationConditions(reporter, program, functionsToAnalyse)
      checkVerificationConditions(vctx, vcs)
    } else {
      reporter.warning("No solver specified. Cannot test verification conditions.")
      VerificationReport.emptyReport
    }

    solvers.foreach(_.free())

    report
  }
}
