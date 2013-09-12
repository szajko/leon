/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package verification

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._


//what I added
import ProceedSetOperators._

import solvers.{Solver,TrivialSolver,TimeoutSolver}
import solvers.z3.FairZ3Solver

import scala.collection.mutable.{Set => MutableSet}

object AnalysisPhase extends LeonPhase[Program,VerificationReport] {
  val name = "Analysis"
  val description = "Leon Verification"

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
    
    val w = new CSVWriter("testfile")
    val statHead : String = "name;isValid;procTime;solvTime;getSolTime;"
    val statHead1 : String = "sngNum;setNum;finitSetNum;cardConstrNum;minMaxConstrNum;clusterNum;minMaxClustNum;"
    val statHead2 : String = "vennRegNum;componentNum;" 
    val statHead3 :String = "kNum;mMNum;ENum;ANum;BNum;cNum;oNum"
    w.writeLine(statHead + statHead1 + statHead2 + statHead3)

    for((funDef, vcs) <- vcs.toSeq.sortWith((a,b) => a._1 < b._1); vcInfo <- vcs if !vctx.shouldStop.get()) {
      val funDef = vcInfo.funDef
      //statistic vars
      val probName : String = vcInfo.funDef.id.toString + ";"
      var isValid : String = "VALID;"
      var processTime = System.currentTimeMillis
      var solvingTime = System.currentTimeMillis
      var getSolutTime = processTime - processTime
      var vc = vcInfo.condition
      
      //handling the operators on sets
      //println(vc)
      
      val time0 : Long = System.currentTimeMillis
      
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
      if (! setConstraints.isEmpty){
        //println(woletvc)
      
        println("----------------------The collected set expresssiona are:----------------------")
	println(setConstraints)
	setCnsrt = proceedSets(setConstraints)
	//println("All added constraints------------------------" + setCnsrt)
      }
      
      vc = Implies(setCnsrt, vc)
      
      val time1 = System.currentTimeMillis
      
      
      
      //let eliminate If then else operators and so on.... FIXME
      //ERROR: it is missing right now
      //println(av)
      
      
      reporter.info("Now considering '" + vcInfo.kind + "' VC for " + funDef.id + "...")
      reporter.info("Verification condition (" + vcInfo.kind + ") for ==== " + funDef.id + " ====")
      reporter.info(simplifyLets(vc))
      

      // try all solvers until one returns a meaningful answer
      var superseeded : Set[String] = Set.empty[String]
      solvers.find(se => {
        reporter.info("Trying with solver: " + se.name)
        if(superseeded(se.name) || superseeded(se.description)) {
          reporter.info("Solver was superseeded. Skipping.")
          false
        } else {
          superseeded = superseeded ++ Set(se.superseeds: _*)

          val t1 = System.nanoTime
          se.init()
          val (satResult, counterexample) = se.solveSAT(Not(vc))
          val solverResult = satResult.map(!_)

          val t2 = System.nanoTime
          val dt = ((t2 - t1) / 1000000) / 1000.0
          val time2 = System.currentTimeMillis
          processTime = time1 - time0
          solvingTime = time2 - time1
          println("The processing of the problem took " + processTime + " ms.")
          println("Solving the problem took " + solvingTime + " ms.")

          solverResult match {
            case _ if vctx.shouldStop.get() =>
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
              //the counter example is in the map counterexample
              //take this map and rewrite it into a map, that only constains variables of the initial problem
              //build sets for set variables...
              isValid = "INVALID;"
              val time3 = System.currentTimeMillis
              getCounterExample(counterexample)
              val time4 = System.currentTimeMillis
              getSolutTime = time4 - time3
              println("Creating a counterexample sets took " + getSolutTime + " ms.")
              reporter.error("==== INVALID ====")
              vcInfo.hasValue = true
              vcInfo.value = Some(false)
              vcInfo.solvedWith = Some(se)
              vcInfo.counterExample = Some(counterexample)
              vcInfo.time = Some(dt)
              true

          }
          
        }
      }) match {
        case None => {
          vcInfo.hasValue = true
          reporter.warning("No solver could prove or disprove the verification condition.")
        }
        case _ =>
      }
      val stat1 : String = probName + isValid + processTime + ";" + solvingTime + ";" + getSolutTime + ";"
      w.writeLine( stat1 + get1SCVLine() )
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

    val trivialSolver = new TrivialSolver(ctx)
    val fairZ3 = new FairZ3Solver(ctx)

    val solvers0 : Seq[Solver] = trivialSolver :: fairZ3 :: Nil
    val solvers: Seq[Solver] = timeout match {
      case Some(t) => solvers0.map(s => new TimeoutSolver(s, 1000L * t))
      case None => solvers0
    }

    solvers.foreach(_.setProgram(program))

    val vctx = VerificationContext(ctx, solvers, reporter)

    val report = if(solvers.size > 1) {
      reporter.info("Running verification condition generation...")
      val vcs = generateVerificationConditions(reporter, program, functionsToAnalyse)
      checkVerificationConditions(vctx, vcs)
    } else {
      reporter.warning("No solver specified. Cannot test verification conditions.")
      VerificationReport.emptyReport
    }

    report
  }
}
