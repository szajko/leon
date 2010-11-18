package purescala

import Common._
import Trees._
import TypeTrees._

object Evaluator {
// Expr should be some ground term. We have call-by-value semantics.
  type EvaluationContext = Map[Identifier,Expr]
  
  sealed abstract class EvaluationResult {
    val finalResult: Option[Expr]
  }
  case class OK(result: Expr) extends EvaluationResult {
    val finalResult = Some(result)
  }
  case class RuntimeError(msg: String) extends EvaluationResult {
    val finalResult = None
  }
  case class TypeError(expression: Expr, expected: TypeTree) extends EvaluationResult {
    lazy val msg = "When typing:\n" + expression + "\nexpected: " + expected + ", found: " + expression.getType
    val finalResult = None
  }
  case class InfiniteComputation() extends EvaluationResult {
    val finalResult = None
  }

  def eval(context: EvaluationContext, expression: Expr, maxSteps: Int=500000) : EvaluationResult = {
    case class RuntimeErrorEx(msg: String) extends Exception
    case class InfiniteComputationEx() extends Exception
    case class TypeErrorEx(typeError: TypeError) extends Exception

    var left: Int = maxSteps

    def rec(ctx: EvaluationContext, expr: Expr) : Expr = if(left <= 0) {
      throw InfiniteComputationEx()
    } else {
      // println("Step on : " + expr)
      // println(ctx)
      left -= 1
      expr match {
        case Variable(id) => {
          if(ctx.isDefinedAt(id)) {
            val res = ctx(id)
            if(!isGround(res)) {
              throw RuntimeErrorEx("Substitution for identifier " + id.name + " is not ground.")
            } else {
              res
            }
          } else {
            throw RuntimeErrorEx("No value for identifier " + id.name + " in context.")
          }
        }
        case Let(i,e,b) => {
          val first = rec(ctx, e)
          rec(ctx + ((i -> first)), b)
        }
        case Error(desc) => throw RuntimeErrorEx("Error reached in evaluation: " + desc)
        case IfExpr(cond, then, elze) => {
          val first = rec(ctx, cond)
          first match {
            case BooleanLiteral(true) => rec(ctx, then)
            case BooleanLiteral(false) => rec(ctx, elze)
            case _ => throw TypeErrorEx(TypeError(first, BooleanType))
          }
        }
        case FunctionInvocation(fd, args) => {
          val evArgs = args.map(a => rec(ctx, a))
          // build a context for the function...
          val frame = Map[Identifier,Expr]((fd.args.map(_.id) zip evArgs) : _*)
          
          if(fd.hasPrecondition) {
            rec(frame, matchToIfThenElse(fd.precondition.get)) match {
              case BooleanLiteral(true) => ;
              case BooleanLiteral(false) => throw RuntimeErrorEx("Precondition violation for " + fd.id.name + " reached in evaluation.")
              case other => throw TypeErrorEx(TypeError(other, BooleanType))
            }
          }

          if(!fd.hasBody) {
            throw RuntimeErrorEx("Evaluation of function with unknown implementation.")
          }
          val callResult = rec(frame, matchToIfThenElse(fd.body.get))

          if(fd.hasPostcondition) {
            val freshResID = FreshIdentifier("result").setType(fd.returnType)
            val postBody = replace(Map(ResultVariable() -> Variable(freshResID)), matchToIfThenElse(fd.postcondition.get))
            rec(frame + ((freshResID -> callResult)), postBody) match {
              case BooleanLiteral(true) => ;
              case BooleanLiteral(false) => throw RuntimeErrorEx("Postcondition violation for " + fd.id.name + " reached in evaluation.")
              case other => throw TypeErrorEx(TypeError(other, BooleanType))
            }
          }

          callResult
        }
        case And(args) if args.isEmpty => BooleanLiteral(true)
        case And(args) => {
          rec(ctx, args.head) match {
            case BooleanLiteral(false) => BooleanLiteral(false)
            case BooleanLiteral(true) => rec(ctx, And(args.tail))
            case other => throw TypeErrorEx(TypeError(other, BooleanType))
          }
        }
        case Or(args) if args.isEmpty => BooleanLiteral(false)
        case Or(args) => {
          rec(ctx, args.head) match {
            case BooleanLiteral(true) => BooleanLiteral(true)
            case BooleanLiteral(false) => rec(ctx, Or(args.tail))
            case other => throw TypeErrorEx(TypeError(other, BooleanType))
          }
        }
        case Not(arg) => rec(ctx, arg) match {
          case BooleanLiteral(v) => BooleanLiteral(!v)
          case other => throw TypeErrorEx(TypeError(other, BooleanType))
        }
        case Implies(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (BooleanLiteral(b1),BooleanLiteral(b2)) => BooleanLiteral(!b1 || b2)
          case (le,re) => throw TypeErrorEx(TypeError(le, BooleanType))
        }
        case Equals(le,re) => {
          val lv = rec(ctx,le)
          val rv = rec(ctx,re)

          (lv,rv) match {
            case (FiniteSet(el1),FiniteSet(el2)) => BooleanLiteral(el1.toSet == el2.toSet)
            case _ => BooleanLiteral(lv == rv)
          }
        }
        case CaseClass(cd, args) => CaseClass(cd, args.map(rec(ctx,_)))
        case CaseClassInstanceOf(cd, expr) => {
          val le = rec(ctx,expr)
          BooleanLiteral(le.getType match {
            case CaseClassType(cd2) if cd2 == cd => true
            case _ => false
          })
        }
        case CaseClassSelector(cd, expr, sel) => {
          val le = rec(ctx, expr)
          le match {
            case CaseClass(cd2, args) if cd == cd2 => args(cd.selectorID2Index(sel))
            case _ => throw TypeErrorEx(TypeError(le, CaseClassType(cd)))
          }
        }
        case Plus(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 + i2)
          case (le,re) => throw TypeErrorEx(TypeError(le, Int32Type))
        }
        case Minus(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 - i2)
          case (le,re) => throw TypeErrorEx(TypeError(le, Int32Type))
        }
        case UMinus(e) => rec(ctx,e) match {
          case IntLiteral(i) => IntLiteral(-i)
          case re => throw TypeErrorEx(TypeError(re, Int32Type))
        }
        case Times(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 * i2)
          case (le,re) => throw TypeErrorEx(TypeError(le, Int32Type))
        }
        case Division(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 / i2)
          case (le,re) => throw TypeErrorEx(TypeError(le, Int32Type))
        }
        case LessThan(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 < i2)
          case (le,re) => throw TypeErrorEx(TypeError(le, Int32Type))
        }
        case GreaterThan(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 > i2)
          case (le,re) => throw TypeErrorEx(TypeError(le, Int32Type))
        }
        case LessEquals(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 <= i2)
          case (le,re) => throw TypeErrorEx(TypeError(le, Int32Type))
        }
        case GreaterEquals(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 >= i2)
          case (le,re) => throw TypeErrorEx(TypeError(le, Int32Type))
        }

        case SetUnion(s1,s2) => (rec(ctx,s1), rec(ctx,s2)) match {
          case (EmptySet(_), f2) => f2
          case (f1, EmptySet(_)) => f1
          case (f@FiniteSet(els1),FiniteSet(els2)) => FiniteSet((els1 ++ els2).distinct).setType(f.getType)
          case (le,re) => throw TypeErrorEx(TypeError(le, s1.getType))
        }
        case SetIntersection(s1,s2) => (rec(ctx,s1), rec(ctx,s2)) match {
          case (e @ EmptySet(_), _) => e
          case (_, e @ EmptySet(_)) => e
          case (f@FiniteSet(els1),FiniteSet(els2)) => {
            val newElems = (els1.toSet intersect els2.toSet).toSeq
            val baseType = f.getType.asInstanceOf[SetType].base
            if(newElems.isEmpty) {
              EmptySet(baseType).setType(f.getType)
            } else {
              FiniteSet(newElems).setType(f.getType)
            }
          }
          case (le,re) => throw TypeErrorEx(TypeError(le, s1.getType))
        }
        case SetDifference(s1,s2) => (rec(ctx,s1), rec(ctx,s2)) match {
          case (e @ EmptySet(_), _) => e
          case (f , EmptySet(_)) => f
          case (f@FiniteSet(els1),FiniteSet(els2)) => {
            val newElems = (els1.toSet -- els2.toSet).toSeq
            val baseType = f.getType.asInstanceOf[SetType].base
            if(newElems.isEmpty) {
              EmptySet(baseType).setType(f.getType)
            } else {
              FiniteSet(newElems).setType(f.getType)
            }
          }
          case (le,re) => throw TypeErrorEx(TypeError(le, s1.getType))
        }

        case f @ FiniteSet(els) => FiniteSet(els.map(rec(ctx,_)).distinct).setType(f.getType)
        case e @ EmptySet(_) => e
        case i @ IntLiteral(_) => i
        case b @ BooleanLiteral(_) => b

        case other => {
          Settings.reporter.error("Error: don't know how to handle " + other + " in Evaluator.")
          throw RuntimeErrorEx("unhandled case in Evaluator") 
        }
      }
    }

    try {
      OK(rec(context, expression))
    } catch {
      case RuntimeErrorEx(msg) => RuntimeError(msg)
      case InfiniteComputationEx() => InfiniteComputation()
      case TypeErrorEx(te) => te
    }
  }

  // quick and dirty.. don't overuse.
  def isGround(expr: Expr) : Boolean = {
    variablesOf(expr) == Set.empty
  }
}