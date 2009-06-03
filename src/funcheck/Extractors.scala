package funcheck

import scala.tools.nsc._

/** Contains extractors to pull-out interesting parts of the Scala ASTs. */
trait Extractors {
  val global: Global
  val pluginInstance: FunCheckPlugin

  import global._
  import global.definitions._

  object StructuralExtractors {
    object ScalaPredef {
      /** Extracts method calls from scala.Predef. */
      def unapply(tree: Tree): Option[String] = tree match {
        case Select(Select(This(scalaName),predefName),symName)
          if("scala".equals(scalaName.toString) && "Predef".equals(predefName.toString)) =>
            Some(symName.toString)
        case _ => None
      }
    }

    object EnsuredExpression {
      /** Extracts the 'ensuring' contract from an expression. */
      def unapply(tree: Tree): Option[(Tree,Function)] = tree match {
        case Apply(
          Select(
            Apply(
              TypeApply(
                ScalaPredef("any2Ensuring"),
                TypeTree() :: Nil),
              body :: Nil),
            ensuringName),
          (anonymousFun @ Function(ValDef(_, resultName, resultType, EmptyTree) :: Nil,
            contractBody)) :: Nil)
          if("ensuring".equals(ensuringName.toString)) => Some((body,anonymousFun))
        case _ => None
      }
    }

    object RequiredExpression {
      /** Extracts the 'require' contract from an expression (only if it's the
       * first call in the block). */
      def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
        case Block(Apply(ScalaPredef("require"), contractBody :: Nil) :: Nil, body) =>
          Some((body,contractBody))
        case _ => None
      }
    }
  }

  object ExpressionExtractors {
    object ExBooleanLiteral {
      /** Extracts the 'true' of 'false' constants. */
      def unapply(tree: Tree): Option[Boolean] = tree match {
        case Literal(Constant(true)) => Some(true)
        case Literal(Constant(false)) => Some(false)
        case _ => None
      }
    }
  }

  object TypeExtractors {

  }
}