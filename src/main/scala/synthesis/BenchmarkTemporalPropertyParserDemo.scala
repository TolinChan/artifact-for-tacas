package synthesis

import java.nio.file.{Files, Path, Paths}

object BenchmarkTemporalPropertyParserDemo extends App {

  if (args.isEmpty) {
    Console.err.println("用法: sbt \"runMain synthesis.BenchmarkTemporalPropertyParserDemo <temporal_properties 路径>\"")
    sys.exit(1)
  }

  val target = Paths.get(args(0))
  if (!Files.exists(target)) {
    Console.err.println(s"文件不存在: $target")
    sys.exit(1)
  }

  val summary = BenchmarkTemporalPropertyParser.parseFile(target)

  println(s"解析文件: $target")
  println(s"成功性质: ${summary.properties.size} 条")
  println(s"失败性质: ${summary.errors.size} 条")
  println()

  summary.properties.zipWithIndex.foreach { case (prop, idx) =>
    println(s"-- 性质 #${idx + 1} --")
    prop.comment.foreach(c => println(s"注释:\n$c"))
    println(s"原始文本:\n${prop.original}")
    println(s"归一化: ${prop.normalized}")
    println(s"解析结果: ${renderFormula(prop.formula)}")
    println()
  }

  if (summary.errors.nonEmpty) {
    println("-- 解析失败 --")
    summary.errors.foreach { err =>
      println(s"行 ${err.line}, 列 ${err.column}: ${err.message}")
      println(s"原始: ${err.original}")
      println(s"归一化: ${err.normalized}")
      println()
    }
  }

  private def renderFormula(formula: BenchmarkTemporalPropertyParser.TemporalFormula): String = {
    val kind = formula.kind match {
      case BenchmarkTemporalPropertyParser.TemporalKind.Always => "ALWAYS"
      case BenchmarkTemporalPropertyParser.TemporalKind.AlwaysNot => "ALWAYSNOT"
    }
    s"$kind ${renderExpr(formula.body)}"
  }

  private def renderExpr(expr: BenchmarkTemporalPropertyParser.Expr): String = {
    import BenchmarkTemporalPropertyParser._
    expr match {
      case Expr.Identifier(name) => name
      case Expr.NumberLiteral(_, raw) => raw
      case Expr.BoolLiteral(value) => value.toString.toUpperCase
      case Expr.FunctionCall(name, args) => s"$name(${args.map(renderExpr).mkString(", ")})"
      case Expr.Unary(op, inner) =>
        val symbol = op match {
          case UnaryOp.Not => "NOT "
          case UnaryOp.Negate => "-"
        }
        symbol + renderExpr(inner)
      case Expr.Binary(op, left, right) =>
        val sym = op match {
          case BinaryOp.And => " AND "
          case BinaryOp.Or => " OR "
          case BinaryOp.Implies => " IMPLIES "
          case BinaryOp.Eq => " == "
          case BinaryOp.Neq => " != "
          case BinaryOp.Gt => " > "
          case BinaryOp.Ge => " >= "
          case BinaryOp.Lt => " < "
          case BinaryOp.Le => " <= "
          case BinaryOp.Add => " + "
          case BinaryOp.Sub => " - "
          case BinaryOp.Mul => " * "
          case BinaryOp.Div => " / "
        }
        val leftStr = wrapIfBinary(left)
        val rightStr = wrapIfBinary(right)
        leftStr + sym + rightStr
    }
  }

  private def wrapIfBinary(expr: BenchmarkTemporalPropertyParser.Expr): String = {
    import BenchmarkTemporalPropertyParser.Expr
    expr match {
      case _: Expr.Binary => s"(${renderExpr(expr)})"
      case _ => renderExpr(expr)
    }
  }
}

