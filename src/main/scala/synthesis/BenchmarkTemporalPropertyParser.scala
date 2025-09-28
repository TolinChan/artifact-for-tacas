package synthesis

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

import scala.collection.mutable
import scala.jdk.CollectionConverters._

object BenchmarkTemporalPropertyParser {

  sealed trait TemporalKind
  object TemporalKind {
    case object Always extends TemporalKind
    case object AlwaysNot extends TemporalKind
  }

  sealed trait Expr
  object Expr {
    final case class Identifier(name: String) extends Expr
    final case class NumberLiteral(value: BigInt, raw: String) extends Expr
    final case class BoolLiteral(value: Boolean) extends Expr
    final case class FunctionCall(name: String, args: List[Expr]) extends Expr
    final case class Unary(op: UnaryOp, expr: Expr) extends Expr
    final case class Binary(op: BinaryOp, left: Expr, right: Expr) extends Expr
  }

  sealed trait UnaryOp
  object UnaryOp {
    case object Not extends UnaryOp
    case object Negate extends UnaryOp
  }

  sealed trait BinaryOp
  object BinaryOp {
    case object And extends BinaryOp
    case object Or extends BinaryOp
    case object Implies extends BinaryOp
    case object Eq extends BinaryOp
    case object Neq extends BinaryOp
    case object Gt extends BinaryOp
    case object Ge extends BinaryOp
    case object Lt extends BinaryOp
    case object Le extends BinaryOp
    case object Add extends BinaryOp
    case object Sub extends BinaryOp
    case object Mul extends BinaryOp
    case object Div extends BinaryOp
  }

  final case class TemporalFormula(kind: TemporalKind, body: Expr)

  final case class TemporalProperty(
      line: Int,
      comment: Option[String],
      original: String,
      normalized: String,
      formula: TemporalFormula
  )

  final case class ParseError(
      line: Int,
      column: Int,
      original: String,
      normalized: String,
      message: String
  )

  final case class ParseSummary(properties: Vector[TemporalProperty], errors: Vector[ParseError]) {
    def isSuccess: Boolean = errors.isEmpty
  }

  final case class FormulaError(message: String, column: Int)

  private final case class RawEntry(
      line: Int,
      comments: Vector[String],
      original: String,
      normalized: String
  )

  def parseFile(path: Path): ParseSummary = {
    val lines = Files.readAllLines(path, StandardCharsets.UTF_8).asScala.toVector
    parseLines(lines)
  }

  def parseLines(lines: Seq[String]): ParseSummary = {
    val entries = collectEntries(lines)
    val properties = Vector.newBuilder[TemporalProperty]
    val errors = Vector.newBuilder[ParseError]

    entries.foreach { entry =>
      parseFormula(entry.normalized) match {
        case Right(formula) =>
          val commentOpt = if (entry.comments.nonEmpty) Some(entry.comments.mkString("\n")) else None
          properties += TemporalProperty(entry.line, commentOpt, entry.original, entry.normalized, formula)
        case Left(failure) =>
          errors += ParseError(entry.line, failure.column, entry.original, entry.normalized, failure.message)
      }
    }

    ParseSummary(properties.result(), errors.result())
  }

  def parseFormula(input: String): Either[FormulaError, TemporalFormula] = FormulaParser.parse(input)

  private def collectEntries(lines: Seq[String]): Vector[RawEntry] = {
    val results = Vector.newBuilder[RawEntry]
    val commentBuffer = mutable.ArrayBuffer.empty[String]
    val snippetBuffer = mutable.ArrayBuffer.empty[String]
    val normalizedBuffer = new mutable.StringBuilder

    var depth = 0
    var inside = false
    var startLine = 0

    lines.zipWithIndex.foreach { case (line, idx) =>
      val trimmed = line.trim
      val isCommentLine = trimmed.startsWith("//")

      if (!inside && isCommentLine) {
        commentBuffer += trimmed.drop(2).trim
      } else {
        val withoutComment = stripInlineComment(line)
        val rawSegment = withoutComment.trim
        val normalizedSegment = normalizeLine(withoutComment)

        if (!inside && normalizedSegment.nonEmpty) {
          inside = true
          startLine = idx + 1
          normalizedBuffer.clear()
          snippetBuffer.clear()
        }

        if (inside) {
          if (rawSegment.nonEmpty) {
            snippetBuffer += rawSegment
          }
          if (normalizedSegment.nonEmpty) {
            if (normalizedBuffer.nonEmpty) normalizedBuffer.append(' ')
            normalizedBuffer.append(normalizedSegment)
          }

          depth += parenDelta(withoutComment)

          val shouldFlush = normalizedSegment.nonEmpty && depth <= 0
          if (shouldFlush) {
            val normalized = normalizedBuffer.result().trim
            if (normalized.nonEmpty) {
              val original = snippetBuffer.mkString("\n")
              results += RawEntry(startLine, commentBuffer.toVector, original, normalized)
            }
            commentBuffer.clear()
            snippetBuffer.clear()
            normalizedBuffer.clear()
            depth = 0
            inside = false
            startLine = 0
          }
        }
      }
    }

    if (inside) {
      val normalized = normalizedBuffer.result().trim
      if (normalized.nonEmpty) {
        val original = snippetBuffer.mkString("\n")
        results += RawEntry(startLine, commentBuffer.toVector, original, normalized)
      }
    }

    results.result()
  }

  private def stripInlineComment(line: String): String = {
    val idx = line.indexOf("//")
    if (idx >= 0) line.substring(0, idx) else line
  }

  private def normalizeLine(input: String): String = {
    val spacedNot = input.replaceAll("(?i)(?<![A-Za-z0-9_])NOT(?=[A-Za-z_(])", "NOT ")
    spacedNot.replaceAll("\\s+", " ").trim
  }

  private def parenDelta(line: String): Int = {
    var delta = 0
    line.foreach {
      case '(' => delta += 1
      case ')' => delta -= 1
      case _ =>
    }
    delta
  }

  private object FormulaParser {

    def parse(input: String): Either[FormulaError, TemporalFormula] = {
      tokenize(input) match {
        case Left(err) => Left(err)
        case Right(tokens) =>
          try {
            val parser = new PrattParser(tokens)
            val formula = parser.parseTemporalFormula()
            parser.expectEnd()
            Right(formula)
          } catch {
            case ParserException(message, column) => Left(FormulaError(message, column))
          }
      }
    }

    private sealed trait Token { def column: Int }
    private final case class KeywordToken(value: String, column: Int) extends Token
    private final case class IdentifierToken(value: String, column: Int) extends Token
    private final case class NumberToken(value: BigInt, raw: String, column: Int) extends Token
    private final case class BoolToken(value: Boolean, column: Int) extends Token
    private final case class SymbolToken(symbol: String, column: Int) extends Token
    private final case class OperatorToken(op: String, column: Int) extends Token
    private final case class EndToken(column: Int) extends Token

    private final case class ParserException(message: String, column: Int) extends RuntimeException(message)

    private val keywordSet: Set[String] = Set("ALWAYS", "ALWAYSNOT", "NOT", "AND", "OR", "IMPLIES", "TRUE", "FALSE")

    private def tokenize(input: String): Either[FormulaError, Vector[Token]] = {
      val tokens = Vector.newBuilder[Token]
      val length = input.length
      var idx = 0
      var column = 1

      def currentChar: Char = input.charAt(idx)

      def bump(): Unit = {
        idx += 1
        column += 1
      }

      while (idx < length) {
        currentChar match {
          case ch if ch.isWhitespace => bump()
          case ch @ ('(' | ')' | ',') =>
            tokens += SymbolToken(ch.toString, column)
            bump()
          case ch @ ('+' | '-' | '*' | '/') =>
            tokens += OperatorToken(ch.toString, column)
            bump()
          case '>' =>
            val col = column
            bump()
            if (idx < length && input.charAt(idx) == '=') {
              bump()
              tokens += OperatorToken(">=", col)
            } else {
              tokens += OperatorToken(">", col)
            }
          case '<' =>
            val col = column
            bump()
            if (idx < length && input.charAt(idx) == '=') {
              bump()
              tokens += OperatorToken("<=", col)
            } else {
              tokens += OperatorToken("<", col)
            }
          case '=' =>
            val col = column
            bump()
            if (idx < length && input.charAt(idx) == '=') {
              bump()
              tokens += OperatorToken("==", col)
            } else {
              tokens += OperatorToken("==", col)
            }
          case '!' =>
            val col = column
            bump()
            if (idx < length && input.charAt(idx) == '=') {
              bump()
              tokens += OperatorToken("!=", col)
            } else {
              return Left(FormulaError("'!' must be followed by '='", col))
            }
          case ch if ch.isDigit =>
            val col = column
            val start = idx
            if (ch == '0' && idx + 1 < length && (input.charAt(idx + 1) == 'x' || input.charAt(idx + 1) == 'X')) {
              idx += 2
              column += 2
              while (idx < length && isHexDigit(input.charAt(idx))) {
                idx += 1
                column += 1
              }
            } else {
              while (idx < length && input.charAt(idx).isDigit) {
                idx += 1
                column += 1
              }
            }
            val raw = input.substring(start, idx)
            val value =
              if (raw.startsWith("0x") || raw.startsWith("0X")) BigInt(raw.drop(2), 16)
              else BigInt(raw, 10)
            tokens += NumberToken(value, raw, col)
          case ch if isIdentStart(ch) =>
            val col = column
            val start = idx
            idx += 1
            column += 1
            while (idx < length && isIdentPart(input.charAt(idx))) {
              idx += 1
              column += 1
            }
            val raw = input.substring(start, idx)
            val upper = raw.toUpperCase
            if (upper == "TRUE" || upper == "FALSE") {
              tokens += BoolToken(upper == "TRUE", col)
            } else if (keywordSet.contains(upper)) {
              tokens += KeywordToken(upper, col)
            } else {
              tokens += IdentifierToken(raw, col)
            }
          case other =>
            return Left(FormulaError(s"Unexpected character '$other'", column))
        }
      }

      tokens += EndToken(column)
      Right(tokens.result())
    }

    private def isIdentStart(ch: Char): Boolean = ch.isLetter || ch == '_'
    private def isIdentPart(ch: Char): Boolean = ch.isLetterOrDigit || ch == '_'
    private def isHexDigit(ch: Char): Boolean = ch.isDigit || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F')

    private final class PrattParser(tokens: Vector[Token]) {
      private var index = 0

      def parseTemporalFormula(): TemporalFormula = {
        peek match {
          case KeywordToken("ALWAYSNOT", _) =>
            next()
            val body = parseTemporalBody()
            TemporalFormula(TemporalKind.AlwaysNot, body)
          case KeywordToken("ALWAYS", _) =>
            next()
            val kind = peek match {
              case KeywordToken("NOT", _) =>
                next()
                TemporalKind.AlwaysNot
              case _ => TemporalKind.Always
            }
            val body = parseTemporalBody()
            TemporalFormula(kind, body)
          case token => error("Expected ALWAYS or ALWAYSNOT", token.column)
        }
      }

      private def parseTemporalBody(): Expr = {
        peek match {
          case SymbolToken("(", _) =>
            next()
            val expr = parseExpression(0)
            expectSymbol(")")
            expr
          case _ => parseExpression(0)
        }
      }

      def expectEnd(): Unit = peek match {
        case EndToken(_) => ()
        case token => error("Unexpected trailing tokens", token.column)
      }

      private def parseExpression(minPrec: Int): Expr = {
        var left = parsePrefix()
        var continue = true
        while (continue) {
          infixInfo(peek) match {
            case Some((op, prec, rightAssoc)) if prec >= minPrec =>
              next()
              val nextMin = if (rightAssoc) prec else prec + 1
              val right = parseExpression(nextMin)
              left = Expr.Binary(op, left, right)
            case _ => continue = false
          }
        }
        left
      }

      private def parsePrefix(): Expr = {
        val token = next()
        token match {
          case SymbolToken("(", _) =>
            val expr = parseExpression(0)
            expectSymbol(")")
            expr
          case OperatorToken("-", _) =>
            Expr.Unary(UnaryOp.Negate, parseExpression(6))
          case KeywordToken("NOT", _) =>
            Expr.Unary(UnaryOp.Not, parseExpression(6))
          case BoolToken(value, _) => Expr.BoolLiteral(value)
          case NumberToken(value, raw, _) => Expr.NumberLiteral(value, raw)
          case IdentifierToken(name, _) =>
            if (peekSymbol("(")) parseFunctionCall(name)
            else Expr.Identifier(name)
          case other => error("Unexpected token", other.column)
        }
      }

      private def parseFunctionCall(name: String): Expr = {
        expectSymbol("(")
        val args = mutable.ListBuffer.empty[Expr]
        if (!peekSymbol(")")) {
          args += parseExpression(0)
          while (consumeIfSymbol(",")) {
            args += parseExpression(0)
          }
        }
        expectSymbol(")")
        Expr.FunctionCall(name, args.toList)
      }

      private def infixInfo(token: Token): Option[(BinaryOp, Int, Boolean)] = token match {
        case KeywordToken("IMPLIES", _) => Some((BinaryOp.Implies, 1, true))
        case KeywordToken("OR", _)      => Some((BinaryOp.Or, 2, false))
        case KeywordToken("AND", _)     => Some((BinaryOp.And, 3, false))
        case OperatorToken("==", _)     => Some((BinaryOp.Eq, 4, false))
        case OperatorToken("!=", _)     => Some((BinaryOp.Neq, 4, false))
        case OperatorToken(">=", _)     => Some((BinaryOp.Ge, 4, false))
        case OperatorToken("<=", _)     => Some((BinaryOp.Le, 4, false))
        case OperatorToken(">", _)      => Some((BinaryOp.Gt, 4, false))
        case OperatorToken("<", _)      => Some((BinaryOp.Lt, 4, false))
        case OperatorToken("+", _)      => Some((BinaryOp.Add, 5, false))
        case OperatorToken("-", _)      => Some((BinaryOp.Sub, 5, false))
        case OperatorToken("*", _)      => Some((BinaryOp.Mul, 6, false))
        case OperatorToken("/", _)      => Some((BinaryOp.Div, 6, false))
        case _ => None
      }

      private def peek: Token = tokens(index)
      private def next(): Token = {
        val token = tokens(index)
        index += 1
        token
      }

      private def expectSymbol(symbol: String): Unit = peek match {
        case SymbolToken(`symbol`, _) => next()
        case token => error(s"'$symbol' expected", token.column)
      }

      private def consumeIfSymbol(symbol: String): Boolean = peek match {
        case SymbolToken(`symbol`, _) =>
          next()
          true
        case _ => false
      }

      private def peekSymbol(symbol: String): Boolean = peek match {
        case SymbolToken(`symbol`, _) => true
        case _ => false
      }

      private def error(message: String, column: Int): Nothing = throw ParserException(message, column)
    }
  }
}

