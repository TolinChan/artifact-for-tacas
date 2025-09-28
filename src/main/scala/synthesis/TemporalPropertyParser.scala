package synthesis

import scala.io.Source
import com.microsoft.z3._

object TemporalPropertyParser {

  def parseTemporalPropertiesBound(stateMachine: StateMachine, propertyPath: String, ctx: Context): List[Expr[BoolSort]] = {
    val rawAll = Source.fromFile(propertyPath).getLines().toList
    val normalizedAll = rawAll.map(_.trim)
    val lines = normalizedAll.filter(l => l.nonEmpty && !l.startsWith("//"))
    val results = scala.collection.mutable.ListBuffer[Expr[BoolSort]]()

    def findOnceVar(eventName: String): Option[Expr[BoolSort]] = {
      val base = eventName.toLowerCase
      val mappedTr = stateMachine.traceEventMapping.getOrElse(base, "")
      val candidates: List[String] =
        if (mappedTr.nonEmpty) List(mappedTr)
        else stateMachine.transitions.filter(t => t.toLowerCase.contains(base))
      candidates.view.flatMap { tr =>
        val byTrKey = stateMachine.once.get(tr).map(_._1.asInstanceOf[Expr[BoolSort]])
        val byOnceName = stateMachine.once.get(s"once_${tr}").map(_._1.asInstanceOf[Expr[BoolSort]])
        byTrKey.orElse(byOnceName)
      }.headOption
    }

    def canonicalizeTemporal(line: String): String = {
      val arrowLike = List("->", "=>", "-->", "==>")
      val arrowsNormalized = arrowLike.foldLeft(line) { case (acc, arrow) => acc.replace(arrow, "→") }
      val replacements = List(
        "(?i)(?<![A-Za-z0-9_])NOT(?=\\s*[A-Za-z_(])" -> "¬",
        "(?i)(?<![A-Za-z0-9_])AND(?=\\s*[A-Za-z_(])" -> "∧",
        "(?i)(?<![A-Za-z0-9_])OR(?=\\s*[A-Za-z_(])" -> "∨",
        "(?i)(?<![A-Za-z0-9_])IMPLIES(?=\\s*[A-Za-z_(])" -> "→",
        "(?i)(?<![A-Za-z0-9_])ALWAYS(?=\\s*\\()" -> "□",
        "(?i)(?<![A-Za-z0-9_])BOX(?=\\s*\\()" -> "□",
        "(?i)(?<![A-Za-z0-9_])DIAMOND(?=\\s*\\()" -> "♦",
        "(?i)(?<![A-Za-z0-9_])EVENTUALLY(?=\\s*\\()" -> "♦"
      )
      replacements.foldLeft(arrowsNormalized) { case (acc, (pattern, token)) => acc.replaceAll(pattern, token) }.trim
    }

    def stripBox(s: String): String = {
      val trimmed = s.trim
      val upper = trimmed.toUpperCase
      if (upper.startsWith("ALWAYS(") && trimmed.endsWith(")"))
        trimmed.substring(trimmed.indexOf('(') + 1, trimmed.length - 1).trim
      else if (trimmed.startsWith("□(") && trimmed.endsWith(")"))
        trimmed.substring(2, trimmed.length - 1).trim
      else trimmed
    }

    def extractEventName(token: String): Option[String] = {
      val compact = token.replaceAll("\\s+", "")
      val upper = compact.toUpperCase
      val wordIdx = upper.indexOf("DIAMOND")
      val symbolIdx = compact.indexOf('♦')
      val startIdx =
        if (wordIdx >= 0) wordIdx + "DIAMOND".length
        else if (symbolIdx >= 0) symbolIdx + 1
        else -1
      if (startIdx >= 0) {
        val after = compact.substring(startIdx)
        val inner = if (after.startsWith("(")) after.drop(1) else after
        val nameEnd = inner.indexOf('(')
        if (nameEnd > 0) Some(inner.substring(0, nameEnd).toLowerCase) else None
      } else None
    }

    def getNumState(name: String): Option[Expr[_]] = stateMachine.states.get(name).map(_._1)

    def mkLt(a: Expr[_], b: Expr[_]): Expr[BoolSort] = (a.getSort, b.getSort) match {
      case (_: IntSort, _: IntSort) => ctx.mkLt(a.asInstanceOf[Expr[IntSort]], b.asInstanceOf[Expr[IntSort]])
      case (_: BitVecSort, _: BitVecSort) => ctx.mkBVULT(a.asInstanceOf[Expr[BitVecSort]], b.asInstanceOf[Expr[BitVecSort]])
      case _ => ctx.mkBool(true)
    }
    def mkLe(a: Expr[_], b: Expr[_]): Expr[BoolSort] = (a.getSort, b.getSort) match {
      case (_: IntSort, _: IntSort) => ctx.mkLe(a.asInstanceOf[Expr[IntSort]], b.asInstanceOf[Expr[IntSort]])
      case (_: BitVecSort, _: BitVecSort) => ctx.mkBVULE(a.asInstanceOf[Expr[BitVecSort]], b.asInstanceOf[Expr[BitVecSort]])
      case _ => ctx.mkBool(true)
    }
    def mkGt(a: Expr[_], b: Expr[_]): Expr[BoolSort] = (a.getSort, b.getSort) match {
      case (_: IntSort, _: IntSort) => ctx.mkGt(a.asInstanceOf[Expr[IntSort]], b.asInstanceOf[Expr[IntSort]])
      case (_: BitVecSort, _: BitVecSort) => ctx.mkBVUGT(a.asInstanceOf[Expr[BitVecSort]], b.asInstanceOf[Expr[BitVecSort]])
      case _ => ctx.mkBool(true)
    }
    def mkGe(a: Expr[_], b: Expr[_]): Expr[BoolSort] = (a.getSort, b.getSort) match {
      case (_: IntSort, _: IntSort) => ctx.mkGe(a.asInstanceOf[Expr[IntSort]], b.asInstanceOf[Expr[IntSort]])
      case (_: BitVecSort, _: BitVecSort) => ctx.mkBVUGE(a.asInstanceOf[Expr[BitVecSort]], b.asInstanceOf[Expr[BitVecSort]])
      case _ => ctx.mkBool(true)
    }
    def mkEq(a: Expr[_], b: Expr[_]): Expr[BoolSort] = ctx.mkEq(a.asInstanceOf[Expr[_]], b.asInstanceOf[Expr[_]]).asInstanceOf[Expr[BoolSort]]

    def pickCompareOp(s: String): Option[String] = {
      val standardized = s.replaceAll("(?i)IMPLIES", "→")
      val rhsLast = standardized.split("→").lastOption.getOrElse(standardized).trim
      val noSpace = rhsLast.replaceAll("\\s+", "")
      if (noSpace.contains(">=" ) || noSpace.contains("≥")) Some(">=")
      else if (noSpace.contains("<=") || noSpace.contains("≤")) Some("<=")
      else if (noSpace.contains("==")) Some("==")
      else if (noSpace.contains("=")) Some("==")
      else if (noSpace.contains(">")) Some(">")
      else if (noSpace.contains("<")) Some("<")
      else None
    }

    lines.foreach { originalLine =>
      val canonicalLine = canonicalizeTemporal(originalLine)
      val line = stripBox(canonicalLine)
      val andPat = """^¬\s*\(\s*♦\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(\)\s*∧\s*♦\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(\)\s*\)$""".r
      val impPat = """^♦\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(\)\s*→\s*¬\s*♦\s*\(?\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(\)\s*\)?\s*$""".r
      val impPat2 = """^♦\s*\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(\)\s*\)\s*→\s*¬\s*♦\s*\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(\)\s*\)\s*$""".r
      val impRaisedTarget = """^♦\s*\(?\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(\)\s*\)?\s*→\s*(.*)$""".r

      line match {
        case andPat(a, b) =>
          (findOnceVar(a), findOnceVar(b)) match {
            case (Some(oa), Some(ob)) => results += ctx.mkNot(ctx.mkAnd(oa, ob)).asInstanceOf[Expr[BoolSort]]
            case _ => ()
          }
        case impPat(a, b) =>
          (findOnceVar(a), findOnceVar(b)) match {
            case (Some(oa), Some(ob)) => results += ctx.mkImplies(oa, ctx.mkNot(ob)).asInstanceOf[Expr[BoolSort]]
            case _ => ()
          }
        case impPat2(a, b) =>
          (findOnceVar(a), findOnceVar(b)) match {
            case (Some(oa), Some(ob)) => results += ctx.mkImplies(oa, ctx.mkNot(ob)).asInstanceOf[Expr[BoolSort]]
            case _ => ()
          }
        case impRaisedTarget(ev, rhs) =>
          val hasRaised = rhs.toLowerCase.contains("raised")
          val hasTarget = rhs.toLowerCase.contains("target")
          (findOnceVar(ev), getNumState("raised"), getNumState("target")) match {
            case (Some(oev), Some(raised), Some(target)) if hasRaised && hasTarget =>
              val opOpt = pickCompareOp(rhs)
              val cmp: Expr[BoolSort] = opOpt match {
                case Some("<")   => mkLt(raised, target)
                case Some("<=")  => mkLe(raised, target)
                case Some(">")   => mkGt(raised, target)
                case Some(">=")  => mkGe(raised, target)
                case Some("==")  => mkEq(raised, target)
                case _             => mkLt(raised, target)
              }
              results += ctx.mkImplies(oev, cmp).asInstanceOf[Expr[BoolSort]]
            case _ => ()
          }
        case _ => ()
      }
    }

    results.toList
  }
}
