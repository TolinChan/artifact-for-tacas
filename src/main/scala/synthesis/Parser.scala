package synthesis

import scala.io.Source
import com.microsoft.z3._
import datalog.Program
import util.Misc.parseProgram

object Parser {


  /**
   * 从 Datalog 文件路径构建并返回一个已填充的 StateMachine。
   * - 使用 parseProgram 解析 .dl
   * - 构建 StateMachine 并调用 readFromProgram
   * - 调用 addOnce() 以与手动流语义一致
   */
  def buildStateMachineFromDatalog(name: String, datalogPath: String, ctx: Context): StateMachine = {
    val dl = parseProgram(datalogPath)
    buildStateMachineFromProgram(name, dl, ctx)
  }

  /**
   * 从已解析的 Program 构建并返回一个已填充的 StateMachine。
   * 统一在此处调用 readFromProgram 与 addOnce()，便于在 synthesis 模块集中入口。
   */
  def buildStateMachineFromProgram(name: String, program: Program, ctx: Context): StateMachine = {
    val stateMachine = new StateMachine(name, ctx)
    populateStateMachineFromProgram(stateMachine, program, ctx)
    // 与手动构建流程保持一致：确保非当前转换的 once 变量保持不变
    stateMachine.addOnce()
    stateMachine
  }

  /**
   * 将 Program 的内容填充到给定 StateMachine。
   * 抽出公共逻辑，供 StateMachine.readFromProgram 与外部构建复用。
   */
  def populateStateMachineFromProgram(stateMachine: StateMachine, program: Program, ctx: Context): Unit = {
    println(s"[DEBUG] readFromProgram: Starting with datalog program")
    println(s"[DEBUG] readFromProgram: Relations = ${program.relations.map(_.name).mkString(", ")}")

    val materializedRelations: Set[datalog.Relation] = Set()
    val impTranslator = new imp.ImperativeTranslator(program, materializedRelations, isInstrument=false,
      enableProjection=true, monitorViolations = false, arithmeticOptimization = true)
    val imperative = impTranslator.translate()

    println(s"Translated to imperative program with ${imperative.onStatements.size} statements")

    // 填充状态与转移
    stateMachine.extractStateVariables(imperative)
    stateMachine.extractTransitions(imperative)
    println(s"Extracted ${stateMachine.transitions.length} transitions: ${stateMachine.transitions.mkString(", ")}")

    // 初始化业务状态变量为 0（标量），数组暂不强约束
    var initState = ctx.mkBool(true)
    stateMachine.states.foreach { case (_, (current, _)) =>
      current.getSort match {
        case _: IntSort => initState = ctx.mkAnd(initState, ctx.mkEq(current, ctx.mkInt(0)))
        case bv: BitVecSort => initState = ctx.mkAnd(initState, ctx.mkEq(current, ctx.mkBV(0, bv.getSize)))
        case _: ArraySort[_, _] => // 不强加默认数组量词
        case _ =>
      }
    }
    stateMachine.setInit(initState.asInstanceOf[BoolExpr])
    println(s"Initialized ${stateMachine.states.size} state variables")
    println(s"State machine ready with ${stateMachine.transferFunc.size} transitions")
    // 与手动构建流程保持一致：确保 once 变量在非当前转换上保持不变
    stateMachine.addOnce()
  }

  /**
   * 从示例轨迹文件构建与 StateMachine 绑定的正例轨迹。
   * 轨迹格式示例：
   *   recv_invest()@1;
   *   invest(p=0x114514, n=500)@2;
   * 空行分隔多条轨迹。会忽略 constructor 行。
   * 每步产出：[ (= func "event"), (= now ts), (= param value) ... ]
   */
  def parsePositiveTracesBound(stateMachine: StateMachine, tracePath: String, ctx: Context): List[List[List[Expr[BoolSort]]]] = {
    val raw = Source.fromFile(tracePath).getLines().toList
    val lines = raw.map(_.trim).filter(l => l.nonEmpty || l == "") // 保留空行用于分段
    val traces = scala.collection.mutable.ListBuffer[List[List[Expr[BoolSort]]]]()
    var current: List[List[Expr[BoolSort]]] = List()

    val eventPattern = """(\w+)\((.*?)\)@(0x[0-9a-fA-F]+|\d+);?""".r
    val kvPattern = """(\w+)=(0x[0-9a-fA-F]+|\d+)""".r

    def parseNum(v: String): Expr[BitVecSort] = {
      // 使用十进制字符串传给 Z3；将 0x 前缀转换为十进制字符串以避免 parser error
      val decStr = if (v.startsWith("0x") || v.startsWith("0X")) {
        new java.math.BigInteger(v.substring(2), 16).toString
      } else v
      ctx.mkBV(decStr, 256)
    }

    def flush(): Unit = {
      if (current.nonEmpty) traces += current; current = List()
    }

    lines.foreach { rawLine =>
      if (rawLine.isEmpty) {
        flush()
      } else if (rawLine.startsWith("//")) {
        ()
      } else {
        // 去掉行尾内联注释
        val line = rawLine.replaceFirst("\\s*//.*$", "").trim
        line match {
          case l if l.isEmpty => ()
          case eventPattern(event, params, timeStr) =>
            if (!event.equalsIgnoreCase("constructor")) {
              val eventName = if (event.startsWith("recv_")) event.substring(5) else event
              val funcEq = ctx.mkEq(stateMachine.func.asInstanceOf[Expr[_]], ctx.mkString(eventName)).asInstanceOf[Expr[BoolSort]]
              val nowEq = ctx.mkEq(stateMachine.now.asInstanceOf[Expr[BitVecSort]], parseNum(timeStr)).asInstanceOf[Expr[BoolSort]]

              val paramEqs: List[Expr[BoolSort]] =
                if (params.trim.isEmpty) List()
                else params.split(',').toList.flatMap {
                  case kvPattern(k, v) =>
                    val lhs = ctx.mkBVConst(k, 256)
                    val rhs = parseNum(v)
                    Some(ctx.mkEq(lhs, rhs).asInstanceOf[Expr[BoolSort]])
                  case _ => None
                }
              val step = (List(funcEq, nowEq) ++ paramEqs)
              current = current :+ step
            }
          case other => throw new IllegalArgumentException(s"Invalid trace line: $other")
        }
      }
    }
    flush()
    traces.toList
  }

  /**
   * 将 temporal_properties.txt 的常见 ♦/互斥 模式绑定到 once 变量；无法识别的行跳过。
   * 支持的形式（忽略外层 □）：
   *  - ¬(♦A() ∧ ♦B())
   *  - (♦A() → ¬♦B())
   */
  def parseTemporalPropertiesBound(stateMachine: StateMachine, propertyPath: String, ctx: Context): List[Expr[BoolSort]] = {
    val rawAll = Source.fromFile(propertyPath).getLines().toList
    val lines = rawAll.map(_.trim).filter(l => l.nonEmpty && !l.startsWith("//"))
    val results = scala.collection.mutable.ListBuffer[Expr[BoolSort]]()

    def findOnceVar(eventName: String): Option[Expr[BoolSort]] = {
      val base = eventName.toLowerCase
      // 优先使用 traceEventMapping（event -> 转移名）
      val mappedTr = stateMachine.traceEventMapping.getOrElse(base, "")
      val candidates: List[String] =
        if (mappedTr.nonEmpty) List(mappedTr)
        else stateMachine.transitions.filter(t => t.toLowerCase.contains(base))
      val found = candidates.view.flatMap { tr =>
        // once 映射的 key 是转移名（tr），而不是 'once_tr'
        val byTrKey = stateMachine.once.get(tr).map(_._1.asInstanceOf[Expr[BoolSort]])
        val byOnceName = stateMachine.once.get(s"once_${tr}").map(_._1.asInstanceOf[Expr[BoolSort]])
        byTrKey.orElse(byOnceName)
      }.headOption
      found
    }

    def stripBox(s: String): String = {
      if (s.startsWith("□(" ) && s.endsWith(")")) s.substring(2, s.length-1).trim else s
    }

    // 事件提取（容忍 ♦event() / ♦(event()) / 大小写）
    def extractEventName(token: String): Option[String] = {
      val s = token.replaceAll("\\s+", "")
      val idx = s.indexOf('♦')
      if (idx >= 0) {
        val after = s.substring(idx + 1)
        // (event()) 或 event()
        val inner = if (after.startsWith("(")) after.drop(1) else after
        val nameEnd = inner.indexOf('(')
        if (nameEnd > 0) Some(inner.substring(0, nameEnd).toLowerCase) else None
      } else None
    }

    def getNumState(name: String): Option[Expr[_]] = {
      val key = name
      stateMachine.states.get(key).map(_._1)
    }

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
      // 仅检查最后一个箭头右侧的比较子句
      val rhsLast = s.split("→").lastOption.getOrElse(s).trim
      val noSpace = rhsLast.replaceAll("\\s+", "")
      if (noSpace.contains(">=" ) || noSpace.contains("≥")) Some(">=")
      else if (noSpace.contains("<=") || noSpace.contains("≤")) Some("<=")
      else if (noSpace.contains("==")) Some("==")
      else if (noSpace.contains("=")) Some("==")
      else if (noSpace.contains(">")) Some(">")
      else if (noSpace.contains("<")) Some("<")
      else None
    }

    lines.foreach { rawLine =>
      val line = stripBox(rawLine)
      // Pattern 1: ¬(♦A() ∧ ♦B())
      val andPat = """^¬\s*\(\s*♦\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(\)\s*∧\s*♦\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(\)\s*\)$""".r
      // Pattern 2: ♦A() → ¬♦B()  以及混合括号：左无右有 / 左有右无
      val impPat = """^♦\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(\)\s*→\s*¬\s*♦\s*\(?\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(\)\s*\)?\s*$""".r
      // Pattern 3: 括号对称：♦(A()) → ¬♦(B())
      val impPat2 = """^♦\s*\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(\)\s*\)\s*→\s*¬\s*♦\s*\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(\)\s*\)\s*$""".r
      // Pattern 4: ♦Event() → raised(r) ∧ target(t) → r < t  （简化为 Event → raised < target）
      val impRaisedTarget = """^♦\s*\(?\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(\)\s*\)?\s*→\s*(.*)$""".r

      line match {
        case andPat(a, b) =>
          (findOnceVar(a), findOnceVar(b)) match {
            case (Some(oa), Some(ob)) =>
              results += ctx.mkNot(ctx.mkAnd(oa, ob)).asInstanceOf[Expr[BoolSort]]
            case _ => ()
          }
        case impPat(a, b) =>
          (findOnceVar(a), findOnceVar(b)) match {
            case (Some(oa), Some(ob)) =>
              results += ctx.mkImplies(oa, ctx.mkNot(ob)).asInstanceOf[Expr[BoolSort]]
            case _ => ()
          }
        case impPat2(a, b) =>
          (findOnceVar(a), findOnceVar(b)) match {
            case (Some(oa), Some(ob)) =>
              results += ctx.mkImplies(oa, ctx.mkNot(ob)).asInstanceOf[Expr[BoolSort]]
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
                case _             => mkLt(raised, target) // 默认回退
              }
              results += ctx.mkImplies(oev, cmp).asInstanceOf[Expr[BoolSort]]
            case _ if rhs.toLowerCase.contains("totalbalance") && getNumState("raised").nonEmpty =>
              ()
            case _ => ()
          }
        case _ => () // 其他行暂不支持
      }
    }
    results.toList
  }
}