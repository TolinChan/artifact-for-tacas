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
    println(s"[DEBUG] First statement sample: ${imperative.onStatements.headOption.map(_.toString).getOrElse("<empty>")}")

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
   * 将 temporal_properties.txt 的常见 ♦/互斥 模式绑定到 once 变量；无法识别的行跳过。
   * 支持的形式（忽略外层 □）：
   *  - ¬(♦A() ∧ ♦B())
   *  - (♦A() → ¬♦B())
   */
  def parseTemporalPropertiesBound(stateMachine: StateMachine, propertyPath: String, ctx: Context): List[Expr[BoolSort]] = {
    TemporalPropertyParser.parseTemporalPropertiesBound(stateMachine, propertyPath, ctx)
  }

  def parsePositiveTracesBound(stateMachine: StateMachine, tracePath: String, ctx: Context): List[List[List[Expr[BoolSort]]]] = {
    val raw = Source.fromFile(tracePath).getLines().toList
    val lines = raw.map(_.trim).filter(l => l.nonEmpty || l == "")
    val traces = scala.collection.mutable.ListBuffer[List[List[Expr[BoolSort]]]]()
    var current: List[List[Expr[BoolSort]]] = List()

    val eventPattern = """(\w+)\((.*?)\)@(0x[0-9a-fA-F]+|\d+);?""".r
    val kvPattern = """(\w+)=(0x[0-9a-fA-F]+|\d+)""".r

    def parseNum(v: String): Expr[BitVecSort] = {
      val decStr = if (v.startsWith("0x") || v.startsWith("0X")) new java.math.BigInteger(v.substring(2), 16).toString else v
      ctx.mkBV(decStr, 256)
    }

    def flush(): Unit = {
      if (current.nonEmpty) traces += current
      current = List()
    }

    lines.foreach { rawLine =>
      if (rawLine.isEmpty) {
        flush()
      } else if (rawLine.startsWith("//")) ()
      else {
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
              val step = List(funcEq, nowEq) ++ paramEqs
              current = current :+ step
            }
          case other => throw new IllegalArgumentException(s"Invalid trace line: $other")
        }
      }
    }
    flush()
    traces.toList
  }
}