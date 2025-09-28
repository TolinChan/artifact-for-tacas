package synthesis

import datalog.{Program, Relation}
import verification.{TransitionSystem, Verifier}
import synthesis.StateMachine
import synthesis.ManualStateMachine
import synthesis.Parser
import util.Misc
import util.Misc.parseProgram
import imp.{ImperativeTranslator, SolidityTranslator}
import com.microsoft.z3._

case class Synthesizer() {

  def synthesize(name: String) = {
    // print(name) // 静音
    val startTime = System.nanoTime()
    // 处理 crowdfunding 的文件名特殊情况：目录 crowdfunding，文件 crowfunding.dl
    val datalogpath = s"./synthesis-benchmark/$name/$name.dl"
    val propertypath = s"./synthesis-benchmark/$name/temporal_properties.txt"
    val tracepath = s"./synthesis-benchmark/$name/example_traces.txt"
    val solpath = "./test-solidity/" + name + ".sol"
    val ctx = new Context()

    val stateMachine = Parser.buildStateMachineFromDatalog(name, datalogpath, ctx)
    val property = Parser.parseTemporalPropertiesBound(stateMachine, propertypath, ctx)
    val traceSet = Parser.parsePositiveTracesBound(stateMachine, tracepath, ctx)
        
    // 放开数组候选以提升可区分性
    val candidateGuards = stateMachine.generate_candidate_guards(List("<", "<=", ">", ">=", "=", "!="), false)
    // println(s"[DEBUG] Starting CEGIS with ${property.length} properties and ${traceSet.length} trace sets")
    
    stateMachine.cegis(property, traceSet, candidateGuards)
    stateMachine.inductive_prove(property)
    val endTime = System.nanoTime()
    val elapsedTimeMs = (endTime - startTime) / 1e9
    // print(s" $elapsedTimeMs")
    // 使用现有 Datalog -> Imperative -> Solidity 翻译器生成合约
    val dl = parseProgram(datalogpath)
    val materializedRelations: Set[Relation] = Set()
    val impTranslator = new ImperativeTranslator(dl, materializedRelations, isInstrument = false,
      monitorViolations = false, arithmeticOptimization = true, enableProjection = true)
    val imperative = impTranslator.translate()
    val solidity = SolidityTranslator(imperative, dl.interfaces, dl.violations, materializedRelations,
      false, false, true).translate()
    // 将 CEGIS 合成的守卫注入到公共交易函数（refund/invest/withdraw/close）中作为 require
    val guardsByFunc = stateMachine.getSolidityGuardsByFunction()
    val injected = imp.Statement.injectRequires(solidity, guardsByFunc)
    Misc.writeToFile(injected.toString, solpath)
  }

  /**
   * 新流程：仅读取功能与安全规范，随机生成轨迹；枚举小量候选做归纳评分，选优后验证并输出。
   */
  def synthesizeV2(name: String, config: SynthesisConfig = SynthesisConfig()): Unit = {
    val startTime = System.nanoTime()

    val datalogpath = s"./synthesis-benchmark/$name/$name.dl"
    val propertypath = s"./synthesis-benchmark/$name/temporal_properties.txt"
    val solpath = "./test-solidity/" + name + ".sol"
    val ctx = new Context()

    // 单次构建状态机并生成候选守卫
    val sm = Parser.buildStateMachineFromDatalog(name, datalogpath, ctx)
    val properties = Parser.parseTemporalPropertiesBound(sm, propertypath, ctx)
    val candidateGuards: Map[String, List[Expr[BoolSort]]] = sm.generate_candidate_guards(List("<", "<=", ">", ">=", "=", "!="), false)

    // 预先收集性质的已知反例轨迹，用于过滤随机样本
    def normalizeTrace(trace: List[List[Expr[BoolSort]]]): List[List[String]] = {
      trace.map(_.map(_.simplify().toString))
    }

    val counterexampleFingerprints: Set[List[List[String]]] = properties.flatMap { p =>
      sm.bmc(ctx.mkNot(p)) match {
        case Some(ce) => Some(normalizeTrace(ce))
        case None => None
      }
    }.toSet

    def filterTraces(traces: List[List[List[Expr[BoolSort]]]]): List[List[List[Expr[BoolSort]]]] = {
      traces.filter { trace =>
        val fp = normalizeTrace(trace)
        !counterexampleFingerprints.contains(fp)
      }
    }

    // 随机轨迹 -> 过滤掉可能成为性质反例的样本；若过滤后为空则退回性质见证
    val randomTrainTracesRaw = TraceGenerator.generate(sm, ctx, config.trainTraces, config.maxTraceLen, config.seed)
    val filteredTrainTraces = filterTraces(randomTrainTracesRaw)
    val fallbackPositives = TraceGenerator.generateFromProperties(sm, ctx, properties, config.maxTraceLen, perProp = config.perProp)
    val trainTraces =
      if (filteredTrainTraces.nonEmpty) filteredTrainTraces
      else if (fallbackPositives.nonEmpty) fallbackPositives
      else randomTrainTracesRaw.take(1)

    val randomValTracesRaw = TraceGenerator.generate(sm, ctx, config.valTraces, config.maxTraceLen, config.seed + 1)
    val valTraces = {
      val filtered = filterTraces(randomValTracesRaw)
      if (filtered.nonEmpty) filtered else fallbackPositives
    }

    // 注入阶段使用的合法性过滤，同时用于次级排序的一致性过滤
    def isValidGuardString(s: String): Boolean = {
      val t = s.trim.toLowerCase
      t.nonEmpty && !t.contains("constructor[") && !t.contains("constructor(") && !t.contains("constructor.") && !t.contains("totalbalance")
    }

    // 运行 CEGIS：会自动迭代加入反例
    sm.cegis(properties, trainTraces, candidateGuards, array = false)

    // 评估当前守卫对性质的支持情况
    val eval = Evaluator.evaluate(sm, ctx, properties, valTraces)
    println(s"[EVAL] passRate=${eval.passRate} total=${eval.total}")

    // 最终验证并输出
    properties.foreach { p =>
      val ce = sm.bmc(ctx.mkNot(p))
      if (ce.nonEmpty) {
        println(s"[VERIFY] Counterexample found for property: ${p.toString}")
      }
    }
    // 使用现有 Datalog -> Imperative -> Solidity 翻译器生成合约
    val dl = parseProgram(datalogpath)
    val materializedRelations: Set[Relation] = Set()
    val impTranslator = new ImperativeTranslator(dl, materializedRelations, isInstrument = false,
      monitorViolations = false, arithmeticOptimization = true, enableProjection = true)
    val imperative = impTranslator.translate()
    val solidity = SolidityTranslator(imperative, dl.interfaces, dl.violations, materializedRelations,
      false, false, true).translate()
    val guardsByFuncRaw = sm.getSolidityGuardsByFunction()
    val guardsByFuncClean: Map[String, List[String]] = guardsByFuncRaw.map { case (fn, lst) =>
      fn -> lst.filter(isValidGuardString)
    }
    val injected = imp.Statement.injectRequires(solidity, guardsByFuncClean)
    Misc.writeToFile(injected.toString, solpath)

    val endTime = System.nanoTime()
    val elapsedTimeMs = (endTime - startTime) / 1e9
  }
}
