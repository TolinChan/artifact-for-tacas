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
    val actualDirName = name
    val actualFileName = if (name == "crowdfunding") "crowfunding" else name
    val datalogpath = "./synthesis-benchmark/" + actualDirName + "/" + actualFileName + ".dl"
    val propertypath = "./synthesis-benchmark/" + actualDirName + "/temporal_properties.txt"
    val tracepath = "./synthesis-benchmark/" + actualDirName + "/example_traces.txt"
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

    val actualDirName = name
    val actualFileName = if (name == "crowdfunding") "crowfunding" else name
    val datalogpath = "./synthesis-benchmark/" + actualDirName + "/" + actualFileName + ".dl"
    val propertypath = "./synthesis-benchmark/" + actualDirName + "/temporal_properties.txt"
    val solpath = "./test-solidity/" + name + ".sol"
    val ctx = new Context()

    // 1) 初次构建仅用于获取候选规模（生成K用）
    val smForK = Parser.buildStateMachineFromDatalog(name, datalogpath, ctx)
    // 放开数组候选以提升可区分性
    smForK.generate_candidate_guards(List("<", "<=", ">", ">=", "=", "!="), false)
    val selections = GuardCandidateManager.enumerateKRandom(smForK, config.K, config.maxPerTr, config.seed)

    // 1.5) 固定一批“性质见证”正样本轨迹，供所有候选共享
    val smForTrace = Parser.buildStateMachineFromDatalog(name, datalogpath, ctx)
    val propertiesForTrace = Parser.parseTemporalPropertiesBound(smForTrace, propertypath, ctx)
    val trainTracesFixed = TraceGenerator.generateFromProperties(smForTrace, ctx, propertiesForTrace, config.maxTraceLen, perProp = config.perProp)
    val valTracesFixed = trainTracesFixed

    // 2) 针对每个候选，独立构建状态机并进行 CEGIS（带反例迭代）与评分
    var bestScore = -1.0
    var bestSm: Option[StateMachine] = None
    var bestSel: Option[GuardSelection] = None
    var bestNonTrivialGuards: Int = -1

    // 注入阶段使用的合法性过滤，同时用于次级排序的一致性过滤
    def isValidGuardString(s: String): Boolean = {
      val t = s.trim.toLowerCase
      t.nonEmpty && !t.contains("constructor[") && !t.contains("constructor(") && !t.contains("constructor.") && !t.contains("totalbalance")
    }

    // 过滤与优先级工具（基于字符串启发式）
    def dropBadGuard(e: Expr[BoolSort]): Boolean = {
      val s = e.toString.toLowerCase
      s.contains("totalbalance") || (s.contains("select") && s.contains("constructor"))
    }
    def priorityScoreStr(s0: String): Int = {
      val s = s0.toLowerCase
      var score = 0
      if (s.contains("raised") && s.contains("target")) {
        if (s.contains("bvult") || s.contains("<")) score += 5
        if (s.contains("bvuge") || s.contains(">=")) score += 5
        if (s.contains("bvugt") || s.contains(">")) score += 3
      }
      if (s.contains("beneficiary") && (s.contains("msgsender") || s.contains("msg.sender"))) score += 3
      if (s.contains("balanceof") && (s.contains("msgsender") || s.contains("msg.sender"))) score += 3
      if (s.contains("closed")) score += 2
      score
    }
    def prioritizeGuards(lst: List[Expr[BoolSort]]): List[Expr[BoolSort]] = {
      val kept = lst.filterNot(dropBadGuard)
      kept.sortBy(e => -priorityScoreStr(e.toString))
    }

    selections.foreach { sel =>
      // 构建独立实例（与轨迹及属性绑定）
      val sm = Parser.buildStateMachineFromDatalog(name, datalogpath, ctx)
      val properties = Parser.parseTemporalPropertiesBound(sm, propertypath, ctx)
      // 放开数组候选以提升可区分性
      val allCandidates: Map[String, List[Expr[BoolSort]]] = sm.generate_candidate_guards(List("<", "<=", ">", ">=", "=", "!="), false)

      // 过滤候选为本次选择的子集（按索引）
      val filtered: Map[String, List[Expr[BoolSort]]] = sm.transitions.map { tr =>
        val chosenIdx = sel.selection.getOrElse(tr, List())
        val full = allCandidates.getOrElse(tr, List())
        val lst = chosenIdx.flatMap(i => if (i >= 0 && i < full.length) Some(full(i)) else None)
        tr -> lst
      }.toMap

      // 使用随机轨迹（回退）
      val trainTraces = TraceGenerator.generate(sm, ctx, config.trainTraces, config.maxTraceLen, config.seed)
      val valTraces = TraceGenerator.generate(sm, ctx, config.valTraces, config.maxTraceLen, config.seed + 1)

      // 3) 运行 CEGIS：会自动将反例加入 neg 并继续迭代
      sm.cegis(properties, trainTraces, filtered, array = false)

      // 4) 评分
      val eval = Evaluator.evaluate(sm, ctx, properties, valTraces)
      // 计算当前候选的非平凡守卫数量（与注入阶段过滤一致）
      val curNonTrivial: Int = sm.getSolidityGuardsByFunction().values.map(_.count(isValidGuardString)).sum

      if (eval.passRate > bestScore) {
        bestScore = eval.passRate
        bestSel = Some(sel)
        bestSm = Some(sm)
        bestNonTrivialGuards = curNonTrivial
      } else if (eval.passRate == bestScore && curNonTrivial > bestNonTrivialGuards) {
        // 次级排序：在分数相等时，优先非平凡守卫数量多者
        bestSel = Some(sel)
        bestSm = Some(sm)
        bestNonTrivialGuards = curNonTrivial
      }
    }

    // 3) 对最佳候选进行最终验证并输出
    bestSm match {
      case Some(sm) =>
        val properties = Parser.parseTemporalPropertiesBound(sm, propertypath, ctx)
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
      case None =>
        println("[SYNTHESIZE V2] No candidate selections were generated.")
    }

    val endTime = System.nanoTime()
    val elapsedTimeMs = (endTime - startTime) / 1e9
  }
}
