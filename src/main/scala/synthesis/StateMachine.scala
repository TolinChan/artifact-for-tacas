package synthesis

import com.microsoft.z3.{ArithSort, ArraySort, BitVecSort, BoolExpr, BoolSort, Context, Expr, IntSort, Sort, Status}
import verification.TransitionSystem
import verification.Z3Helper
import synthesis.BoundedModelChecking
import util.Misc.parseProgram
import verification.Verifier._
import java.io._
import scala.collection.mutable
import datalog.Program
import imp.ImperativeTranslator

/**
 * StateMachine - A CEGIS-based synthesis engine for smart contracts
 * 
 * Core Features:
 * - State variable management (inspired by Python version)
 * - Transition function handling using transferFunc (no ts.tr)
 * - Counter-example guided inductive synthesis (CEGIS)
 * - Bounded model checking for property verification
 * - Solidity code generation
 */
class StateMachine(name: String, ctx: Context) {

  // ===== CORE DATA STRUCTURES =====
  
  // Transition management
  var transitions: List[String] = List()
  val conditionGuards: mutable.Map[String, Expr[BoolSort]] = mutable.Map()
  val candidateConditionGuards: mutable.Map[String, List[Expr[BoolSort]]] = mutable.Map()
  val symbolicGuardVariables: mutable.Map[String, List[Expr[BoolSort]]] = mutable.Map()
  val trParameters: mutable.Map[String, List[Expr[_]]] = mutable.Map()
  val transferFunc: mutable.Map[String, Expr[BoolSort]] = mutable.Map()
  // Candidate generation constants (align with Python: self.constants)
  private var constants: List[Expr[_]] = List()
  def addConstant(e: Expr[_]): Unit = { constants = constants :+ e }
  def addConstants(es: Seq[Expr[_]]): Unit = { constants = constants ++ es }
  
  // State management (inspired by Python version)
  val states: mutable.Map[String, (Expr[_], Expr[_])] = mutable.Map()
  val prevStates: mutable.Map[String, (Expr[_], Expr[_])] = mutable.Map()
  val once: mutable.Map[String, (Expr[_], Expr[_])] = mutable.Map()
  
  // Event mapping for trace processing
  val traceEventMapping: mutable.Map[String, String] = mutable.Map()
  
  // Legacy transition system (only used for init state)
  val ts: TransitionSystem = new TransitionSystem(name, ctx)
  var nowState: Option[Expr[BoolSort]] = None

  // System state variables
  val (now, nowOut): (Expr[BitVecSort], Expr[BitVecSort]) = addState("now", ctx.mkBitVecSort(256)).asInstanceOf[(Expr[BitVecSort], Expr[BitVecSort])]
  val (func, funcOut): (Expr[_], Expr[_]) = addState("func", ctx.mkStringSort())
  
  // ===== STATE MANAGEMENT =====
  
  /**
   * Add a state variable to the state machine
   * Automatically tracks business state variables (inspired by Python version)
   */
  def addState(stateName: String, stateType: Sort): (Expr[_], Expr[_]) = {
    val current = ctx.mkConst(stateName, stateType)
    val next = ctx.mkConst(s"${stateName}_next", stateType)
    
    // Track business state variables (not system variables)
    if (stateName != "func" && !stateName.startsWith("once_") && stateName != "now") {
      states(stateName) = (current, next)
      val prevCurrent = ctx.mkConst(s"prev_$stateName", stateType)
      val prevNext = ctx.mkConst(s"prev_${stateName}_next", stateType)
      prevStates(stateName) = (prevCurrent, prevNext)
    }
    
    (current, next)
  }



  /**
   * Add a transition to the state machine
   * Core method that uses transferFunc (not ts.tr)
   */
  def addTr(trName: String, parameters: List[Expr[_]], guard: Expr[BoolSort], transferFunc: Expr[BoolSort]): Unit = {
    transitions = transitions :+ trName
    once(trName) = addState(s"once_$trName", ctx.mkBoolSort())
    trParameters(trName) = parameters
    conditionGuards(trName) = guard
    candidateConditionGuards(trName) = List()
    
    // Create transfer function with state updates and system constraints
    var newTransferFunc = ctx.mkAnd(
      transferFunc,  // Actual state update logic
      ctx.mkEq(funcOut, ctx.mkString(trName)), 
      ctx.mkEq(once(trName)._2, ctx.mkBool(true))
    )

    // ===== 添加关键的状态约束循环（匹配Python版本第48-53行）=====
    states.foreach { case (stateName, (current, next)) =>
      if (stateName != "now" && stateName != "func") {
        // 添加prev状态约束: prev_state_next == current_state
        // 对应Python: transfer_func = z3.And(transfer_func, self.prev(self.states[state][0])[1] == self.states[state][0])
        val (prevCurrent, prevNext) = prevStates(stateName)
        newTransferFunc = ctx.mkAnd(newTransferFunc, ctx.mkEq(prevNext, current))
        
        // 如果状态变量没有在transferFunc中被修改，添加保持不变约束
        // 对应Python: if not contains(self.states[state][1], transfer_func):
        //             transfer_func = z3.And(transfer_func, self.states[state][1] == self.states[state][0])
        if (!contains(next, transferFunc)) {
          newTransferFunc = ctx.mkAnd(newTransferFunc, ctx.mkEq(next, current))
        }
      }
    }

    // Store in transferFunc (not ts.tr)
    this.transferFunc += (trName -> newTransferFunc)
    
    // // 关键调试输出：新增转移与总数（已静音）
    // println(s"[STATE] Added Transition: $trName (transitions=${transitions.size})")
  }

  /**
   * Update once variables for all transitions
   */
  def addOnce(): Unit = {
    transitions.foreach { tr =>
      once.foreach { case (onceName, onceVal) =>
        // 修复逻辑错误：onceName是"once_trName"格式，需要提取trName进行比较
        // 对应Python版本的逻辑：其他转换的once变量保持不变
        val onceTransitionName = if (onceName.startsWith("once_")) onceName.substring(5) else onceName
        if (onceTransitionName != tr) {
          transferFunc(tr) = ctx.mkAnd(transferFunc(tr), ctx.mkEq(onceVal._2, onceVal._1))
        }
      }
    }
  }

  /**
   * Clear all guards (set to true)
   */
  def clearGuards(): Unit = {
    conditionGuards.keys.foreach { key =>
      conditionGuards(key) = ctx.mkBool(true)
    }
  }

  /**
   * Reset all guards to true (alias of clearGuards for external callers)
   */
  def resetGuards(): Unit = clearGuards()

  /**
   * Apply a selection of candidate guard indices per transition.
   * sel: Map from transition name to list of indices in candidateConditionGuards(tr)
   */
  def applyGuardSelection(sel: Map[String, List[Int]]): Unit = {
    // Start from all-true guards
    clearGuards()
    transitions.foreach { tr =>
      val indices: List[Int] = sel.getOrElse(tr, List())
      val candidates: List[Expr[BoolSort]] = candidateConditionGuards.getOrElse(tr, List())
      val picked: List[Expr[BoolSort]] = indices.flatMap { i =>
        if (i >= 0 && i < candidates.length) Some(candidates(i)) else None
      }
      if (picked.nonEmpty) {
        conditionGuards(tr) = ctx.mkAnd(picked: _*)
      } else {
        conditionGuards(tr) = ctx.mkBool(true)
      }
    }
  }

  /**
   * Change guard condition for a transition
   */
  def changeGuard(trName: String, newGuards: Expr[BoolSort]*): Boolean = {
    if (!transitions.contains(trName)) {
      println(s"Warning: Transition '$trName' not found!")
      false
    } else {
      conditionGuards(trName) = ctx.mkAnd(newGuards: _*)
      true
    }
  }

  /**
   * Add guard conditions to an existing transition
   */
  def addGuard(trName: String, newGuards: Expr[BoolSort]*): Boolean = {
    if (!transitions.contains(trName)) {
      println(s"Warning: Transition '$trName' not found!")
      false
    } else {
      val oldGuard = conditionGuards(trName)
      val allGuards = Seq(oldGuard) ++ newGuards
      val combinedGuard = ctx.mkAnd(allGuards: _*)
      conditionGuards(trName) = combinedGuard

      true
    }
  }

  /**
   * Initialize the state machine with proper ERC20 state variables
   */
  def setInit(initState: Expr[BoolSort]): Unit = {
    var initialState = initState
    
    // Set system variables
    initialState = ctx.mkAnd(initialState, ctx.mkEq(now, ctx.mkBV(0, 256)), ctx.mkEq(func, ctx.mkString("init")))
    
    // Set once variables to false
    once.values.foreach { case (onceVar, _) =>
      initialState = ctx.mkAnd(initialState, ctx.mkEq(onceVar, ctx.mkBool(false)))
    }
    
    ts.setInit(initialState.asInstanceOf[BoolExpr])
  }
  
  // ===== CEGIS SYNTHESIS ALGORITHM =====
  
  /**
   * Execute a single transition
   */
  def transfer(tr_name: String, candidates: Map[String, List[Expr[BoolSort]]], next: List[Expr[BoolSort]], parameters: Expr[BoolSort]*): Option[List[Expr[BoolSort]]] = {
    if (!transitions.contains(tr_name)) {
      return None
    }
    
    val success = ctx.mkAnd(nowState.getOrElse(ctx.mkBool(true)), conditionGuards(tr_name), ctx.mkBVUGT(nowOut, now), ctx.mkAnd(parameters: _*))
    val s = ctx.mkSolver()
    s.add(success)
    val result = s.check()

    if (result == Status.UNSATISFIABLE) {
      None
    } else {
      s.reset()
      s.add(ctx.mkAnd(nowState.getOrElse(ctx.mkBool(true)), transferFunc(tr_name), ctx.mkAnd(parameters: _*)))
      val result2 = s.check()
      val model = s.getModel()
      
      // ===== 状态推进仅绑定业务状态（对齐Python）=====
      var newNowState = ctx.mkBool(true)
      states.values.foreach { case (current, nextVar) =>
        val nextValue = model.eval(nextVar, false)
        newNowState = ctx.mkAnd(newNowState, ctx.mkEq(current, nextValue))
      }
      
      s.reset()
      s.add(newNowState)
      s.add(next.tail: _*)
      val finalCheck = s.check()

      if (finalCheck == Status.SATISFIABLE) {
        val m = s.getModel()
        // Use parsed transition name for key lookup
        val nextHeadExpr = next.head
        val nextHeadStr = nextHeadExpr.toString
        val parsedNextTr = if (nextHeadStr.contains("\"")) nextHeadStr.substring(nextHeadStr.indexOf("\"")+1, nextHeadStr.lastIndexOf("\"")) else nextHeadStr
        val newLine = candidates.getOrElse(parsedNextTr, List()).map(c => m.eval(c, false))
        
        // ===== 更新nowState以保持状态一致性 =====
        // 对应Python版本：状态在转换后需要更新
        nowState = Some(newNowState)
        
        Some(newLine)
      } else {
        println("error")
        None
      }
    }
  }

  /**
   * Simulate a trace through the state machine
   */
  def simulate(trace: List[List[Expr[BoolSort]]], candidates: Map[String, List[Expr[BoolSort]]]): List[List[Expr[BoolSort]]] = {
    var res: List[List[Expr[BoolSort]]] = List()

    
    nowState = Some(ts.getInit())

    // Hold the evaluated candidate booleans for the current step (align Python logic)
    var currentEval: List[Expr[BoolSort]] = List()

    if (trace.nonEmpty && trace.head.nonEmpty) {
      val solver = ctx.mkSolver()
      solver.add(nowState.get)
      solver.add(trace.head.tail: _*)
      if (solver.check() == Status.SATISFIABLE) {
        val model = solver.getModel()
        val headExpr = trace.head.head
        val headStr = headExpr.toString
        val trKey = parseTransitionName(headStr)
        val firstEval = candidates.getOrElse(trKey, List()).map(c => model.eval(c, false))
        currentEval = firstEval.asInstanceOf[List[Expr[BoolSort]]]
      } else {
        currentEval = List()
      }
    }

 
    var i = 0
    while (i < trace.size) {
      if (trace(i).nonEmpty) {
        val raw_tr_name = trace(i).head.toString
        val tr_name = parseTransitionName(raw_tr_name)
        val trExpr = ctx.mkString(tr_name)
        val resLine = List(trExpr.asInstanceOf[Expr[BoolSort]]) ++ currentEval
        res = res :+ resLine

        if (i < trace.size - 1) {
          val nextLine = transfer(tr_name, candidates, trace(i + 1), trace(i).tail: _*)
          // 不做空检查提前返回；空则使用空评估继续
          currentEval = nextLine.getOrElse(List())
        }
      }
      i += 1
    }
    res
  }

  // ===== MODEL CHECKING =====
  
  /**
   * Bounded model checking using transferFunc (not ts.tr)
   */
  def bmc(property: Expr[BoolSort]): Option[List[List[Expr[BoolSort]]]] = {
    // Build combined transition from transferFunc entries
    val allTransitions = transitions.map { tr =>
      val guard = conditionGuards(tr)
      val transfer = transferFunc(tr)
      
      // Create transition: guard AND transfer AND time_increment
      ctx.mkAnd(guard, transfer, ctx.mkBVUGT(nowOut, now))
    }
    
    // 组合所有transitions用OR连接
    val combinedTransition = if (allTransitions.nonEmpty) {
      ctx.mkOr(allTransitions: _*)
    } else {
      ctx.mkBool(false)
    }
    


    // 构建正确的状态变量数组，完全匹配Python版本的顺序
    val stateVars = states.values.map(_._1).toList  // 当前状态变量
    val stateNextVars = states.values.map(_._2).toList  // next状态变量
    val prevStateVars = prevStates.values.map(_._1).toList  // prev状态变量 - 这个之前缺失了！
    val prevStateNextVars = prevStates.values.map(_._2).toList  // prev next状态变量
    val onceVars = once.values.map(_._1).toList  // once变量
    val onceNextVars = once.values.map(_._2).toList  // once next变量
    
    // 构建完整的xs（当前状态）和xns（下一状态）数组，匹配Python版本的顺序：
    // Python: [states] + [prev_states] + [once] + [func] + [now]
    val xs = (stateVars ++ prevStateVars ++ onceVars ++ List(func, now)).toArray
    val xns = (stateNextVars ++ prevStateNextVars ++ onceNextVars ++ List(funcOut, nowOut)).toArray
    
    // 构建自由变量数组（从转换参数中提取），匹配Python版本逻辑
    val fvs = {
      val allFreeVars = mutable.ListBuffer[Expr[_]]()
      trParameters.values.foreach { paramList =>
        if (paramList.nonEmpty) {  // 对应Python的 if p != None
          paramList.foreach { param =>
            allFreeVars += param
          }
        }
      }
      allFreeVars.toArray
    }
    
    // by yyyouch --这里把bmc的7个输入打印出来 如果看不清楚就和python版本对比
    // println(s"[BMC DEBUG] ========== BMC参数调试 ==========")
    // println(s"[BMC DEBUG] 参数1 - ctx: $ctx")
    // println(s"[BMC DEBUG] 参数2 - init: ${ts.getInit()}")
    // println(s"[BMC DEBUG] 参数3 - transition: $combinedTransition")
    // println(s"[BMC DEBUG] 参数4 - property: ${property.asInstanceOf[BoolExpr]}")
    // println(s"[BMC DEBUG] 参数5 - fvs: [${fvs.length}个] ${fvs.take(fvs.length).mkString(", ")}")
    // println(s"[BMC DEBUG] 参数6 - xs: [${xs.length}个] ${xs.take(xs.length).mkString(", ")}")
    // println(s"[BMC DEBUG] 参数7 - xns: [${xns.length}个] ${xns.take(xns.length).mkString(", ")}")
    // println(s"[BMC DEBUG] Python版本对比: bmc(init, tr, property, fvs, xs, xns) - 6个参数")
    // println(s"[BMC DEBUG] ===================================")
    
    val model = BoundedModelChecking.bmc(ctx, ts.getInit(), combinedTransition, property.asInstanceOf[BoolExpr], fvs, xs, xns)
    
    // by yyyouch --把model和提取出来的trace都打印出来
    // println(s"[BMC DEBUG] BMC返回的模型: ${if(model.nonEmpty) s"找到模型，长度=${model.length}" else "未找到模型"}")
    model match {
      case m if m.nonEmpty =>
        // Generate trace from BMC model - 匹配Python版本的简洁逻辑
        var firstInvalidFuncLogged = false
        val trace = if (m.length >= 2) {
          (1 until m.length - 1).flatMap { i =>
            val funcValue = m(i).getOrElse("func", ctx.mkString(""))
            val nowValue = m(i).getOrElse("now", now)
            val funcStr = funcValue.toString
            // 过滤 constructor 和 init 步骤
            if (funcStr.isEmpty || funcStr == "\"\"" || funcStr.contains("init") || funcStr.toLowerCase.contains("constructor")) {
              if (!firstInvalidFuncLogged) {
                val prevFuncStr = if (i-1 >= 0) m(i-1).getOrElse("func", ctx.mkString("")) else ctx.mkString("")
                val prevNowStr = if (i-1 >= 0) m(i-1).getOrElse("now", now) else now
                // println(s"[BMC] first-invalid-func step=${i} prev.func=${prevFuncStr.toString} prev.now=${prevNowStr.toString}")
                firstInvalidFuncLogged = true
              }
              None
            } else {
              val trName = funcStr.replace("\"", "")
              val stepBase: List[Expr[BoolSort]] = List(funcValue.asInstanceOf[Expr[BoolSort]], ctx.mkEq(nowOut, nowValue))
              // Debug: available keys in current model step
              // val stepKeys = m(i).keys.mkString(", ")
              // println(s"[BMC] Step $i func=$trName keys: $stepKeys")
              // 参数等式补齐：优先用第i轮值，缺失则用i-1轮
              val paramConds: List[Expr[BoolSort]] = trParameters.getOrElse(trName, List()).flatMap { p =>
                val key = BoundedModelChecking.pureName(p.toString)
                val currVal = m(i).get(key)
                val prevVal = if (i-1 >= 0) m(i-1).get(key) else None
                // println(s"[BMC] Step $i param ${p.toString} key=$key curr=${currVal.map(_.toString).getOrElse("NA")} prev=${prevVal.map(_.toString).getOrElse("NA")}")
                val chosen = currVal.orElse(prevVal)
                chosen.map(v => ctx.mkEq(p.asInstanceOf[Expr[Sort]], v.asInstanceOf[Expr[Sort]]).asInstanceOf[Expr[BoolSort]])
              }
              // println(s"[BMC] Step $i param conditions added: ${paramConds.length}")
              Some(stepBase ++ paramConds)
            }
          }.toList
        } else if (m.nonEmpty) {
          val funcValue = m(0).getOrElse("func", ctx.mkString(""))
          val nowValue = m(0).getOrElse("now", now)
          val funcStr = funcValue.toString
          // 过滤 constructor 和 init
          if (funcStr.isEmpty || funcStr == "\"\"" || funcStr.contains("init") || funcStr.toLowerCase.contains("constructor")) {
            List()
          } else {
            val trName = funcStr.replace("\"", "")
            // val stepKeys = m(0).keys.mkString(", ")
            // println(s"[BMC] Step 0 func=$trName keys: $stepKeys")
            List(List(funcValue.asInstanceOf[Expr[BoolSort]], ctx.mkEq(nowOut, nowValue)))
          }
        } else {
          List()
        }
        Some(trace)
      case _ =>
        None
    }
  }

  /**
   * Generate candidate guard conditions
   */
  def generate_candidate_guards(predicates: List[String], array: Boolean): Map[String, List[Expr[BoolSort]]] = {
    var candidateGuards: Map[String, List[Expr[BoolSort]]] = Map()

    // Heuristics to restrict semantically invalid candidates in crowdfunding-like contracts
    def isAddressLikeName(s: String): Boolean = {
      val l = s.toLowerCase
      l.contains("owner") || l.contains("beneficiary") || l.contains("sender")
    }
    def isNumericLikeName(s: String): Boolean = {
      val l = s.toLowerCase
      l.contains("raised") || l.contains("target") || l.contains("totalbalance") || l.contains("msgvalue") || l.contains("select")
    }
    def expectsAddressKey(arrayName: String): Boolean = {
      val l = arrayName.toLowerCase
      // Common mappings keyed by address in these benchmarks
      l.contains("balanceof") || l.contains("invest") || l.contains("refund") || l.contains("withdraw")
    }

    // Helper to check numeric sorts (BitVec or Int)
    def isNumeric(e: Expr[_]): Boolean = e.getSort.isInstanceOf[BitVecSort] || e.getSort.isInstanceOf[IntSort]

    // Build base pool per transition: constants ++ business state currents ++ parameters ++ nowOut
    transitions.foreach { tr =>
      candidateGuards += tr -> List()

      val businessStateCurrents: List[Expr[_]] = states.values.map(_._1).toList
      var pool: List[Expr[_]] = businessStateCurrents ++ constants ++ trParameters.getOrElse(tr, List()) ++ List(nowOut)

      // Debug: print pool composition before enumeration
        // println(s"[GUARDS] '$tr' pool pre-enum: states=${businessStateCurrents.length}, params=${trParameters.getOrElse(tr, List()).length}, consts=${constants.length}")

      // 修复：分离常量和数组索引
      // 首先确保状态变量与常量的直接比较被优先生成
      val directConstants = constants.filter(!isArray(_))
      val stateVariables = businessStateCurrents.filter(!isArray(_))
      
      // println(s"[GUARDS] directConsts=${directConstants.length}, stateVars=${stateVariables.length}")
      
      // 不做重复追加，避免产生重复元素；仅输出快照信息（已静音）
      // println(s"[CANDIDATE FIX] Pool snapshot: ${pool.map(_.toString).take(10).mkString(", ")}...")
      // println(s"[CANDIDATE FIX] Pool size: ${pool.length}")
      
      // Array element enumeration: 与Python版本完全一致，不过滤大常量索引
      if (array) {
        val arrays = pool.filter(isArray)
        // 对齐Python：仅排除now'，不过滤大常量（如GOAL, CLOSETIME）
        val validIndicesBase = pool.filter(isNumeric).filter { idx =>
          idx.toString != nowOut.toString
        }

        val enumerated: List[Expr[_]] = arrays.flatMap { a =>
          val arrSort = a.getSort.asInstanceOf[ArraySort[Sort, Sort]]
          val arrName = a.toString
          // 索引过滤：
          // - 若数组按地址索引，仅允许 owner/beneficiary/sender 等地址样式；
          // - 否则禁止使用地址样式索引；
          val validIndices = if (expectsAddressKey(arrName)) {
            validIndicesBase.filter(e => isAddressLikeName(e.toString))
          } else {
            validIndicesBase.filter(e => !isAddressLikeName(e.toString))
          }

          validIndices.flatMap { idx =>
            try {
              if (idx.getSort == arrSort.getDomain && !idx.toString.equals(nowOut.toString)) {
                val sel = ctx.mkSelect(a.asInstanceOf[Expr[ArraySort[Sort, Sort]]], idx.asInstanceOf[Expr[Sort]])
                Some(sel.asInstanceOf[Expr[_]])
              } else None
            } catch { case _: Throwable => None }
          }
        }
        pool = pool ++ enumerated
        // println(s"[GUARDS] '$tr': arrays enumerated=${enumerated.length}")
      }

      // Add boolean vars and their negation
      var boolAdded = 0
      pool.foreach { e =>
        if (isBool(e)) {
          val be = e.asInstanceOf[Expr[BoolSort]]
          candidateGuards += tr -> (candidateGuards(tr) ++ List(be, ctx.mkNot(be)))
          boolAdded += 2
        }
      }
      // println(s"[GUARDS] '$tr': bool guards added=$boolAdded")

      // Add binary predicates between non-array, same-sort pairs
      val poolArr = pool.toArray
      val constantsSetStr = constants.map(_.toString).toSet
      def isLiteralConstantStr(s: String): Boolean = constantsSetStr.contains(s) || s.startsWith("#x") || s.forall(_.isDigit)
      var binAdded = 0
      for (i <- poolArr.indices; j <- i + 1 until poolArr.length) {
        val ls = poolArr(i)
        val rs = poolArr(j)
        if (!isArray(ls) && !isArray(rs) && !isBool(rs) && ls.getSort == rs.getSort) {
          val lsStr = ls.toString
          val rsStr = rs.toString
          val leftIsAddr  = isAddressLikeName(lsStr)
          val rightIsAddr = isAddressLikeName(rsStr)
          val leftIsNum   = isNumericLikeName(lsStr)
          val rightIsNum  = isNumericLikeName(rsStr)
          val involvingAddress = leftIsAddr || rightIsAddr
          val mixedAddrNumeric = (leftIsAddr && rightIsNum) || (rightIsAddr && leftIsNum)

          // 通用过滤：跳过常量-常量比较
          if (!(isLiteralConstantStr(lsStr) && isLiteralConstantStr(rsStr))) {
            predicates.foreach { predicate =>
              try {
                // 语义过滤：
                // - 地址参与的比较仅允许 == / !=；
                // - 地址与数值混合的比较全部跳过；
                if (mixedAddrNumeric) {
                  // skip
                } else if (involvingAddress && (predicate != "=" && predicate != "!=")) {
                  // skip non-equality ops on addresses
                } else {
                  val guard: Expr[BoolSort] = (predicate, ls.getSort) match {
                    case ("<", s: BitVecSort) => ctx.mkBVULT(ls.asInstanceOf[Expr[BitVecSort]], rs.asInstanceOf[Expr[BitVecSort]])
                    case ("<", _: Sort)       => ctx.mkLt(ls.asInstanceOf[Expr[IntSort]], rs.asInstanceOf[Expr[IntSort]])
                    case ("<=", s: BitVecSort) => ctx.mkBVULE(ls.asInstanceOf[Expr[BitVecSort]], rs.asInstanceOf[Expr[BitVecSort]])
                    case ("<=", _: Sort)       => ctx.mkLe(ls.asInstanceOf[Expr[IntSort]], rs.asInstanceOf[Expr[IntSort]])
                    case (">", s: BitVecSort) => ctx.mkBVUGT(ls.asInstanceOf[Expr[BitVecSort]], rs.asInstanceOf[Expr[BitVecSort]])
                    case (">", _: Sort)       => ctx.mkGt(ls.asInstanceOf[Expr[IntSort]], rs.asInstanceOf[Expr[IntSort]])
                    case (">=", s: BitVecSort) => ctx.mkBVUGE(ls.asInstanceOf[Expr[BitVecSort]], rs.asInstanceOf[Expr[BitVecSort]])
                    case (">=", _: Sort)       => ctx.mkGe(ls.asInstanceOf[Expr[IntSort]], rs.asInstanceOf[Expr[IntSort]])
                    case ("=", _)             => ctx.mkEq(ls.asInstanceOf[Expr[_]], rs.asInstanceOf[Expr[_]]).asInstanceOf[Expr[BoolSort]]
                    case ("!=", _)            => ctx.mkNot(ctx.mkEq(ls.asInstanceOf[Expr[_]], rs.asInstanceOf[Expr[_]])).asInstanceOf[Expr[BoolSort]]
                    case _                      => ctx.mkBool(true)
                  }
                  candidateGuards += tr -> (candidateGuards(tr) :+ guard)
                  binAdded += 1
                }
              } catch { case _: Throwable => () }
            }
          }
        }
      }
      // println(s"[GUARDS] '$tr': binary added=$binAdded total=${candidateGuards(tr).size}")

      // 关键变量优先候选：针对常见众包合约
      try {
        val maybeRaised = states.get("raised").map(_._1)
        val maybeTarget = states.get("target").map(_._1)
        val maybeClosed = states.get("closed").map(_._1)
        val maybeBeneficiary = states.get("beneficiary").map(_._1)
        val maybeMsgSender = states.get("msgSender").map(_._1)
        val maybeBalanceOf = states.get("balanceOf").map(_._1)
        val hasRaisedTarget = maybeRaised.nonEmpty && maybeTarget.nonEmpty
        if (hasRaisedTarget) {
          val r = maybeRaised.get.asInstanceOf[Expr[BitVecSort]]
          val t = maybeTarget.get.asInstanceOf[Expr[BitVecSort]]
          val specials: List[Expr[BoolSort]] = List(
            ctx.mkBVULT(r, t),
            ctx.mkBVULE(r, t),
            ctx.mkBVUGT(r, t),
            ctx.mkBVUGE(r, t),
            ctx.mkEq(r, t).asInstanceOf[Expr[BoolSort]]
          )
          candidateGuards += tr -> (candidateGuards(tr) ++ specials)
        }

        // nowOut > closeTime: 如果 closeTime 存在于常量池，尝试加入
        val closeConstOpt = constants.find(c => c.getSort.isInstanceOf[BitVecSort] && (c.toString == "#x00000000000000000000000000000000000000000000000000000000000f423f" || c.toString.contains("998877")))
        if (closeConstOpt.nonEmpty) {
          val ct = closeConstOpt.get.asInstanceOf[Expr[BitVecSort]]
          candidateGuards += tr -> (candidateGuards(tr) :+ ctx.mkBVUGT(nowOut.asInstanceOf[Expr[BitVecSort]], ct))
        }

        // closed 布尔为真/假
        maybeClosed.foreach { c =>
          if (isBool(c)) {
            val cb = c.asInstanceOf[Expr[BoolSort]]
            candidateGuards += tr -> (candidateGuards(tr) ++ List(cb, ctx.mkNot(cb)))
          }
        }

        // 领域模板：beneficiary == msgSender
        if (maybeBeneficiary.nonEmpty && maybeMsgSender.nonEmpty) {
          val b = maybeBeneficiary.get
          val s = maybeMsgSender.get
          if (b.getSort == s.getSort) {
            val eq = ctx.mkEq(b.asInstanceOf[Expr[_]], s.asInstanceOf[Expr[_]]).asInstanceOf[Expr[BoolSort]]
            candidateGuards += tr -> (candidateGuards(tr) :+ eq)
          }
        }

        // 领域模板：balanceOf[msgSender] > 0 / != 0
        if (maybeBalanceOf.nonEmpty && maybeMsgSender.nonEmpty && isArray(maybeBalanceOf.get)) {
          val arr = maybeBalanceOf.get.asInstanceOf[Expr[ArraySort[Sort, Sort]]]
          val key = maybeMsgSender.get.asInstanceOf[Expr[Sort]]
          // 仅当 key sort 匹配数组域
          val arrSort = arr.getSort.asInstanceOf[ArraySort[Sort, Sort]]
          if (key.getSort == arrSort.getDomain) {
            val sel = ctx.mkSelect(arr, key)
            val valSort = arrSort.getRange
            // > 0 与 != 0 两类
            val guardsFromSelect: List[Expr[BoolSort]] = try {
              val gts: Option[Expr[BoolSort]] =
                if (valSort.isInstanceOf[BitVecSort]) {
                  val bv0 = ctx.mkBV(0, valSort.asInstanceOf[BitVecSort].getSize)
                  Some(ctx.mkBVUGT(sel.asInstanceOf[Expr[BitVecSort]], bv0))
                } else if (valSort.isInstanceOf[IntSort]) {
                  Some(ctx.mkGt(sel.asInstanceOf[Expr[IntSort]], ctx.mkInt(0)))
                } else None
              val ne0: Option[Expr[BoolSort]] =
                if (valSort.isInstanceOf[BitVecSort]) {
                  val bv0 = ctx.mkBV(0, valSort.asInstanceOf[BitVecSort].getSize)
                  Some(ctx.mkNot(ctx.mkEq(sel.asInstanceOf[Expr[BitVecSort]], bv0)))
                } else if (valSort.isInstanceOf[IntSort]) {
                  Some(ctx.mkNot(ctx.mkEq(sel.asInstanceOf[Expr[IntSort]], ctx.mkInt(0))))
                } else None
              (gts.toList ++ ne0.toList)
            } catch { case _: Throwable => List() }
            if (guardsFromSelect.nonEmpty) {
              candidateGuards += tr -> (candidateGuards(tr) ++ guardsFromSelect)
            }
          }
        }

        // 领域模板：totalBalance 与 raised/target 比较（当 totalBalance 存在时）
        val maybeTotalBalance = states.get("totalBalance").map(_._1)
        if (maybeTotalBalance.nonEmpty) {
          try {
            val tb = maybeTotalBalance.get.asInstanceOf[Expr[BitVecSort]]
            states.get("raised").foreach { case (r, _) =>
              val rv = r.asInstanceOf[Expr[BitVecSort]]
              candidateGuards += tr -> (candidateGuards(tr) ++ List(
                ctx.mkBVULT(tb, rv), ctx.mkBVULE(tb, rv), ctx.mkBVUGT(tb, rv), ctx.mkBVUGE(tb, rv)
              ))
            }
            states.get("target").foreach { case (t, _) =>
              val tv = t.asInstanceOf[Expr[BitVecSort]]
              candidateGuards += tr -> (candidateGuards(tr) ++ List(
                ctx.mkBVULT(tb, tv), ctx.mkBVULE(tb, tv), ctx.mkBVUGT(tb, tv), ctx.mkBVUGE(tb, tv)
              ))
            }
          } catch { case _: Throwable => () }
        }
      } catch { case _: Throwable => () }
    }

    // Clear guards before creating symbolic variables (对应Python第255行)
    clearGuards()
    
    // Create symbolic boolean variables for each candidate guard
    transitions.foreach { tr =>
      val candidates = candidateGuards.getOrElse(tr, List())
      val symbolicVars = candidates.indices.map(idx => ctx.mkBoolConst(s"${tr}_guard_$idx")).toList
      symbolicGuardVariables += (tr -> symbolicVars)
      candidateConditionGuards += (tr -> candidates)
    }

    candidateGuards
  }

  /**
   * Synthesis algorithm (Python-style implementation)
   */
  def synthesize(pos: List[List[List[Expr[BoolSort]]]], neg: List[List[List[Expr[BoolSort]]]], candidates: Map[String, List[Expr[BoolSort]]]): Boolean = {
    println(s"Starting synthesis with ${pos.size} positive and ${neg.size} negative traces")
    
    // 参照Python版本的逻辑实现
    val s = ctx.mkSolver()

    // 对齐Python：根据传入的 candidates（可能是筛选子集）重建符号守卫变量，确保索引与 tr_res.tail 对齐
    transitions.foreach { tr =>
      val count = candidates.getOrElse(tr, List()).length
      val symVars: List[Expr[BoolSort]] = (0 until count).map(i => ctx.mkBoolConst(s"${tr}_guard_${i}")).toList
      symbolicGuardVariables += (tr -> symVars)
    }
    
    // 处理正样本 (approvePos) — Python风格：仅使用蕴含 g_i -> r_i
    var approvePos = ctx.mkBool(true)
    pos.foreach { postrace =>
      var approveT = ctx.mkBool(true)
      postrace.foreach { tr_res =>
        if (tr_res.nonEmpty) {
          val trHeadExpr = tr_res.head
          val trHeadStr = trHeadExpr.toString
          val tr = parseTransitionName(trHeadStr)
          val symbolicVarsForTr = symbolicGuardVariables.getOrElse(tr, List())

          var approvetx = ctx.mkBool(true)

          tr_res.tail.zipWithIndex.foreach { case (res, idx) =>
            if (idx < symbolicVarsForTr.length) {
              val g = symbolicVarsForTr(idx)
              approvetx = ctx.mkAnd(approvetx, ctx.mkImplies(g, res))
            }
          }

          approveT = ctx.mkAnd(approveT, approvetx)
        }
      }
      approvePos = ctx.mkAnd(approvePos, approveT)
    }
    
    // 处理负样本 (approveNeg)
    var approveNeg = ctx.mkBool(true)
    neg.zipWithIndex.foreach { case (negtrace, negIdx) =>
      println(s"[SYNTHESIS DEBUG] Processing negative trace $negIdx with ${negtrace.size} steps")
      
      var approveT = ctx.mkBool(true)
      negtrace.zipWithIndex.foreach { case (tr_res, stepIdx) =>
        if (tr_res.nonEmpty) {
          val trHeadExpr = tr_res.head
          val trHeadStr = trHeadExpr.toString
          val tr = parseTransitionName(trHeadStr)
          val resBools = tr_res.tail.map(_.toString)
          val symVarsForTr = symbolicGuardVariables.getOrElse(tr, List())
          
          println(s"[SYNTHESIS DEBUG]   Step $stepIdx: tr='$tr', candidates=${symVarsForTr.size}, results=${tr_res.tail.size}")
          
          var approvetx = ctx.mkBool(true)
          
          tr_res.tail.zipWithIndex.foreach { case (res, idx) =>
            val symbolicVarsForTr = symbolicGuardVariables.getOrElse(tr, List())
            if (idx < symbolicVarsForTr.length) {
              val symbolicVar = symbolicVarsForTr(idx)
              approvetx = ctx.mkAnd(approvetx, ctx.mkImplies(symbolicVar, res))
            }
          }
          approveT = ctx.mkAnd(approveT, approvetx)
        }
      }
      
      // 对齐Python：无条件加入 Not(approveT)
      approveNeg = ctx.mkAnd(approveNeg, ctx.mkNot(approveT))
    }
    

    // 添加约束并求解
    s.add(approvePos)
    s.add(approveNeg)
    val result = s.check()
    
    println(s"[SYNTHESIS] Solver result: $result")
    
    if (result == Status.SATISFIABLE) {
      // 对应Python: self.clear_guards()
      clearGuards()
      
      val model = s.getModel()
      var updatedGuards = 0
      
      // 对应Python: for tr in self.transitions
      transitions.foreach { tr =>
        val candidatesForTr = candidates.getOrElse(tr, List())
        val symbolicVarsForTr = symbolicGuardVariables.getOrElse(tr, List())
        
        // println(s"[SYNTHESIS] Processing '$tr' candidates=${candidatesForTr.size}")
        
        // 对应Python: for c in range(len(candidates[tr]))
        candidatesForTr.zipWithIndex.foreach { case (candidateGuard, idx) =>
          if (idx < symbolicVarsForTr.length) {
            val symbolicVar = symbolicVarsForTr(idx)
            // 对应Python: if m[self.candidate_condition_guards[tr][c]]
            val isTrue = model.eval(symbolicVar, false).isTrue
            if (isTrue) {
              // 对应Python: self.add_guard(tr, candidates[tr][c])
              addGuard(tr, candidateGuard)
              // println(s"[SYNTHESIS] SELECTED tr='$tr' idx=$idx guard='${candidateGuard.toString}'")
              updatedGuards += 1
            } else {
              // 调试：显示被拒绝的候选
              // if (idx < 5) println(s"[SYNTHESIS] REJECTED tr='$tr' idx=$idx guard='${candidateGuard.toString}'")
            }
          }
        }
        
        if (candidatesForTr.nonEmpty && updatedGuards == 0) {
          println(s"[SYNTHESIS] WARNING: no guard selected for '$tr' (candidates=${candidatesForTr.size})")
        }
      }
      if (updatedGuards > 0) {
        println(s"[GUARDS] final selected=$updatedGuards")
        conditionGuards.foreach { case (trName, guard) =>
          val simplified = guard.simplify()
          println(s"[GUARD] $trName: ${simplified.toString}")
        }
      }
      true // synthesis成功
    } else {
      println("No solution found for guard synthesis")
      false // synthesis失败
    }
  }

  /**
   * Main CEGIS loop for counter-example guided inductive synthesis
   */
  def cegis(properties: List[Expr[BoolSort]], positive_traces: List[List[List[Expr[BoolSort]]]], candidate_guard: Map[String, List[Expr[BoolSort]]], array: Boolean = true): Unit = {
    println(s"[CEGIS] start: props=${properties.length}, pos=${positive_traces.length}, tr=${candidate_guard.size}")
    
    var pos = List[List[List[Expr[BoolSort]]]]()
    var neg = List[List[List[Expr[BoolSort]]]]()

    // Simulate positive traces
    positive_traces.foreach { trace =>
      pos :+= simulate(trace, candidate_guard)
    }
    
    println(s"[CEGIS] simulated positive traces: ${pos.length}")
    
    var syn_time = 0.0
    var bmc_time = 0.0
    var iter = 0
    var continue = true
    val MAX_ITERATIONS = 20 // 防止死循环
    
    while (continue && iter < MAX_ITERATIONS) {
      iter += 1
      println(s"[CEGIS] iter=$iter pos=${pos.length} neg=${neg.length}")
            val startTime = System.nanoTime()
   
      val synthesizeSuccess = synthesize(pos, neg, candidate_guard)
      val endTime = System.nanoTime()
      val elapsedTimeMs = (endTime - startTime) / 1e9
      syn_time = syn_time + elapsedTimeMs
      println(s"[CEGIS] synth done in ${elapsedTimeMs} s")
      
      // 如果synthesis失败，直接退出CEGIS
      if (!synthesizeSuccess) {
        println(s"[CEGIS DEBUG] ========== CEGIS综合失败! ==========")
        println(s"[CEGIS DEBUG] 在第 $iter 次迭代中综合失败")
        println(s"[CEGIS DEBUG] 无法找到满足当前约束的保护条件")
        println(s"[CEGIS DEBUG] 总综合时间: ${syn_time}秒")
        println(s"[CEGIS DEBUG] 总BMC时间: ${bmc_time}秒") 
        println(s"[CEGIS DEBUG] =======================================")
        return // 直接退出，不进行BMC验证
      }
      
      var new_ntraces = List[List[List[Expr[BoolSort]]]]()
      val startTime2 = System.nanoTime()
      println(s"[CEGIS] BMC phase ...")
      
      properties.zipWithIndex.foreach { case (p, idx) =>
        println(s"[CEGIS] verify property ${idx + 1}/${properties.length}")
        val ntrace = bmc(ctx.mkNot(p))
        if (ntrace.isEmpty) {
          println(s"[CEGIS] property ${idx + 1} OK")
        } else {
          println(s"[CEGIS] property ${idx + 1} counterexample found")
          new_ntraces = new_ntraces :+ ntrace.get
        }
      }
      
      val endTime2 = System.nanoTime()
      val elapsedTimeMs2 = (endTime2 - startTime2) / 1e9
      bmc_time = bmc_time + elapsedTimeMs2
      println(s"[CEGIS] BMC done in ${elapsedTimeMs2} s")
      
      if (new_ntraces.isEmpty) {
        println(s"[CEGIS] converged at iter=$iter; synth=${syn_time}s bmc=${bmc_time}s")
        continue = false
      } else {
        println(s"[CEGIS] new counterexamples: ${new_ntraces.length}")
        // Update negative traces
        new_ntraces.zipWithIndex.foreach { case (negtrace, idx) =>
          // println(s"[CEGIS] negative trace $idx: len=${negtrace.length}")
          negtrace.zipWithIndex.foreach { case (step, stepIdx) =>
            println(s"[CEGIS DEBUG]     Step $stepIdx: ${step.length} elements - ${step.take(3).map(_.toString).mkString(", ")}...")
          }
          val simulatedTrace = simulate(negtrace, candidate_guard)
          // println(s"[CEGIS] after simulation: ${simulatedTrace.length} steps")
          simulatedTrace.zipWithIndex.foreach { case (step, stepIdx) =>
            println(s"[CEGIS DEBUG]     Simulated step $stepIdx: ${step.length} elements - ${step.take(3).map(_.toString).mkString(", ")}...")
          }
          neg :+= simulatedTrace
        }
      }
    }
    
    if (iter >= MAX_ITERATIONS) {
      println(s"[CEGIS] possible loop: maxIter=$MAX_ITERATIONS pos=${pos.length} neg=${neg.length}")
    }
    
    println(s"[CEGIS] done: iter=$iter synth=${syn_time}s bmc=${bmc_time}s")
  }

  /**
   * Property verification using inductive proof
   */
  def inductive_prove(properties: List[Expr[BoolSort]]): Unit = {
    properties.foreach { property =>
      println(s"Proving property: $property")
      val result = bmc(ctx.mkNot(property))
      if (result.isEmpty) {
        println("Property verified!")
      } else {
        println("Property not verified!")
      }
    }
  }

  // ===== PROGRAM ANALYSIS AND CODE GENERATION =====
  
  /**
   * Main entry point: read Datalog program and build state machine
   */
  def readFromProgram(p: datalog.Program): Unit = {
    Parser.populateStateMachineFromProgram(this, p, ctx)
  }
  
  def extractStateVariables(imperative: imp.ImperativeAbstractProgram): Unit = {
    imperative.relations.foreach { relation =>
      relation match {
        case sr: datalog.SimpleRelation =>
          if (sr.sig.nonEmpty) {
            if (sr.sig.length > 1) {
              // Multi-field relation: create array
              val keyType = Z3Helper.typeToSort(ctx, sr.sig.head)
              val valueType = Z3Helper.typeToSort(ctx, sr.sig.last)
              val arrayType = ctx.mkArraySort(keyType, valueType)
              addState(relation.name, arrayType)
            } else {
              // Single field relation: create single value
              val valueType = Z3Helper.typeToSort(ctx, sr.sig.head)
              addState(relation.name, valueType)
            }
          }
        case sr: datalog.SingletonRelation =>
          if (sr.sig.nonEmpty) {
            val valueType = Z3Helper.typeToSort(ctx, sr.sig.head)
            addState(relation.name, valueType)
          }
        case _ =>
          // Skip other relation types
      }
    }

  }
  
  // 使用Z3Helper.typeToSort替代自定义的getZ3Sort
  
  def extractTransitions(imperative: imp.ImperativeAbstractProgram): Unit = {
    imperative.onStatements.zipWithIndex.foreach { case (onStatement, idx) =>
      val relName = onStatement.relation.name
      val baseName = if (relName.startsWith("recv_")) relName.substring(5) else relName
      // 使用 ruleId 使转移名唯一，避免同名覆盖
      val trName = s"${baseName}_${onStatement.ruleId}"
      val parameters = onStatement.literal.fields.map(field => Z3Helper.paramToConst(ctx, field, "")._1)
      val guard = ctx.mkBool(true) // Default guard
      val transferFunc = try {
        createTransferFunction(onStatement)
      } catch {
        case ex: Throwable =>
          println(s"[DEBUG][extractTransitions] Failed on statement #$idx for relation $relName rule ${onStatement.ruleId}")
          println(s"[DEBUG][extractTransitions] Statement literal: ${onStatement.literal}")
          println(s"[DEBUG][extractTransitions] Statement body: ${onStatement.statement}")
          throw ex
      }
      
      addTr(trName, parameters, guard, transferFunc)
      
      // 建立trace事件映射：
      // 1) 若是 recv_xxx，则直接映射到对应唯一转移
      // 2) 否则，为了让正例轨迹中的 "invest/withdraw/refund/close" 能落到具体唯一转移，
      //    在未设置过映射时，设置一次默认映射到第一次出现的该 baseName 对应转移。
      if (relName.startsWith("recv_")) {
        traceEventMapping += (baseName -> trName)
      } else if (!traceEventMapping.contains(baseName)) {
        traceEventMapping += (baseName -> trName)
      }
    }
    
    // All transitions generated from datalog program only
  }


  
  // 使用Z3Helper.functorToZ3替代自定义的convertConditionToZ3
  private def convertConditionToZ3(condition: imp.Condition): Expr[BoolSort] = {
    // 将imp.Condition转换为datalog.Functor，然后使用Z3Helper
    condition match {
      case imp.True() => ctx.mkBool(true)
      case imp.False() => ctx.mkBool(false)
      case imp.Match(a, b) => {
        val functor = datalog.Equal(a.asInstanceOf[datalog.Arithmetic], b.asInstanceOf[datalog.Arithmetic])
        Z3Helper.functorToZ3(ctx, functor, "")
      }
      case imp.Greater(a, b) => {
        val functor = datalog.Greater(a.asInstanceOf[datalog.Arithmetic], b.asInstanceOf[datalog.Arithmetic])
        Z3Helper.functorToZ3(ctx, functor, "")
      }
      case imp.Lesser(a, b) => {
        val functor = datalog.Lesser(a.asInstanceOf[datalog.Arithmetic], b.asInstanceOf[datalog.Arithmetic])
        Z3Helper.functorToZ3(ctx, functor, "")
      }
      case imp.Geq(a, b) => {
        val functor = datalog.Geq(a.asInstanceOf[datalog.Arithmetic], b.asInstanceOf[datalog.Arithmetic])
        Z3Helper.functorToZ3(ctx, functor, "")
      }
      case imp.Leq(a, b) => {
        val functor = datalog.Leq(a.asInstanceOf[datalog.Arithmetic], b.asInstanceOf[datalog.Arithmetic])
        Z3Helper.functorToZ3(ctx, functor, "")
      }
      case imp.Unequal(a, b) => {
        val functor = datalog.Unequal(a.asInstanceOf[datalog.Arithmetic], b.asInstanceOf[datalog.Arithmetic])
        Z3Helper.functorToZ3(ctx, functor, "")
      }
      case imp.And(a, b) => ctx.mkAnd(convertConditionToZ3(a), convertConditionToZ3(b))
      case imp.Or(a, b) => ctx.mkOr(convertConditionToZ3(a), convertConditionToZ3(b))
      case _ => ctx.mkBool(true) // Default fallback
    }
  }
  
  private def convertMatchRelationFieldToZ3(matchField: imp.MatchRelationField): Expr[BoolSort] = {
    val relation = matchField.relation
    val keys = matchField.keys.map(field => Z3Helper.paramToConst(ctx, field, "")._1)
    val value = Z3Helper.paramToConst(ctx, matchField.p, "")._1

    relation match {
      case sr: datalog.SimpleRelation if sr.sig.nonEmpty =>
        val keyTypes = sr.sig.dropRight(1)
        val valueType = sr.sig.last
        if (keyTypes.isEmpty) {
          val valueSort = Z3Helper.typeToSort(ctx, valueType)
          val stateExpr = ctx.mkConst(relation.name, valueSort)
          ctx.mkEq(stateExpr, value.asInstanceOf[Expr[Sort]])
        } else {
          val arrayExpr = createArrayExpr(relation.name, keyTypes, valueType)
          val selectExpr = nestedSelect(arrayExpr, keyTypes, keys.take(keyTypes.length))
          val valueExpr = value.asInstanceOf[Expr[Sort]]
          val expectedSort = Z3Helper.typeToSort(ctx, valueType)
          if (valueExpr.getSort != expectedSort) {
            println(s"[DEBUG][convertMatchRelationFieldToZ3] Sort mismatch for relation ${relation.name}: expected ${expectedSort}, actual ${valueExpr.getSort}")
          }
          ctx.mkEq(selectExpr.asInstanceOf[Expr[Sort]], valueExpr)
        }

      case sr: datalog.SingletonRelation if sr.sig.nonEmpty =>
        val valueSort = Z3Helper.typeToSort(ctx, sr.sig.head)
        val stateExpr = ctx.mkConst(relation.name, valueSort)
        ctx.mkEq(stateExpr, value.asInstanceOf[Expr[Sort]])

      case _ =>
        ctx.mkBool(true)
    }
  }
  
  // 使用Z3Helper.functorExprToZ3替代自定义的convertArithmeticToZ3
  
  // 使用Z3Helper.paramToConst替代自定义的convertParameterToZ3
  
  private def createTransferFunction(onStatement: imp.OnStatement): Expr[BoolSort] = {
    // Create a transfer function that represents the state change
    // Extract the actual update logic from the statement
    val updateLogic = extractUpdateLogicFromStatement(onStatement.statement)
    
    if (updateLogic.isEmpty) {
      // If no specific update logic found, create a basic transfer function
      // that keeps all states unchanged - 使用TransitionSystem管理状态
      ctx.mkBool(true) // 简化处理，让TransitionSystem处理状态更新
    } else {
      // Combine all update logic with AND
      ctx.mkAnd(updateLogic: _*)
    }
  }
  
  private def extractUpdateLogicFromStatement(statement: imp.Statement): List[Expr[BoolSort]] = {
    statement match {
      case imp.Empty() =>
        List(ctx.mkBool(true))
        
      case imp.Seq(a, b) =>
        extractUpdateLogicFromStatement(a) ++ extractUpdateLogicFromStatement(b)
        
      case imp.If(condition, thenStmt) =>
        val conditionExpr = convertConditionToZ3(condition)
        val thenLogic = extractUpdateLogicFromStatement(thenStmt)
        if (thenLogic.isEmpty) {
          List(ctx.mkBool(true))
        } else {
          // Create implication: condition -> update_logic
          List(ctx.mkImplies(conditionExpr, ctx.mkAnd(thenLogic: _*)))
        }
        
      case imp.Search(relation, conditions, statement) =>
        // Extract conditions and combine with statement logic
        val conditionExprs = conditions.map(convertMatchRelationFieldToZ3).toList
        val statementLogic = extractUpdateLogicFromStatement(statement)
        conditionExprs ++ statementLogic
        
      case imp.Insert(literal) =>
        // Handle insert operation
        List(createInsertLogic(literal))
        
      case imp.Delete(literal) =>
        // Handle delete operation
        List(createDeleteLogic(literal))
        
      case imp.Increment(relation, literal, keyIndices, valueIndex, delta) =>
        // Handle increment operation
        List(createIncrementLogic(relation, literal, keyIndices, valueIndex, delta))
        
      case imp.Assign(param, expr) =>
        // Handle assignment
        List(createAssignmentLogic(param, expr))
        
      case imp.GroundVar(p, relation, keys, valueIndex, enableProjection) =>
        // Handle ground variable assignment
        List(ctx.mkBool(true))
        
      case imp.ReadTuple(relation, keyList, outputVar) =>
        // Handle read tuple operation
        List(ctx.mkBool(true))
        
      case imp.UpdateDependentRelations(update) =>
        // Handle update dependent relations
        extractUpdateLogicFromStatement(update)
        
      case imp.IncrementAndInsert(increment) =>
        // Handle increment and insert operation
        List(createIncrementLogic(increment.relation, increment.literal, increment.keyParams.map(_.name).map(_.toInt), increment.valueIndex, increment.delta))
        
      case imp.Return(p) =>
        // Handle return statement
        List(ctx.mkBool(true))
        
      case _ =>
        // Default case - no specific update logic
        List(ctx.mkBool(true))
    }
  }
  
  private def createInsertLogic(literal: datalog.Literal): Expr[BoolSort] = {
    // Create logic for inserting a tuple
    val relation = literal.relation
    val fields = literal.fields
    
    if (fields.isEmpty) {
      println(s"[DEBUG][createInsertLogic] Relation ${relation.name} has empty fields: literal=${literal}")
      return ctx.mkBool(true)
    }

    relation match {
      case sr: datalog.SimpleRelation if sr.sig.nonEmpty =>
        val keyTypes = sr.sig.dropRight(1)
        val valueType = sr.sig.last
        if (keyTypes.isEmpty) {
          val valueExpr = Z3Helper.paramToConst(ctx, fields.head, "")._1
          val stateExpr = ctx.mkConst(relation.name, Z3Helper.typeToSort(ctx, valueType))
          val stateNextExpr = ctx.mkConst(s"${relation.name}_next", Z3Helper.typeToSort(ctx, valueType))
          ctx.mkEq(stateNextExpr, valueExpr)
        } else {
          val keyExprs = keyTypes.zip(fields.take(keyTypes.length)).map {
            case (_, field) => Z3Helper.paramToConst(ctx, field, "")._1
          }
          val valueExpr = Z3Helper.paramToConst(ctx, fields.last, "")._1
          val arrayExpr = createArrayExpr(relation.name, keyTypes, valueType)
          val arrayNextExpr = createArrayExpr(s"${relation.name}_next", keyTypes, valueType)
          val storeExpr = storeNested(arrayExpr, keyTypes, keyExprs, valueExpr)
          ctx.mkEq(arrayNextExpr.asInstanceOf[Expr[Sort]], storeExpr.asInstanceOf[Expr[Sort]])
        }

      case sr: datalog.SingletonRelation =>
        val valueExpr = Z3Helper.paramToConst(ctx, fields.head, "")._1
        val stateExpr = ctx.mkConst(relation.name, Z3Helper.typeToSort(ctx, sr.sig.head))
        val stateNextExpr = ctx.mkConst(s"${relation.name}_next", Z3Helper.typeToSort(ctx, sr.sig.head))
        ctx.mkEq(stateNextExpr, valueExpr)

      case _ =>
        ctx.mkBool(true) // Default fallback
    }
  }
  
  private def createDeleteLogic(literal: datalog.Literal): Expr[BoolSort] = {
    // Create logic for deleting a tuple
    // For now, return true - can be enhanced later
    ctx.mkBool(true)
  }
  
  private def createIncrementLogic(relation: datalog.Relation, literal: datalog.Literal, 
                                 keyIndices: List[Int], valueIndex: Int, delta: datalog.Arithmetic): Expr[BoolSort] = {
    // Create logic for incrementing a value
    relation match {
      case sr: datalog.SimpleRelation =>
        if (sr.sig.length > 1) {
          // Multi-field relation: increment array value
          val keyExpr = Z3Helper.paramToConst(ctx, literal.fields(keyIndices.head), "")._1
                      val keyType = Z3Helper.typeToSort(ctx, sr.sig(keyIndices.head))
                      val valueType = Z3Helper.typeToSort(ctx, sr.sig(valueIndex))
          val arrayType = ctx.mkArraySort(keyType, valueType)
          val arrayExpr = ctx.mkConst(relation.name, arrayType)
          val arrayNextExpr = ctx.mkConst(s"${relation.name}_next", arrayType)
          
          // Get current value and add delta
          val currentValue = ctx.mkSelect(arrayExpr.asInstanceOf[Expr[ArraySort[Sort, Sort]]], keyExpr.asInstanceOf[Expr[Sort]])
          val deltaExpr = Z3Helper.functorExprToZ3(ctx, delta, "")
          val newValue = ctx.mkAdd(currentValue.asInstanceOf[Expr[ArithSort]], deltaExpr.asInstanceOf[Expr[ArithSort]])
          val storeExpr = ctx.mkStore(arrayExpr.asInstanceOf[Expr[ArraySort[Sort, Sort]]], keyExpr.asInstanceOf[Expr[Sort]], newValue.asInstanceOf[Expr[Sort]])
          ctx.mkEq(arrayNextExpr, storeExpr)
        } else {
          // Single field relation: increment single value
          val currentValue = ctx.mkConst(relation.name, Z3Helper.typeToSort(ctx, sr.sig.head))
          val currentNextValue = ctx.mkConst(s"${relation.name}_next", Z3Helper.typeToSort(ctx, sr.sig.head))
          val deltaExpr = Z3Helper.functorExprToZ3(ctx, delta, "")
          val newValue = ctx.mkAdd(currentValue.asInstanceOf[Expr[ArithSort]], deltaExpr.asInstanceOf[Expr[ArithSort]])
          ctx.mkEq(currentNextValue, newValue)
        }
        
      case _ =>
        ctx.mkBool(true) // Default fallback
    }
  }
  
  private def createAssignmentLogic(param: datalog.Param, expr: datalog.Expr): Expr[BoolSort] = {
    // Create logic for assignment
    val paramExpr = Z3Helper.paramToConst(ctx, param.p, "")._1
    val exprValue = Z3Helper.functorExprToZ3(ctx, expr.asInstanceOf[datalog.Arithmetic], "")
    ctx.mkEq(paramExpr, exprValue)
  }

  private def createArrayExpr(name: String, keyTypes: Seq[datalog.Type], valueType: datalog.Type): Expr[_] = {
    val arraySort = keyTypes.reverse.foldLeft(Z3Helper.typeToSort(ctx, valueType)) { (acc, keyType) =>
      ctx.mkArraySort(Z3Helper.typeToSort(ctx, keyType), acc)
    }
    ctx.mkConst(name, arraySort)
  }

  private def nestedSelect(arrayExpr: Expr[_], keyTypes: Seq[datalog.Type], keyExprs: Seq[Expr[_]]): Expr[_] = {
    var current = arrayExpr
    keyExprs.foreach { keyExpr =>
      current = ctx.mkSelect(current.asInstanceOf[Expr[ArraySort[Sort, Sort]]], keyExpr.asInstanceOf[Expr[Sort]])
    }
    current
  }

  private def storeNested(arrayExpr: Expr[_], keyTypes: Seq[datalog.Type], keyExprs: Seq[Expr[_]], valueExpr: Expr[_]): Expr[_] = {
    def helper(expr: Expr[_], keys: List[Expr[_]]): Expr[_] = keys match {
      case Nil => valueExpr
      case key :: rest =>
        val arr = expr.asInstanceOf[Expr[ArraySort[Sort, Sort]]]
        val stored = ctx.mkStore(arr, key.asInstanceOf[Expr[Sort]], helper(ctx.mkSelect(arr, key.asInstanceOf[Expr[Sort]]), rest).asInstanceOf[Expr[Sort]])
        stored
    }
    helper(arrayExpr, keyExprs.toList)
  }

  // ===== Z3 -> Solidity (minimal) =====
  private def z3ExprToSolidityCondition(expr: Expr[_]): String = {
    val z3String = expr.simplify().toString
    convertZ3ToSolidity(z3String)
  }
  private def convertZ3ToSolidity(z3Expr: String): String = {
    val expr = z3Expr.trim
    if (expr == "true") return "true"

    def stripOuterParens(s: String): String = {
      val t = s.trim
      if (t.startsWith("(") && t.endsWith(")")) {
        var depth = 0
        var i = 0
        var valid = true
        while (i < t.length && valid) {
          val c = t.charAt(i)
          if (c == '(') depth += 1
          else if (c == ')') depth -= 1
          if (depth == 0 && i != t.length - 1) valid = false
          i += 1
        }
        if (valid) t.substring(1, t.length - 1).trim else t
      } else t
    }

    def splitTopLevel(s: String): List[String] = {
      val res = scala.collection.mutable.ListBuffer[String]()
      val sb = new StringBuilder
      var depth = 0
      var i = 0
      while (i < s.length) {
        val c = s.charAt(i)
        c match {
          case '(' =>
            depth += 1
            sb.append(c)
          case ')' =>
            depth -= 1
            sb.append(c)
          case ' ' | '\n' | '\t' | '\r' if depth == 0 =>
            if (sb.nonEmpty) {
              res += sb.toString()
              sb.clear()
            }
          case _ => sb.append(c)
        }
        i += 1
      }
      if (sb.nonEmpty) res += sb.toString()
      res.toList
    }

    def toDecimalIfHex(t: String): String = {
      val x = t.trim
      if (x.startsWith("#x")) {
        try { java.lang.Long.parseUnsignedLong(x.drop(2), 16).toString }
        catch { case _: Throwable => x }
      } else x
    }

    def convertRec(s: String): String = {
      val t = s.trim
      if (t == "true" || t == "false") return t
      if (!t.startsWith("(")) {
        val tok = toDecimalIfHex(t)
        tok match {
          case "target" => return "target.t"
          case "raised" => return "raised.n"
          case "totalBalance" => return "totalBalance.n"
          case "closed" => return "closed.b"
          case "owner" => return "owner.p"
          case "beneficiary" => return "beneficiary.p"
          case "msgSender" => return "msg.sender"
          case "msgValue" => return "msg.value"
          case _ => return tok
        }
      }
      val inner = stripOuterParens(t)
      val parts = splitTopLevel(inner)
      if (parts.isEmpty) return "true"
      val op = parts.head
      val args = parts.tail

      op match {
        case "and" =>
          val items = args.map(convertRec).filter(_ != "true")
          if (items.isEmpty) "true" else items.map(a => s"($a)").mkString(" && ")
        case "or" =>
          val items = args.map(convertRec).filter(_ != "false")
          if (items.isEmpty) "false" else items.map(a => s"($a)").mkString(" || ")
        case "not" => s"!(${convertRec(args.headOption.getOrElse("true"))})"
        case "=" => s"(${convertRec(args.lift(0).getOrElse("true"))} == ${convertRec(args.lift(1).getOrElse("true"))})"
        case "bvult" | "<" => s"(${convertRec(args(0))} < ${convertRec(args(1))})"
        case "bvule" | "<=" => s"(${convertRec(args(0))} <= ${convertRec(args(1))})"
        case "bvugt" | ">" => s"(${convertRec(args(0))} > ${convertRec(args(1))})"
        case "bvuge" | ">=" => s"(${convertRec(args(0))} >= ${convertRec(args(1))})"
        case "bvadd" | "+" =>
          args.map(convertRec) match {
            case a :: b :: Nil => s"(${a} + ${b})"
            case list if list.nonEmpty => list.mkString("(", " + ", ")")
            case _ => "true"
          }
        case "bvsub" | "-" =>
          args.map(convertRec) match {
            case a :: b :: Nil => s"(${a} - ${b})"
            case a :: Nil => s"(-${a})"
            case _ => "true"
          }
        case "bvmul" | "*" =>
          args.map(convertRec) match {
            case a :: b :: Nil => s"(${a} * ${b})"
            case list if list.nonEmpty => list.mkString("(", " * ", ")")
            case _ => "true"
          }
        case "select" => {
          val a0 = convertRec(args(0))
          val a1 = convertRec(args(1))
          if (a0 == "constructor") {
            a1 match {
              case "target" | "target.t" => "target.t"
              case "raised" | "raised.n" => "0"
              case "totalBalance" | "raised.n" => "0"
              case "closed" | "closed.b" => "false"
              case "owner" | "owner.p" => "owner.p"
              case "beneficiary" | "beneficiary.p" => "beneficiary.p"
              case _ => "true"
            }
          } else s"${a0}[${a1}]"
        }
        case _ => "true"
      }
    }

    convertRec(expr)
  }

  // ===== UTILITY METHODS =====
  
  /**
   * Parse transition name from expression string, handling quotes and event formats
   */
  private def parseTransitionName(exprString: String): String = {
    if (exprString.startsWith("\"") && exprString.endsWith("\"")) {
      exprString.substring(1, exprString.length - 1)
    } else if (exprString.contains("(")) {
      exprString.substring(1, exprString.indexOf(" "))
    } else {
      exprString
    }
  }
  
  // contains(x, e): check whether expression e (recursively) contains x (align with Python)
  def contains(x: Expr[_], e: Expr[_]): Boolean = {
    if (x.toString == e.toString) true
    else e.getArgs.exists(arg => contains(x, arg))
  }

  def isBool(expr: Expr[_]): Boolean = {
    expr.getSort.isInstanceOf[BoolSort]
  }

  def isArray(expr: Expr[_]): Boolean = {
    expr.getSort.isInstanceOf[ArraySort[_, _]]
  }

  /**
   * Export synthesized guards grouped by base function name for Solidity injection.
   * baseName is inferred from transition name pattern: <base>_<ruleId>
   * Returns: Map(functionName -> List(solidityGuardString))
   */
  def getSolidityGuardsByFunction(): Map[String, List[String]] = {
    val rawGrouped: scala.collection.mutable.Map[String, List[String]] = scala.collection.mutable.Map()
    val anyTrue: scala.collection.mutable.Set[String] = scala.collection.mutable.Set()
    val anyFalse: scala.collection.mutable.Set[String] = scala.collection.mutable.Set()

    // 收集每个 base 的原始条件，同时标记是否出现过 true/false
    conditionGuards.foreach { case (trName, guardExpr) =>
      val idx = trName.lastIndexOf("_")
      val base = if (idx > 0) trName.substring(0, idx) else trName
      // 先对 Z3 表达式进行化简，再转换为 Solidity 条件字符串，避免出现 !(true) 等平凡式泄漏
      val simplifiedGuard = guardExpr.simplify()
      val condStrRaw = z3ExprToSolidityCondition(simplifiedGuard).trim
      // 归一化以识别被括号包裹的平凡条件
      def stripOuterParensSafe(s: String): String = {
        val t = s.trim
        if (t.length >= 2 && t.head == '(' && t.last == ')') {
          var depth = 0
          var i = 0
          var ok = true
          while (i < t.length && ok) {
            val c = t.charAt(i)
            if (c == '(') depth += 1
            else if (c == ')') depth -= 1
            if (depth == 0 && i != t.length - 1) ok = false
            i += 1
          }
          if (ok) t.substring(1, t.length - 1).trim else t
        } else t
      }
      var prev = condStrRaw
      var curr = stripOuterParensSafe(prev)
      while (curr != prev) { prev = curr; curr = stripOuterParensSafe(prev) }
      val condStr = curr
      if (condStr == "true") anyTrue += base
      else if (condStr == "false") anyFalse += base
      else if (condStr.nonEmpty) {
        val prev = rawGrouped.getOrElse(base, List())
        rawGrouped(base) = prev :+ condStr
      }
    }

    // 生成最终映射：
    // - 若某 base 有非平凡条件，使用它们（OR 拼接由注入逻辑完成）
    // - 否则若有 true，则不注入 require（视作无条件允许）
    // - 否则若全为 false 或为空，也不注入（避免 require(false) 锁死函数）
    rawGrouped.toMap
  }
}