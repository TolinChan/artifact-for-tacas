package synthesis

import com.microsoft.z3._

object ManualStateMachine {
  
  /**
   * 手动构建crowdfunding合约的状态机
   * 参考: /home/youch/tolin/smart_contract_synthesis/input/crowdfunding.py
   */
  def buildCrowdfundingStateMachine(stateMachine: StateMachine, ctx: Context): Unit = {
    println("[DEBUG] 开始手动构建crowdfunding状态机...")
    
    // 常量定义 - 参考Python版本
    val GOAL = 10000
    val CLOSETIME = 998877
    val OPEN = 0
    val SUCCESS = 1 
    val REFUND = 2
    
    // 注意：与Python版本一致，将业务常量注入状态机常量池（供候选守卫生成使用）
    println(s"[DEBUG] 使用常量: GOAL=$GOAL, CLOSETIME=$CLOSETIME")
    
    // 添加状态变量 - 参考Python版本
    val (state, stateOut) = stateMachine.addState("state", ctx.mkBitVecSort(2))
    val (deposits, depositsOut) = stateMachine.addState("deposits", 
      ctx.mkArraySort(ctx.mkBitVecSort(256), ctx.mkBitVecSort(256)))
    val (totalDeposits, totalDepositsOut) = stateMachine.addState("totalDeposits", ctx.mkBitVecSort(256))
    val (raised, raisedOut) = stateMachine.addState("raised", ctx.mkBitVecSort(256))
    
    println("[DEBUG] 添加状态变量: state, deposits, totalDeposits, raised")
    
    // 参数变量定义
    val sender = ctx.mkBVConst("sender", 256)
    val value = ctx.mkBVConst("amount", 256)  
    val p = ctx.mkBVConst("p", 256)
    
    // 创建常量表达式并注入到状态机
    val goalExpr = ctx.mkBV(GOAL, 256)
    val closetimeExpr = ctx.mkBV(CLOSETIME, 256)
    val openExpr = ctx.mkBV(OPEN, 2)
    val successExpr = ctx.mkBV(SUCCESS, 2)
    val refundExpr = ctx.mkBV(REFUND, 2)
    stateMachine.addConstants(Seq(goalExpr, closetimeExpr, openExpr, successExpr, refundExpr))
    
    // 添加转换 1: invest
    stateMachine.addTr(
      "invest",
      List(value, sender),
      ctx.mkAnd(
        // guard: raised < GOAL (Python版本的条件)
        ctx.mkBVULT(raised.asInstanceOf[BitVecExpr], goalExpr)
      ),
      ctx.mkAnd(
        // transfer_func: 更新raised, deposits, totalDeposits
        ctx.mkEq(raisedOut, ctx.mkBVAdd(raised.asInstanceOf[BitVecExpr], value)),
        ctx.mkEq(depositsOut, ctx.mkStore(deposits.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], 
          sender, ctx.mkBVAdd(ctx.mkSelect(deposits.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], sender).asInstanceOf[BitVecExpr], value))),
        ctx.mkEq(totalDepositsOut, ctx.mkBVAdd(totalDeposits.asInstanceOf[BitVecExpr], value))
      )
    )
    
    // 添加转换 2: close_success  
    stateMachine.addTr(
      "close_success",
      List(),
      ctx.mkAnd(
        // guard: raised >= GOAL
        ctx.mkBVUGE(raised.asInstanceOf[BitVecExpr], goalExpr)
      ),
      ctx.mkAnd(
        // transfer_func: state = SUCCESS
        ctx.mkEq(stateOut, successExpr)
      )
    )
    
    // 添加转换 3: close_refund
    stateMachine.addTr(
      "close_refund", 
      List(),
      ctx.mkAnd(
        // guard: now > CLOSETIME && raised < GOAL
        ctx.mkBVUGT(stateMachine.nowOut, closetimeExpr),
        ctx.mkBVULT(raised.asInstanceOf[BitVecExpr], goalExpr)
      ),
      ctx.mkAnd(
        // transfer_func: state = REFUND
        ctx.mkEq(stateOut, refundExpr)
      )
    )
    
    // 添加转换 4: claimrefund
    stateMachine.addTr(
      "claimrefund",
      List(p),
      ctx.mkAnd(
        // guard: state == REFUND && raised < GOAL
        ctx.mkEq(state, refundExpr),
        ctx.mkBVULT(raised.asInstanceOf[BitVecExpr], goalExpr)
      ),
      ctx.mkAnd(
        // transfer_func: deposits[p] = 0, totalDeposits -= deposits[p]
        ctx.mkEq(depositsOut, ctx.mkStore(deposits.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], p, ctx.mkBV(0, 256))),
        ctx.mkEq(totalDepositsOut, 
          ctx.mkBVSub(totalDeposits.asInstanceOf[BitVecExpr], 
            ctx.mkSelect(deposits.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], p).asInstanceOf[BitVecExpr]))
      )
    )
    
    // 添加转换 5: withdraw
    stateMachine.addTr(
      "withdraw",
      List(),
      ctx.mkAnd(
        // guard: state == SUCCESS
        ctx.mkEq(state, successExpr)
      ),
      ctx.mkAnd(
        // transfer_func: totalDeposits = 0
        ctx.mkEq(totalDepositsOut, ctx.mkBV(0, 256))
      )
    )
    
    println("[DEBUG] 添加了5个转换: invest, close_success, close_refund, claimrefund, withdraw")
    
    // 调用addOnce() - 参考Python版本
    stateMachine.addOnce()
    
    // 设置初始状态 - 参考Python版本
    val pForAll = ctx.mkBVConst("p_init", 256)
    val initCondition = ctx.mkAnd(
      // ForAll p: deposits[p] == 0
      ctx.mkForall(Array(pForAll), 
        ctx.mkEq(ctx.mkSelect(deposits.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], pForAll), ctx.mkBV(0, 256)),
        1, null, null, null, null),
      // raised == 0
      ctx.mkEq(raised, ctx.mkBV(0, 256)),
      // totalDeposits == 0  
      ctx.mkEq(totalDeposits, ctx.mkBV(0, 256)),
      // state == OPEN
      ctx.mkEq(state, openExpr)
    )
    
    stateMachine.setInit(initCondition)
    
    println("[DEBUG] 设置初始状态: deposits全为0, raised=0, totalDeposits=0, state=OPEN")
    
    // 设置属性 - 参考Python版本第109-114行
    println("[DEBUG] 设置安全属性...")
    setProperties(stateMachine, ctx, state, raised)
    
    println("[DEBUG] crowdfunding状态机构建完成！")
  }
  
  /**
   * 构建crowdfunding的属性列表
   * 参考Python版本第109-114行
   */
  def buildCrowdfundingProperties(ctx: Context): List[Expr[BoolSort]] = {
    println("[DEBUG] 开始构建crowdfunding属性...")
    
    // 属性1: r2 = Not(And(once('withdraw'), once('claimrefund')))
    // 意思：withdraw和claimrefund不能同时发生
    val onceWithdraw = ctx.mkBoolConst("once_withdraw") 
    val onceClaimrefund = ctx.mkBoolConst("once_claimrefund")
    val r2 = ctx.mkNot(ctx.mkAnd(onceWithdraw, onceClaimrefund))
    
    // 属性2: r3 = Implies(prev(raised) >= GOAL, Not(func("invest")))
    // 意思：如果之前已经达到目标，就不能再投资
    val GOAL = 10000
    val goalExpr = ctx.mkBV(GOAL, 256)
    val prevRaised = ctx.mkBVConst("prev_raised", 256)
    val funcVar = ctx.mkConst("func", ctx.mkStringSort())
    val r3 = ctx.mkImplies(
      ctx.mkBVUGE(prevRaised, goalExpr),
      ctx.mkNot(ctx.mkEq(funcVar, ctx.mkString("invest")))
    )
    
    println(s"[DEBUG] 构建了2个属性：withdraw和claimrefund互斥，达到目标后不能投资")
    List(r2, r3)
  }
  
  /**
   * 构建crowdfunding的正例轨迹
   * 参考Python版本第116-170行
   */
  def buildCrowdfundingTraces(ctx: Context): List[List[List[Expr[BoolSort]]]] = {
    println("[DEBUG] 开始构建crowdfunding正例轨迹...")
    
    val GOAL = 10000
    val CLOSETIME = 998877
    
    // 轨迹1：多次投资 (Python第118-127行)
    val trace1 = List(
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("invest")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(1, 256)),
        ctx.mkEq(ctx.mkBVConst("sender", 256), ctx.mkBV(0x114514L, 256)),
        ctx.mkEq(ctx.mkBVConst("amount", 256), ctx.mkBV(100, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("invest")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(2, 256)),
        ctx.mkEq(ctx.mkBVConst("sender", 256), ctx.mkBV(0x114515L, 256)),
        ctx.mkEq(ctx.mkBVConst("amount", 256), ctx.mkBV(100, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("invest")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(3, 256)),
        ctx.mkEq(ctx.mkBVConst("sender", 256), ctx.mkBV(0x114516L, 256)),
        ctx.mkEq(ctx.mkBVConst("amount", 256), ctx.mkBV(100, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("invest")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(12224, 256)),
        ctx.mkEq(ctx.mkBVConst("sender", 256), ctx.mkBV(0x114517L, 256)),
        ctx.mkEq(ctx.mkBVConst("amount", 256), ctx.mkBV(100, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("invest")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(22225, 256)),
        ctx.mkEq(ctx.mkBVConst("sender", 256), ctx.mkBV(0x114518L, 256)),
        ctx.mkEq(ctx.mkBVConst("amount", 256), ctx.mkBV(100, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("invest")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(33336, 256)),
        ctx.mkEq(ctx.mkBVConst("sender", 256), ctx.mkBV(0x114519L, 256)),
        ctx.mkEq(ctx.mkBVConst("amount", 256), ctx.mkBV(100, 256))
      )
    )
    
    // 轨迹2：成功投资并提取 (Python第129-136行)
    val trace2 = List(
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("invest")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(1, 256)),
        ctx.mkEq(ctx.mkBVConst("sender", 256), ctx.mkBV(0x114514L, 256)),
        ctx.mkEq(ctx.mkBVConst("amount", 256), ctx.mkBV(100, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("invest")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(2, 256)),
        ctx.mkEq(ctx.mkBVConst("sender", 256), ctx.mkBV(0x114515L, 256)),
        ctx.mkEq(ctx.mkBVConst("amount", 256), ctx.mkBV(GOAL, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("close_success")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(3, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("withdraw")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(4, 256))
      )
    )
    
    // 轨迹3：延时成功提取 (Python第137-144行)
    val trace3 = List(
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("invest")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(1, 256)),
        ctx.mkEq(ctx.mkBVConst("sender", 256), ctx.mkBV(0x114514L, 256)),
        ctx.mkEq(ctx.mkBVConst("amount", 256), ctx.mkBV(100, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("invest")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(2, 256)),
        ctx.mkEq(ctx.mkBVConst("sender", 256), ctx.mkBV(0x114515L, 256)),
        ctx.mkEq(ctx.mkBVConst("amount", 256), ctx.mkBV(GOAL, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("close_success")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(11200, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("withdraw")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(11234, 256))
      )
    )
    
    // 轨迹4：超时后成功 (Python第146-153行)
    val trace4 = List(
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("invest")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(1, 256)),
        ctx.mkEq(ctx.mkBVConst("sender", 256), ctx.mkBV(0x114514L, 256)),
        ctx.mkEq(ctx.mkBVConst("amount", 256), ctx.mkBV(100, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("invest")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(2, 256)),
        ctx.mkEq(ctx.mkBVConst("sender", 256), ctx.mkBV(0x114515L, 256)),
        ctx.mkEq(ctx.mkBVConst("amount", 256), ctx.mkBV(GOAL, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("close_success")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(CLOSETIME + 1, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("withdraw")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(CLOSETIME + 2, 256))
      )
    )
    
    // 轨迹5：失败后退款 (Python第155-162行)
    val trace5 = List(
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("invest")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(1, 256)),
        ctx.mkEq(ctx.mkBVConst("sender", 256), ctx.mkBV(0x114514L, 256)),
        ctx.mkEq(ctx.mkBVConst("amount", 256), ctx.mkBV(100, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("invest")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(2, 256)),
        ctx.mkEq(ctx.mkBVConst("sender", 256), ctx.mkBV(0x114515L, 256)),
        ctx.mkEq(ctx.mkBVConst("amount", 256), ctx.mkBV(100, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("close_refund")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(CLOSETIME + 1, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("claimrefund")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(CLOSETIME + 2, 256)),
        ctx.mkEq(ctx.mkBVConst("p", 256), ctx.mkBV(0x114514L, 256))
      )
    )
    
    // 轨迹6：仅成功关闭 (Python第164-170行)
    val trace6 = List(
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("invest")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(1, 256)),
        ctx.mkEq(ctx.mkBVConst("sender", 256), ctx.mkBV(0x114514L, 256)),
        ctx.mkEq(ctx.mkBVConst("amount", 256), ctx.mkBV(100, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("invest")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(2, 256)),
        ctx.mkEq(ctx.mkBVConst("sender", 256), ctx.mkBV(0x114515L, 256)),
        ctx.mkEq(ctx.mkBVConst("amount", 256), ctx.mkBV(GOAL, 256))
      ),
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("close_success")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(3, 256))
      )
    )
    
    val traces = List(trace1, trace2, trace3, trace4, trace5, trace6)
    println(s"[DEBUG] 构建了${traces.length}个正例轨迹")
    traces
  }
  
  /**
   * 设置crowdfunding的安全属性
   * 参考Python版本第109-114行
   */
  private def setProperties(stateMachine: StateMachine, ctx: Context, state: Expr[_], raised: Expr[_]): Unit = {
    // 辅助函数定义 - 参考Python版本第98-105行
    def prev(stateVar: Expr[_]): Expr[_] = {
      // 这里需要调用stateMachine.prev方法，但需要适配Scala版本
      // Python版本: statemachine.prev(state)[0]
      // 暂时占位，实际实现可能需要调整
      stateVar  // 占位实现
    }
    
    def func(name: String): Expr[BoolSort] = {
      ctx.mkEq(stateMachine.func, ctx.mkString(name))
    }
    
    def once(funcname: String): Expr[BoolSort] = {
      // Python版本: statemachine.once[funcname][0]
      // 需要访问stateMachine的once映射
      ctx.mkBoolConst(s"once_$funcname") // 占位实现
    }
    
    // 属性1: r2 = Not(And(once('withdraw'), once('claimrefund')))
    // 意思：withdraw和claimrefund不能同时发生
    val r2 = ctx.mkNot(ctx.mkAnd(once("withdraw"), once("claimrefund")))
    
    // 属性2: r3 = Implies(prev(raised) >= GOAL, Not(func("invest")))  
    // 意思：如果之前已经达到目标，就不能再投资
    val GOAL = 10000
    val goalExpr = ctx.mkBV(GOAL, 256)
    val r3 = ctx.mkImplies(
      ctx.mkBVUGE(prev(raised).asInstanceOf[BitVecExpr], goalExpr),
      ctx.mkNot(func("invest"))
    )
    
    println(s"[DEBUG] 属性r2: withdraw和claimrefund互斥")
    println(s"[DEBUG] 属性r3: 达到目标后不能投资")
    
    // 注意：这里只是构建了属性，实际使用需要在Synthesizer中传递给CEGIS
    // Python版本在最后调用: statemachine.cegis(properties, positive_traces, None)
  }
  
  /**
   * 构建BNB的属性列表
   * 参考Python版本第128-133行
   */
  def buildBnbProperties(ctx: Context): List[Expr[BoolSort]] = {
    println("[DEBUG] 开始构建BNB属性...")
    
    // 属性1: r1 = Implies(func('freeze'), freezeTotal > prev(freezeTotal))
    // 意思：freeze操作必须增加freezeTotal
    val prevFreezeTotal = ctx.mkBVConst("prev_freezeTotal", 256)
    val funcVar = ctx.mkConst("func", ctx.mkStringSort())
    val freezeTotalVar = ctx.mkBVConst("freezeTotal", 256)
    val r1 = ctx.mkImplies(
      ctx.mkEq(funcVar, ctx.mkString("freeze")),
      ctx.mkBVUGT(freezeTotalVar, prevFreezeTotal)
    )
    
    // 属性2: r2 = Implies(func('unfreeze'), freezeTotal < prev(freezeTotal))
    // 意思：unfreeze操作必须减少freezeTotal
    val r2 = ctx.mkImplies(
      ctx.mkEq(funcVar, ctx.mkString("unfreeze")),
      ctx.mkBVULT(freezeTotalVar, prevFreezeTotal)
    )
    
    println(s"[DEBUG] 构建了2个属性：freeze必须增加freezeTotal，unfreeze必须减少freezeTotal")
    List(r1, r2)
  }
  
  /**
   * 构建BNB的正例轨迹
   * 参考Python版本第138-147行
   */
  def buildBnbTraces(ctx: Context): List[List[List[Expr[BoolSort]]]] = {
    println("[DEBUG] 开始构建BNB正例轨迹...")
    
    // 轨迹1：复杂的代币操作轨迹 (Python第138-147行)
    val trace1 = List(
      // Step 1: transfer
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("transfer")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(1, 256)),
        ctx.mkEq(ctx.mkBVConst("to", 256), ctx.mkBV(0x114515L, 256)),
        ctx.mkEq(ctx.mkBVConst("value", 256), ctx.mkBV(20, 256)),
        ctx.mkEq(ctx.mkBVConst("sender1", 256), ctx.mkBV(0x114514L, 256))
      ),
      // Step 2: burn
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("burn")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(2, 256)),
        ctx.mkEq(ctx.mkBVConst("sender4", 256), ctx.mkBV(0x114514L, 256)),
        ctx.mkEq(ctx.mkBVConst("value4", 256), ctx.mkBV(10, 256))
      ),
      // Step 3: freeze
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("freeze")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(3, 256)),
        ctx.mkEq(ctx.mkBVConst("sender5", 256), ctx.mkBV(0x114514L, 256)),
        ctx.mkEq(ctx.mkBVConst("value5", 256), ctx.mkBV(10, 256))
      ),
      // Step 4: unfreeze
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("unfreeze")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(4, 256)),
        ctx.mkEq(ctx.mkBVConst("sender6", 256), ctx.mkBV(0x114514L, 256)),
        ctx.mkEq(ctx.mkBVConst("value6", 256), ctx.mkBV(10, 256))
      ),
      // Step 5: approve
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("approve")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(5, 256)),
        ctx.mkEq(ctx.mkBVConst("spender", 256), ctx.mkBV(0x114518L, 256)),
        ctx.mkEq(ctx.mkBVConst("value2", 256), ctx.mkBV(10, 256)),
        ctx.mkEq(ctx.mkBVConst("sender2", 256), ctx.mkBV(0x114514L, 256))
      ),
      // Step 6: transferFrom
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("transferFrom")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(6, 256)),
        ctx.mkEq(ctx.mkBVConst("from", 256), ctx.mkBV(0x114514L, 256)),
        ctx.mkEq(ctx.mkBVConst("to2", 256), ctx.mkBV(0x114515L, 256)),
        ctx.mkEq(ctx.mkBVConst("value3", 256), ctx.mkBV(10, 256)),
        ctx.mkEq(ctx.mkBVConst("sender3", 256), ctx.mkBV(0x114518L, 256))
      )
    )
    
    val traces = List(trace1)
    println(s"[DEBUG] 构建了${traces.length}个正例轨迹")
    traces.zipWithIndex.foreach { case (trace, idx) =>
      println(s"[DEBUG] 轨迹${idx + 1}: ${trace.length}个步骤")
    }
    traces
  }
  
  /**
   * 构建voting的属性列表
   * 参考Python版本第52行
   */
  def buildVotingProperties(ctx: Context): List[Expr[BoolSort]] = {
    println("[DEBUG] 开始构建voting属性...")
    
    // 属性1: r1 = Implies(func("vote"), prev(hasVinner) == False)
    // 意思：投票时必须还没有获胜者
    val prevHasVinner = ctx.mkBoolConst("prev_hasVinner")
    val funcVar = ctx.mkConst("func", ctx.mkStringSort())
    val r1 = ctx.mkImplies(
      ctx.mkEq(funcVar, ctx.mkString("vote")),
      ctx.mkEq(prevHasVinner, ctx.mkBool(false))
    )
    
    println(s"[DEBUG] 构建了1个属性：投票时必须还没有获胜者")
    List(r1)
  }
  
  /**
   * 构建voting的正例轨迹
   * 严格按照Python版本第58-62行
   */
  def buildVotingTraces(ctx: Context): List[List[List[Expr[BoolSort]]]] = {
    println("[DEBUG] 开始构建voting正例轨迹...")
    
    // 轨迹1：严格对应Python第58-62行的简单投票
    val trace1 = List(
      List(
        ctx.mkEq(ctx.mkConst("func", ctx.mkStringSort()), ctx.mkString("vote")),
        ctx.mkEq(ctx.mkBVConst("now", 256), ctx.mkBV(1, 256)),
        ctx.mkEq(ctx.mkBVConst("proposal", 256), ctx.mkBV(0x114514L, 256)),
        ctx.mkEq(ctx.mkBVConst("sender", 256), ctx.mkBV(0x114514L, 256))
      )
    )
    
    val traces = List(trace1)
    println(s"[DEBUG] 构建了${traces.length}个正例轨迹")
    traces.zipWithIndex.foreach { case (trace, idx) =>
      println(s"[DEBUG] 轨迹${idx + 1}: ${trace.length}个步骤")
    }
    traces
  }
  
  /**
   * 可以添加其他合约的手动构建方法
   */
  def buildBnbStateMachine(stateMachine: StateMachine, ctx: Context): Unit = {
    println("[DEBUG] 开始手动构建BNB状态机...")
    
    // 添加状态变量 - 参考Python版本第8-13行
    val (totalSupply, totalSupplyOut) = stateMachine.addState("totalSupply", ctx.mkBitVecSort(256))
    val (totalBalance, totalBalanceOut) = stateMachine.addState("totalBalance", ctx.mkBitVecSort(256))
    val (freezeTotal, freezeTotalOut) = stateMachine.addState("freezeTotal", ctx.mkBitVecSort(256))
    val (balanceOf, balanceOfOut) = stateMachine.addState("balanceOf",
      ctx.mkArraySort(ctx.mkBitVecSort(256), ctx.mkBitVecSort(256)))
    val (freezeOf, freezeOfOut) = stateMachine.addState("freezeOf",
      ctx.mkArraySort(ctx.mkBitVecSort(256), ctx.mkBitVecSort(256)))
    val (allowance, allowanceOut) = stateMachine.addState("allowance",
      ctx.mkArraySort(ctx.mkBitVecSort(256), ctx.mkArraySort(ctx.mkBitVecSort(256), ctx.mkBitVecSort(256))))
    
    println("[DEBUG] 添加状态变量: totalSupply, totalBalance, freezeTotal, balanceOf, freezeOf, allowance")
    
    // 添加常量 - 参考Python版本第15行
    val zeroExpr = ctx.mkBV(0, 256)
    stateMachine.addConstants(Seq(zeroExpr))
    
    // 参数变量定义
    val to = ctx.mkBVConst("to", 256)
    val value = ctx.mkBVConst("value", 256)
    val sender1 = ctx.mkBVConst("sender1", 256)
    val spender = ctx.mkBVConst("spender", 256)
    val value2 = ctx.mkBVConst("value2", 256)
    val sender2 = ctx.mkBVConst("sender2", 256)
    val froM = ctx.mkBVConst("from", 256)
    val to2 = ctx.mkBVConst("to2", 256)
    val value3 = ctx.mkBVConst("value3", 256)
    val sender3 = ctx.mkBVConst("sender3", 256)
    val sender4 = ctx.mkBVConst("sender4", 256)
    val value4 = ctx.mkBVConst("value4", 256)
    val sender5 = ctx.mkBVConst("sender5", 256)
    val value5 = ctx.mkBVConst("value5", 256)
    val sender6 = ctx.mkBVConst("sender6", 256)
    val value6 = ctx.mkBVConst("value6", 256)
    
    // 添加转换 1: transfer - 参考Python版本第24-30行
    stateMachine.addTr(
      "transfer",
      List(to, value, sender1),
      ctx.mkBool(true), // guard = True
      ctx.mkAnd(
        // balanceOfOut == Update(Update(balanceOf, to, balanceOf[to] + value), sender1, balanceOf[sender1] - value)
        ctx.mkEq(balanceOfOut,
          ctx.mkStore(
            ctx.mkStore(balanceOf.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], to,
              ctx.mkBVAdd(ctx.mkSelect(balanceOf.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], to).asInstanceOf[BitVecExpr], value)),
            sender1,
            ctx.mkBVSub(ctx.mkSelect(balanceOf.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], sender1).asInstanceOf[BitVecExpr], value)
          )
        )
      )
    )
    
    // 添加转换 2: approve - 参考Python版本第36-42行
    stateMachine.addTr(
      "approve",
      List(spender, value2, sender2),
      ctx.mkBool(true), // guard = True
      ctx.mkAnd(
        // allowanceOut == Update(allowance, sender2, Update(allowance[sender2], spender, value2))
        ctx.mkEq(allowanceOut,
          ctx.mkStore(allowance.asInstanceOf[ArrayExpr[BitVecSort, ArraySort[BitVecSort, BitVecSort]]], sender2,
            ctx.mkStore(
              ctx.mkSelect(allowance.asInstanceOf[ArrayExpr[BitVecSort, ArraySort[BitVecSort, BitVecSort]]], sender2).asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]],
              spender, value2
            )
          )
        )
      )
    )
    
    // 添加转换 3: transferFrom - 参考Python版本第49-56行
    stateMachine.addTr(
      "transferFrom",
      List(froM, to2, value3),
      ctx.mkBool(true), // guard = True
      ctx.mkAnd(
        // balanceOfOut == Update(Update(balanceOf, to2, balanceOf[to2] + value3), froM, balanceOf[froM] - value3)
        ctx.mkEq(balanceOfOut,
          ctx.mkStore(
            ctx.mkStore(balanceOf.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], to2,
              ctx.mkBVAdd(ctx.mkSelect(balanceOf.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], to2).asInstanceOf[BitVecExpr], value3)),
            froM,
            ctx.mkBVSub(ctx.mkSelect(balanceOf.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], froM).asInstanceOf[BitVecExpr], value3)
          )
        ),
        // allowanceOut == Update(allowance, froM, Update(allowance[froM], sender3, allowance[froM][sender3] - value3))
        ctx.mkEq(allowanceOut,
          ctx.mkStore(allowance.asInstanceOf[ArrayExpr[BitVecSort, ArraySort[BitVecSort, BitVecSort]]], froM,
            ctx.mkStore(
              ctx.mkSelect(allowance.asInstanceOf[ArrayExpr[BitVecSort, ArraySort[BitVecSort, BitVecSort]]], froM).asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]],
              sender3,
              ctx.mkBVSub(
                ctx.mkSelect(
                  ctx.mkSelect(allowance.asInstanceOf[ArrayExpr[BitVecSort, ArraySort[BitVecSort, BitVecSort]]], froM).asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]],
                  sender3
                ).asInstanceOf[BitVecExpr],
                value3
              )
            )
          )
        )
      )
    )
    
    // 添加转换 4: burn - 参考Python版本第61-69行
    stateMachine.addTr(
      "burn",
      List(sender4, value4),
      ctx.mkBool(true), // guard = True
      ctx.mkAnd(
        // balanceOfOut == Update(balanceOf, sender4, balanceOf[sender4] - value4)
        ctx.mkEq(balanceOfOut,
          ctx.mkStore(balanceOf.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], sender4,
            ctx.mkBVSub(ctx.mkSelect(balanceOf.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], sender4).asInstanceOf[BitVecExpr], value4)
          )
        ),
        // totalSupplyOut == totalSupply - value4
        ctx.mkEq(totalSupplyOut, ctx.mkBVSub(totalSupply.asInstanceOf[BitVecExpr], value4)),
        // totalBalanceOut == totalBalance - value4
        ctx.mkEq(totalBalanceOut, ctx.mkBVSub(totalBalance.asInstanceOf[BitVecExpr], value4))
      )
    )
    
    // 添加转换 5: freeze - 参考Python版本第75-84行
    stateMachine.addTr(
      "freeze",
      List(sender5, value5),
      ctx.mkBool(true), // guard = True
      ctx.mkAnd(
        // balanceOfOut == Update(balanceOf, sender5, balanceOf[sender5] - value5)
        ctx.mkEq(balanceOfOut,
          ctx.mkStore(balanceOf.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], sender5,
            ctx.mkBVSub(ctx.mkSelect(balanceOf.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], sender5).asInstanceOf[BitVecExpr], value5)
          )
        ),
        // freezeOfOut == Update(freezeOf, sender5, freezeOf[sender5] + value5)
        ctx.mkEq(freezeOfOut,
          ctx.mkStore(freezeOf.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], sender5,
            ctx.mkBVAdd(ctx.mkSelect(freezeOf.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], sender5).asInstanceOf[BitVecExpr], value5)
          )
        ),
        // totalBalanceOut == totalBalance - value5
        ctx.mkEq(totalBalanceOut, ctx.mkBVSub(totalBalance.asInstanceOf[BitVecExpr], value5)),
        // freezeTotalOut == freezeTotal + value5
        ctx.mkEq(freezeTotalOut, ctx.mkBVAdd(freezeTotal.asInstanceOf[BitVecExpr], value5))
      )
    )
    
    // 添加转换 6: unfreeze - 参考Python版本第89-98行
    stateMachine.addTr(
      "unfreeze",
      List(sender6, value6),
      ctx.mkBool(true), // guard = True
      ctx.mkAnd(
        // balanceOfOut == Update(balanceOf, sender6, balanceOf[sender6] + value6)
        ctx.mkEq(balanceOfOut,
          ctx.mkStore(balanceOf.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], sender6,
            ctx.mkBVAdd(ctx.mkSelect(balanceOf.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], sender6).asInstanceOf[BitVecExpr], value6)
          )
        ),
        // freezeOfOut == Update(freezeOf, sender6, freezeOf[sender6] - value6)
        ctx.mkEq(freezeOfOut,
          ctx.mkStore(freezeOf.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], sender6,
            ctx.mkBVSub(ctx.mkSelect(freezeOf.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], sender6).asInstanceOf[BitVecExpr], value6)
          )
        ),
        // totalBalanceOut == totalBalance + value6
        ctx.mkEq(totalBalanceOut, ctx.mkBVAdd(totalBalance.asInstanceOf[BitVecExpr], value6)),
        // freezeTotalOut == freezeTotal - value6
        ctx.mkEq(freezeTotalOut, ctx.mkBVSub(freezeTotal.asInstanceOf[BitVecExpr], value6))
      )
    )
    
    println("[DEBUG] 添加了6个转换: transfer, approve, transferFrom, burn, freeze, unfreeze")
    
    // 调用addOnce() - 参考Python版本第104行
    stateMachine.addOnce()
    
    // 设置初始状态 - 参考Python版本第107-114行
    val pForAll = ctx.mkBVConst("p_init", 256)
    val qForAll = ctx.mkBVConst("q_init", 256)
    val initCondition = ctx.mkAnd(
      // totalBalance == 0
      ctx.mkEq(totalBalance, ctx.mkBV(0, 256)),
      // totalSupply == 0
      ctx.mkEq(totalSupply, ctx.mkBV(0, 256)),
      // freezeTotal == 0
      ctx.mkEq(freezeTotal, ctx.mkBV(0, 256)),
      // ForAll p: balanceOf[p] == 0
      ctx.mkForall(Array(pForAll),
        ctx.mkEq(ctx.mkSelect(balanceOf.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], pForAll), ctx.mkBV(0, 256)),
        1, null, null, null, null),
      // ForAll p: freezeOf[p] == 0
      ctx.mkForall(Array(pForAll),
        ctx.mkEq(ctx.mkSelect(freezeOf.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], pForAll), ctx.mkBV(0, 256)),
        1, null, null, null, null),
      // ForAll p: ForAll q: allowance[p][q] == 0
      ctx.mkForall(Array(pForAll),
        ctx.mkForall(Array(qForAll),
          ctx.mkEq(
            ctx.mkSelect(
              ctx.mkSelect(allowance.asInstanceOf[ArrayExpr[BitVecSort, ArraySort[BitVecSort, BitVecSort]]], pForAll).asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]],
              qForAll
            ),
            ctx.mkBV(0, 256)
          ),
          1, null, null, null, null
        ),
        1, null, null, null, null
      )
    )
    
    stateMachine.setInit(initCondition)
    
    println("[DEBUG] 设置初始状态: 所有余额、冻结余额、授权都为0")
    
    println("[DEBUG] BNB状态机构建完成！")
  }

  def buildWalletStateMachine(stateMachine: StateMachine, ctx: Context): Unit = {
    // TODO: 实现wallet合约的手动构建
    println("[DEBUG] wallet状态机构建 - 待实现")
  }
  
  def buildVotingStateMachine(stateMachine: StateMachine, ctx: Context): Unit = {
    println("[DEBUG] 开始手动构建voting状态机...")
    
    // 常量定义 - 参考Python版本第9行
    val QUORUM = 10
    
    println(s"[DEBUG] 使用常量: QUORUM=$QUORUM")
    
    // 添加状态变量 - 参考Python版本第10-15行
    val (votes, votesOut) = stateMachine.addState("votes", 
      ctx.mkArraySort(ctx.mkBitVecSort(256), ctx.mkBitVecSort(256)))
    val (isVoter, isVoterOut) = stateMachine.addState("isVoter",
      ctx.mkArraySort(ctx.mkBitVecSort(256), ctx.mkBoolSort()))
    val (hasVoted, hasVotedOut) = stateMachine.addState("hasVoted",
      ctx.mkArraySort(ctx.mkBitVecSort(256), ctx.mkBoolSort()))
    val (wins, winsOut) = stateMachine.addState("wins",
      ctx.mkArraySort(ctx.mkBitVecSort(256), ctx.mkBoolSort()))
    val (hasVinner, hasVinnerOut) = stateMachine.addState("hasVinner", ctx.mkBoolSort())
    val (winner, winnerOut) = stateMachine.addState("winner", ctx.mkBitVecSort(256))
    
    println("[DEBUG] 添加状态变量: votes, isVoter, hasVoted, wins, hasVinner, winner")
    
    // 参数变量定义 - 参考Python版本第18-19行
    val sender = ctx.mkBVConst("sender", 256)
    val proposal = ctx.mkBVConst("proposal", 256)
    
    // 创建常量表达式并注入到状态机
    val quorumExpr = ctx.mkBV(QUORUM, 256)
    stateMachine.addConstants(Seq(quorumExpr))
    
    // 添加转换: vote - 严格按照Python版本第21-29行
    stateMachine.addTr(
      "vote",
      List(proposal, sender),
      ctx.mkBool(true), // guard将由CEGIS学习，期望学到：hasVinner == false
      ctx.mkAnd(
        // 严格对应Python: hasVinnerOut == True
        ctx.mkEq(hasVinnerOut, ctx.mkBool(true)),
        // 严格对应Python: hasVotedOut == Update(hasVoted, sender, True)
        ctx.mkEq(hasVotedOut, ctx.mkStore(hasVoted.asInstanceOf[ArrayExpr[BitVecSort, BoolSort]], sender, ctx.mkBool(true))),
        // 严格对应Python: winnerOut == proposal
        ctx.mkEq(winnerOut, proposal)
        // 注意：Python版本没有更新votes，所以这里也不更新
      )
    )
    
    println("[DEBUG] 添加了1个转换: vote")
    
    // 调用addOnce() - 参考Python版本第31行
    stateMachine.addOnce()
    
    // 设置初始状态 - 参考Python版本第33-39行
    val pForAll = ctx.mkBVConst("p_init", 256)
    val initCondition = ctx.mkAnd(
      // ForAll p: votes[p] == 0
      ctx.mkForall(Array(pForAll),
        ctx.mkEq(ctx.mkSelect(votes.asInstanceOf[ArrayExpr[BitVecSort, BitVecSort]], pForAll), ctx.mkBV(0, 256)),
        1, null, null, null, null),
      // ForAll p: isVoter[p] == True
      ctx.mkForall(Array(pForAll),
        ctx.mkEq(ctx.mkSelect(isVoter.asInstanceOf[ArrayExpr[BitVecSort, BoolSort]], pForAll), ctx.mkBool(true)),
        1, null, null, null, null),
      // ForAll p: hasVoted[p] == False
      ctx.mkForall(Array(pForAll),
        ctx.mkEq(ctx.mkSelect(hasVoted.asInstanceOf[ArrayExpr[BitVecSort, BoolSort]], pForAll), ctx.mkBool(false)),
        1, null, null, null, null),
      // ForAll p: wins[p] == False
      ctx.mkForall(Array(pForAll),
        ctx.mkEq(ctx.mkSelect(wins.asInstanceOf[ArrayExpr[BitVecSort, BoolSort]], pForAll), ctx.mkBool(false)),
        1, null, null, null, null),
      // hasVinner == False
      ctx.mkEq(hasVinner, ctx.mkBool(false))
    )
    
    stateMachine.setInit(initCondition)
    
    println("[DEBUG] 设置初始状态: 所有数组初始化为默认值, hasVinner=false")
    
    println("[DEBUG] voting状态机构建完成！")
  }
}