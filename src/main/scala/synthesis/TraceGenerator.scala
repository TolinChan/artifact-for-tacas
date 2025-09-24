package synthesis

import com.microsoft.z3._
import scala.util.Random

object TraceGenerator {
  type Step = List[Expr[BoolSort]]
  type Trace = List[Step]

  /**
   * 基于当前状态机和守卫，随机生成可执行轨迹。
   * - 逐步推进：每步选择一个可行转移，采样参数与时间，刷新业务状态。
   * - 返回格式：与 parsePositiveTracesBound 一致的 Step： [ (= func "tr"), (= now t), (= param v) ... ]
   */
  def generate(stateMachine: StateMachine, ctx: Context, numTraces: Int, maxLen: Int, seed: Int): List[Trace] = {
    val rng = new Random(seed)
    (0 until numTraces).toList.flatMap { _ =>
      generateOne(stateMachine, ctx, maxLen, rng)
    }
  }

  /**
   * 基于性质直接调用 BMC 生成“正向见证”轨迹。
   * - 对每条性质 p，尝试 perProp 次 sm.bmc(p)，收集到的可执行轨迹作为正样本。
   * - 若某性质不可满足（返回 None），跳过即可。
   * - 为与随机接口保持一致，返回 List[Trace]。
   */
  def generateFromProperties(stateMachine: StateMachine,
                             ctx: Context,
                             properties: List[Expr[BoolSort]],
                             maxTraceLen: Int,
                             perProp: Int): List[Trace] = {
    val buf = scala.collection.mutable.ListBuffer[Trace]()
    properties.foreach { p =>
      var i = 0
      while (i < perProp) {
        stateMachine.bmc(p) match {
          case Some(trace) =>
            val clipped = if (maxTraceLen > 0 && trace.length > maxTraceLen) trace.take(maxTraceLen) else trace
            if (clipped.nonEmpty) buf += clipped
          case None => () // 找不到见证就跳过
        }
        i += 1
      }
    }
    buf.toList.distinct
  }

  private def generateOne(stateMachine: StateMachine, ctx: Context, maxLen: Int, rng: Random): Option[Trace] = {
    // 初始状态
    var nowState: BoolExpr = stateMachine.ts.getInit()
    var steps: Trace = List()
    var lastNow: BigInt = BigInt(0)

    // 过滤 constructor_* 转移
    val availableTransitionsAll = stateMachine.transitions.filterNot(_.toLowerCase.startsWith("constructor"))
    if (availableTransitionsAll.isEmpty) return None
    val maxTrialsPerStep = 8

    var i = 0
    while (i < maxLen) {
      // 随机尝试若干转移，找到可推进的一步
      val solver = ctx.mkSolver()
      solver.setParameters({ val p = ctx.mkParams(); p.add("timeout", 1000); p })
      solver.add(nowState)

      var picked: Option[(String, List[Expr[BoolSort]], Model)] = None
      val trOrder = rng.shuffle(availableTransitionsAll)
      var trials = 0
      while (picked.isEmpty && trials < maxTrialsPerStep) {
        trials += 1
        trOrder.foreach { tr =>
          if (picked.isEmpty) {
            val guard = stateMachine.conditionGuards.getOrElse(tr, ctx.mkBool(true))
            val transfer = stateMachine.transferFunc.getOrElse(tr, ctx.mkBool(true))

            // 采样 now'：比 lastNow 大的一个随机值（用 BitVec 256）
            val delta = BigInt(rng.between(1L, 4L))
            val nextNowVal = lastNow + delta
            val nowCond = ctx.mkBVUGT(stateMachine.nowOut.asInstanceOf[Expr[BitVecSort]], stateMachine.now.asInstanceOf[Expr[BitVecSort]])

            val s = ctx.mkSolver()
            s.setParameters({ val p = ctx.mkParams(); p.add("timeout", 1000); p })
            s.add(nowState)
            s.add(guard)
            s.add(transfer)
            s.add(nowCond)
            val res = s.check()
            if (res == Status.SATISFIABLE) {
              val m = s.getModel
              val step = buildStep(ctx, stateMachine, tr, m)
              // 推进业务状态：将 next 赋值回 current
              var newNowState: BoolExpr = ctx.mkBool(true)
              stateMachine.states.values.foreach { case (cur, nxt) =>
                val nv = m.eval(nxt, false)
                newNowState = ctx.mkAnd(newNowState, ctx.mkEq(cur, nv))
              }
              nowState = newNowState
              steps = steps :+ step
              picked = Some((tr, step, m))
              lastNow = nextNowVal
            }
          }
        }
      }
      if (picked.isEmpty) {
        // 推进失败则结束
        i = maxLen
      } else {
        i += 1
      }
    }

    if (steps.nonEmpty) Some(steps) else None
  }

  private def buildStep(ctx: Context, sm: StateMachine, trName: String, m: Model): Step = {
    val trExpr = ctx.mkEq(sm.func.asInstanceOf[Expr[_]], ctx.mkString(trName)).asInstanceOf[Expr[BoolSort]]
    val nowEq = ctx.mkEq(sm.now.asInstanceOf[Expr[BitVecSort]], m.eval(sm.now.asInstanceOf[Expr[BitVecSort]], false)).asInstanceOf[Expr[BoolSort]]
    val paramEqs: List[Expr[BoolSort]] = sm.trParameters.getOrElse(trName, List()).map { p =>
      val v = m.eval(p.asInstanceOf[Expr[Sort]], false)
      ctx.mkEq(p.asInstanceOf[Expr[Sort]], v.asInstanceOf[Expr[Sort]]).asInstanceOf[Expr[BoolSort]]
    }
    trExpr :: nowEq :: paramEqs
  }
}


