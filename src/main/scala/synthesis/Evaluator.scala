package synthesis

import com.microsoft.z3._

case class EvalResult(passRate: Double, total: Int)

object Evaluator {
  /**
   * 仅基于性质做评估：以同一批“见证+反例”公平比较，不依赖随机通过率。
   */
  def evaluate(sm: StateMachine, ctx: Context, properties: List[Expr[BoolSort]], traces: List[List[List[Expr[BoolSort]]]]): EvalResult = {
    if (properties.isEmpty) return EvalResult(1.0, 0)
    val okCount = properties.count(p => sm.bmc(ctx.mkNot(p)).isEmpty)
    EvalResult(okCount.toDouble / properties.length, properties.length)
  }
}












