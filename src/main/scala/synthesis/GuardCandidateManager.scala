package synthesis

import com.microsoft.z3._
import scala.util.Random

case class GuardSelection(selection: Map[String, List[Int]])

object GuardCandidateManager {
  /**
   * 从 stateMachine.candidateConditionGuards 随机生成 K 个候选组合。
   * 每个组合对每个转移最多选择 maxPerTr 个候选索引。
   */
  def enumerateKRandom(stateMachine: StateMachine, K: Int, maxPerTr: Int, seed: Int): List[GuardSelection] = {
    val rng = new Random(seed)
    val transitions = stateMachine.transitions
    val byTr: Map[String, Int] = transitions.map(tr => tr -> stateMachine.candidateConditionGuards.getOrElse(tr, List()).length).toMap

    (0 until K).map { _ =>
      val sel: Map[String, List[Int]] = transitions.map { tr =>
        val total = byTr.getOrElse(tr, 0)
        if (total == 0 || maxPerTr <= 0) tr -> List()
        else {
          val pickCount = math.min(maxPerTr, total)
          val idxs = rng.shuffle((0 until total).toList).take(pickCount).sorted
          tr -> idxs
        }
      }.toMap
      GuardSelection(sel)
    }.toList
  }
}












