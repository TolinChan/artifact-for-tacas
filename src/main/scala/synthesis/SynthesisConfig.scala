package synthesis

case class SynthesisConfig(
  // candidate settings
  K: Int = 5,                    // 候选数量较小
  maxPerTr: Int = 3,             // 每个转移最多选择的原子谓词数
  strategy: String = "random",   // 候选生成策略：random/greedy（后续可扩展）
  seed: Int = 114514,

  // trace generation
  trainTraces: Int = 60,
  valTraces: Int = 60,
  maxTraceLen: Int = 6,
  perProp: Int = 1,

  // synthesis & verify
  maxLightCegisIter: Int = 3,
  bmcDepth: Int = 16
)









