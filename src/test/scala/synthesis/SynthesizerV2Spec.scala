package synthesis

import org.scalatest.funsuite.AnyFunSuite
import java.nio.file.{Files, Paths}

class SynthesizerV2Spec extends AnyFunSuite {

  test("synthesizeV2 runs on crowdfunding and outputs solidity file") {
    val syn = Synthesizer()
    val out = Paths.get("./test-solidity/crowdfunding.sol")
    if (Files.exists(out)) Files.delete(out)

    val cfg = SynthesisConfig(
      K = 2,
      maxPerTr = 2,
      trainTraces = 8,
      valTraces = 4,
      maxTraceLen = 5,
      maxLightCegisIter = 2,
      seed = 123
    )

    syn.synthesizeV2("crowdfunding", cfg)

    assert(Files.exists(out), s"Expected output file not found: ${out.toAbsolutePath}")
    // 简单 sanity：文件非空
    assert(Files.size(out) > 0, s"Output file is empty: ${out.toAbsolutePath}")
  }
}



