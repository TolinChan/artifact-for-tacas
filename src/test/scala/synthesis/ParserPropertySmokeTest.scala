package synthesis

import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters._
import scala.util.Using
import com.microsoft.z3.Context

/**
 * 简单验证：枚举 `synthesis-benchmark` 下的所有 temporal_properties.txt，
 * 调用 Parser.parseTemporalPropertiesBound，看是否有解析异常。
 */
object ParserPropertySmokeTest extends App {

  val baseDir = Paths.get("synthesis-benchmark")
  if (!Files.exists(baseDir)) {
    System.err.println(s"基准目录不存在：${baseDir.toAbsolutePath}")
    sys.exit(1)
  }

  val propertyFiles: List[Path] = Using.resource(Files.walk(baseDir)) { stream =>
    stream.iterator().asScala
      .filter(path => Files.isRegularFile(path) && path.getFileName.toString == "temporal_properties.txt")
      .toList
  }

  var failures = List.empty[(Path, Throwable)]

  propertyFiles.foreach { propertyPath =>
    val dir = propertyPath.getParent
    val benchmarkName = dir.getFileName.toString
    val datalogName = if (benchmarkName == "crowdfunding") "crowfunding" else benchmarkName
    val datalogPath = dir.resolve(s"$datalogName.dl")

    if (!Files.exists(datalogPath)) {
      System.err.println(s"跳过 $benchmarkName：缺少 Datalog 文件 ${datalogPath.getFileName}")
    } else {
      val ctx = new Context()
      try {
        val stateMachine = Parser.buildStateMachineFromDatalog(benchmarkName, datalogPath.toString, ctx)
        Parser.parseTemporalPropertiesBound(stateMachine, propertyPath.toString, ctx)
      } catch {
        case t: Throwable =>
          failures ::= (propertyPath -> t)
      } finally {
        ctx.close()
      }
    }
  }

  if (failures.nonEmpty) {
    System.err.println("以下属性文件解析失败：")
    failures.reverse.foreach { case (path, err) =>
      System.err.println(s"- ${path.toString}: ${err.getClass.getSimpleName} - ${err.getMessage}")
    }
    sys.exit(1)
  } else {
    println(s"成功解析 ${propertyFiles.size} 个 temporal_properties.txt 文件。")
  }
}


