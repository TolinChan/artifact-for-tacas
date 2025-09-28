package synthesis

import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters._
import scala.util.Using
import org.scalatest.funsuite.AnyFunSuite
import com.microsoft.z3.Context

class ParserPropertySpec extends AnyFunSuite {

  private val baseDir = Paths.get("synthesis-benchmark")

  test("所有 benchmark temporal_properties 均可被解析") {
    assume(Files.exists(baseDir), s"基准目录不存在：${baseDir.toAbsolutePath}")

    val propertyFiles: List[Path] = Using.resource(Files.walk(baseDir)) { stream =>
      stream.iterator().asScala
        .filter(path => Files.isRegularFile(path) && path.getFileName.toString == "temporal_properties.txt")
        .toList
    }

    val failures = propertyFiles.flatMap { propertyPath =>
      val dir = propertyPath.getParent
      val benchmarkName = dir.getFileName.toString
      val datalogName = if (benchmarkName == "crowdfunding") "crowfunding" else benchmarkName
      val datalogPath = dir.resolve(s"$datalogName.dl")

      if (!Files.exists(datalogPath)) {
        Some(propertyPath -> new IllegalStateException(s"缺少 Datalog 文件 ${datalogPath.getFileName}"))
      } else {
        val ctx = new Context()
        try {
          val stateMachine = Parser.buildStateMachineFromDatalog(benchmarkName, datalogPath.toString, ctx)
          Parser.parseTemporalPropertiesBound(stateMachine, propertyPath.toString, ctx)
          None
        } catch {
          case t: Throwable => Some(propertyPath -> t)
        } finally {
          ctx.close()
        }
      }
    }

    if (failures.nonEmpty) {
      val msg = failures.map { case (path, err) =>
        s"${path.toString}: ${err.getClass.getSimpleName} - ${Option(err.getMessage).getOrElse("<no message>")}"
      }.mkString("\n")
      fail("解析失败:\n" + msg)
    }
  }
}


