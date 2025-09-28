ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "2.13.8"

lazy val root = (project in file("."))
  .settings(
    name := "declarative-smart-contract"

  )

Compile / mainClass := Some("synthesis.Driver")
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.17" % Test

Compile / unmanagedJars += {
  baseDirectory.value / "unmanaged" / "com.microsoft.z3.jar"
}