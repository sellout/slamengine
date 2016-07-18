import precog.PlatformBuild._

def scalazVersion = "7.2.3"

lazy val root = project.setup.root.noArtifacts aggregate (blueeyes, common, yggdrasil, mimir) dependsOn (yggdrasil % BothScopes) also (
  initialCommands in console := "import blueeyes._, json._"
)

/** This used to be the evaluator project.
 */
lazy val mimir = project.setup.noArtifacts dependsOn yggdrasil % BothScopes

lazy val yggdrasil = (
  project.setup dependsOn (common % BothScopes, blueeyes % BothScopes) deps (
    "org.objectweb.howl"  % "howl"  % "1.0.1-1",
    "org.slamdata"        % "jdbm"  %  "3.0.0"
  )
)

lazy val common = ( project.setup dependsOn (blueeyes % BothScopes)
  deps (
    "com.google.code.findbugs" % "jsr305"          % "3.0.1",
    "com.google.guava"         % "guava"           % "12.0.1",
    "com.rubiconproject.oss"   % "jchronic"        % "0.2.6",
    "ch.qos.logback"           % "logback-classic" %  "1.0.0"  % Test
  )
)

lazy val blueeyes = (
  project.setup deps (
    "com.googlecode.concurrentlinkedhashmap"  % "concurrentlinkedhashmap-lru" %      "1.1",
    "javolution"                              % "javolution"                  %     "5.5.1",
    "io.netty"                                % "netty"                       %  "3.6.3.Final",
    "org.xlightweb"                           % "xlightweb"                   %     "2.13.2",
    "javax.servlet"                           % "javax.servlet-api"           %      "3.0.1"      % "provided",
    "org.streum"                             %% "configrity-core"             %  "1.0.1-precog",
    "com.chuusai"                            %% "shapeless"                   %     "2.3.1",
    "org.slf4s"                              %% "slf4s-api"                   %     "1.7.13",
    "org.spire-math"                         %% "spire"                       %     "0.7.4",
    "org.scalaz"                             %% "scalaz-core"                 %   scalazVersion   %    Test,
    "org.scalaz"                             %% "scalaz-effect"               %  scalazVersion,
    "org.scalaz"                             %% "scalaz-concurrent"           %  scalazVersion,
    "org.scalaz.stream"                      %% "scalaz-stream"               %     "0.8.1a"      %    Test,
    "joda-time"                               % "joda-time"                   %     "1.6.2",
    "org.mockito"                             % "mockito-all"                 %      "1.9.0"      %    Test,
    "org.eclipse.jetty"                       % "jetty-server"                % "8.1.3.v20120416" %    Test,
    "org.eclipse.jetty"                       % "jetty-servlet"               % "8.1.3.v20120416" %    Test,
    "org.specs2"                             %% "specs2-scalacheck"           %       "3.7"       %    Test,
    "org.specs2"                             %% "specs2-core"                 %       "3.7"       %    Test
  )
)
