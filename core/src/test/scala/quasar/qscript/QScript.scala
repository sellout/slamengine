/*
 * Copyright 2014–2016 SlamData Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package quasar.qscript

import quasar.Predef._
import quasar.LogicalPlan
import quasar.fp._

import matryoshka._, FunctorT.ops._
import org.specs2.mutable._
import org.specs2.scalaz._
import pathy.Path._
//import shapeless.contrib.scalaz.instances.deriveEqual
import scalaz._
import Scalaz._

class QScriptSpec extends Specification with ScalazMatchers {
  import DataLevelOps._
  import MapFuncs._
  import Transform._

  import scala.Predef.implicitly

  implicit val ma: Mergeable.Aux[Fix, QScriptPure[Fix, Unit]] = scala.Predef.implicitly

  def callIt(lp: Fix[LogicalPlan]): Inner[Fix] = lp.transCata(lpToQScript[Fix]).transCata(liftQSAlgebra(elideNopMaps[Fix, QScriptPure[Fix, ?]]))

  def RootR = CorecursiveOps[Fix, QScriptPure[Fix, ?]](E.inj(Const[DeadEnd, Inner[Fix]](Root))).embed

  def ObjectProjectR[A](src: Free[MapFunc[Fix, ?], A], field: Free[MapFunc[Fix, ?], A]): Free[MapFunc[Fix, ?], A] =
    Free.roll(ObjectProject(src, field))

  def StrR[A](s: String): Free[MapFunc[Fix, ?], A] =
    Free.roll(StrLit[Fix, Free[MapFunc[Fix, ?], A]](s))

  //Equal[Fix[QScriptPure[Fix, ?]]]

  implicitly[Equal[Unit]]
  implicitly[Equal[DeadEnd]]
  implicitly[Equal[Const[DeadEnd, Unit]]]
  implicitly[Equal[Fix[Const[DeadEnd, ?]]]]
  implicitly[Delay[Equal, ThetaJoin[Fix, ?]]]
  implicitly[Equal[ThetaJoin[Fix, Unit]]]
  implicitly[Equal[QScriptCore[Fix, Unit]]]
  implicitly[Equal[SourcedPathable[Fix, Unit]]]
  implicitly[Equal[Pathable[Fix, Unit]]]
  implicitly[Equal[QScriptPrim[Fix, Unit]]]
  implicitly[Equal[QScriptPure[Fix, Unit]]]
  implicitly[Equal[Fix[QScriptPure[Fix, ?]]]]

  implicitly[Show[Unit]]
  implicitly[Show[DeadEnd]]
  implicitly[Show[Const[DeadEnd, Unit]]]
  implicitly[Show[Fix[Const[DeadEnd, ?]]]]
  implicitly[Delay[Show, ThetaJoin[Fix, ?]]]
  implicitly[Show[ThetaJoin[Fix, Unit]]]
  implicitly[Show[QScriptCore[Fix, Unit]]]
  implicitly[Show[SourcedPathable[Fix, Unit]]]
  implicitly[Show[Pathable[Fix, Unit]]]
  implicitly[Show[QScriptPrim[Fix, Unit]]]
  implicitly[Show[QScriptPure[Fix, Unit]]]
  implicitly[Show[Fix[QScriptPure[Fix, ?]]]]

  //val z = callIt(quasar.LogicalPlan.Read(file("/some/foo/bar")))

  "replan" should {
    "convert a very simple read" in {
      callIt(quasar.LogicalPlan.Read(file("/"))) must
      equal(RootR)
    }

    "convert a simple read" in {
      callIt(quasar.LogicalPlan.Read(file("/some/foo/bar"))) must
      //equal(RootR)
      equal(
        F[Fix].inj(
          Map[Fix, Inner[Fix]](RootR,
            ObjectProjectR[Unit](
              ObjectProjectR[Unit](
                ObjectProjectR[Unit](
                  UnitF[Fix],
                  StrR[Unit]("some")),
                StrR[Unit]("foo")),
              StrR[Unit]("bar")))).embed)(Fix.equal(
                coproductEqual(
                  ThetaJoin.equal,
                  coproductEqual(
                    QScriptCore.equal, implicitly[Delay[Equal, Pathable[Fix, ?]]]))), implicitly[Show[Fix[QScriptPure[Fix, ?]]]])

      // Map(Root, ObjectProject(ObjectProject(ObjectProject((), "some"), "foo"), "bar"))
    }
  }
}
