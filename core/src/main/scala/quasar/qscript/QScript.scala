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

import scalaz._


// Need to keep track of our non-type-ensured guarantees:
// - all conditions in a ThetaJoin will refer to both sides of the join
// - each `Free` structure in a *Join or Union will have exactly one `point`
// - the common source in a Join or Union will be the longest common branch
// - all Reads have a Root (or another Read?) as their source
// - in `Pathable`, the only `MapFunc` node allowed is a `ProjectField`

// TODO use real EJson when it lands in master
trait EJson[A]

object DataLevelOperations {

  sealed trait MapFunc[T[_[_]], A]
  final case class MapFunc0[T[_[_]], A](value: T[EJson]) extends MapFunc[T, A]
  final case class MapFunc1[T[_[_]], A](a1: A) extends MapFunc[T, A]
  final case class MapFunc2[T[_[_]], A](a1: A, a2: A) extends MapFunc[T, A]
  final case class MapFunc3[T[_[_]], A](a1: A, a2: A, a3: A) extends MapFunc[T, A]

  sealed trait ReduceFunc

  sealed trait JoinSide
  case object LeftSide extends JoinSide
  case object RightSide extends JoinSide

  type JoinFunc[T[_[_]]] = Free[MapFunc[T, ?], JoinSide]
  type FreeMap[T[_[_]]] = Free[MapFunc[T, ?], Unit]
}

import DataLevelOperations._

object ReduceFuncs {
  final case object Sum extends ReduceFunc
}

object MapFuncs {
  def ObjectProject[T[_[_]], A](a1: A, a2: A) = MapFunc2(a1, a2)
}
