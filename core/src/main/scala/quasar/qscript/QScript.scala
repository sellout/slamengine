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

import pathy.Path._
import scalaz._


// Need to keep track of our non-type-ensured guarantees:
// - all conditions in a ThetaJoin will refer to both sides of the join
// - each `Free` structure in a *Join or Union will have exactly one `point`
// - the common source in a Join or Union will be the longest common branch
// - all Reads have a Root (or another Read?) as their source
// - in `Pathable`, the only `MapFunc` node allowed is a `ProjectField`

// TODO use real EJson when it lands in master
trait EJson[A]

sealed trait QScript[T[_[_]], A]

object DataLevelOps {
  sealed trait MapFunc[T[_[_]], A]
  final case class MapFunc0[T[_[_]], A](value: T[EJson]) extends MapFunc[T, A]
  final case class MapFunc1[T[_[_]], A](a1: A) extends MapFunc[T, A]
  final case class MapFunc2[T[_[_]], A](a1: A, a2: A) extends MapFunc[T, A]
  final case class MapFunc3[T[_[_]], A](a1: A, a2: A, a3: A) extends MapFunc[T, A]

  type FreeMap[T[_[_]]] = Free[MapFunc[T, ?], Unit]

  sealed trait ReduceFunc

  sealed trait JoinSide
  final case object LeftSide extends JoinSide
  final case object RightSide extends JoinSide
  
  type JoinFunc[T[_[_]]] = Free[MapFunc[T, ?], JoinSide]
  type JoinBranch[T[_[_]]] = Free[QScript[T, ?], Unit]
}

import DataLevelOps._

object ReduceFuncs {
  final case object Sum extends ReduceFunc
}

object MapFuncs {
  def ObjectProject[T[_[_]], A](a1: A, a2: A) = MapFunc2(a1, a2)
}

sealed trait SortDir
final case object Ascending  extends SortDir
final case object Descending extends SortDir

object SortDir {
  implicit val equal: Equal[SortDir] = Equal.equalRef
}

sealed trait JoinType
final case object Inner extends JoinType
final case object FullOuter extends JoinType
final case object LeftOuter extends JoinType
final case object RightOuter extends JoinType

object JoinType {
  implicit val equal: Equal[JoinType] = Equal.equalRef
}

sealed trait Pathable[T[_[_]], A] extends QScript[T, A]

/** The top level of a filesystem. During compilation this represents `/`, but
  * in the structure a backend sees, it represents the mount point.
  */
final case class Root[T[_[_]], A]() extends Pathable[T, A]

/** A data-level transformation.
  */
final case class Map[T[_[_]], A](src: A, f: FreeMap[T]) extends Pathable[T, A]

/** Zooms in one level on the data, turning each map or array into a set of
  * values. Other data types become undefined.
  */
final case class LeftShift[T[_[_]], A](src: A) extends Pathable[T, A]

/** Creates a new dataset, |a|+|b|, containing all of the entries from each of
  * the input sets, without any indication of which set they came from
  *
  * This could be handled as another join type, the anti-join
  * (T[EJson] \/ T[EJson] => T[EJson], specifically as `_.merge`), with the
  * condition being `κ(true)`,
  */
final case class Union[T[_[_]], A](
  src: A,
  lBranch: JoinBranch[T],
  rBranch: JoinBranch[T])
    extends Pathable[T, A]

sealed trait QScriptCore[T[_[_]], A] extends QScript[T, A]

/** Performs a reduction over a dataset, with the dataset partitioned by the
  * result of the MapFunc. So, rather than many-to-one, this is many-to-fewer.
  *
  * @group MRA
  */
final case class Reduce[T[_[_]], A](src: A, bucket: FreeMap[T], f: ReduceFunc)
    extends QScriptCore[T, A]

/** Sorts values within a bucket. This could be represented with
  *     LeftShift(Map(_.sort, Reduce(_ :: _, ???))
  * but backends tend to provide sort directly, so this avoids backends having
  * to recognize the pattern. We could provide an algebra
  *     (Sort :+: QScript)#λ => QScript
  * so that a backend without a native sort could eliminate this node.
  */
// Should this operate on a sequence of mf/order pairs? Might be easier for
// implementers to handle stable sorting that way.
final case class Sort[T[_[_]], A](src: A, bucket: FreeMap[T], order: SortDir)
    extends QScriptCore[T, A]

/** Eliminates some values from a dataset, based on the result of FilterFunc.
  */
final case class Filter[T[_[_]], A](src: A, f: FreeMap[T])
    extends QScriptCore[T, A]

/** A backend-resolved `Root`, which is now a path. */
final case class Read[A](src: A, path: AbsFile[Sandboxed])

/** Applies a function across two datasets, in the cases where the JoinFunc
  * evaluates to true. The branches represent the divergent operations applied
  * to some common src. Each branch references the src exactly once. (Since no
  * constructor has more than one recursive component, it’s guaranteed that
  * neither side references the src _more_ than once.)
  *
  * This case represents a full θJoin, but we could have an algebra that
  * rewites it as
  *     Filter(_, EquiJoin(...))
  * to simplify behavior for the backend.
  */
final case class ThetaJoin[T[_[_]], A](
  on: JoinFunc[T],
  f: JoinType,
  src: A,
  lBranch: JoinBranch[T],
  rBranch: JoinBranch[T]) extends QScript[T, A]
