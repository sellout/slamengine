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
import quasar.ejson.EJson
import quasar.fp._

import java.lang.String
import scala.{Boolean, Option}

import scalaz._

object DataLevelOperations {
  // TODO: These aren’t really functions
  type MapFunc[T[_[_]]] = T[EJson] => T[EJson]
  type ReduceFunc[T[_[_]]] = (T[EJson], T[EJson]) => T[EJson]
  type FilterFunc[T[_[_]]] = T[EJson] => Boolean
  type CombineFunc[T[_[_]]] = (T[EJson], T[EJson]) => T[EJson]
  type JoinFunc[T[_[_]]] = (T[EJson], T[EJson]) => Boolean

  // Like a MRA dataset, but without any dimensionality
  type Dataset[T[_[_]]] = List[T[EJson]]
}

import DataLevelOperations._

trait SortDir
final case object Ascending  extends SortDir
final case object Descending extends SortDir

/** This is like CombineFunc, except to handle the various types of optionality
  * of joins.
  */
trait JoinType[T[_[_]]]
final case class Inner[T[_[_]]](f: (T[EJson], T[EJson]) => T[EJson])
    extends JoinType[T]
final case class Full[T[_[_]]](f: T[EJson] \&/ T[EJson] => T[EJson])
    extends JoinType[T]
final case class Left[T[_[_]]](f: (T[EJson], Option[T[EJson]]) => T[EJson])
    extends JoinType[T]
final case class Right[T[_[_]]](f: (Option[T[EJson]], T[EJson]) => T[EJson])
    extends JoinType[T]

/** Here we no longer care about provenance. Backends can’t do anything with it,
  * so we simply represent joins and crosses directly. This also means that we
  * don’t need to model certain things – project_d is just a data-level
  * function, nest_d & swap_d only modify provenance and so are irrelevant here,
  * and autojoin_d has been replaced with a lower-level join operation that
  * doesn’t include the cross portion.
  */
sealed trait QScript[T[_[_]], A]

/** Represents data that we already know. Any operations on this are statically
  * calculated. I can think of two ways to handle this in normalized form:
  * 1. it’s invalid to have a Literal node anywhere other than in a Join or
  *    Cross (and, even then, only one side can have a Literal node), or
  * 2. Literal nodes don’t exist at all in normalized forms (via partially-
  *    applying Joins involving them to turn them into Maps).
  * The second approach seems overall nicer - Literal can be separated from this
  * ADT altogether. Backends will still need to deal with EJson, but it will be
  * in a slightly more restricted fashion.
  */
final case class Literal[T[_[_]], A](value: Dataset[T]) extends QScript[T, A]

/** The top level of a filesystem. During compilation this represents `/`, but
  * in the structure a backend sees, it represents the mount point.
  */
final case class Root[T[_[_]], A]() extends QScript[T, A]

/** A data-level transformation.
  */
final case class Map[T[_[_]], A](f: MapFunc[T], a: A) extends QScript[T, A]

/** Performs a reduction over a dataset, with the dataset partitioned by the
  * result of the MapFunc. So, rather than many-to-one, this is many-to-fewer.
  *
  * @group MRA
  */
final case class Reduce[T[_[_]], A](bucket: MapFunc[T], f: ReduceFunc[T], a: A)
    extends QScript[T, A]

/** Sorts values within a bucket. This could be represented with
  *     LeftShift(Map(_.sort, Reduce(_ :: _, ???))
  * but backends tend to provide sort directly, so this avoids backends having
  * to recognize the pattern. We could provide an algebra
  *     (Sort :+: QScript)#λ => QScript
  * so that a backend without a native sort could eliminate this node.
  */
final case class Sort[T[_[_]], A](bucket: MapFunc[T], order: SortDir, a: A)
    extends QScript[T, A]

/** Eliminates some values from a dataset, based on the result of FilterFunc.
  */
final case class Filter[T[_[_]], A](f: FilterFunc[T], a: A)
    extends QScript[T, A]

/** Creates a new dataset, |a|+|b|, containing all of the entries from each of
  * the input sets, without any indication of which set they came from
  *
  * This could be handled as another join type, the anti-join
  * (T[EJson] \/ T[EJson] => T[EJson], specifically as
  * `_fold(identity)(identity)`), with the condition being `κ(false)`,
  */
final case class Union[T[_[_]], A](a: A, b: A) extends QScript[T, A]

/** Applies a function across two datasets, in the cases where the JoinFunc
  * evaluates to true.
  *
  * This case represents a full θJoin, but we could have an algebra that
  * rewites it as
  *     Filter(_,
  *            EquiJoin(lkey: MapFunc, rkey: MapFunc, f: JoinType, a: A, b: A))
  * to simplify behavior for the backend.
  */
final case class ThetaJoin[T[_[_]], A](on: JoinFunc[T], f: JoinType[T], a: A, b: A)
    extends QScript[T, A]

/** Zooms in one level on the data, turning each map or array into a set of
  * values. Other data types become undefined.
  */
final case class LeftShift[T[_[_]], A](a: A) extends QScript[T, A]

/** Holds a common operation that is used in multiple places, prevents the need
  * to repeatedly read from the same collection, etc.
  */
final case class Let[T[_[_]], A](name: String, form: A, body: A)
    extends QScript[T, A]

/** References a dataset defined in a `Let`.
  */
final case class Vari[T[_[_]], A](name: String) extends QScript[T, A]

object QScript {
  // some simple aliases for other common operations. These could potentially be
  // view patterns for backend authors to take advantage of (or they could be
  // node types, mixed in or out with an algebra).
  def Cross[T[_[_]], A](f: CombineFunc[T], l: A, r: A) =
    ThetaJoin[T, A](κ(true), Inner(f), l, r)
  def Intersection[T[_[_]], A](l: A, r: A)(implicit eq: Equal[T[EJson]]) =
    ThetaJoin[T, A](eq.equal, Inner((l, r) => r), l, r)

  // I currently picture some types like this:
  // data QScriptCore = Root | Map | Reduce | Filter | Union | LeftShift | Let | Vari
  // type StandardQScript = Sort :+: ThetaJoin :+: QScriptCore
  // …
}
