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

package quasar

import quasar.Predef._

import scalaz._

/** Here we no longer care about provenance. Backends can’t do anything with
  * it, so we simply represent joins and crosses directly. This also means that
  * we don’t need to model certain things – project_d is just a data-level
  * function, nest_d & swap_d only modify provenance and so are irrelevant
  * here, and autojoin_d has been replaced with a lower-level join operation
  * that doesn’t include the cross portion.
  */
package object qscript {
  type Pathable[T[_[_]], F[_], A] =
    Coproduct[Const[DeadEnd, ?], SourcedPathable[T, F, ?], A]

  /** These are the operations included in all forms of QScript.
    */
  type QScriptPrim[T[_[_]], F[_], A] =
    Coproduct[QScriptCore[T, F, ?], Pathable[T, F, ?], A]

  /** This is the target of the core compiler. Normalization is applied to this
    * structure, and it contains no Read or EquiJoin.
    */
  type QScriptPure[T[_[_]], F[_], A] =
    Coproduct[ThetaJoin[T, F, ?], QScriptPrim[T, F, ?], A]

  /** These nodes exist in all QScript structures that a backend sees.
    */
  type QScriptCommon[T[_[_]], F[_], A] =
    Coproduct[Read, QScriptPrim[T, F, ?], A]

  // The following two types are the only ones that should be seen by a backend.

  /** This is the primary form seen by a backend. It contains reads of files.
    */
  type QScript[T[_[_]], F[_], A] =
    Coproduct[ThetaJoin[T, F, ?], QScriptCommon[T, F, ?], A]

  /** A variant with a simpler join type. A backend can choose to operate on this
    * structure by applying the `equiJoinsOnly` transformation. Backends
    * without true join support will likely find it easier to work with this
    * than to handle full ThetaJoins.
    */
  type EquiQScript[T[_[_]], F[_], A] =
    Coproduct[EquiJoin[T, F, ?], QScriptCommon[T, F, ?], A]

  final case class AbsMerge[F[_], A](
    src: A, left: Free[F, Unit], right: Free[F, Unit])
}
