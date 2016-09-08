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
import quasar.qscript.MapFuncs._

import matryoshka._
import scalaz._, Scalaz._

sealed abstract class Prov {
  // NB: Identity should not always affect equality
  /** */
  def identity: Option[FreeMap[T]]
  def path: Option[FreeMap[T]]
}
@Lenses final case class Nada() extends Prov {
  def identity = None
  def path = None
}
@Lenses final case class Value(value: FreeMap[T], path: FreeMap[T]) extends Prov {
  def identity = value.some
}

// TODO: Should we distinguish between map and array projections? (swap_d could
//       cause twe different kinds of projections to end up with the same
//       provenance)
@Lenses final case class Proj(value: FreeMap[T]) extends Prov {
  def identity = None
  def path = None
}
@Lenses final case class Join() extends Prov {

}
@Lenses final case class Union() extends Prov {

}

object Prov {
  implicit val equal: Equal[Prov] = Equal.equal {
    case (Nada(),      Nada())      => true
    case (Value(_, _), Value(_, _)) => true
    case (Proj(v1)),   Proj(v2)     => v1 ≟ v2
    case (Join(_, _),  Join(_, _))  => ???
    case (Union(_, _), Union(_, _)) => ???
    case (_,           _)           => false
  }

  /** Converts a list of provenances into a QScript expression that is evaluated
    * for bucketing.
    */
  def reify(ps: List[Prov]): (FreeMap[T], List[Prov]) =
    ps.foldLeft[(List[FreeMap[T]], List[Prov])](
      (Nil, Nil))(
      (acc, p) => p match {
        case Value(v, path) =>
          acc.bimap(
            path :: _,
            Value(v, ProjectIndex((), IntLit(acc._1.length))) :: _)
        case _ => acc.map(p :: _)
      })

  // NB: Should we use char lits instead?
  class} Provenance[T[_[_]]: Corecursive] {
  private def tagIdentity[A](tag: String, mf: Free[MapFunc[T, ?], A]):
      Free[MapFunc[T, ?], A] =
    Free.roll(MakeMap[T, Free[MapFunc[T, ?], A]](StrLit(tag), mf))

  // provenances:
  // projectfield: f
  // projectindex: i
  // join:         j [] // should be commutative, but currently isn’t
  // union:        u [] // should be commutative, but currently isn’t
  // nest:         n []
  // shiftmap:     m
  // shiftarray:   a
  def projectField[A](mf: Free[MapFunc[T, ?], A]) = tagIdentity("f", mf)
  def projectIndex[A](mf: Free[MapFunc[T, ?], A]) = tagIdentity("i", mf)
  def shiftMap[A](mf: Free[MapFunc[T, ?], A]) = tagIdentity("m", mf)
  def shiftArray[A](mf: Free[MapFunc[T, ?], A]) = tagIdentity("a", mf)

  def join[A](left: Free[MapFunc[T, ?], A], right: Free[MapFunc[T, ?], A]) =
    tagIdentity("j",
      Free.roll(ConcatArrays(
        Free.roll(MakeArray[T, Free[MapFunc[T, ?], A]](left)),
        Free.roll(MakeArray[T, Free[MapFunc[T, ?], A]](right)))))

  def union[A](left: Free[MapFunc[T, ?], A], right: Free[MapFunc[T, ?], A]) =
    tagIdentity("u",
      Free.roll(ConcatArrays(
        Free.roll(MakeArray[T, Free[MapFunc[T, ?], A]](left)),
        Free.roll(MakeArray[T, Free[MapFunc[T, ?], A]](right)))))

  def nest[A](car: Free[MapFunc[T, ?], A], cadr: Free[MapFunc[T, ?], A]) =
    tagIdentity("n", car match {
      case NullLit() => cadr
      case _ =>
        Free.roll(ConcatArrays(
          Free.roll(MakeArray[T, Free[MapFunc[T, ?], A]](car)),
          Free.roll(MakeArray[T, Free[MapFunc[T, ?], A]](cadr))))
    })

  def joinProvenances(leftBuckets: List[FreeMap[T]], rightBuckets: List[FreeMap[T]]):
      List[FreeMap[T]] =
    leftBuckets.alignWith(rightBuckets) {
      case \&/.Both(l, r) => join(l, r)
      case \&/.This(l)    => join(l, NullLit())
      case \&/.That(r)    => join(NullLit(), r)
    }

  def unionProvenances(leftBuckets: List[FreeMap[T]], rightBuckets: List[FreeMap[T]]):
      List[FreeMap[T]] =
    leftBuckets.alignWith(rightBuckets) {
      case \&/.Both(l, r) => union(l, r)
      case \&/.This(l)    => union(l, NullLit[T, Hole]())
      case \&/.That(r)    => union(NullLit[T, Hole](), r)
    }

  def nestProvenances(buckets: List[FreeMap[T]]): List[FreeMap[T]] =
    buckets match {
      case a :: b :: tail => nest(a, b) :: tail
      case _              => buckets
    }

  def squashProvenances(buckets: List[FreeMap[T]]): List[FreeMap[T]] =
    buckets match {
      case a :: b :: tail => squashProvenances(nest(a, b) :: tail)
      case _              => buckets
    }

  def swapProvenances(buckets: List[FreeMap[T]]): List[FreeMap[T]] =
    buckets match {
      case a :: b :: tail => b :: a :: tail
      case _              => buckets
    }
}
