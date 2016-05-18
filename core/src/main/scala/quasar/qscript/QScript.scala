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
import quasar.Planner.PlannerError

import matryoshka._, Recursive.ops._, FunctorT.ops._
import pathy.Path._
import scala.{Boolean, Option}

import scalaz.{:+: => _, _}, Scalaz._

// Need to keep track of our non-type-ensured guarantees:
// - all conditions in a ThetaJoin will refer to both sides of the join
// - each `Free` structure in a *Join or Union will have exactly one `point`
// - the common source in a Join or Union will be the longest common branch
// - all Reads have a Root (or another Read?) as their source
// - in `Pathable`, the only `MapFunc` node allowed is a `ProjectField`

object DataLevelOperations {
  // TODO: These aren’t really functions
  type MapFunc[T[_[_]]] = T[EJson] => T[EJson]
  /** This should be able to reduce across many fields, not just one. I.e.:
    * { foo: sum(…), bar: push(…), … }
    */
  type ReduceFunc[T[_[_]]] = (T[EJson], T[EJson]) => T[EJson]
  type FilterFunc[T[_[_]]] = T[EJson] => Boolean
  type CombineFunc[T[_[_]]] = (T[EJson], T[EJson]) => T[EJson]
  type JoinFunc[T[_[_]]] = (T[EJson], T[EJson]) => Boolean

  // Like a MRA dataset, but without any dimensionality
  type Dataset[T[_[_]]] = List[T[EJson]]

  implicit def mapFuncEqual[T[_[_]]]: Equal[MapFunc[T]] = ???
  implicit def reduceFuncEqual[T[_[_]]]: Equal[ReduceFunc[T]] = ???
  implicit def filterFuncEqual[T[_[_]]]: Equal[FilterFunc[T]] = ???
  implicit def combineFuncEqual[T[_[_]]]: Equal[CombineFunc[T]] = ???
  implicit def joinFuncEqual[T[_[_]]]: Equal[JoinFunc[T]] = ???
}

import DataLevelOperations._

// NB: Need a PlannerError to cover cases where QScript failed to maintain its
//     non-type-checked guarantees. E.g., if one side of a ThetaJoin has no
//     reference to the common src.
//     ?: InvalidQScript(node, "join with no source reference")
//     => error in Quasar core: provided Mongo backend an invalid QScript: join
//        with no source reference
//
//     We could potentially even have one for _each_ guarantee, so no message-
//     writing on the part of the backend.

trait SortDir
final case object Ascending  extends SortDir
final case object Descending extends SortDir

object SortDir {
  implicit val equal: Equal[SortDir] = Equal.equalRef
}

/** This is like CombineFunc, except to handle the various types of optionality
  * of joins.
  */
trait JoinType[T[_[_]]]
final case class Inner[T[_[_]]](f: CombineFunc[T])
    extends JoinType[T]
final case class Full[T[_[_]]](f: T[EJson] \&/ T[EJson] => T[EJson])
    extends JoinType[T]
final case class Left[T[_[_]]](f: (T[EJson], Option[T[EJson]]) => T[EJson])
    extends JoinType[T]
final case class Right[T[_[_]]](f: (Option[T[EJson]], T[EJson]) => T[EJson])
    extends JoinType[T]

object JoinType {
  implicit def equal[T[_[_]]]: Equal[JoinType[T]] = ???
}

sealed trait Pathable[T[_[_]], A]
/** The top level of a filesystem. During compilation this represents `/`, but
  * in the structure a backend sees, it represents the mount point.
  */
final case class Root[T[_[_]], A]() extends Pathable[T, A]
/** A data-level transformation.
  */
final case class Map[T[_[_]], A](f: MapFunc[T], a: A) extends Pathable[T, A]
/** Zooms in one level on the data, turning each map or array into a set of
  * values. Other data types become undefined.
  */
final case class LeftShift[T[_[_]], A](a: A) extends Pathable[T, A]
/** Creates a new dataset, |a|+|b|, containing all of the entries from each of
  * the input sets, without any indication of which set they came from
  *
  * This could be handled as another join type, the anti-join
  * (T[EJson] \/ T[EJson] => T[EJson], specifically as `_.merge`), with the
  * condition being `κ(true)`,
  */
final case class Union[T[_[_]], A](
  src: A,
  lBranch: Free[QScript[T, ?], Unit],
  rBranch: Free[QScript[T, ?], Unit])
    extends Pathable[T, A]

object Pathable {
  implicit def equal[T[_[_]]]: Equal ~> (Equal ∘ Pathable[T, ?])#λ =
    new (Equal ~> (Equal ∘ Pathable[T, ?])#λ) {
      def apply[A](eq: Equal[A]) =
        Equal.equal {
          case (Root(), Root()) => true
          case (Map(f1, a1), Map(f2, a2)) => f1 ≟ f2 && eq.equal(a1, a2)
          case (LeftShift(a1), LeftShift(a2)) => eq.equal(a1, a2)
          case (Union(a1, l1, r1), Union(a2, l2, r2)) =>
            eq.equal(a1, a2) && l1 ≟ l2 && r1 ≟ r2
          case (_, _) => false
        }
    }

  implicit def traverse[T[_[_]]]: Traverse[Pathable[T, ?]] =
    new Traverse[Pathable[T, ?]] {
      def traverseImpl[G[_], A, B](
        fa: Pathable[T, A])(
        f: A => G[B])(
        implicit G: Applicative[G]):
          G[Pathable[T, B]] =
        fa match {
          case Root()         => G.point(Root())
          case Map(func, a)   => f(a) ∘ (Map(func, _))
          case LeftShift(a)   => f(a) ∘ (LeftShift(_))
          case Union(a, l, r) => f(a) ∘ (Union(_, l, r))
        }
    }
}

sealed trait QScriptCore[T[_[_]], A]
/** Performs a reduction over a dataset, with the dataset partitioned by the
  * result of the MapFunc. So, rather than many-to-one, this is many-to-fewer.
  *
  * @group MRA
  */
final case class Reduce[T[_[_]], A](bucket: MapFunc[T], f: ReduceFunc[T], a: A)
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
final case class Sort[T[_[_]], A](bucket: MapFunc[T], order: SortDir, a: A)
    extends QScriptCore[T, A]

/** Eliminates some values from a dataset, based on the result of FilterFunc.
  */
final case class Filter[T[_[_]], A](f: FilterFunc[T], a: A)
    extends QScriptCore[T, A]

object QScriptCore {
  implicit def equal[T[_[_]]]: Equal ~> (Equal ∘ QScriptCore[T, ?])#λ =
    new (Equal ~> (Equal ∘ QScriptCore[T, ?])#λ) {
      def apply[A](eq: Equal[A]) =
        Equal.equal {
          case (Reduce(b1, f1, a1), Reduce(b2, f2, a2)) =>
            b1 ≟ b2 && f1 ≟ f2 && eq.equal(a1, a2)
          case (Sort(b1, o1, a1), Sort(b2, o2, a2)) =>
            b1 ≟ b2 && o1 ≟ o2 && eq.equal(a1, a2)
          case (Filter(f1, a1), Filter(f2, a2)) => f1 ≟ f2 && eq.equal(a1, a2)
          case (_, _) => false
        }
    }

  implicit def traverse[T[_[_]]]: Traverse[QScriptCore[T, ?]] =
    new Traverse[QScriptCore[T, ?]] {
      def traverseImpl[G[_]: Applicative, A, B](
        fa: QScriptCore[T, A])(
        f: A => G[B]) =
        fa match {
          case Reduce(b, func, a) => f(a) ∘ (Reduce(b, func, _))
          case Sort(b, o, a)      => f(a) ∘ (Sort(b, o, _))
          case Filter(func, a)    => f(a) ∘ (Filter(func, _))
        }
    }
}

/** A backend-resolved `Root`, which is now a path. */
final case class Read[A](src: A, path: AbsFile[Sandboxed])

object Read {
  implicit def equal[T[_[_]]]: Equal ~> (Equal ∘ Read)#λ =
    new (Equal ~> (Equal ∘ Read)#λ) {
      def apply[A](eq: Equal[A]) =
        Equal.equal {
          case (Read(a1, p1), Read(a2, p2)) => eq.equal(a1, a2) && p1 ≟ p2
        }
    }

  implicit def traverse[T[_[_]]]: Traverse[Read] =
    new Traverse[Read] {
      def traverseImpl[G[_]: Applicative, A, B](fa: Read[A])(f: A => G[B]) =
        f(fa.src) ∘ (Read(_, fa.path))
    }
}

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
  f: JoinType[T],
  src: A,
  lBranch: Free[QScript[T, ?], Unit],
  rBranch: Free[QScript[T, ?], Unit])

object ThetaJoin {
  implicit def equal[T[_[_]]]: Equal ~> (Equal ∘ ThetaJoin[T, ?])#λ =
    new (Equal ~> (Equal ∘ ThetaJoin[T, ?])#λ) {
      def apply[A](eq: Equal[A]) =
        Equal.equal {
          case (ThetaJoin(o1, f1, a1, l1, r1), ThetaJoin(o2, f2, a2, l2, r2)) =>
            o1 ≟ o2 && f1 ≟ f2 && eq.equal(a1, a2) && l1 ≟ l2 && r1 ≟ r2
        }
    }

  implicit def traverse[T[_[_]]]: Traverse[ThetaJoin[T, ?]] =
    new Traverse[ThetaJoin[T, ?]] {
      def traverseImpl[G[_]: Applicative, A, B](
        fa: ThetaJoin[T, A])(
        f: A => G[B]) =
        f(fa.src) ∘ (ThetaJoin(fa.on, fa.f, _, fa.lBranch, fa.rBranch))
    }
}

final case class EquiJoin[T[_[_]], A](
  lKey: MapFunc[T], rKey: MapFunc[T], f: JoinType[T], src: A,  lBranch: Free[QScript[T, ?], Unit], rBranch: Free[QScript[T, ?], Unit])

object EquiJoin {
  implicit def equal[T[_[_]]]: Equal ~> (Equal ∘ EquiJoin[T, ?])#λ =
    new (Equal ~> (Equal ∘ EquiJoin[T, ?])#λ) {
      def apply[A](eq: Equal[A]) =
        Equal.equal {
          case (EquiJoin(lk1, rk1, f1, a1, l1, r1),
                EquiJoin(lk2, rk2, f2, a2, l2, r2)) =>
            lk1 ≟ lk2 && rk1 ≟ rk2 && f1 ≟ f2 && eq.equal(a1, a2) && l1 ≟ l2 && r1 ≟ r2
        }
    }

  implicit def traverse[T[_[_]]]: Traverse[EquiJoin[T, ?]] =
    new Traverse[EquiJoin[T, ?]] {
      def traverseImpl[G[_]: Applicative, A, B](
        fa: EquiJoin[T, A])(
        f: A => G[B]) =
        f(fa.src) ∘
          (EquiJoin(fa.lKey, fa.rKey, fa.f, _, fa.lBranch, fa.rBranch))
    }
}

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
// final case class Literal[T[_[_]], A](value: Dataset[T]) extends QScript[T, A]

object EJsonFuncs {
  def True[T[_[_]]]: MapFunc[T] = κ(EJson.Bool(true))
  def Null[T[_[_]]]: MapFunc[T] = κ(EJson.Null)
  def Eq[T[_[_]]]: JoinFunc[T] = _ == _
  def Identity[T[_[_]]]: MapFunc[T] = ι
  def Left[T[_[_]]]: CombineFunc[T] = (l, r) => l
  def Right[T[_[_]]]: CombineFunc[T] = (l, r) => r
}

/** When matching this (or Intersection), take care to do it prior to other
  * `*Join` cases. */
object CrossJoin {
  def apply[T[_[_]], A](f: CombineFunc[T], src: A, lBranch: Free[QScript[T, ?], Unit], rBranch: Free[QScript[T, ?], Unit]) =
    ThetaJoin[T, A](κ(true), Inner(f), src, lBranch, rBranch)

  def unapply[T[_[_]], A](obj: scala.Any):
      Option[(CombineFunc[T], A, Free[QScript[T, ?], Unit], Free[QScript[T, ?], Unit])] =
    obj match {
      case ThetaJoin(EJsonFuncs.True, Inner(f), src, l, r) => (f, src, l, r).some
      case EquiJoin(EJsonFuncs.Null, EJsonFuncs.Null, Inner(f), src, l, r) => (f, src, l, r).some
      case _ => None
    }
}

object Intersection {
  def apply[T[_[_]], A](src: A, lBranch: Free[QScript[T, ?], Unit], rBranch: Free[QScript[T, ?], Unit]) =
    ThetaJoin[T, A](_ == _, Inner((l, r) => l), src, lBranch, rBranch)

  def unapply[T[_[_]], A](obj: scala.Any):
      Option[(A, Free[QScript[T, ?], Unit], Free[QScript[T, ?], Unit])] =
    obj match {
      case ThetaJoin(EJsonFuncs.Eq, Inner(EJsonFuncs.Left | EJsonFuncs.Right), src, l, r) => (src, l, r).some
      case EquiJoin(EJsonFuncs.Identity, EJsonFuncs.Identity, Inner(EJsonFuncs.Left | EJsonFuncs.Right), src, l, r) => (src, l, r).some
      case _ => None
    }
}

object QScriptTransformations {
  type Equi[T[_[_]], A] = (Filter[T, ?] :+: EquiJoin[T, ?])#λ[A]

  /** Converts a ThetaJoin to a mixture of Filters and EquiJoins. */
  // This is a subset of what optimizer.rewriteCrossJoinsƒ does. That should
  // continue to pull conditions that don’t reference both sides of a join out
  // of the join. At this point, we assume that every condition references both
  // sides. We now just have to extract any non-equi conditions into post-join
  // conditions.
  // There may also need to be a point where we try to rewrite things like
  // `7 = left.a + right.b` into `left.a = 7 - right.b`. This won’t affect the
  // implementation of the backend, but allows us to maintain more conditions as
  // equi-conditions, making the final queries more efficient.
  //
  // The result of this is one of two cases:
  // 1. if the existing join is simpliy an equijoin (or Cross), it remains so.
  // 2. if it contains non-Anded conditions, conditions that have a comparison
  //    other than `=`, or conditions that are unbalanced (7 = l + r), then it
  //    creates a `Filter(Equi(?))` structure.
  // That’s all this can do.
  def equiJoinsOnly[T[_[_]]]: ThetaJoin[T, ?] ~> (Equi[T, ?] ∘ Free[Equi[T, ?], ?])#λ = ???






  // TODO: Is just using `Read` better than `Const` here?
  type Pathed[T[_[_]], A] =
    (NonEmptyList ∘ (Const[AbsFile[Sandboxed], ?] :+: Pathable[T, ?])#λ)#λ[A]

/*
  /
  foo
    moo
    mee
  bar
    boo
    bee
  baz
    baa
    bzz
  meh
    me
      foo
      bar
    mo

/meh/me/bar
/mhe/mo

Union(Read("/meh/me/bar"), ProjectField(Read("/meh/mo"), "bar"))

*/

  /** A backend-or-mount-specific `f` is provided, that allows us to rewrite
    * `Root` (and projections, etc.) into `Read`, so then we can handle exposing
    * only “true” joins and converting intra-data joins to map operations.
    *
    * `f` takes QScript representing a _potential_ path to a file, converts
    * `Root` and its children to path, with the operations post-file remaining.
    */
  def pathify[T[_[_]]: Recursive, F[_]](f: AlgebraM[PlannerError \/ ?, Pathable[T, ?], T[Pathed[T, ?]]])(implicit F: Pathable[T, ?] :<: F):
      T[F] => PlannerError \/ T[(Read :+: F)#λ] =
    _.cataM[PlannerError \/ ?, T[(Read :+: F)#λ]](pathifyƒ(f)).flatMap(_.fold(_.right, toRead(f)))

  /** Applied after the backend-supplied function, to convert the files into
    * reads and combine them as necessary.
    */
  def postPathify[T[_[_]], F[_], A](p: Pathed[T, A])(implicit F: Pathable[T, ?] :<: F):
      Pathed[T, ?] ~> (Read :+: F)#λ =
    new (Pathed[T, ?] ~> Free[(Read :+: F)#λ, ?]) {
      def apply[A](p: Pathed[T, A]) =
        p.tail.foldRight[A => Free[(Read :+: F)#λ, A]](
          src => Read(src, p.head))(
          (r, acc) => Union(_, Free.roll(Read(Free.point(()), r)), Free.roll(acc(Free.point(())))))(Root ().embed).embed
    }

  def toRead[T[_[_]]: Recursive, F[_]](f: AlgebraM[PlannerError \/ ?, Pathable[T, ?], T[Pathed[T, ?]]])(implicit F: Pathable[T, ?] :<: F):
      T[Pathable[T, ?]] => PlannerError \/ T[(Read :+: F)#λ] =
    _.cataM[PlannerError \/ ?, T[Pathed[T, ?]]](f) ∘ (_.transform(postPathify))

  def pathifyƒ[T[_[_]], F[_]: Traverse](f: AlgebraM[PlannerError \/ ?, Pathable[T, ?], T[Pathed[T, ?]]])(implicit F: Pathable[T, ?] :<: F):
      AlgebraM[PlannerError \/ ?, F, T[(Read :+: F)#λ] \/ T[Pathable[T, ?]]] = {
    case Root() => F.inj(Root[T, T[(Read :+: F)#λ]]()).embed.right.right
    // The LeftShift case is interesting. It pretty much means “grab everything
    // at this directory level”, so we have to handle getting back multiple
    // paths at any point. What is the easiest way for a backend to implement
    // this?
    // Now … should we grab it _statically_, or should the backend generate
    // something like an `ls`, so the physical plan could be run later?
    //
    // in the Union case, the backend should just concatenate the
    // lists from the two sides
    case pp @ (Map(ProjectField(_), _) | LeftShift(_) | Union(_, _, _)) => pp.sequence.right
    case nonPath => nonPath.traverseU(_.fold(_.right, toRead(f))).map(InR(_).embed.left[T[Pathable[T, ?]]])
  }
}
