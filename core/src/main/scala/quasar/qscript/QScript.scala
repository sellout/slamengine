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
import MapFuncs._
import quasar._
import quasar.fp._
import quasar.std.StdLib._

import scala.Predef.implicitly

import matryoshka._, FunctorT.ops._, Recursive.ops._
import matryoshka.patterns._
import monocle.macros._
import pathy.Path._
import scalaz.{:+: => _, _}, Scalaz._, Inject._, Leibniz._
import shapeless.{:: => _, Data => _, Coproduct => _, Const => _, _}

// Need to keep track of our non-type-ensured guarantees:
// - all conditions in a ThetaJoin will refer to both sides of the join
// - each `Free` structure in a *Join or Union will have exactly one `point`
// - the common source in a Join or Union will be the longest common branch
// - all Reads have a Root (or another Read?) as their source
// - in `Pathable`, the only `MapFunc` node allowed is a `ObjectProject`

// TODO use real EJson when it lands in master
sealed trait EJson[A]
object EJson {
  def toEJson[T[_[_]]](data: Data): T[EJson] = ???

  final case class Null[A]() extends EJson[A]
  final case class Str[A](str: String) extends EJson[A]

  //def str[A] = pPrism[EJson[A], String] { case Str(str) => str } (Str(_))

  implicit def equal: Delay[Equal, EJson] = new Delay[Equal, EJson] {
    def apply[A](in: Equal[A]): Equal[EJson[A]] = Equal.equal {
      case _ => true
    }
  }

  implicit def functor: Functor[EJson] = new Functor[EJson] {
    def map[A, B](fa: EJson[A])(f: A => B): EJson[B] = fa match {
      case Null() => Null[B]()
      case Str(str) => Str[B](str)
    }
  }

  implicit def show: Delay[Show, EJson] = new Delay[Show, EJson] {
    def apply[A](sh: Show[A]): Show[EJson[A]] = Show.show {
      case Null() => Cord("Null()")
      case Str(str) => Cord(s"Str($str)")
    }
  }
}

object DataLevelOps {

  // TODO this should be found from matryoshka - why isn't it being found!?!?
  implicit def NTEqual[F[_], A](implicit A: Equal[A], F: Equal ~> λ[α => Equal[F[α]]]):
    Equal[F[A]] =
  F(A)

  implicit def JoinBranchEqual[F[_]: Functor](implicit F: Delay[Equal, F]):
      Equal[JoinBranch[F]] =
    freeEqual[F].apply(Equal[Unit])

  sealed trait JoinSide
  final case object LeftSide extends JoinSide
  final case object RightSide extends JoinSide

  object JoinSide {
    implicit val equal: Equal[JoinSide] = Equal.equalRef
    implicit val show: Show[JoinSide] = Show.showFromToString
  }

  type FreeMap[T[_[_]]] = Free[MapFunc[T, ?], Unit]
  type JoinFunc[T[_[_]]] = Free[MapFunc[T, ?], JoinSide]
  type JoinBranch[F[_]] = Free[F, Unit]

  def UnitF[T[_[_]]] = Free.point[MapFunc[T, ?], Unit](())
}

import DataLevelOps._

sealed trait SortDir
final case object Ascending  extends SortDir
final case object Descending extends SortDir

// TODO: Just reuse the version of this from LP?
object SortDir {
  implicit val equal: Equal[SortDir] = Equal.equalRef
  implicit val show: Show[SortDir] = Show.showFromToString
}

sealed trait JoinType
final case object Inner extends JoinType
final case object FullOuter extends JoinType
final case object LeftOuter extends JoinType
final case object RightOuter extends JoinType

object JoinType {
  implicit val equal: Equal[JoinType] = Equal.equalRef
  implicit val show: Show[JoinType] = Show.showFromToString
}

sealed trait DeadEnd

sealed trait SourcedPathable[T[_[_]], F[_], A] {
  def src: A
}

object SourcedPathable {
  implicit def equal[T[_[_]], F[_]: Functor](implicit E: Equal[T[EJson]], F: Delay[Equal, F]):
      Delay[Equal, SourcedPathable[T, F, ?]] =
    new Delay[Equal, SourcedPathable[T, F, ?]] {
      def apply[A](eq: Equal[A]) =
        Equal.equal {
          case (Map(a1, f1), Map(a2, f2)) => f1 ≟ f2 && eq.equal(a1, a2)
          case (LeftShift(a1, s1, r1), LeftShift(a2, s2, r2)) =>
            eq.equal(a1, a2) && s1 ≟ s2 && r1 ≟ r2
          case (Union(a1, l1, r1), Union(a2, l2, r2)) =>
            eq.equal(a1, a2) && l1 ≟ l2 && r1 ≟ r2
          case (_, _) => false
        }
    }

  implicit def traverse[T[_[_]], F[_]]: Traverse[SourcedPathable[T, F, ?]] =
    new Traverse[SourcedPathable[T, F, ?]] {
      def traverseImpl[G[_], A, B](
        fa: SourcedPathable[T, F, A])(
        f: A => G[B])(
        implicit G: Applicative[G]):
          G[SourcedPathable[T, F, B]] =
        fa match {
          case Map(a, func)       => f(a) ∘ (Map[T, F, B](_, func))
          case LeftShift(a, s, r) => f(a) ∘ (LeftShift(_, s, r))
          case Union(a, l, r)     => f(a) ∘ (Union(_, l, r))
        }
    }

  implicit def show[T[_[_]], F[_]](implicit shEj: Show[T[EJson]]): Delay[Show, SourcedPathable[T, F, ?]] =
    new Delay[Show, SourcedPathable[T, F, ?]] {
      def apply[A](s: Show[A]): Show[SourcedPathable[T, F, A]] = Show.show(_ match {
        case Map(src, mf) => Cord("Map(") ++ s.show(src) ++ Cord(",") ++ Show[FreeMap[T]].show(mf) ++ Cord(")")
        case _ => Cord("some other sourced pathable sorry")
      })
    }

  implicit def mergeable[T[_[_]]: Corecursive, F[_]]: Mergeable.Aux[T, SourcedPathable[T, F, Unit]] = new Mergeable[SourcedPathable[T, F, Unit]] {
    type IT[F[_]] = T[F]

    def mergeSrcs(
      left: FreeMap[IT],
      right: FreeMap[IT],
      p1: SourcedPathable[IT, F, Unit],
      p2: SourcedPathable[IT, F, Unit]) =
      (p1, p2) match {
        case (Map(_, m1), Map(_, m2)) => {
          val lf =
            Free.roll(ObjectProject[IT, FreeMap[IT]](UnitF, Free.roll[MapFunc[IT, ?], Unit](StrLit[IT, FreeMap[IT]]("tmp1"))))
          val rf =
            Free.roll(ObjectProject[IT, FreeMap[IT]](UnitF, Free.roll[MapFunc[IT, ?], Unit](StrLit[IT, FreeMap[IT]]("tmp2"))))

          AbsMerge[MapFunc[IT, ?], SourcedPathable[IT, F, Unit]](Map((), Free.roll[MapFunc[IT, ?], Unit](
            ObjectConcat(
              Free.roll[MapFunc[IT, ?], Unit](MakeObject[IT, FreeMap[T]](Free.roll(StrLit[IT, FreeMap[T]]("tmp1")), m1 >> left)),
              Free.roll[MapFunc[IT, ?], Unit](MakeObject[IT, FreeMap[T]](Free.roll(StrLit[IT, FreeMap[T]]("tmp2")), m2 >> right))))),
            lf, rf).some
        }
        case _ => None
      }
  }

}

object DeadEnd {
  implicit def equal: Equal[DeadEnd] = Equal.equalRef
  implicit def show: Show[DeadEnd] = Show.showFromToString

  implicit def mergeable[T[_[_]]]: Mergeable.Aux[T, DeadEnd] =
    new Mergeable[DeadEnd] {
      type IT[F[_]] = T[F]

      def mergeSrcs(
        left: FreeMap[IT],
        right: FreeMap[IT],
        p1: DeadEnd,
        p2: DeadEnd) =
        if (p1 === p2)
          Some(AbsMerge[MapFunc[IT, ?], DeadEnd](p1, UnitF, UnitF))
        else
          None
    }
}

/** The top level of a filesystem. During compilation this represents `/`, but
  * in the structure a backend sees, it represents the mount point.
  */
final case object Root extends DeadEnd

final case object Empty extends DeadEnd

/** A data-level transformation.
  */
final case class Map[T[_[_]], F[_], A](src: A, f: FreeMap[T])
    extends SourcedPathable[T, F, A]
// Map(LeftShift(/foo/bar/baz), ObjectConcat(ObjectProject((), "foo"), ObjectProject((), "bar")))

/** Flattens nested structure, converting each value into a data set, which are
  * then unioned.
  *
  * `struct` is an expression that evaluates to an array or object, which is
  * then “exploded” into multiple values. `repair` is applied across the new
  * set, integrating the exploded values into the original set.
  */

 //{ ts: 2016.01... }
 //{ ts: "2016-..." }
 //...

 // /foo/bar/baz: { date: ___, time: ___ }
 // /foo/bar/baz: { 1: 2016 }
 // TIMESTAMP(OP((), date) || OP((), time))


 // select [quux, timestamp(date, time){*}] from `/foo/bar/baz`
 //
 // { quux: ???, 1: "2016" } 
 // { quux: ???, 1: "05" } 
 //
 // /foo/bar/baz: 

final case class LeftShift[T[_[_]], F[_], A](
  src: A,
  struct: FreeMap[T],
  repair: JoinFunc[T])
    extends SourcedPathable[T, F, A]

/** Creates a new dataset, |a|+|b|, containing all of the entries from each of
  * the input sets, without any indication of which set they came from
  *
  * This could be handled as another join type, the anti-join
  * (T[EJson] \/ T[EJson] => T[EJson], specifically as `_.merge`), with the
  * condition being `κ(true)`,
  */
final case class Union[T[_[_]], F[_], A](
  src: A,
  lBranch: JoinBranch[F],
  rBranch: JoinBranch[F])
    extends SourcedPathable[T, F, A]

sealed trait QScriptCore[T[_[_]], F[_], A] {
  def src: A
}

object QScriptCore {
  implicit def equal[T[_[_]], F[_]: Functor](
    implicit E: Equal[T[EJson]], F: Delay[Equal, F]):
      Delay[Equal, QScriptCore[T, F, ?]] =
    new Delay[Equal, QScriptCore[T, F, ?]] {
      def apply[A](eq: Equal[A]) =
        Equal.equal {
          case (Reduce(a1, b1, f1, r1), Reduce(a2, b2, f2, r2)) =>
            b1 ≟ b2 && f1 ≟ f2 && r1 ≟ r2 && eq.equal(a1, a2)
          case (Sort(a1, b1, o1), Sort(a2, b2, o2)) =>
            b1 ≟ b2 && o1 ≟ o2 && eq.equal(a1, a2)
          case (Filter(a1, f1), Filter(a2, f2)) => f1 ≟ f2 && eq.equal(a1, a2)
          case (Take(a1, f1, c1), Take(a2, f2, c2)) => eq.equal(a1, a2) && f1 ≟ f2 && c1 ≟ c2
          case (Drop(a1, f1, c1), Drop(a2, f2, c2)) => eq.equal(a1, a2) && f1 ≟ f2 && c1 ≟ c2
          case (_, _) => false
        }
    }

  implicit def traverse[T[_[_]], F[_]]: Traverse[QScriptCore[T, F, ?]] =
    new Traverse[QScriptCore[T, F, ?]] {
      def traverseImpl[G[_]: Applicative, A, B](
        fa: QScriptCore[T, F, A])(
        f: A => G[B]) =
        fa match {
          case Reduce(a, b, func, repair) => f(a) ∘ (Reduce(_, b, func, repair))
          case Sort(a, b, o)              => f(a) ∘ (Sort(_, b, o))
          case Filter(a, func)            => f(a) ∘ (Filter(_, func))
          case Take(a, from, c)           => f(a) ∘ (Take(_, from, c))
          case Drop(a, from, c)           => f(a) ∘ (Drop(_, from, c))
          case PatternGuard(a, typ, cont, fb) => f(a) ∘ (PatternGuard(_, typ, cont, fb))
        }
    }

  implicit def show[T[_[_]], F[_]](implicit EJ: Show[T[EJson]]):
      Delay[Show, QScriptCore[T, F, ?]] =
    new Delay[Show, QScriptCore[T, F, ?]] {
      def apply[A](s: Show[A]): Show[QScriptCore[T, F, A]] =
        Show.show {
          case Reduce(a, b, func, repair) => Cord("Reduce(") ++ s.show(a) ++ b.show ++ // func.show ++ repair.show ++
            Cord(")")
          case Sort(a, b, o)              => Cord("Sort(") ++ s.show(a) ++ b.show ++ o.show ++ Cord(")")
          case Filter(a, func)            => Cord("Filter(") ++ s.show(a) ++ func.show ++ Cord(")")
          case Take(a, f, c)              => Cord("Take(") ++ s.show(a) ++ // f.show ++ c.show ++
            Cord(")")
          case Drop(a, f, c)              => Cord("Drop(") ++ s.show(a) ++ // f.show ++ c.show ++
            Cord(")")
          case PatternGuard(a, typ, cont, fb) =>
            Cord("PatternGuard(") ++ s.show(a) ++ typ.show ++ cont.show ++ fb.show ++ Cord(")")
        }
    }

  implicit def mergeable[T[_[_]], F[_]]:
      Mergeable.Aux[T, QScriptCore[T, F, Unit]] =
    new Mergeable[QScriptCore[T, F, Unit]] {
      type IT[F[_]] = T[F]

      def mergeSrcs(
        left: FreeMap[IT],
        right: FreeMap[IT],
        p1: QScriptCore[IT, F, Unit],
        p2: QScriptCore[IT, F, Unit]) =
        (p1, p2) match {
          case (t1, t2) if t1 == t2 => AbsMerge[MapFunc[IT, ?], QScriptCore[IT, F, Unit]](t1, UnitF, UnitF).some
          case (Reduce(_, bucket1, func1, rep1), Reduce(_, bucket2, func2, rep2)) => {
            val mapL = bucket1 >> left
            val mapR = bucket2 >> right

            if (mapL == mapR)
              AbsMerge[MapFunc[IT, ?], QScriptCore[IT, F, Unit]](
                Reduce((), mapL, func1 // ++ func2 // TODO: append Sizeds
                  , rep1),
                UnitF,
                UnitF).some
            else
              None
          }
          case (_, _) => None
        }
    }
}

// This is _perhaps_ just another MapFunc case.
final case class PatternGuard[T[_[_]], F[_], A](
  src: A,
  typ: Type,
  cont: FreeMap[T],
  fallback: FreeMap[T])
    extends QScriptCore[T, F, A]

/** Performs a reduction over a dataset, with the dataset partitioned by the
  * result of the MapFunc. So, rather than many-to-one, this is many-to-fewer.
  *
  * `bucket` partitions the values into buckets based on the result of the
  * expression, `reducers` applies the provided reduction to each expression,
  * and repair finally turns those reduced expressions into a final value.
  *
  * @group MRA
  */
final case class Reduce[T[_[_]], F[_], A, N <: Succ[_]](
  src: A,
  bucket: FreeMap[T],
  reducers: Sized[List[ReduceFunc[FreeMap[T]]], N],
  repair: Free[MapFunc[T, ?], Fin[N]])
    extends QScriptCore[T, F, A]

/** Sorts values within a bucket. This could be represented with
  *     LeftShift(Map(_.sort, Reduce(_ :: _, ???))
  * but backends tend to provide sort directly, so this avoids backends having
  * to recognize the pattern. We could provide an algebra
  *     (Sort :+: QScript)#λ => QScript
  * so that a backend without a native sort could eliminate this node.
  */
// Should this operate on a sequence of mf/order pairs? Might be easier for
// implementers to handle stable sorting that way.
final case class Sort[T[_[_]], F[_], A](src: A, bucket: FreeMap[T], order: SortDir)
    extends QScriptCore[T, F, A]

/** Eliminates some values from a dataset, based on the result of FilterFunc.
  */
final case class Filter[T[_[_]], F[_], A](src: A, f: FreeMap[T])
    extends QScriptCore[T, F, A]

final case class Take[T[_[_]], F[_], A](src: A, from: JoinBranch[F], count: JoinBranch[F])
    extends QScriptCore[T, F, A]

final case class Drop[T[_[_]], F[_], A](src: A, from: JoinBranch[F], count: JoinBranch[F])
    extends QScriptCore[T, F, A]

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
@Lenses final case class ThetaJoin[T[_[_]], F[_], A](
  src: A,
  lBranch: JoinBranch[F],
  rBranch: JoinBranch[F],
  on: JoinFunc[T],
  f: JoinType,
  combine: JoinFunc[T])

object ThetaJoin {
  implicit def equal[T[_[_]], F[_]: Functor](
    implicit E: Equal[T[EJson]], F: Delay[Equal, F]):
      Delay[Equal, ThetaJoin[T, F, ?]] =
    new Delay[Equal, ThetaJoin[T, F, ?]] {
      def apply[A](eq: Equal[A]) =
        Equal.equal {
          case (ThetaJoin(a1, l1, r1, o1, f1, c1), ThetaJoin(a2, l2, r2, o2, f2, c2)) =>
            eq.equal(a1, a2) && l1 ≟ l2 && r1 ≟ r2 && o1 ≟ o2 && f1 ≟ f2 && c1 ≟ c2
        }
    }

  implicit def traverse[T[_[_]], F[_]]: Traverse[ThetaJoin[T, F, ?]] =
    new Traverse[ThetaJoin[T, F, ?]] {
      def traverseImpl[G[_]: Applicative, A, B](
        fa: ThetaJoin[T, F, A])(
        f: A => G[B]) =
        f(fa.src) ∘ (ThetaJoin(_, fa.lBranch, fa.rBranch, fa.on, fa.f, fa.combine))
    }


  implicit def show[T[_[_]]: Recursive, F[_]: Functor](
    implicit E: Show[T[EJson]], F: Delay[Show, F]):
      Delay[Show, ThetaJoin[T, F, ?]] =
    new Delay[Show, ThetaJoin[T, F, ?]] {
      def apply[A](showA: Show[A]): Show[ThetaJoin[T, F, A]] = Show.show {
        case ThetaJoin(src, lBr, rBr, on, f, combine) =>
          Cord("ThetaJoin(") ++
          showA.show(src) ++ Cord(",") ++
          Show[JoinBranch[F]].show(lBr) ++ Cord(",") ++
          Show[JoinBranch[F]].show(rBr) ++ Cord(",") ++
          Show[JoinFunc[T]].show(on) ++ Cord(",") ++
          Show[JoinType].show(f) ++ Cord(",") ++
          Show[JoinFunc[T]].show(combine) ++ Cord(")")
      }
    }

  implicit def mergeable[T[_[_]], F[_]]:
      Mergeable.Aux[T, ThetaJoin[T, F, Unit]] =
    new Mergeable[ThetaJoin[T, F, Unit]] {
      type IT[F[_]] = T[F]

      def mergeSrcs(
        left: FreeMap[IT],
        right: FreeMap[IT],
        p1: ThetaJoin[IT, F, Unit],
        p2: ThetaJoin[IT, F, Unit]) =
        if (p1 == p2)
          Some(AbsMerge[MapFunc[IT, ?], ThetaJoin[IT, F, Unit]](p1, UnitF, UnitF))
        else
          None
    }
}

// backends can choose to rewrite joins using EquiJoin
// can rewrite a ThetaJoin as EquiJoin + Filter
final case class EquiJoin[T[_[_]], F[_], A](
  lKey: FreeMap[T],
  rKey: FreeMap[T],
  f: JoinType,
  src: A,
  lBranch: JoinBranch[F],
  rBranch: JoinBranch[F])

object EquiJoin {
  implicit def equal[T[_[_]], F[_]: Functor](
    implicit E: Equal[T[EJson]], F: Delay[Equal, F]):
      Delay[Equal, EquiJoin[T, F, ?]] =
    new Delay[Equal, EquiJoin[T, F, ?]] {
      def apply[A](eq: Equal[A]) =
        Equal.equal {
          case (EquiJoin(lk1, rk1, f1, a1, l1, r1),
                EquiJoin(lk2, rk2, f2, a2, l2, r2)) =>
            lk1 ≟ lk2 && rk1 ≟ rk2 && f1 ≟ f2 && eq.equal(a1, a2) && l1 ≟ l2 && r1 ≟ r2
        }
    }

  implicit def traverse[T[_[_]], F[_]]: Traverse[EquiJoin[T, F, ?]] =
    new Traverse[EquiJoin[T, F, ?]] {
      def traverseImpl[G[_]: Applicative, A, B](
        fa: EquiJoin[T, F, A])(
        f: A => G[B]) =
        f(fa.src) ∘
          (EquiJoin(fa.lKey, fa.rKey, fa.f, _, fa.lBranch, fa.rBranch))
    }
}

class Transform[T[_[_]]: Recursive: Corecursive, F[_]: Functor: Linearizable](
  implicit DE: Const[DeadEnd, ?] :<: F,
           SP: SourcedPathable[T, F, ?] :<: F,
           QC: QScriptCore[T, F, ?] :<: F,
           TJ: ThetaJoin[T, F, ?] :<: F,
           F:  Mergeable.Aux[T, F[Unit]],
           EJ: Equal[T[EJson]]) {
  import MapFuncs._

  type Merge[A] = AbsMerge[MapFunc[T, ?], A]

  // TODO[matryoshka]: This is in the version after 0.11.0.
  implicit def coenvFunctor[F[_]: Functor, A]: Functor[CoEnv[A, F, ?]] =
    new Functor[CoEnv[A, F, ?]] {
      def map[R, B](fa: CoEnv[A, F, R])(f: R => B): CoEnv[A, F, B] =
        CoEnv(fa.run.map(_.map(f)))
    }

  implicit def coproductLinearizable[F[_]: Linearizable, G[_]: Linearizable]:
      Linearizable[Coproduct[F, G, ?]] =
    new Linearizable[Coproduct[F, G, ?]] {
      def linearize[H[_]](
        fl: Coproduct[F, G, List[H[Unit]]])(
        implicit Co: Coproduct[F, G, ?] :<: H) =
        fl.run.fold(Linearizable[F].linearize[H], Linearizable[G].linearize[H])
    }

  implicit def constLinearizable[A]: Linearizable[Const[A, ?]] =
    new Linearizable[Const[A, ?]] {
      def linearize[G[_]](
        fl: Const[A, List[G[Unit]]])(
        implicit F: Const[A, ?] :<: G) =
        Nil
    }

  implicit def sourcedPathableLinearizable[T[_[_]], F[_]]:
      Linearizable[SourcedPathable[T, F, ?]] =
    new Linearizable[SourcedPathable[T, F, ?]] {
      def linearize[G[_]](
        fl: SourcedPathable[T, F, List[G[Unit]]])(
        implicit F: SourcedPathable[T, F, ?] :<: G) =
        F.inj(fl.void) :: fl.src
    }

  implicit def qscriptCoreLinearizable[T[_[_]], F[_]]:
      Linearizable[QScriptCore[T, F, ?]] =
    new Linearizable[QScriptCore[T, F, ?]] {
      def linearize[G[_]](fl: QScriptCore[T, F, List[G[Unit]]])(
        implicit F: QScriptCore[T, F, ?] :<: G) =
        F.inj(fl.void) :: fl.src
    }

  implicit def thetaJoinLinearizable[T[_[_]], F[_]]:
      Linearizable[ThetaJoin[T, F, ?]] =
    new Linearizable[ThetaJoin[T, F, ?]] {
      def linearize[G[_]](fl: ThetaJoin[T, F, List[G[Unit]]])(
        implicit F: ThetaJoin[T, F, ?] :<: G) =
        F.inj(fl.void) :: fl.src
    }

  def delinearizeInner[F[_]: Functor, A](implicit D: Const[DeadEnd, ?] :<: F):
      Coalgebra[F, List[F[A]]] = {
    case Nil    => D.inj(Const(Root))
    case h :: t => h.map(_ => t)
  }

  def delinearizeJoinBranch[F[_]: Functor, A]:
      Coalgebra[CoEnv[Unit, F, ?], List[F[A]]] =
    fs => CoEnv(fs match {
      case Nil => ().left
      case h :: t => h.map(_ => t).right
    })

  type Pures[F[_], A] = List[F[A]]
  type DoublePures[F[_]] = (Pures[F, Unit], Pures[F, Unit])
  type DoubleFreeMap[T[_[_]]] = (FreeMap[T], FreeMap[T])
  type TriplePures[F[_]] = (Pures[F, Unit], Pures[F, Unit], Pures[F, Unit])

  val consZipped: Algebra[ListF[F[Unit], ?], TriplePures[F]] = {
    case NilF() => (Nil, Nil, Nil)
    case ConsF(head, (acc, l, r)) => (head :: acc, l, r)
  }

  val zipper:
      ElgotCoalgebra[
        TriplePures[F] \/ ?,
        ListF[F[Unit], ?],
        (DoubleFreeMap[T], DoublePures[F])] = {
    case ((_, _), (Nil, Nil)) => (Nil, Nil, Nil).left
    case ((_, _), (Nil, r))   => (Nil, Nil, r).left
    case ((_, _), (l,   Nil)) => (Nil, l,   Nil).left
    case ((lm, rm), (l :: ls, r :: rs)) => {
      scala.Predef.println(s"($lm, $rm), ($l :: $ls, $r :: $rs)")

      F.mergeSrcs(lm, rm, l, r).fold[TriplePures[F] \/ ListF[F[Unit], (DoubleFreeMap[T], DoublePures[F])]](
        (Nil, l :: ls, r :: rs).left) {
        case AbsMerge(inn, lmf, rmf) => ConsF(inn, ((lmf, rmf), (ls, rs))).right[TriplePures[F]]
      }
    }
  }

  def merge(left: T[F], right: T[F]): AbsMerge[F, T[F]] = {
    val lLin: List[F[Unit]] = left.cata(Linearizable[F].linearize[F]).reverse
    val rLin: List[F[Unit]] = right.cata(Linearizable[F].linearize[F]).reverse

    val (common, lTail, rTail) =
      ((UnitF[T], UnitF[T]), (lLin, rLin)).elgot(consZipped, zipper)

    AbsMerge[F, T[F]](
      common.reverse.ana[T, F](delinearizeInner),
      foldIso(CoEnv.freeIso[Unit, F]).get(lTail.reverse.ana[T, CoEnv[Unit, F, ?]](delinearizeJoinBranch)),
      foldIso(CoEnv.freeIso[Unit, F]).get(rTail.reverse.ana[T, CoEnv[Unit, F, ?]](delinearizeJoinBranch)))
  }

  def merge2Map(
    values: Func.Input[T[F], nat._2])(
    func: (FreeMap[T], FreeMap[T]) => MapFunc[T, FreeMap[T]]):
      SourcedPathable[T, F, T[F]] = {

    val AbsMerge(merged, left, right) = merge(values(0), values(1))
    val res: Merge[ThetaJoin[T, F, T[F]]] = makeBasicTheta(merged, left, right)

    Map(TJ.inj(res.src).embed, Free.roll(func(res.left, res.right)))
  }

  def merge3Map(
    values: Func.Input[T[F], nat._3])(
    func: (FreeMap[T], FreeMap[T], FreeMap[T]) => MapFunc[T, FreeMap[T]]):
      SourcedPathable[T, F, T[F]] = {

    val AbsMerge(merged, first, second) = merge(values(0), values(1))
    val AbsMerge(merged2, fands, third) = merge(merged, values(2))

    val res = makeBasicTheta(merged2, first, second)
    val res2 = makeBasicTheta(TJ.inj(res.src).embed, fands, third)

    Map(TJ.inj(res2.src).embed,
      Free.roll(func(
        res2.left >> res.left,
        res2.left >> res.right,
        res2.right)))
  }

  def makeBasicTheta[A](src: A, left: JoinBranch[F], right: JoinBranch[F]):
      Merge[ThetaJoin[T, F, A]] = {
    AbsMerge[MapFunc[T, ?], ThetaJoin[T, F, A]](
      ThetaJoin(src, left, right, basicJF, Inner,
        Free.roll(ObjectConcat(
          Free.roll(MakeObject(Free.roll(StrLit[T, JoinFunc[T]]("tmp1")), Free.point(LeftSide))),
          Free.roll(MakeObject(Free.roll(StrLit[T, JoinFunc[T]]("tmp2")), Free.point(RightSide)))))),
      Free.roll(ObjectProject(UnitF, Free.roll(StrLit("tmp1")))),
      Free.roll(ObjectProject(UnitF, Free.roll(StrLit("tmp2")))))
  }

  def wrapUnary[A](func: Unary[T, FreeMap[T]]):
      Coalgebra[SourcedPathable[T, F, ?], A] =
    Map(_, Free.roll(func))

  def invokeMapping1[T[_[_]], A](
    func: UnaryFunc, values: Func.Input[A, nat._1]):
      SourcedPathable[T, F, A] =
    Map(
      values(0),
      Free.roll(func match {
        case structural.MakeArray => MakeArray(UnitF)
        case _ => ??? // TODO
      }))

  def invokeMapping2(func: BinaryFunc, values: Func.Input[T[F], nat._2]):
      SourcedPathable[T, F, T[F]] =
    merge2Map(values)(func match {
      case structural.MakeObject => MakeObject(_, _)
      case math.Add      => Add(_, _)
      case math.Multiply => Multiply(_, _)
      case math.Subtract => Subtract(_, _)
      case math.Divide   => Divide(_, _)
      case string.Concat
         | structural.ArrayConcat
         | structural.ConcatOp => ArrayConcat(_, _)
      case _ => ??? // TODO
    })

  def invokeMapping3(func: TernaryFunc, values: Func.Input[T[F], nat._3]):
      SourcedPathable[T, F, T[F]] =
    merge3Map(values)(func match {
      case relations.Between => Between(_, _, _)
      case _ => ??? // TODO
    })

  // TODO we need to handling bucketing from GroupBy
  // the buckets will not always be UnitF, if we have grouped previously
  //
  // TODO also we should be able to statically guarantee that we are matching on all reductions here
  // this involves changing how DimensionalEffect is assigned (algebra rather than parameter)
  def invokeReduction[A](func: UnaryFunc, values: Func.Input[A, nat._1]):
      QScriptCore[T, F, A] =
    Reduce[T, F, A, nat._1](values(0), UnitF, Sized[List](func match {
      case agg.Count     => Count[FreeMap[T]](UnitF)
      case agg.Sum       => Sum[FreeMap[T]](UnitF)
      case agg.Min       => Min[FreeMap[T]](UnitF)
      case agg.Max       => Max[FreeMap[T]](UnitF)
      case agg.Avg       => Avg[FreeMap[T]](UnitF)
      case agg.Arbitrary => Arbitrary[FreeMap[T]](UnitF)
    }), Free.point(Fin[nat._0, nat._1]))

  val basicJF: JoinFunc[T] =
    Free.roll(Eq(Free.point(LeftSide), Free.point(RightSide)))

  val elideNopMaps: SourcedPathable[T, F, T[F]] => F[T[F]] = {
    case Map(src, mf) if Equal(quasar.qscript.DataLevelOps.NTEqual[Free[MapFunc[T, ?], ?], Unit](implicitly, freeEqual[MapFunc[T, ?]])).equal(mf, UnitF) => src.project
    case x                          => SP.inj(x)
  }

  def elideNopJoins(implicit F: Delay[Equal, F]):
      ThetaJoin[T, F, T[F]] => F[T[F]] = {
    case ThetaJoin(src, l, r, on, _, combine)
        if l ≟ Free.point(()) && r ≟ Free.point(()) && on ≟ basicJF =>
      SP.inj(Map(src, combine.void))
    case x => TJ.inj(x)
  }

  // TODO write extractor for inject
  val coalesceMap:
      SourcedPathable[T, F, T[F]] => SourcedPathable[T, F, T[F]] = {
    case x @ Map(Embed(src), mf) => SP.prj(src) match {
      case Some(Map(srcInner, mfInner)) => Map(srcInner, mf >> mfInner)
      case _ => x
    }
    case x => x
  }

  def liftQSAlgebra[F[_], G[_], A](orig: G[A] => F[A])(
    implicit G: G :<: F): (F[A] => F[A]) = ftf => {
    G.prj(ftf).fold(ftf)(orig) //Option[ThetaJoin[T, F, T[F]]]
  }

  def liftQSAlgebra2[F[_], G[_], A](orig: G[A] => G[A])(
    implicit G: G :<: F): (F[A] => F[A]) = ftf => {
    G.prj(ftf).fold(ftf)(orig.andThen(G.inj))
  }

  def pathToProj(path: pathy.Path[_, _, _]): FreeMap[T] =
    pathy.Path.peel(path).fold[FreeMap[T]](
      Free.point(())) {
      case (p, n) =>
        Free.roll(ObjectProject(pathToProj(p),
          Free.roll(StrLit[T, FreeMap[T]](n.fold(_.value, _.value)))))
    }

  val lpToQScript: LogicalPlan[T[F]] => F[T[F]] = {
    case LogicalPlan.ReadF(path) =>
      SP.inj(Map(DE.inj(Const[DeadEnd, T[F]](Root)).embed, pathToProj(path)))

    case LogicalPlan.ConstantF(data) => SP.inj(Map(
      DE.inj(Const[DeadEnd, T[F]](Root)).embed,
      Free.roll[MapFunc[T, ?], Unit](Nullary[T, FreeMap[T]](EJson.toEJson[T](data)))))

    case LogicalPlan.FreeF(name) => SP.inj(Map(
      DE.inj(Const[DeadEnd, T[F]](Empty)).embed,
      Free.roll(ObjectProjectFree(Free.roll(StrLit(name.toString)), UnitF))))

      // case LogicalPlan.TypecheckF(expr, typ, cont, fallback) =>
      //   QC.inj(PatternGuard(expr, typ, ???, ???))

    // TODO this illustrates the untypesafe ugliness b/c the pattern match does not guarantee the appropriate sized `Sized`
    // https://github.com/milessabin/shapeless/pull/187
    case LogicalPlan.InvokeFUnapply(func @ UnaryFunc(_, _, _, _, _, _, _, _), Sized(a1)) if func.effect == Mapping =>
      SP.inj(invokeMapping1(func, Func.Input1(a1)))

    case LogicalPlan.InvokeFUnapply(func @ BinaryFunc(_, _, _, _, _, _, _, _), Sized(a1, a2)) if func.effect == Mapping =>
      SP.inj(invokeMapping2(func, Func.Input2(a1, a2)))

    case LogicalPlan.InvokeFUnapply(func @ TernaryFunc(_, _, _, _, _, _, _, _), Sized(a1, a2, a3)) if func.effect == Mapping =>
      SP.inj(invokeMapping3(func, Func.Input3(a1, a2, a3)))

    case LogicalPlan.InvokeFUnapply(func @ UnaryFunc(_, _, _, _, _, _, _, _), Sized(a1)) if func.effect == Reduction =>
      QC.inj(invokeReduction(func, Func.Input1(a1)))

    case LogicalPlan.InvokeFUnapply(set.Take, Sized(a1, a2)) =>
      val AbsMerge(src, jb1, jb2) = merge(a1, a2)
      QC.inj(Take(src, jb1, jb2))

    case LogicalPlan.InvokeFUnapply(set.Drop, Sized(a1, a2)) =>
      val AbsMerge(src, jb1, jb2) = merge(a1, a2)
      QC.inj(Drop(src, jb1, jb2))

    case LogicalPlan.InvokeFUnapply(set.Filter, Sized(a1, a2)) =>
      val AbsMerge(src, jb1, jb2) = merge(a1, a2)

      makeBasicTheta(src, jb1, jb2) match {
        case AbsMerge(src, fm1, fm2) =>
          SP.inj(Map(QC.inj(Filter(TJ.inj(src).embed, fm2)).embed, fm1))
      }

      //case LogicalPlan.InvokeF(func @ BinaryFunc(_, _, _, _, _, _, _, _), input) if func.effect == Expansion => invokeLeftShift(func, input)

      //// handling bucketing for sorting
      //// e.g. squashing before a reduce puts everything in the same bucket
      //// TODO consider removing Squashing entirely - and using GroupBy exclusively
      //// Reduce(Sort(LeftShift(GroupBy)))  (LP)
      //// Reduce(Add(GB, GB))
      //// LeftShift and Projection can change grouping/bucketing metadata
      //// y := select sum(pop) (((from zips) group by state) group by substring(city, 0, 2))
      //// z := select sum(pop) from zips group by city
      //case LogicalPlan.InvokeF(func @ UnaryFunc(_, _, _, _, _, _, _, _), input) if func.effect == Squashing => ??? // returning the source with added metadata - mutiple buckets

      //case LogicalPlan.InvokeF(func @ BinaryFunc(_, _, _, _, _, _, _, _), input) => {
      //  func match {
      //    case GroupBy => ??? // returning the source with added metadata - mutiple buckets
      //    case UnionAll => ??? //UnionAll(...)
      //    // input(0) ~ (name, thing)
      //    case IntersectAll => ObjProj(left, ThetaJoin(Eq, Inner, Root(), input(0), input(1)))  // inner join where left = right, combine func = left (whatever)
      //    case Except => ObjProj(left, ThetaJoin(False, LeftOuter, Root(), input(0), input(1)))
      //  }
      //}
      //case LogicalPlan.InvokeF(func @ TernaryFunc, input) => {
      //  func match {
      //    // src is Root() - and we rewrite lBranch/rBranch so that () refers to Root()
      //    case InnerJoin => ThetaJoin(input(2), Inner, Root(), input(0), input(1)) // TODO use input(2)
      //    case LeftOuterJoin => ThetaJoin(input(2), LeftOuter, Root(), input(0), input(1)) // TODO use input(2)
      //    case RightOuterJoin => ???
      //    case FullOuterJoin => ???
      //  }
      //}

      //// Map(src=form, MakeObject(name, ()))
      //// Map(Map(src=form, MakeObject(name, ())), body)
      //case LogicalPlan.LetF(name, form, body) => rewriteLet(body)(qsRewrite(name, form))

    case _ => ??? // TODO
  }
}
