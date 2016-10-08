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
import quasar.contrib.matryoshka._
import quasar.fp._
import quasar.fs.MonadFsErr
import quasar.qscript.MapFunc._
import quasar.qscript.MapFuncs._

import matryoshka._,
  Recursive.ops._,
  FunctorT.ops._,
  TraverseT.nonInheritedOps._
import matryoshka.patterns._
import scalaz.{:+: => _, Divide => _, _}, Scalaz._, Inject.{ reflexiveInjectInstance => _, _ }, Leibniz._

class Optimize[T[_[_]]: Recursive: Corecursive: EqualT: ShowT] extends TTypes[T] {
  private val UnrefedSrc: QScriptTotal[FreeQS] =
    Inject[QScriptCore, QScriptTotal] inj Unreferenced[T, FreeQS]()

  // TODO: These optimizations should give rise to various property tests:
  //       • elideNopMap ⇒ no `Map(???, HoleF)`
  //       • normalize ⇒ a whole bunch, based on MapFuncs
  //       • elideNopJoin ⇒ no `ThetaJoin(???, HoleF, HoleF, LeftSide === RightSide, ???, ???)`
  //       • coalesceMaps ⇒ no `Map(Map(???, ???), ???)`
  //       • coalesceMapJoin ⇒ no `Map(ThetaJoin(???, …), ???)`

  def elideNopQC[F[_]: Functor, G[_]: Functor]
    (FtoG: F ~> G)
    (implicit QC: QScriptCore :<: F)
      : QScriptCore[T[G]] => G[T[G]] = {
    case Filter(Embed(src), BoolLit(true)) => src
    case Map(Embed(src), mf) if mf ≟ HoleF => src
    case x                                 => FtoG(QC.inj(x))
  }

  def unifySimpleBranches[F[_], A]
    (src: A, l: FreeQS, r: FreeQS, combine: JoinFunc[T])
    (implicit
      QC: QScriptCore :<: F,
      FI: Injectable.Aux[F, QScriptTotal])
      : Option[F[A]] =
    (l.resumeTwice, r.resumeTwice) match {
      case (-\/(m1), -\/(m2)) =>
        (FI.project(m1) >>= QC.prj, FI.project(m2) >>= QC.prj) match {
          // both sides only map over the same data
          case (Some(Map(\/-(SrcHole), mf1)), Some(Map(\/-(SrcHole), mf2))) =>
            QC.inj(Map(src, combine >>= {
              case LeftSide  => mf1
              case RightSide => mf2
            })).some
          // neither side references the src
          case (Some(Map(-\/(src1), mf1)), Some(Map(-\/(src2), mf2)))
              if src1 ≟ UnrefedSrc && src2 ≟ UnrefedSrc =>
            QC.inj(Map(src, combine >>= {
              case LeftSide  => mf1
              case RightSide => mf2
            })).some
          case (_, _) => None
        }
      // one side maps over the src while the other passes the src untouched
      case (-\/(m1), \/-(SrcHole)) => (FI.project(m1) >>= QC.prj) match {
        case Some(Map(\/-(SrcHole), mf1)) =>
          QC.inj(Map(src, combine >>= {
            case LeftSide  => mf1
            case RightSide => HoleF
          })).some
        case _ => None
      }
      case (\/-(SrcHole), -\/(m2)) => (FI.project(m2) >>= QC.prj) match {
        case Some(Map(\/-(SrcHole), mf2)) =>
          QC.inj(Map(src, combine >>= {
            case LeftSide  => HoleF
            case RightSide => mf2
          })).some
        case _ => None
      }
      case (\/-(SrcHole), \/-(SrcHole)) =>
        QC.inj(Map(src, combine.as(SrcHole))).some
      case (_, _) => None
    }

  // FIXME: This really needs to ensure that the condition is that of an
  //        autojoin, otherwise it’ll elide things that are truly meaningful.
  def elideNopJoin[F[_]](implicit QC: QScriptCore :<: F, FI: Injectable.Aux[F, QScriptTotal]) =
    λ[ThetaJoin ~> (Option ∘ F)#λ] {
      case ThetaJoin(src, l, r, on, _, combine) => unifySimpleBranches(src, l, r, combine)(QC, FI)
      case _                                    => None
    }

  def rebaseT[F[_]: Traverse](
    target: FreeQS)(
    src: T[F])(
    implicit FI: Injectable.Aux[F, QScriptTotal]):
      Option[T[F]] =
    freeCata[QScriptTotal, T[QScriptTotal], T[QScriptTotal]](
      target.as(src.transAna(FI.inject)))(recover(_.embed)).transAnaM(FI project _)

  def rebaseTCo[F[_]: Traverse](
    target: FreeQS)(
    srcCo: T[CoEnv[Hole, F, ?]])(
    implicit FI: Injectable.Aux[F, QScriptTotal]):
      Option[T[CoEnv[Hole, F, ?]]] =
    // TODO: with the right instances & types everywhere, this should look like
    //       target.transAnaM(_.htraverse(FI project _)) ∘ (srcCo >> _)
    freeTransCataM[T, Option, QScriptTotal, F, Hole, Hole](
      target)(
      coEnvHtraverse(λ[QScriptTotal ~> (Option ∘ F)#λ](FI.project(_))).apply)
      .map(targ => (targ >> srcCo.fromCoEnv).toCoEnv[T])

  /** Similar to [[elideNopJoin]], this has a more constrained type, because we
    * need to integrate one branch of the join into the source of the resulting
    * map.
    */
  // FIXME: This really needs to ensure that the condition is that of an
  //        autojoin, otherwise it’ll elide things that are truly meaningful.
  def elideOneSidedJoin[F[_], G[_]](
    rebase: FreeQS => T[G] => Option[T[G]])(
    implicit QC: QScriptCore :<: F,
             FI: Injectable.Aux[F, QScriptTotal]):
      ThetaJoin[T[G]] => Option[F[T[G]]] = {

    case ThetaJoin(src, left, right, on, Inner, combine) =>
      (left.resumeTwice, right.resumeTwice) match {
        case (-\/(m1), -\/(m2)) => (FI.project(m1) >>= QC.prj, FI.project(m2) >>= QC.prj) match {
          case (Some(Map(-\/(src1), mf1)), _) if src1 ≟ UnrefedSrc =>
            rebase(right)(src).map(
              tf => QC.inj(Map(tf, combine >>= {
                case LeftSide  => mf1
                case RightSide => HoleF
              })))
          case (_, Some(Map(-\/(src2), mf2))) if src2 ≟ UnrefedSrc =>
            rebase(left)(src).map(
              tf => QC.inj(Map(tf, combine >>= {
                case LeftSide  => HoleF
                case RightSide => mf2
              })))
          case (_, _)=> None
        }
        case (_, _) => None
      }
    case _ => None
  }

  /** Pull more work to _after_ count operations, limiting the dataset. */
  // TODO: we should be able to pull _most_ of a Reduce repair function to after a Subset
  def swapMapSubset[F[_], G[_]: Functor]
    (FtoG: F ~> G)
    (implicit QC: QScriptCore :<: F)
      : QScriptCore[T[G]] => Option[QScriptCore[T[G]]] = {

    val FI = Injectable.inject[QScriptCore, QScriptTotal]

    {
      case Subset(src, from, sel, count) =>
        from.resume.swap.toOption >>= (FI project _) >>= {
          case Map(fromInner, mf) =>
            Map(FtoG(QC.inj(Subset(src, fromInner, sel, count))).embed, mf).some
          case _ => None
        }
      case _ => None
    }
  }

  def compactQC = λ[QScriptCore ~> (Option ∘ QScriptCore)#λ] {
    case LeftShift(src, struct, repair) =>
      rewriteShift(struct, repair) ∘ (xy => LeftShift(src, xy._1, xy._2))

    case Reduce(src, bucket, reducers, repair0) =>
      // `indices`: the indices into `reducers` that are used
      val used    = repair0.map(_.idx).toSet
      val indices = reducers.indices filter used
      val repair  = repair0 map (r => r.copy(indices indexOf r.idx))
      val done    = repair ≟ repair0 || (repair element ReduceIndex.Empty)

      !done option Reduce(src, bucket, (indices map reducers).toList, repair)

    case _ => None
  }

  // /** Chains multiple transformations together, each of which can fail to change
  //   * anything.
  //   */
  // def applyTransforms
  //   (transform: F[T[F]] => Option[F[T[F]]],
  //     transforms: (F[T[F]] => Option[F[T[F]]])*)
  //     : F[T[F]] => Option[F[T[F]]] =
  //   transforms.foldLeft(
  //     transform)(
  //     (prev, next) => x => prev.fold(next(x))(y => next(y).orElse(y.some)))

  // TODO: add reordering
  // - Filter can be moved ahead of Sort
  // - Subset can have a normalized order _if_ their counts are constant
  //   (maybe in some additional cases)

  // The order of optimizations is roughly this:
  // - elide NOPs
  // - read conversion given to us by the filesystem
  // - convert any remaning projects to maps
  // - coalesce nodes
  // - normalize mapfunc
  def applyNormalizations[F[_]: Traverse: Normalizable, G[_]: Traverse](
    prism: PrismNT[G, F],
    rebase: FreeQS => T[G] => Option[T[G]])(
    implicit C: Coalesce.Aux[T, F, F],
             QC: QScriptCore :<: F,
             TJ: ThetaJoin :<: F,
             FI: Injectable.Aux[F, QScriptTotal]):
      F[T[G]] => G[T[G]] =
    repeatedly(Normalizable[F].normalize(_: F[T[G]])) ⋙
      liftFG(injectRepeatedly(elideNopJoin[F].apply[T[G]])) ⋙
      liftFG(injectRepeatedly(elideOneSidedJoin[F, G](rebase))) ⋙
      repeatedly(C.coalesceQC[G](prism)) ⋙
      liftFG(injectRepeatedly(C.coalesceTJ[G](prism.get))) ⋙
      liftFF(repeatedly(compactQC(_: QScriptCore[T[G]]))) ⋙
      (fa => QC.prj(fa).fold(prism.reverseGet(fa))(elideNopQC[F, G](prism.reverseGet)))

  def applyToFreeQS[F[_]: Traverse: Normalizable](
    implicit C:  Coalesce.Aux[T, F, F],
             QC: QScriptCore :<: F,
             TJ: ThetaJoin :<: F,
             FI: Injectable.Aux[F, QScriptTotal]):
      F[T[CoEnv[Hole, F, ?]]] => CoEnv[Hole, F, T[CoEnv[Hole, F, ?]]] =
    applyNormalizations[F, CoEnv[Hole, F, ?]](coenvPrism, rebaseTCo)

  def applyAll[F[_]: Traverse: Normalizable](
    implicit C:  Coalesce.Aux[T, F, F],
             QC: QScriptCore :<: F,
             TJ: ThetaJoin :<: F,
             FI: Injectable.Aux[F, QScriptTotal]):
      F[T[F]] => F[T[F]] =
    applyNormalizations[F, F](idPrism, rebaseT)

  /** Should only be applied after all other QScript transformations. This gives
    * the final, optimized QScript for conversion.
    */
  def optimize[F[_], G[_]: Functor](FtoG: F ~> G)(implicit QC: QScriptCore :<: F)
      : F[T[G]] => F[T[G]] =
    liftFF(repeatedly(swapMapSubset(FtoG)))

  /** A backend-or-mount-specific `f` is provided, that allows us to rewrite
    * [[Root]] (and projections, etc.) into [[Read]], so then we can handle
    * exposing only “true” joins and converting intra-data joins to map
    * operations.
    *
    * `f` takes QScript representing a _potential_ path to a file, converts
    * [[Root]] and its children to path, with the operations post-file remaining.
    */
  def pathify[M[_]: MonadFsErr, IN[_]: Traverse, OUT[_]: Traverse]
    (g: DiscoverPath.ListContents[M])
    (implicit
      FS: DiscoverPath.Aux[T, IN, OUT],
      R:     Const[Read, ?] :<: OUT,
      QC: QScriptCore :<: OUT,
      FI: Injectable.Aux[OUT, QScriptTotal])
      : T[IN] => M[T[OUT]] =
    _.cataM(FS.discoverPath[M](g)) >>= DiscoverPath.unionAll[T, M, OUT](g)
}
