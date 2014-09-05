package slamdata.engine.analysis

import scalaz.{Tree => ZTree, _}
import scalaz.std.list._

import fixplate._
import slamdata.engine.fp._

sealed trait Diff[F[_]]
object Diff {
  /** This branch is the same all the way to the tips of its leaves */
  case class Same[F[_]](ident: F[Term[F]]) extends Diff[F]
  /** This node is the same, but it has at least one branch that differs */
  case class Similar[F[_]](ident: F[Diff[F]]) extends Diff[F]
  /** This node differs between the two trees */
  case class Different[F[_]](left: F[Term[F]], right: F[Term[F]])
      extends Diff[F]
  /** This node differs, but only in its parameters, not its shape. */
  case class LocallyDifferent[F[_]](left: F[Diff[F]], right: F[Any])
      extends Diff[F]
  /** This node has some incomparable value. */
  case class Unknown[F[_]](left: F[Diff[F]], right: F[Any])
      extends Diff[F]

  implicit def ShowDiff[F[_]](implicit showF: Show[F[_]], foldF: Foldable[F]) =
    new Show[Diff[F]] {
      override def show(v: Diff[F]): Cord = {
        def toTree(term: Diff[F]): ZTree[Cord] = term match {
          case Same(_) => ZTree.node(Cord("..."), Nil.toStream)
          case Similar(x) =>
            ZTree.node(
              showF.show(x),
              foldF.foldMap(x)(_ :: Nil).toStream.map(toTree _))
          case Different(l, r) =>
            ZTree.node(
              Cord("vvvvvvvvv left  vvvvvvvvv\n") ++
                Show[Term[F]].show(Term(l)) ++
                Cord("=========================\n") ++
                Show[Term[F]].show(Term(r)) ++
                Cord("^^^^^^^^^ right ^^^^^^^^^"),
              Nil.toStream)
          case LocallyDifferent(l, r) =>
            ZTree.node(
              showF.show(l) ++ " <=/=> " ++ showF.show(r),
              foldF.foldMap(l)(_ :: Nil).toStream.map(toTree _))
          case Unknown(l, r) =>
            ZTree.node(
              showF.show(l) ++ " <???> " ++ showF.show(r),
              foldF.foldMap(l)(_ :: Nil).toStream.map(toTree _))
        }

        Cord(toTree(v).drawTree)
      }
    }
}

trait Diffable[F[+_]] {
  import Diff._

  def dift0(sameLocally: Boolean)(left: F[Term[F]], right: F[Any])(f: => F[Diff[F]]):
      Diff[F] =
    if (sameLocally) Same(left)
    else LocallyDifferent(f, right)
  def dift(sameLocally: Boolean, a: Diff[F])(left: F[Term[F]], right: F[Any])(f: Diff[F] => F[Diff[F]]):
      Diff[F] =
    if (sameLocally)
      a match {
        case Same(_) => Same(left)
        case _       => Similar(f(a))
      }
      else LocallyDifferent(f(a), right)
  def dift2(sameLocally: Boolean, a: Diff[F], b: Diff[F])(left: F[Term[F]], right: F[Any])(f: (Diff[F], Diff[F]) => F[Diff[F]]): Diff[F] =
    if (sameLocally)
      (a, b) match {
        case (Same(_), Same(_)) => Same(left)
        case _                  => Similar(f(a, b))
      }
      else LocallyDifferent(f(a, b), right)

  def dift3(sameLocally: Boolean, a: Diff[F], b: Diff[F], c: Diff[F])(left: F[Term[F]], right: F[Any])(f: (Diff[F], Diff[F], Diff[F]) => F[Diff[F]]): Diff[F] =
    if (sameLocally)
      (a, b, c) match {
        case (Same(_), Same(_), Same(_)) => Same(left)
        case _                           => Similar(f(a, b, c))
      }
      else LocallyDifferent(f(a, b, c), right)
  def dift4(sameLocally: Boolean, a: Diff[F], b: Diff[F], c: Diff[F], d: Diff[F])(left: F[Term[F]], right: F[Any])(f: (Diff[F], Diff[F], Diff[F], Diff[F]) => F[Diff[F]]): Diff[F] =
    if (sameLocally)
      (a, b, c, d) match {
        case (Same(_), Same(_), Same(_), Same(_)) => Same(left)
        case _                                    => Similar(f(a, b, c, d))
      }
      else LocallyDifferent(f(a, b, c, d), right)
  def diftl(sameLocally: Boolean, g: List[Diff[F]])(left: F[Term[F]], right: F[Any])(f: List[Diff[F]] => F[Diff[F]]):
      Diff[F] =
    if (sameLocally)
      if (Nil == g.filter(_ match {
        case Same(_) => false
        case _       => true
      }))
        Same(left)
      else Similar(f(g))
      else LocallyDifferent(f(g), right)

  def diffImpl(left: F[Term[F]], right: F[Term[F]], merged: F[Diff[F]]): Diff[F]

  def diff(left: Term[F], right: Term[F])(implicit FF: Functor[F], FM: Merge[F]): Diff[F] =
    left.merga(right)(Different(_, _), diffImpl)
}
