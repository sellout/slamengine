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
  /** This node differs, but only in its parameters, not its shape. */
  case class LocallyDifferent[F[_]](left: F[Diff[F]], right: F[Any])
      extends Diff[F]
  /** This node exists only in the right tree, but some descendent is similar */
  case class Inserted[F[_]](right: F[Diff[F]]) extends Diff[F]
  /** This node exists only in the left tree, but some descendent is similar. */
  case class Deleted[F[_]](left: F[Diff[F]]) extends Diff[F]
  /** This node differs between the two trees */
  case class Different[F[_]](left: F[Term[F]], right: F[Term[F]])
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
          case Inserted(x) =>
            ZTree.node(
              Cord("+++> ") ++ showF.show(x),
              foldF.foldMap(x)(_ :: Nil).toStream.map(toTree _))
          case Deleted(x) =>
            ZTree.node(
              Cord("<--- ") ++ showF.show(x),
              foldF.foldMap(x)(_ :: Nil).toStream.map(toTree _))
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

trait Diffable[F[_]] {
  import Diff._

  def diffImpl(left: F[Term[F]], right: F[Term[F]]): Diff[F]

  def diff(left: Term[F], right: Term[F])(
    implicit FF: Functor[F], FoldF: Foldable[F], FM: Merge[F]):
      Diff[F] =
    left.paramerga(right)((l, r, merged: Option[F[Diff[F]]]) =>
      merged match {
        case None         => diffImpl(l, r)
        case Some(merged) =>
          val children = FoldF.foldMap(merged)(_ :: Nil)
          if (children.length == children.collect { case Same(_) => () }.length)
            Same(l)
          else Similar(merged)
      })
}
object Diffable {
  @inline def apply[F[_]](implicit F: Diffable[F]): Diffable[F] = F
}
