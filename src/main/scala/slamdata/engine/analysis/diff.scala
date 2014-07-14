package slamdata.engine.analysis

import scalaz.{Tree => ZTree, _}
import scalaz.std.list._

import fixplate._

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
  import Diffable._
  def diff(left: Term[F], right: Term[F]): Diff[F]
  // = {
  //   val (l, r) = (left.unFix, right.unFix) 
  //   diffImpl[F](l, r) match {
  //     case Same => {
  //       val children = (left.children, right.children).zipped map diff
  //       if (Nil == children.filter(_ match {
  //         case Diff.Same(_) => false
  //         case _       => true
  //       }))
  //         Diff.Same(l)
  //       else
  //         Diff.Similar(l.apply(children))
  //     }
  //     case Different => {
  //       val children = (left.children, right.children).zipped map diff
  //       Diff.LocallyDifferent(l.apply(children), r)
  //     }
  //     case DifferentShape => Diff.Different(l, r)
  //     case Unknown => {
  //       val children = (left.children, right.children).zipped map diff
  //       Diff.Unknown(l.apply(children), r)
  //     }
  //   }
  // }
  // def diffImpl[F[+_]](left: F[Any], right: F[Any]): DiffType
}
object Diffable {
  sealed trait DiffType
  case object Same           extends DiffType
  case object Different      extends DiffType
  case object DifferentShape extends DiffType
  case object Unknown        extends DiffType
}

