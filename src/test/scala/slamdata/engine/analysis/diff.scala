package slamdata.engine.analysis

import fixplate._

import scalaz._
import scalaz.std.list._
import scalaz.std.set._

import org.specs2.mutable._
import org.specs2.matcher.{Matcher, Expectable}

class DiffSpec extends Specification {
  sealed trait Example[+A]
  case object Empty extends Example[Nothing]
  case class NonRecursive(a: String, b: Int) extends Example[Nothing]
  case class MultiRecursion[A](a: A, b: A) extends Example[A]
  case class OneList[A](l: List[A]) extends Example[A]
  case class TwoLists[A](first: List[A], second: List[A]) extends Example[A]

  implicit val ExampleTraverse = new Traverse[Example] {
    def traverseImpl[G[_], A, B](fa: Example[A])(f: A => G[B])(
      implicit G: Applicative[G]):
        G[Example[B]] = fa match {
      case Empty => G.point(Empty)
      case x @ NonRecursive(_, _) => G.point(x)
      case MultiRecursion(a, b) => G.apply2(f(a), f(b))(MultiRecursion(_, _))
      case OneList(a) =>
        G.apply(Traverse[List].sequence(a.map(f)))(OneList(_))
      case TwoLists(a, b) =>
        G.apply2(
          Traverse[List].sequence(a.map(f)),
          Traverse[List].sequence(b.map(f)))(
          TwoLists(_, _))
    }
  }

  implicit val ExampleDiff = new Diffable[Example] {
    val diffImpl: DiffImpl[Example] = {
      case (l @ Empty,                r @ Empty)              => localDiff(l, r)
      case (l @ NonRecursive(_, _),   r @ NonRecursive(_, _)) => localDiff(l, r)
      case (l @ MultiRecursion(_, _), r @ MultiRecursion(_, _)) =>
        localDiff(l, r)
      case (OneList(l),               OneList(r))             =>
        Diff.Similar(OneList(diffLists(l, r)))
      case (TwoLists(l1, l2),         TwoLists(r1, r2))       =>
        Diff.Similar(TwoLists(diffLists(l1, r1), diffLists(l2, r2)))
    }
  }

  "diff" should {
    import Diff._
    val diff = Diffable[Example].diff _

    "create `Removed` for shorter list" in {
      diff(
        Term(OneList(List(Term[Example](Empty), Term[Example](Empty)))),
        Term(OneList(List(Term[Example](NonRecursive("x", 3)))))) must_==
      Similar[Example](OneList(List(
        Different[Example](Empty, NonRecursive("x", 3)),
        Removed[Example](Empty))))
    }

    "create `Added` for longer list" in {
      diff(
        Term(OneList(List(Term[Example](NonRecursive("x", 3))))),
        Term(OneList(List(Term[Example](Empty), Term[Example](Empty))))) must_==
      Similar[Example](OneList(List(
        Different[Example](NonRecursive("x", 3), Empty),
        Added[Example](Empty))))
    }

    "choose “simplest” diff" in {
      diff(
        Term(OneList(List(Term[Example](Empty)))),
        Term(OneList(List(Term[Example](NonRecursive("x", 3)), Term[Example](Empty))))) must_==
      Similar[Example](OneList(List(
        Added[Example](NonRecursive("x", 3)),
        Same[Example](Empty))))
    }.pendingUntilFixed("can’t just walk lists from start to finish")

    "create `Removed` and `Added` for mixed lists" in {
      diff(
        Term(TwoLists(
          List(Term[Example](Empty), Term[Example](Empty)),
          List(Term[Example](Empty)))),
        Term(TwoLists(
          List(Term[Example](NonRecursive("x", 3))),
          List(Term[Example](Empty), Term[Example](Empty), Term[Example](Empty))))) must_==
      Similar[Example](TwoLists(
        List(
          Different[Example](Empty, NonRecursive("x", 3)),
          Removed[Example](Empty)),
        List(Same[Example](Empty), Added[Example](Empty), Added[Example](Empty))))
    }
  }
}
