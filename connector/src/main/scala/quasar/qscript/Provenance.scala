/*
 * Copyright 2014–2017 SlamData Inc.
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

package quasar.qscript.provenance

import slamdata.Predef._
import quasar.contrib.matryoshka._
import quasar.ejson.EJson
import quasar.fp._
import quasar.fp.ski._
import quasar.qscript._
import quasar.qscript.MapFuncs._

import scala.Predef.$conforms

import matryoshka._
import matryoshka.data._
import monocle.macros.Lenses
import scalaz._, Scalaz._

// TODO: Convert to fixed-point
sealed abstract class Provenance[T[_[_]]]
@Lenses final case class Nada[T[_[_]]]() extends Provenance[T]
@Lenses final case class Value[T[_[_]]](expr: FreeMap[T]) extends Provenance[T]
@Lenses final case class Proj[T[_[_]]](field: T[EJson]) extends Provenance[T]
@Lenses final case class Both[T[_[_]]](l: Provenance[T], r: Provenance[T])
    extends Provenance[T]
@Lenses final case class OneOf[T[_[_]]](l: Provenance[T], r: Provenance[T])
    extends Provenance[T]
@Lenses final case class Then[T[_[_]]](l: Provenance[T], r: Provenance[T])
    extends Provenance[T]

object Provenance {
  // TODO: This might not be the proper notion of equality – this just tells us
  //       which things align properly for autojoins.
  implicit def order[T[_[_]]: CorecursiveT: OrderT: EqualT]: Order[Provenance[T]] = {
    val t = new ProvenanceT[T]
    import t._

    def thenEq(l: t.Provenance, r: t.Provenance) =
      flattenThen(l).map(_.map(_._2)).toSet[List[t.Provenance]].cmp(flattenThen(r).map(_.map(_._2)).toSet[List[t.Provenance]])

    def bothEq(l: t.Provenance, r: t.Provenance) =
      flattenBoth(l).map(l => nubNadas(l.map(_._2)).toSet).toSet[Set[t.Provenance]].cmp(flattenBoth(r).map(l => nubNadas(l.map(_._2)).toSet).toSet[Set[t.Provenance]])

    def oneOfEq(l: t.Provenance, r: t.Provenance) =
      nubNadas(flattenOneOf(l).map(_._2)).toSet[t.Provenance].cmp(nubNadas(flattenOneOf(r).map(_._2)).toSet[t.Provenance])

    def nubNadas(provs: List[t.Provenance]): List[t.Provenance] =
      provs.filter(_ =/= Nada())

    Order.order {
      case (Nada(),          Nada())          => Ordering.EQ
      case (Value(_),        Value(_))        => Ordering.EQ
      case (Value(_),        Proj(_))         => Ordering.EQ
      case (Proj(_),         Value(_))        => Ordering.EQ
      case (Proj(d1),        Proj(d2))        => d1.cmp(d2)
      case (l @ Both(_, _),  r)               => bothEq(l, r)
      case (l,               r @ Both(_, _))  => bothEq(l, r)
      case (l @ OneOf(_, _), r)               => oneOfEq(l, r)
      case (l,               r @ OneOf(_, _)) => oneOfEq(l, r)
      case (l @ Then(_, _),  r)               => thenEq(l, r)
      case (l,               r @ Then(_, _))  => thenEq(l, r)
      case (Nada(),          _)               => Ordering.LT
      case (_,               Nada())          => Ordering.GT
      case (Value(_),        _)               => Ordering.LT
      case (_,               Value(_))        => Ordering.GT
      case (Proj(_),         _)               => Ordering.LT
      case (_,               Proj(_))         => Ordering.GT
    }
  }

  implicit def show[T[_[_]]: ShowT]: Show[Provenance[T]] = Show.show {
    case Nada()      => Cord("Nada")
    case Value(expr) => Cord("Value(") ++ expr.show ++ Cord(")")
    case Proj(field) => Cord("Proj(") ++ field.show ++ Cord(")")
    case Both(l, r)  => Cord("Both(") ++ l.show ++ Cord(", ") ++ r.show ++ Cord(")")
    case OneOf(l, r) => Cord("OneOf(") ++ l.show ++ Cord(", ") ++ r.show ++ Cord(")")
    case Then(l, r)  => Cord("Then(") ++ l.show ++ Cord(", ") ++ r.show ++ Cord(")")
  }
}

final case class JoinKeys[T[_[_]]](unJoinKeys: List[(FreeMap[T], FreeMap[T])])

object JoinKeys {
  implicit def monoid[T[_[_]]]: Monoid[JoinKeys[T]] = new Monoid[JoinKeys[T]] {
    def zero = JoinKeys(Nil)

    def append(l: JoinKeys[T], r: => JoinKeys[T]) =
      JoinKeys(l.unJoinKeys ++ r.unJoinKeys)
  }
}

class ProvenanceT[T[_[_]]: CorecursiveT: OrderT: EqualT] extends TTypes[T] {
  type Provenance = quasar.qscript.provenance.Provenance[T]

  val valueJoin: JoinKeys[T] = JoinKeys(List((HoleF, HoleF)))

  val joinKeys: (Provenance, Provenance) => JoinKeys[T] = {
    case (Nada(),          r)               => Monoid[JoinKeys[T]].zero
    case (l,               Nada())          => Monoid[JoinKeys[T]].zero
    case (Value(_),        Value(_))        => valueJoin
    case (Proj(d1),        Proj(d2))        => if (d1 ≟ d2) valueJoin else Monoid[JoinKeys[T]].zero
    case (Value(_),        Proj(d2))        => JoinKeys(List((HoleF, Free.roll(Constant(d2)))))
    case (Proj(d1),        Value(_))        => JoinKeys(List((Free.roll(Constant(d1)), HoleF)))
    case (l @ Both(_, _),  r)               => joinBoths(l, r)
    case (l,               r @ Both(_, _))  => joinBoths(l, r)
    case (l @ OneOf(_, _), r)               => joinOneOfs(l, r)
    case (l,               r @ OneOf(_, _)) => joinOneOfs(l, r)
    case (l @ Then(_, _),  r)               => joinThens(l, r)
    case (l,               r @ Then(_, _))  => joinThens(l, r)
  }

  def joinBoths(l: Provenance, r: Provenance): JoinKeys[T] =
    JoinKeys(for {
      lefts  <- flattenBoth(l)
      rights <- flattenBoth(r)
      left   <- lefts
      right  <- rights
      if (left._2 ≟ right._2)
      key    <- joinKeys(left._2, right._2).unJoinKeys
    } yield (left._1 >> key._1, right._1 >> key._2))

  def joinOneOfs(l: Provenance, r: Provenance): JoinKeys[T] =
    JoinKeys(for {
      left  <- flattenOneOf(l)
      right <- flattenOneOf(r)
      if (left._2 ≟ right._2)
      key   <- joinKeys(left._2, right._2).unJoinKeys
    } yield (left._1 >> key._1, right._1 >> key._2))

  def joinThens(l: Provenance, r: Provenance): JoinKeys[T] = {
    def longestPrefix[A: Equal](l: List[A], r: List[A]): Int =
      Zip[List].zipWith(l, r)(_ ≟ _).takeWhile(ι).length

    JoinKeys(for {
      lefts  <- flattenThen(l)
      rights <- flattenThen(r)
      n = longestPrefix(lefts.map(_._2), rights.map(_._2))
      if (n > 0)
      boths = lefts.take(n).zip(rights.take(n))
      (left, right) <- boths
      key  <- joinKeys(left._2, right._2).unJoinKeys
    } yield (left._1 >> key._1, right._1 >> key._2))
  }

  type Alternatives[A] = List[A]

  type Flattening = Alternatives[List[(FreeMap, Provenance)]]

  def nest0(root: FreeMap, v: List[(FreeMap, Provenance)])
      : List[(FreeMap, Provenance)] =
    v.map(_.leftMap(root >> _))

  def nest(root: FreeMap, alts: Flattening): Flattening =
    alts.map(nest0(root, _))

  def get(field: String): FreeMap =
    Free.roll(ProjectField(HoleF, StrLit(field)))

  val _Both = "both"
  val _Left = "left"
  val _Right = "right"
  val _Value = "value"
  val _OneOf = "one of"
  val _Then = "then"

  /** Flattens products, correctly handling the distributivity of sums.
    * The result is a sum (Alternatives) of the flattened terms in the product.
    */
  val flattenBoth: Provenance => Flattening = {
    case Both(l, r)  => (flattenBoth(l) ⊛ flattenBoth(r))(nest0(get(_Both) >> get(_Left), _) |+| nest0(get(_Both) >> get(_Right), _))
    case OneOf(l, r) => nest(get(_OneOf) >> get(_Left), flattenBoth(l)) |+| nest(get(_OneOf) >> get(_Right), flattenBoth(r))
    case v           => List(List((HoleF[T], v)))
  }
      
  /** Flattens sequences, correctly handling the distributivity of sums.
    * The result is a sum (Alternatives) of the flattened terms in the sequence.
    */
  val flattenThen: Provenance => Flattening = {
    case Then(l, r)  => (flattenThen(l) ⊛ flattenThen(r))(nest0(get(_Then) >> get(_Left), _) |+| nest0(get(_Then) >> get(_Right), _))
    case OneOf(l, r) => nest(get(_OneOf) >> get(_Left), flattenThen(l)) |+| nest(get(_OneOf) >> get(_Right), flattenThen(r))
    case v           => List(List((HoleF[T], v)))
  }

  /** Flattens sums, correctly handling the distributivity of sums.
    * The result is a sum (Alternatives) of the flattened terms.
    */
  val flattenOneOf: Provenance => Alternatives[(FreeMap, Provenance)] = {
    case Both(l, r)  => nest0(get(_Both)  >> get(_Left), flattenOneOf(l)) |+| nest0(get(_Both)  >> get(_Right), flattenOneOf(r))
    case Then(l, r)  => nest0(get(_Then)  >> get(_Left), flattenOneOf(l)) |+| nest0(get(_Then)  >> get(_Right), flattenOneOf(r))
    case OneOf(l, r) => nest0(get(_OneOf) >> get(_Left), flattenOneOf(l)) |+| nest0(get(_OneOf) >> get(_Right), flattenOneOf(r))
    case v           => List((HoleF[T], v))
  }

  def genComparisons(lps: List[Provenance], rps: List[Provenance]): JoinFunc =
    lps.reverse.zip(rps.reverse).takeWhile { case (l, r) => l ≟ r }.reverse.map((genComparison(_, _)).tupled(_).toList).join match {
      case Nil    => BoolLit(true)
      case h :: t => t.foldLeft(h)((a, e) => Free.roll(And(a, e)))
    }

  def genComparison(lp: Provenance, rp: Provenance): Option[JoinFunc] =
    (lp, rp) match {
      case (Value(v1), Value(v2)) => Free.roll(MapFuncs.Eq[T, JoinFunc](v1.as(LeftSide), v2.as(RightSide))).some
      case (Value(v1), Proj(d2)) => Free.roll(MapFuncs.Eq[T, JoinFunc](v1.as(LeftSide), Free.roll(Constant(d2)))).some
      case (Proj(d1), Value(v2)) => Free.roll(MapFuncs.Eq[T, JoinFunc](Free.roll(Constant(d1)), v2.as(RightSide))).some
      case (Both(l1, r1),  Both(l2, r2)) =>
        genComparison(l1, l2).fold(
          genComparison(r1, r2))(
          lc => genComparison(r1, r2).fold(lc)(rc => Free.roll(And[T, JoinFunc](lc, rc))).some)
      case (OneOf(l1, r1),  OneOf(l2, r2)) =>
        genComparison(l1, l2).fold(
          genComparison(r1, r2))(
          lc => genComparison(r1, r2).fold(lc)(rc => Free.roll(And[T, JoinFunc](lc, rc))).some)
      case (Then(l1, r1),  Then(l2, r2)) =>
        genComparison(l1, l2).fold(
          genComparison(r1, r2))(
          lc => genComparison(r1, r2).fold(lc)(rc => Free.roll(And[T, JoinFunc](lc, rc))).some)
      case (_, _) => None
    }

  def rebase0(newBase: FreeMap): Provenance => Option[Provenance] = {
    case Value(expr) => Value(expr >> newBase).some
    case Both(l, r)  => (rebase0(newBase)(l), rebase0(newBase)(r)) match {
      case (None,     None)     => None
      case (None,     Some(r0)) => Both(l, r0).some
      case (Some(l0), None)     => Both(l0, r).some
      case (Some(l0), Some(r0)) => Both(l0, r0).some
    }
    case OneOf(l, r) => (rebase0(newBase)(l), rebase0(newBase)(r)) match {
      case (None,     None)     => None
      case (None,     Some(r0)) => OneOf(l, r0).some
      case (Some(l0), None)     => OneOf(l0, r).some
      case (Some(l0), Some(r0)) => OneOf(l0, r0).some
    }
    case Then(l, r)  => (rebase0(newBase)(l), rebase0(newBase)(r)) match {
      case (None,     None)     => None
      case (None,     Some(r0)) => Then(l, r0).some
      case (Some(l0), None)     => Then(l0, r).some
      case (Some(l0), Some(r0)) => Then(l0, r0).some
    }
    case _           => None
  }

  def rebase(newBase: FreeMap, ps: List[Provenance]): List[Provenance] =
    ps.map(orOriginal(rebase0(newBase)))

  def concatFreeMaps(ps: List[FreeMap]): Option[FreeMap] = ps match {
    case Nil      => None
    case h :: t   =>
      t.foldLeft(
        Free.roll(MakeArray[T, FreeMap](h)))(
        (a, e) => Free.roll(ConcatArrays(a, Free.roll(MakeArray(e))))).some
  }

  /** Reifies the part of the provenance that must exist in the plan.
    */
  def genBuckets(ps: List[Provenance]): Option[(List[Provenance], FreeMap)] =
    ps.traverse(genBucket).eval(0).unzip.traverse(_.join match {
      case Nil      => None
      case h :: t   =>
        t.foldLeft(
          Free.roll(MakeArray[T, FreeMap](h)))(
          (a, e) => Free.roll(ConcatArrays(a, Free.roll(MakeArray(e))))).some
    })

  val genBucket: Provenance => State[Int, (Provenance, List[FreeMap])] = {
    case Nada()      => (Nada[T](): Provenance, Nil: List[FreeMap]).point[State[Int, ?]]
    case Value(expr) =>
      State(i => (i + 1, (Value(Free.roll(ProjectIndex(HoleF, IntLit(i)))), List(expr))))
    case Proj(d)     => (Proj(d): Provenance, Nil: List[FreeMap]).point[State[Int, ?]]
    case Both(l, r)  => (genBucket(l) ⊛ genBucket(r)) {
      case ((lp, lf), (rp, rf)) => (Both(lp, rp), lf ++ rf)
    }
    case OneOf(l, r)  => (genBucket(l) ⊛ genBucket(r)) {
      case ((lp, lf), (rp, rf)) => (OneOf(lp, rp), lf ++ rf)
    }
    case Then(l, r)  => (genBucket(l) ⊛ genBucket(r)) {
      case ((lp, lf), (rp, rf)) => (Then(lp, rp), lf ++ rf)
    }
  }

  def joinProvenances(leftBuckets: List[Provenance], rightBuckets: List[Provenance]):
      List[Provenance] =
    leftBuckets.reverse.alignWith(rightBuckets.reverse) {
      case \&/.Both(l, r) => if (l ≟ r) l else Both(l, r)
      case \&/.This(l)    => Both(l, Nada())
      case \&/.That(r)    => Both(Nada(), r)
    }.reverse

  def unionProvenances(leftBuckets: List[Provenance], rightBuckets: List[Provenance]):
      List[Provenance] =
    leftBuckets.reverse.alignWith(rightBuckets.reverse) {
      case \&/.Both(l, r) => OneOf(l, r)
      case \&/.This(l)    => OneOf(l, Nada())
      case \&/.That(r)    => OneOf(Nada(), r)
    }.reverse

  def nestProvenances(buckets: List[Provenance]): List[Provenance] =
    buckets match {
      case a :: b :: tail => Then(a, b) :: tail
      case _              => buckets
    }

  def squashProvenances(buckets: List[Provenance]): List[Provenance] =
    buckets match {
      case a :: b :: tail => squashProvenances(Then(a, b) :: tail)
      case _              => buckets
    }

  def swapProvenances(buckets: List[Provenance]): List[Provenance] =
    buckets match {
      case a :: b :: tail => b :: a :: tail
      case _              => buckets
    }
}
