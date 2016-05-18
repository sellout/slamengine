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

package quasar.ejson

import quasar.Predef._
import quasar.fp._

import org.threeten.bp.{Instant, LocalDate, LocalTime, Duration}
import scalaz._, Scalaz._

/** This is an extended variant of JSON that, in addition to the usual stuff
  * allows arbitrary expressions as object keys and adds additional primitive
  * types, including distinguishing between integers and floating point.
  */
sealed trait EJson[A]
final case class Arr[A](value: List[A])                 extends EJson[A]
final case class Obj[A](value: List[(A, A)])            extends EJson[A]
final case class Null[A]()                              extends EJson[A]
final case class Bool[A](value: Boolean)                extends EJson[A]
final case class Char[A](value: scala.Char)             extends EJson[A]
final case class Str[A](value: String)                  extends EJson[A]
final case class Dec[A](value: BigDecimal)              extends EJson[A]
final case class Int[A](value: BigInt)                  extends EJson[A]
final case class Timestamp[A](value: Instant)           extends EJson[A]
final case class Date[A](value: LocalDate)              extends EJson[A]
final case class Time[A](value: LocalTime)              extends EJson[A]
final case class Interval[A](value: Duration)           extends EJson[A]
final case class Binary[A](value: ImmutableArray[Byte]) extends EJson[A]

object EJson {
  implicit val traverse: Traverse[EJson] = new Traverse[EJson] {
    def traverseImpl[G[_], A, B](
      fa: EJson[A])(
      f: A => G[B])(
      implicit G: Applicative[G]):
        G[EJson[B]] =
      fa match {
        case Arr(value)       => value.traverse(f).map(Arr(_))
        case Obj(value)       => value.traverse(_.bitraverse(f, f)).map(Obj(_))
        case Null()           => G.point(Null())
        case Bool(value)      => G.point(Bool(value))
        case Char(value)      => G.point(Char(value))
        case Str(value)       => G.point(Str(value))
        case Dec(value)       => G.point(Dec(value))
        case Int(value)       => G.point(Int(value))
        case Timestamp(value) => G.point(Timestamp(value))
        case Date(value)      => G.point(Date(value))
        case Time(value)      => G.point(Time(value))
        case Interval(value)  => G.point(Interval(value))
        case Binary(value)    => G.point(Binary(value))
      }
  }

  // TODO: This misbehaves on Int/Dec
  implicit val equal: Equal ~> (Equal ∘ EJson)#λ =
    new (Equal ~> (Equal ∘ EJson)#λ) {
      def apply[α](eq: Equal[α]) = Equal.equal((a, b) => (a, b) match {
        case (Arr(l),       Arr(r))       => listEqual(eq).equal(l, r)
        case (Obj(l),       Obj(r))       =>
          listEqual(tuple2Equal(eq, eq)).equal(l, r)
        case (Null(),       Null())       => true
        case (Bool(l),      Bool(r))      => l ≟ r
        case (Char(l),      Char(r))      => l ≟ r
        case (Str(l),       Str(r))       => l ≟ r
        case (Dec(l),       Dec(r))       => l ≟ r
        case (Int(l),       Int(r))       => l ≟ r
        case (Timestamp(l), Timestamp(r)) => l == r
        case (Date(l),      Date(r))      => l == r
        case (Time(l),      Time(r))      => l == r
        case (Interval(l),  Interval(r))  => l == r
        case (Binary(l),    Binary(r))    => l ≟ r
        case (_,            _)            => false
      })
    }

  // implicit def syntax[S[_]: Syntax]: S ~> (S ∘ EJson)#λ =
  //   new(S ~> (S ∘ EJson)#λ) {
  //     def apply[A](aSyntax: S[A]) =
  //       (null <> nullLit) <|>
  //         (bool <> boolLit) <|>
  //         (char <> charLit) <|>
  //         (str <> string) <|>
  //         (dec <> decimal) <|>
  //         (int <> integer) <|>
  //         (map <> mapLit(aSyntax)) <|>
  //         (arr <> array(aSyntax)) <|>
  //         (timestamp <> timestampLit) <|>
  //         (date <> dateLit) <|>
  //         (time <> timeLit) <|>
  //         (interval <> intervalLit) <|>
  //         (binary <> binaryLit)

  //     val nullLit = text("null")

  //     val integer =
  //       (chars >>> total[String, Int](_.toInt, _.toString)) <> many1(digit)

  //     val string = between(text("\""), text("\"")) >>> str

  //     val ops = (mulOp <> text("*")) <|> (addOp <> text("+"))

  //     def seq[A]: S[A] => S[List[A]] =
  //       fb => fb <*> opt(text(",") *> seq(fb)) >>> (_ :: _.getOrElse(Nil))

  //     def array[A]: S[A] => S[EJson[A]] =
  //       between(text("["), text("]"))(seq(fa))

  //     def pair[A]: S[A] => S[(A, A)] =
  //       fa => fa <*> text(":") <*> fa

  //     def mapLit[A]: S[A] => S[EJson[A]] =
  //       fa => between(text("["), text("]"))(seq(pair(fa)))
  //   }
}
