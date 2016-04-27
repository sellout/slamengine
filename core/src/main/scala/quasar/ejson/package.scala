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

package quasar

import quasar.Predef._

import matryoshka._
import scalaz._, Scalaz._

// From Matryoshka, until we upgrade
final case class CoEnv[E, F[_], A](run: E \/ F[A])
object CoEnv {
  // TODO: Need to have lower-prio instances of Functor and Foldable, with
  //       corresponding constraints on F.
  implicit def traverse[F[_]: Traverse, A]: Traverse[CoEnv[A, F, ?]] =
    new Traverse[CoEnv[A, F, ?]] {
      def traverseImpl[G[_], R, B](
        fa: CoEnv[A, F, R])(
        f: R => G[B])(
        implicit G: Applicative[G]):
          G[CoEnv[A, F, B]] =
        fa.run.traverse(_.traverse(f)).map(CoEnv(_))
    }

  implicit def monad[F[_]: Monad: Traverse, A]: Monad[CoEnv[A, F, ?]] =
    new Monad[CoEnv[A, F, ?]] {
      def bind[B, C](fa: CoEnv[A, F, B])(f: (B) ⇒ CoEnv[A, F, C]) =
        CoEnv(fa.run.fold(_.left, _.traverse[CoEnv[A, F, ?], C](f).run.map(_.join)))
      def point[B](x: => B) = CoEnv(x.point[F].right)
    }

  implicit def monadCo[F[_]: Applicative: Comonad, A]: Monad[CoEnv[A, F, ?]] =
    new Monad[CoEnv[A, F, ?]] {
      def bind[B, C](fa: CoEnv[A, F, B])(f: (B) ⇒ CoEnv[A, F, C]) =
        fa.run.fold(a => CoEnv(a.left), fb => f(fb.copoint))
      def point[B](x: => B) = CoEnv(x.point[F].right)
    }
}

// Something like this should turn a Syntax for any F into a fixed-point one
// implicit def syntax[T[_[_]]: Recursive, S[_]: Syntax, F[_]](
//   implicit  F: S ~> (S ∘ F)#λ):
//     S[T[F]] =
//   recCorec <> F(syntax)
// def recCorec[T[_[_]]: Recursive: Corecursive, F[_]: Functor] =
//   Iso[F[T[F]], T[F]](_.embed.some, _.project.some)

// And then we need something to handle Syntax for `:+:`. Then we can compose
// our syntaxes and get a Syntax[Mu(EJson :+: Sql)#λ]]
// implicit def syntax[S[_]: Syntax, F[_], G[_], A](
//   implicit F: S[F[A]], G: S[G[A]]):
//     S[Coproduct[F, G, A]] =
//   ???

package object ejson {
  // TODO: Data should be replaced with EJson. These just exist to bridge the
  //       gap in the meantime.
  val toData: Algebra[EJson, Data] = {
    case Arr(value)       => Data.Arr(value)
    case Obj(value)       => Data.Obj(ListMap(value ∘ (_.leftMap {
      case Data.Str(key) => key
      case _             => scala.Predef.??? // FIXME: fail on non-string keys
    }): _*))
    case Null()           => Data.Null
    case Bool(value)      => Data.Bool(value)
    // FIXME: cheating, but it’s what we’re already doing in the SQL parser
    case Char(value)      => Data.Str(value.toString)
    case Str(value)       => Data.Str(value)
    case Dec(value)       => Data.Dec(value)
    case Int(value)       => Data.Int(value)
    case Timestamp(value) => Data.Timestamp(value)
    case Date(value)      => Data.Date(value)
    case Time(value)      => Data.Time(value)
    case Interval(value)  => Data.Interval(value)
    case Binary(value)    => Data.Binary(value)
  }

  /** Converts the parts of `Data` that it can, then stores the rest in,
    * effectively, `Free.Pure`.
    */
  val fromData: Coalgebra[CoEnv[Data, EJson, ?], Data] = {
    case Data.Arr(value)       => CoEnv(Arr(value).right)
    case Data.Obj(value)       =>
      CoEnv(Obj(value.toList.map(_.leftMap(Data.Str(_)))).right)
    case Data.Null             => CoEnv(Null().right)
    case Data.Bool(value)      => CoEnv(Bool(value).right)
    case Data.Str(value)       => CoEnv(Str(value).right)
    case Data.Dec(value)       => CoEnv(Dec(value).right)
    case Data.Int(value)       => CoEnv(Int(value).right)
    case Data.Timestamp(value) => CoEnv(Timestamp(value).right)
    case Data.Date(value)      => CoEnv(Date(value).right)
    case Data.Time(value)      => CoEnv(Time(value).right)
    case Data.Interval(value)  => CoEnv(Interval(value).right)
    case Data.Binary(value)    => CoEnv(Binary(value).right)
    case data                  => CoEnv(data.left)
  }

  val recoverData: Algebra[CoEnv[Data, EJson, ?], Data] =
    _.run.fold(x => x, toData)
}
