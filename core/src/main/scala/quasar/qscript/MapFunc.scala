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
import quasar.fp._

import scalaz._

sealed trait MapFunc[T[_[_]], A]

final case class Nullary[T[_[_]], A](ejson: T[EJson]) extends MapFunc[T, A]

trait Unary[T[_[_]], A] extends MapFunc[T, A] {
  def a1: A
}
trait Binary[T[_[_]], A] extends MapFunc[T, A] {
  def a1: A
  def a2: A
}
trait Ternary[T[_[_]], A] extends MapFunc[T, A] {
  def a1: A
  def a2: A
  def a3: A
}

object MapFunc {
  // TODO: The `T` passed to MapFunc and the `T` wrapping MapFunc should be distinct
  // def normalize[T[_[_]]: Recursive](implicit EJ: Equal[T[EJson]]):
  //     MapFunc[T, T[MapFunc[T, ?]]] => Option[MapFunc[T, T[MapFunc[T, ?]]]] = {
  //   val mf = new MapFuncs[T, T[MapFunc[T, ?]]]
  //   import mf._
  //   {
  //     case ConcatArrays(as) =>
  //       as.find {
  //         case Embed(ConcatArrays(_)) => true
  //         case _                      => false
  //       }.map(_ => ConcatArrays(as >>= {
  //         case Embed(ConcatArrays(moreAs)) => moreAs
  //         case a                           => List(a)
  //       }))
  //     case ConcatObjects(as) =>
  //       as.find {
  //         case Embed(ConcatObjects(_)) => true
  //         case _                       => false
  //       }.map(_ => ConcatObjects(as >>= {
  //         case Embed(ConcatObjects(moreAs)) => moreAs
  //         case a                            => List(a)
  //       }))
  //     case ProjectField(Embed(ConcatObjects(objs)), Embed(Nullary(field))) =>
  //       objs >>= {
  //         case Embed(MakeObject(Embed(Nullary(src)), value)) =>
  //           if (field ≟ src) value else Nil
  //         case x => List(x)
  //       }
  //   }
  // }
  import MapFuncs._

  implicit def functor[T[_[_]]]: Functor[MapFunc[T, ?]] = new Functor[MapFunc[T, ?]] {
    def map[A, B](fa: MapFunc[T, A])(f: A => B): MapFunc[T, B] =
      fa match {
        case Nullary(v) => Nullary[T, B](v)
        case Negate(a1) => Negate(f(a1))
        case _ => ???
      }
  }

  implicit def equal[T[_[_]], A](implicit eqTEj: Equal[T[EJson]]):
      Delay[Equal, MapFunc[T, ?]] =
    new Delay[Equal, MapFunc[T, ?]] {
      // TODO this is wrong - we need to define equality on a function by function basis
      def apply[A](in: Equal[A]): Equal[MapFunc[T, A]] = Equal.equal {
        case (Nullary(v1), Nullary(v2)) => v1.equals(v2)
        case (Negate(a1), Negate(a2)) => in.equal(a1, a1)
        case (_, _) => false
      }
    }

  implicit def show[T[_[_]]](implicit shEj: Show[T[EJson]]): Delay[Show, MapFunc[T, ?]] =
    new Delay[Show, MapFunc[T, ?]] {
      def apply[A](sh: Show[A]): Show[MapFunc[T, A]] = Show.show {
        case Nullary(v) => Cord("Nullary(") ++ shEj.show(v) ++ Cord(")")
        case Negate(a1) => Cord("Negate(") ++ sh.show(a1) ++ Cord(")")
        case _ => ???
      }
    }
}
