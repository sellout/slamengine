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

import matryoshka._

object MapFuncs {
  // array
  final case class Length[T[_[_]], A](a1: A) extends Unary[T, A]

  // date
  final case class Date[T[_[_]], A](a1: A) extends Unary[T, A]
  final case class Time[T[_[_]], A](a1: A) extends Unary[T, A]
  final case class Timestamp[T[_[_]], A](a1: A) extends Unary[T, A]
  final case class Interval[T[_[_]], A](a1: A) extends Unary[T, A]
  final case class TimeOfDay[T[_[_]], A](a1: A) extends Unary[T, A]
  final case class ToTimestamp[T[_[_]], A](a1: A) extends Unary[T, A]
  final case class Extract[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]

  // math
  final case class Negate[T[_[_]], A](a1: A) extends Unary[T, A]
  final case class Add[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class Multiply[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class Subtract[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class Divide[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class Modulo[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class Power[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]

  // relations
  final case class Not[T[_[_]], A](a1: A) extends Unary[T, A]
  final case class Eq[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class Neq[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class Lt[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class Lte[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class Gt[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class Gte[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class IfUndefined[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class And[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class Or[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class Coalesce[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class Between[T[_[_]], A](a1: A, a2: A, a3: A) extends Ternary[T, A]
  final case class Cond[T[_[_]], A](a1: A, a2: A, a3: A) extends Ternary[T, A]

  // set
  final case class In[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class Within[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class Constantly[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]

  // string
  final case class Lower[T[_[_]], A](a1: A) extends Unary[T, A]
  final case class Upper[T[_[_]], A](a1: A) extends Unary[T, A]
  final case class Bool[T[_[_]], A](a1: A) extends Unary[T, A]
  final case class Integer[T[_[_]], A](a1: A) extends Unary[T, A]
  final case class Decimal[T[_[_]], A](a1: A) extends Unary[T, A]
  final case class Null[T[_[_]], A](a1: A) extends Unary[T, A]
  final case class ToString[T[_[_]], A](a1: A) extends Unary[T, A]
  final case class Like[T[_[_]], A](a1: A, a2: A, a3: A) extends Ternary[T, A]
  final case class Search[T[_[_]], A](a1: A, a2: A, a3: A) extends Ternary[T, A]
  final case class Substring[T[_[_]], A](a1: A, a2: A, a3: A) extends Ternary[T, A]

  // structural
  final case class MakeArray[T[_[_]], A](a1: A) extends Unary[T, A]
  final case class MakeObject[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class ConcatArrays[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class ConcatObjects[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class ProjectIndex[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class ProjectField[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]
  final case class DeleteField[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]

  // helpers & QScript-specific
  final case class DupMapKeys[T[_[_]], A](a1: A) extends Unary[T, A]
  final case class DupArrayIndices[T[_[_]], A](a1: A) extends Unary[T, A]
  final case class Range[T[_[_]], A](a1: A, a2: A) extends Binary[T, A]

  def StrLit[T[_[_]], A](str: String)(implicit T: Corecursive[T]) =
    Nullary[T, A](EJson.Str[T[EJson]](str).embed)
}
