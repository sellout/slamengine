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
  def ArrayLength[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)

  // date
  def Date[T[_[_]], A](a1: A) = Unary[T, A](a1)
  def Time[T[_[_]], A](a1: A) = Unary[T, A](a1)
  def Timestamp[T[_[_]], A](a1: A) = Unary[T, A](a1)
  def Interval[T[_[_]], A](a1: A) = Unary[T, A](a1)
  def TimeOfDay[T[_[_]], A](a1: A) = Unary[T, A](a1)
  def ToTimestamp[T[_[_]], A](a1: A) = Unary[T, A](a1)
  def Extract[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)

  // math
  def Negate[T[_[_]], A](a1: A) = Unary[T, A](a1)
  def Add[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def Multiply[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def Subtract[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def Divide[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def Modulo[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def Power[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)

  // relations
  def Not[T[_[_]], A](a1: A) = Unary[T, A](a1)
  def Eq[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def Neq[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def Lt[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def Lte[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def Gt[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def Gte[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def IfUndefined[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def And[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def Or[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def Coalesce[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def Between[T[_[_]], A](a1: A, a2: A, a3: A) = Ternary[T, A](a1, a2, a3)
  def Cond[T[_[_]], A](a1: A, a2: A, a3: A) = Ternary[T, A](a1, a2, a3)

  // set
  def In[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def Within[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def Constantly[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)

  // string
  def Length[T[_[_]], A](a1: A) = Unary[T, A](a1)
  def Lower[T[_[_]], A](a1: A) = Unary[T, A](a1)
  def Upper[T[_[_]], A](a1: A) = Unary[T, A](a1)
  def Boolean[T[_[_]], A](a1: A) = Unary[T, A](a1)
  def Integer[T[_[_]], A](a1: A) = Unary[T, A](a1)
  def Decimal[T[_[_]], A](a1: A) = Unary[T, A](a1)
  def Null[T[_[_]], A](a1: A) = Unary[T, A](a1)
  def ToString[T[_[_]], A](a1: A) = Unary[T, A](a1)
  def Like[T[_[_]], A](a1: A, a2: A, a3: A) = Ternary[T, A](a1, a2, a3)
  def Search[T[_[_]], A](a1: A, a2: A, a3: A) = Ternary[T, A](a1, a2, a3)
  def Substring[T[_[_]], A](a1: A, a2: A, a3: A) = Ternary[T, A](a1, a2, a3)

  // structural
  def MakeArray[T[_[_]], A](a1: A) = Unary[T, A](a1)
  def MakeObject[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def ConcatArrays[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def ConcatObjects[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def ProjectIndex[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def ProjectField[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)
  def DeleteField[T[_[_]], A](a1: A, a2: A) = Binary[T, A](a1, a2)

  // helpers & QScript-specific
  def StrLit[T[_[_]]: Corecursive, A](str: String) = Nullary[T, A](EJson.Str[T[EJson]](str).embed)
}
