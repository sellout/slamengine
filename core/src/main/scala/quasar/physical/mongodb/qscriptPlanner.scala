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

package quasar.physical.mongodb

import quasar._, Planner.PlannerError, Type._
import quasar.qscript._, DataLevelOperations._
import quasar.std._, StdLib.structural._, StdLib.math._

import scala.Predef.ArrowAssoc

import matryoshka._
import scalaz._

// TODO: How do we distinguish between components of MapFunc and FilterFunc?
//       Should we unify them?

object QScriptPlanner {

  type MapAlgebra[A] = AlgebraM[PlannerError \/ ?, EnvT[MapFunc, Type, ?], A]

  def jsExpr[T[_[_]]]: MapAlgebra[T[JsExpr]] = env => {
    val (typ, f) = env.run
    f match {
      case ConcatOp =>
        matchTypes(typ)(AnyArray -> Binop(Add, _, _))
    }
  }

  def selector[T[_[_]]]: MapAlgebra[T[Selector]] = {
  }

  def expr[T[_[_]]]: MapAlgebra[T[ExprOp]] =
    env => {
      val (typ, f) = env.run
      f match {
        case ConcatOp => matchTypes(typ)(
          Str      -> $concat(_, _).right,
          AnyArray -> arrayConcat(_, _)
        ) \/> InvalidQScript(qs, "impossible type")
      }
    }

  def plan[T[_[_]]]:
      AlgebraM[PlannerError \/ ?, EnvT[QScript[T, ?], Type, ?], T[Workflow]] =
    env => {
      val (typ, qs) = env.run
      qs match {
        case Root() => $read(Path("/")).right
        // Javascript can only appear here and in filter(?)
        case Map(f, src) => f match {
          case ProjectField(EJson.Str(field)) => src match {
            case $read(path) => ??? // decide (based on the mount) whether this
                                    // is an extension of the read or a
                                    // projectField
            case _           => projectField(src, field).right
          }
          case ProjectField(_) => ??? // gonna need the JS in this case
        }
        case Reduce(f, src) => reduce(src)(f match {
          case Count     => _ => $sum($literal(Bson.Int32(1)))
          case Sum       => $sum(_)
          case Avg       => $avg(_)
          case Min       => $min(_)
          case Max       => $max(_)
          case Arbitrary => $first(_)
        }).right
        case Sort(f, o, src) => sortBy(src, List(f), List(o)).right
         // Selectors can only be used here.
         // JS can be used here, followed by a Where selector
        case Filter(f, src) => ???
        case Union(src, lBranch, rBranch) => ???
        // Because we were smart and rewrote it before we got here
        case EquiJoin(lkey, rkey, f, src, lBranch, rBranch) =>
        case LeftShift(src) => matchTypes(typ)(
          AnyArray -> flattenArray(src),
          // TODO: ensure string keys
          AnyMap   -> flattenMap(src)) \/> InvalidQScript(qs, "impossible type")
      }
    }
}
