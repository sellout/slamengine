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

package quasar.physical.sparkcore.fs

import quasar.Predef._
import quasar.PlannerErrT
import quasar.{PhaseResults, PhaseResultT, PhaseResult, LogicalPlan, Data}
import quasar.fp.eitherT._
import quasar.qscript._
import quasar.fs.QueryFile
import quasar.fs.QueryFile._
import quasar.fs._
import quasar.Planner._
import quasar.fs.FileSystemError._
import quasar.fp.free._
import quasar.effect.{MonotonicSeq, Read, KeyValueStore}
import quasar.contrib.pathy._

import org.apache.spark._
import org.apache.spark.rdd._
import matryoshka._, Recursive.ops._
import scalaz._
import Scalaz._
import scalaz.concurrent.Task

object queryfile {

  final case class Input(
    fromFile: (SparkContext, AFile) => Task[RDD[String]],
    store: (RDD[Data], AFile) => Task[Unit],
    fileExists: AFile => Task[Boolean],
    listContents: ADir => EitherT[Task, FileSystemError, Set[PathSegment]]
  )

  type SparkContextRead[A] = Read[SparkContext, A]

  def chrooted[S[_]](input: Input, prefix: ADir)(implicit
    s0: Task :<: S,
    s1: SparkContextRead :<: S,
    s2: MonotonicSeq :<: S,
    s3: KeyValueStore[ResultHandle, RddState, ?] :<: S
  ): QueryFile ~> Free[S, ?] =
    flatMapSNT(interpreter(input)) compose chroot.queryFile[QueryFile](prefix)

  def interpreter[S[_]](input: Input)(implicit
    s0: Task :<: S,
    s1: SparkContextRead :<: S,
    s2: MonotonicSeq :<: S,
    s3: KeyValueStore[ResultHandle, RddState, ?] :<: S
  ): QueryFile ~> Free[S, ?] =
    new (QueryFile ~> Free[S, ?]) {
      def apply[A](qf: QueryFile[A]) = qf match {
        case FileExists(f) => fileExists(input, f)
        case ListContents(dir) => listContents(input, dir)
        case ExecutePlan(lp: Fix[LogicalPlan], out: AFile) => {
          val lc: ConvertPath.ListContents[FileSystemErrT[PhaseResultT[Free[S, ?],?],?]] = (adir: ADir) => EitherT(listContents(input, adir).liftM[PhaseResultT]) 
          val qs = (QueryFile.convertToQScript(lc.some)(lp)) >>=
          (qs => EitherT(WriterT(executePlan(input, qs, out, lp).map(_.run.run))))

          qs.run.run
        }
        case EvaluatePlan(lp: Fix[LogicalPlan]) => {
          val lc: ConvertPath.ListContents[FileSystemErrT[PhaseResultT[Free[S, ?],?],?]] = (adir: ADir) => EitherT(listContents(input, adir).liftM[PhaseResultT]) 
          val qs = (QueryFile.convertToQScript(lc.some)(lp)) >>=
          (qs => EitherT(WriterT(evaluatePlan(input, qs, lp).map(_.run.run))))

          qs.run.run
        }
        case QueryFile.More(h) => more(h)
        case QueryFile.Close(h) => close(h)
        case _ => ???
      }
    } 

  implicit def composedFunctor[F[_]: Functor, G[_]: Functor]:
      Functor[(F ∘ G)#λ] =
    new Functor[(F ∘ G)#λ] {
      def map[A, B](fa: F[G[A]])(f: A => B) = fa ∘ (_ ∘ f)
    }

  // f => EitherT(WriterT(f.map(_.run)))

  private def executePlan[S[_]](input: Input, qs: Fix[QScriptTotal[Fix, ?]], out: AFile, lp: Fix[LogicalPlan]) (implicit
    s0: Task :<: S,
    read: Read.Ops[SparkContext, S]
  ): Free[S, EitherT[Writer[PhaseResults, ?], FileSystemError, AFile]] = {

    val total = scala.Predef.implicitly[Planner.Aux[Fix, QScriptTotal[Fix, ?]]]

    read.asks { sc =>
      val sparkStuff: Task[PlannerError \/ RDD[Data]] =
        qs.cataM(total.plan(input.fromFile)).eval(sc).run

      injectFT.apply {
        sparkStuff >>= (mrdd => mrdd.bitraverse[(Task ∘ Writer[PhaseResults, ?])#λ, FileSystemError, AFile](
          planningFailed(lp, _).point[Writer[PhaseResults, ?]].point[Task],
          rdd => input.store(rdd, out).as (Writer(Vector(PhaseResult.Detail("RDD", rdd.toDebugString)), out))).map(EitherT(_)))
      }
    }.join
  }


  // TODO for Q4.2016  - unify it with ReadFile
  final case class RddState(maybeRDD: Option[RDD[(Data, Long)]], pointer: Int)

  private def evaluatePlan[S[_]](input: Input, qs: Fix[QScriptTotal[Fix, ?]], lp: Fix[LogicalPlan])(implicit
      s0: Task :<: S,
      kvs: KeyValueStore.Ops[ResultHandle, RddState, S],
      read: Read.Ops[SparkContext, S],
      ms: MonotonicSeq.Ops[S]
  ): Free[S, EitherT[Writer[PhaseResults, ?], FileSystemError, ResultHandle]] = {

    val total = scala.Predef.implicitly[Planner.Aux[Fix, QScriptTotal[Fix, ?]]]


    val temp: EitherT[Free[S, ?], PlannerError, ResultHandle] = for {
      h <- EitherT(ms.next map (ResultHandle(_).right[PlannerError]))
      rdd <- EitherT(read.asks { sc =>
        lift(qs.cataM(total.plan(input.fromFile)).eval(sc).run).into[S]
      }.join)
      _ <- kvs.put(h, RddState(rdd.zipWithIndex.some, 0)).liftM[PlannerErrT]
    } yield (h)

    val temp2: Free[S, PlannerError \/ ResultHandle] = temp.run

    val temp3 =
      temp2
         .map(_.leftMap(planningFailed(lp, _)))
         .map(mrh => EitherT(mrh.point[Writer[PhaseResults, ?]]))

    temp3
  }

  private def more[S[_]](h: ResultHandle)(implicit
      s0: Task :<: S,
      kvs: KeyValueStore.Ops[ResultHandle, RddState, S]
  ): Free[S, FileSystemError \/ Vector[Data]] = {

    val step = 5000

    kvs.get(h).toRight(unknownResultHandle(h)).flatMap {
      case RddState(None, _) =>
        Vector.empty[Data].pure[EitherT[Free[S, ?], FileSystemError, ?]]
      case RddState(Some(rdd), p) =>
        for {
          collected <- lift(Task.delay {
            rdd
              .filter(d => d._2 >= p && d._2 < (p + step))
              .map(_._1).collect.toVector
          }).into[S].liftM[FileSystemErrT]
          rddState = if(collected.isEmpty) RddState(None, 0) else RddState(Some(rdd), p + step)
          _ <- kvs.put(h, RddState(None, 0)).liftM[FileSystemErrT]
        } yield(collected)
    }.run
  }

  private def close[S[_]](h: ResultHandle)(implicit
      kvs: KeyValueStore.Ops[ResultHandle, RddState, S]
     ): Free[S, Unit] = kvs.delete(h)

  private def fileExists[S[_]](input: Input, f: AFile)(implicit
    s0: Task :<: S): Free[S, Boolean] =
    injectFT[Task, S].apply (input.fileExists(f))

  private def listContents[S[_]](input: Input, d: ADir)(implicit
    s0: Task :<: S): Free[S, FileSystemError \/ Set[PathSegment]] =
    injectFT[Task, S].apply(input.listContents(d).run)
}
