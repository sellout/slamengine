package slamdata.engine.analysis

import slamdata.engine.fp._

import scalaz._
import Scalaz._

sealed trait hTerm {
  // HFix

  case class HTerm[H[_[_], _], Ix](hunFix: H[HTerm[H, ?], Ix])

  def hfrom[Phi[_], Ix](phi: Phi[Ix], index: Ix)
    (implicit Fp: Fam[Phi], Hp: HFunctor[Phi, PfResolver[Phi]#Pf]):
      HTerm[PfResolver[Phi]#Pf, Ix] = {
    type PartHTerm[A] = HTerm[PfResolver[Phi]#Pf, A]
    fold[Phi, Ix, PartHTerm](phi, index)(new Algebra[Phi, PartHTerm] {
      def apply[Ix](p: Phi[Ix], x: PfResolver[Phi]#Pf[PartHTerm, Ix]) =
        HTerm[PfResolver[Phi]#Pf, Ix](x)
    })
  }

  def hto[Phi[_], Ix](phi: Phi[Ix], pf: HTerm[PfResolver[Phi]#Pf, Ix])
    (implicit Fp: Fam[Phi], Hp: HFunctor[Phi, PfResolver[Phi]#Pf]):
      Ix = {
    type PartHTerm[A] = HTerm[PfResolver[Phi]#Pf, A]
    unfold[Phi, Ix, PartHTerm](phi, pf)(new CoAlgebra[Phi, PartHTerm] {
      def apply[Ix](p: Phi[Ix], x: PartHTerm[Ix]) = x.hunFix
    })
  }

  // Constructor

  trait Constructor[C] {
    val name: String
    val fixity: Fixity = Prefix
    // def name[T[_, _, _, _], R[_], Ix](x: T[C, F[_[_], _], R[_], Ix]):
    //     String
    // def fixity[T[_, _, _, _], R[_], Ix](x: T[C, F[_[_], _], R[_], Ix]):
    //     Fixity = Prefix
  }

  sealed trait Fixity
  case object Prefix extends Fixity
  case class Infix(assoc: Associativity, i: Int) extends Fixity

  sealed trait Associativity
  case object LeftAssociative extends Associativity
  case object RightAssociative extends Associativity
  case object NotAssociative extends Associativity

  // Base

  case class I[Xi]() { case class Rec[R[_], Ix](unI: R[Xi]) }
  case class K[A]()  { case class Rec[R[_], Ix](unK: A) }
  // NB: I would nest this for consistency, but Scala doesn’t like when the
  //     container is either a case object, or a case class without type params
  case class U[R[_], Ix]()
  case class Sum[F[_[_], _], G[_[_], _]]() {
    sealed trait Rec[R[_], Ix]
    case class L[R[_], Ix](unL: F[R, Ix]) extends Rec[R, Ix]
    case class R[R[_], Ix](unL: G[R, Ix]) extends Rec[R, Ix]
  }
  case class Product[F[_[_], _], G[_[_], _]]() {
    case class Rec[R[_], Ix](fst: F[R, Ix], snd: G[R, Ix])
  }
  case class Tag[F[_[_], _], Ix0]() {
    case class Rec[R[_], Ix](untag: F[R, Ix0])
  }
  case class D[F[_], G[_[_], _]]() { case class Rec[R[_], Ix](unD: F[G[R, Ix]]) }
  case class C[C, F[_[_], _]]()    { case class Rec[R[_], Ix](unC: F[R, Ix]) }

  case class I0[A](unI0: A)
  case class K0[A, B](unK0: A)

  implicit val I0Applicative: Applicative[I0] = new Applicative[I0] {
    def point[A](x: => A) = I0(x)
    def ap[A, B](fa: => I0[A])(f: => I0[A => B]): I0[B] = I0(f.unI0(fa.unI0))
  }

  type PartialK0[B] = K0[_, B]

  implicit val K0Functor: Functor[PartialK0] = new Functor[PartialK0] {
    def map[A, B](fa: PartialK0[A])(f: A => B) = K0(fa.unK0)
  }

  trait PfResolver[Phi[_]] { type Pf[F[_], A] }

  trait El[Phi[_], Ix] {
    val proof: Phi[Ix]
  }

  trait Fam[Phi[_]] {
    def from[Ix](phi: Phi[Ix], index: Ix): PfResolver[Phi]#Pf[I0, Ix]
    def to[Ix](phi: Phi[Ix], pf: PfResolver[Phi]#Pf[I0, Ix]): Ix
  }

  trait EqS[Phi[_]] {
    def eqS[Ix, Ix0](a: Phi[Ix], b: Phi[Ix0]): Ix =:= Ix0
  }

  // HFunctor

  trait HFunctor[Phi[_], F[_[_], _]] {
    def hmapA[R[_], R0[_], Ix, A[_]]
      (p: Phi[Ix], x: F[R, Ix])
      (f: (Phi[Ix], R[Ix]) => A[R0[Ix]] forSome { type Ix })
      (implicit A: Applicative[A]):
        A[F[R0, Ix]]
  }

  // implicit def IHFunctor[Phi[_], Xi](implicit El: El[Phi, Xi]) = {
  //   type PartialI[R[_], Ix] = I[Xi, R, Ix]
  //   new HFunctor[Phi, PartialI] {
  //     def hmapA[R[_], R0[_], Ix, A[_]]
  //       (f: Function2[Phi[Ix], R[Ix], A[R0[Ix]]], p: Phi[Ix], x: PartialI[R, Ix])
  //       (implicit A: Applicative[A]) =
  //       A.ap(f(El.proof, x.unI))(A.point(I))
  //   }}

  implicit def KHFunctor[Phi[_], X]() = {
    new HFunctor[Phi, K[X]#Rec] {
      def hmapA[R[_], R0[_], Ix, A[_]]
        (p: Phi[Ix], x: K[X]#Rec[R, Ix])
        (f: (Phi[Ix], R[Ix]) => A[R0[Ix]] forSome { type Ix })
        (implicit A: Applicative[A]) =
        A.point(K[X].Rec[R0, Ix](x.unK))
    }
  }

  implicit def UHFunctor[Phi[_]]() = new HFunctor[Phi, U] {
    def hmapA[R[_], R0[_], Ix, A[_]]
      (p: Phi[Ix], x: U[R, Ix])
      (f: (Phi[Ix], R[Ix]) => A[R0[Ix]] forSome { type Ix })
      (implicit A: Applicative[A]) =
      A.point(U[R0, Ix]())
  }

  // implicit def SumHFunctor[Phi[_], F[_[_], _], G[_[_], _]]
  //   (implicit Lh: HFunctor[Phi, F], Rh: HFunctor[Phi, G]) = {
  //   type PartialSum[R[_], Ix] = Sum[F, G, R, Ix]
  //   new HFunctor[Phi, PartialSum] {
  //     def hmapA[R[_], R0[_], Ix, A[_]]
  //       (f: Function2[Phi[Ix], R[Ix], A[R0[Ix]]], p: Phi[Ix], x: PartialSum[R, Ix])
  //       (implicit A: Applicative[A]) = x match {
  //         case L(y) => A.ap(Lh.hmapA(f, p, y))(A.point(L[F, R, Ix]))
  //         case R(y) => A.ap(Rh.hmapA(f, p, y))(A.point(R[G, R, Ix]))
  //       }
  //   }
  // }

  implicit def ProductHFunctor[Phi[_], F[_[_], _], G[_[_], _]]
    (implicit Lh: HFunctor[Phi, F], Rh: HFunctor[Phi, G]) = {
    new HFunctor[Phi, Product[F,G]#Rec] {
      def hmapA[R[_], R0[_], Ix, A[_]]
        (p: Phi[Ix], x: Product[F,G]#Rec[R, Ix])
        (f: (Phi[Ix], R[Ix]) => A[R0[Ix]] forSome { type Ix })
        (implicit A: Applicative[A]) =
        (Lh.hmapA(p, x.fst)(f) |@| Rh.hmapA(p, x.snd)(f))(Product[F,G].Rec.apply _)
        
    }
  }

  // implicit def ConstructorHFunctor[Phi[_], C, F[_[_], _]]
  //   (implicit C: Constructor[C], Hf: HFunctor[Phi, F]) = {
  //   type PartialConstruct[R[_], Ix] = Construct[C, F, R, Ix]
  //   new HFunctor[Phi, PartialConstruct] {
  //     def hmapA[R[_], R0[_], Ix, A[_]]
  //       (f: Function2[Phi[Ix], R[Ix], A[R0[Ix]]], p: Phi[Ix], x: PartialConstruct[R, Ix])
  //       (implicit A: Applicative[A]) =
  //       A.ap(Hf.hmapA(f, p, x.unC))(A.point(Construct.apply _))
  //   }
  // }

  def hmap[Phi[_], R[_], R0[_], Ix, F[_[_], _]]
    (p: Phi[Ix], x: F[R, Ix])
    (f: (Phi[Ix], R[Ix]) => R0[Ix])
    (implicit Hf: HFunctor[Phi, F]):
      F[R0, Ix] =
    Hf.hmapA(p, x)((ix, x) => I0(f(ix, x))).unI0

  // Fold

  trait Algebra0[Phi[_], F[_[_], _], R[_]] {
    def apply[Ix](p: Phi[Ix], x: F[R, Ix]): R[Ix]
  }
  type Algebra[Phi[_], R[_]] = Algebra0[Phi, PfResolver[Phi]#Pf, R]
  trait AlgebraF0[Phi[_], F[_[_], _], G[_], R[_]] {
    def apply[Ix](p: Phi[Ix], x: F[R, Ix]): G[R[Ix]]
  }
  type AlgebraF[Phi[_], G[_], R[_]] = AlgebraF0[Phi, PfResolver[Phi]#Pf, G, R]

  def fold[Phi[_], Ix, R[_]](p: Phi[Ix], x: Ix)(f: Algebra[Phi, R])
    (implicit Fp: Fam[Phi], Hp: HFunctor[Phi, PfResolver[Phi]#Pf]):
      R[Ix] = {
    f(p, hmap[Phi, I0, R, Ix, PfResolver[Phi]#Pf](p, Fp.from(p, x))((p, x) => fold(p, x.unI0)(f)))
  }

  def foldM[Phi[_], Ix, R[_], M[_]](p:Phi[Ix], x: Ix)(f: AlgebraF[Phi, M, R])
    (implicit Fp: Fam[Phi], Hp: HFunctor[Phi, PfResolver[Phi]#Pf], Mm: Monad[M]):
      M[R[Ix]] =
    Mm.bind(Hp.hmapA(p, Fp.from(p, x))((p, x) => foldM(p, x.unI0)(f)))(f(p, _))

  trait CoAlgebra0[Phi[_], F[_[_], _], R[_]] {
    def apply[Ix](p: Phi[Ix], x: R[Ix]): F[R, Ix]
  }
  type CoAlgebra[Phi[_], R[_]] = CoAlgebra0[Phi, PfResolver[Phi]#Pf, R]
  trait CoAlgebraF0[Phi[_], F[_[_], _], G[_], R[_]] {
    def apply[Ix](p: Phi[Ix], x: R[Ix]): G[F[R, Ix]]
  }
  type CoAlgebraF[Phi[_], G[_], R[_]] =
    CoAlgebraF0[Phi, PfResolver[Phi]#Pf, G, R]

  def unfold[Phi[_], Ix, R[_]](p: Phi[Ix], x: R[Ix])(f: CoAlgebra[Phi, R])
    (implicit Fp: Fam[Phi], Hp: HFunctor[Phi, PfResolver[Phi]#Pf]):
      Ix = 
    Fp.to(p, hmap[Phi, R, I0, Ix, PfResolver[Phi]#Pf](p, f(p, x))((p, x) => I0(unfold(p, x)(f))))
  

  def unfoldM[Phi[_], Ix, R[_], M[_]](p: Phi[Ix], x: R[Ix])(f: CoAlgebraF[Phi, M, R])
    (implicit Fp: Fam[Phi], Hp: HFunctor[Phi, PfResolver[Phi]#Pf], Mm: Monad[M]):
      M[Ix] =
    Mm.bind(f(p, x))(
      Mm.lift((pf: PfResolver[Phi]#Pf[I0, Ix]) => Fp.to(p, pf)) compose
      (y => Hp.hmapA(p, y)((p, x) => Mm.lift((a: Ix) => I0(a))(unfoldM(p, x)(f)))))
}

object mutualrec extends hTerm
