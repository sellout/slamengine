package slamdata.engine.analysis

import slamdata.engine.fp._

import scalaz._
import Scalaz._

sealed trait hTerm {
  // HFix

  case class HTerm[H[_[_], _], Ix](hunFix: H[HTerm[H, ?], Ix])

  // def hfrom[Phi[_], Ix](phi: Phi[Ix], index: Ix)
  //   (implicit Fp: Fam[Phi], Hp: HFunctor[Phi, λ[(F[_], A) => Pf[Phi, F, A]]]):
  //     HTerm[λ[(F[_], A) => Pf[Phi, F, A]], Ix] =
  //   fold[Phi, Ix, HTerm[λ[(F[_], A) => Pf[Phi, F, A]], ?]](phi, index)((
  //     _: Phi[Ix],
  //     x: λ[(F[_], A) => Pf[Phi, F, A]][HTerm[λ[(F[_], A) => Pf[Phi, F, A]], ?], Ix]) =>
  //     HTerm(x))

  // def hto[Phi[_], Ix](phi: Phi[Ix], pf: HTerm[λ[(F[_], A) => Pf[Phi, F, A]], Ix])
  //   (implicit Fp: Fam[Phi], Hp: HFunctor[Phi, λ[(F[_], A) => Pf[Phi, F, A]]]):
  //     Ix =
  //   unfold[Phi, Ix, HTerm[λ[(F[_], A) => Pf[Phi, F, A]], ?]](phi, pf)((_, x) => x.hunFix)

  // Constructor

  trait Constructor[C] {
    def name[T[_, _, _, _], R[_], Ix](x: T[C, Function2[_, _, _], R[_], Ix]):
        String
    def fixity[T[_, _, _, _], R[_], Ix](x: T[C, Function2[_, _, _], R[_], Ix]):
        Fixity = Prefix
  }

  sealed trait Fixity
  case object Prefix extends Fixity
  case class Infix(assoc: Associativity, i: Int) extends Fixity

  sealed trait Associativity
  case object LeftAssociative extends Associativity
  case object RightAssociative extends Associativity
  case object NotAssociative extends Associativity

  // Base

  case class I[Xi, R[_], Ix](unI: R[Xi])
  case class K[A, R[_], Ix](unK: A)
  case class U[R[_], Ix]()
  sealed trait Sum[F[_[_], _], G[_[_], _], R[_], Ix]
  case class L[F[_[_], _], R[_], Ix](unL: F[R, Ix])
      extends Sum[F, Nothing, R, Ix]
  case class R[G[_[_], _], R[_], Ix](unR: G[R, Ix])
      extends Sum[Nothing, G, R, Ix]
  case class Product[F[_[_], _], G[_[_], _], R[_], Ix](fst: F[R, Ix], snd: G[R, Ix])
  case class Tag[F[_[_], _], Ix0, R[_], Ix](untag: F[R, Ix0])
  case class Compose[F[_], G[_[_], _], R[_], Ix](unD: F[G[R, Ix]])
  case class Construct[C, F[_[_], _], R[_], Ix](unC: F[R, Ix])

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

  trait Pf[Phi[_], F[_], A]

  trait El[Phi[_], Ix] {
    def proof: Phi[Ix]
  }

  trait Fam[Phi[_]] {
    def from[Ix](phi: Phi[Ix], index: Ix): Pf[Phi, I0, Ix]
    def to[Ix](phi: Phi[Ix], pf: Pf[Phi, I0, Ix]): Ix
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

  implicit def KHFunctor[Phi[_]]() = {
    type PartialK[R[_], Ix] = K[_, R, Ix]
    new HFunctor[Phi, PartialK] {
      def hmapA[R[_], R0[_], Ix, A[_]]
        (p: Phi[Ix], x: PartialK[R, Ix])
        (f: (Phi[Ix], R[Ix]) => A[R0[Ix]] forSome { type Ix })
        (implicit A: Applicative[A]) =
        A.point(K(x))
    }
  }

  implicit def UHFunctor[Phi[_]]() = new HFunctor[Phi, U] {
    def hmapA[R[_], R0[_], Ix, A[_]]
      (p: Phi[Ix], x: U[R, Ix])
      (f: (Phi[Ix], R[Ix]) => A[R0[Ix]] forSome { type Ix })
      (implicit A: Applicative[A]) =
      A.point(U[R0, Ix])
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
    type PartialProduct[R[_], Ix] = Product[F, G, R, Ix]
    new HFunctor[Phi, PartialProduct] {
      def hmapA[R[_], R0[_], Ix, A[_]]
        (p: Phi[Ix], x: PartialProduct[R, Ix])
        (f: (Phi[Ix], R[Ix]) => A[R0[Ix]] forSome { type Ix })
        (implicit A: Applicative[A]) = x match {
          case Product(x, y) =>
            (Lh.hmapA(p, x)(f) |@| Rh.hmapA(p, y)(f))(Product.apply _)
        }
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
  type Algebra[Phi[_], R[_]] =
    Algebra0[Phi, λ[(F[_], A) => Pf[Phi, F, A]], R]
  trait AlgebraF0[Phi[_], F[_[_], _], G[_], R[_]] {
    def apply[Ix](p: Phi[Ix], x: F[R, Ix]): G[R[Ix]]
  }
  type AlgebraF[Phi[_], G[_], R[_]] =
    AlgebraF0[Phi, λ[(F[_], A) => Pf[Phi, F, A]], G, R]

  def fold[Phi[_], Ix, R[_]](p: Phi[Ix], x: Ix)(f: Algebra[Phi, R])
    (implicit Fp: Fam[Phi], Hp: HFunctor[Phi, λ[(F[_], A) => Pf[Phi, F, A]]]):
      R[Ix] =
    f(p, hmap[Phi, I0, R, Ix, λ[(F[_], A) => Pf[Phi, F, A]]](p, Fp.from(p, x))((p, x) => fold(p, x.unI0)(f)))

  def foldM[Phi[_], Ix, R[_], M[_]](p:Phi[Ix], x: Ix)(f: AlgebraF[Phi, M, R])
    (implicit Fp: Fam[Phi], Hp: HFunctor[Phi, λ[(F[_], A) => Pf[Phi, F, A]]], Mm: Monad[M]):
      M[R[Ix]] =
    Mm.bind(Hp.hmapA(p, Fp.from(p, x))((p, x) => foldM(p, x.unI0)(f)))(f(p, _))

  trait CoAlgebra0[Phi[_], F[_[_], _], R[_]] {
    def apply[Ix](p: Phi[Ix], x: R[Ix]): F[R, Ix]
  }
  type CoAlgebra[Phi[_], R[_]] = CoAlgebra0[Phi, λ[(F[_], A) => Pf[Phi, F, A]], R]
  trait CoAlgebraF0[Phi[_], F[_[_], _], G[_], R[_]] {
    def apply[Ix](p: Phi[Ix], x: R[Ix]): G[F[R, Ix]]
  }
  type CoAlgebraF[Phi[_], G[_], R[_]] = CoAlgebraF0[Phi, λ[(F[_], A) => Pf[Phi, F, A]], G, R]

  def unfold[Phi[_], Ix, R[_]](p: Phi[Ix], x: R[Ix])(f: CoAlgebra[Phi, R])
    (implicit Fp: Fam[Phi], Hp: HFunctor[Phi, λ[(F[_], A) => Pf[Phi, F, A]]]):
      Ix =
    Fp.to(p, hmap[Phi, R, I0, Ix, λ[(F[_], A) => Pf[Phi, F, A]]](p, f(p, x))((p, x) => I0(unfold(p, x)(f))))

  // def unfoldM[Phi[_], Ix, R[_], M[_]](p: Phi[Ix], x: R[Ix])(f: CoAlgebraF[Phi, M, R])
  //   (implicit Fp: Fam[Phi], Hp: HFunctor[Phi, ({type λ[F[_], A] = Pf[Phi, F, A]})#λ], Mm: Monad[M]):
  //     M[Ix] =
  //   Mm.bind(f(p, x))(Fp.to(p, hmap(p, _)((p, x) => liftM(I0, unfoldM(p, x)(f)))).liftM)

}
