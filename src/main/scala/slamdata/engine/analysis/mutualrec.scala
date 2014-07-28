package slamdata.engine.analysis

import slamdata.engine.fp._

import scalaz._
import Scalaz._
import Leibniz._

sealed trait HFix extends Base with HFunctor with Fold {

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
}

sealed trait HConstructor {

  trait Constructor {
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
}

sealed trait Base extends HConstructor {

  case class I[Xi, R[_], Ix](unI: R[Xi])
  case class K[A, R[_], Ix](unK: A)
  case class U[R[_], Ix]()
  sealed trait Sum[F[_[_], _], G[_[_], _], R[_], Ix]
  case class Lef[F[_[_], _], R[_], Ix](unL: F[R, Ix]) extends Sum[F, Nothing, R, Ix]
  case class Righ[G[_[_], _], R[_], Ix](unR: G[R, Ix]) extends Sum[Nothing, G, R, Ix]
  case class Product[F[_[_], _], G[_[_], _], R[_], Ix](fst: F[R, Ix], snd: G[R, Ix])
  case class Tag[F[_[_], _], Ix0, R[_], Ix](unTag: F[R, Ix0])
  case class D[F[_], G[_[_], _], R[_], Ix](unD: F[G[R, Ix]])
  case class C[Con, F[_[_], _], R[_], Ix](unC: F[R, Ix])

  trait IT[Xi] { type Rec[R[_], Ix] = I[Xi, R, Ix] }
  trait KT[A]  { type Rec[R[_], Ix] = K[A, R, Ix] }
  trait SumT[F[_[_], _], G[_[_], _]] {
    type Rec[R[_], Ix] = Sum[F, G, R, Ix]
  }
  trait LefT[F[_[_], _]] {
    type Rec[R[_], Ix] = Lef[F, R, Ix]
  }
  trait RighT[G[_[_], _]] {
    type Rec[R[_], Ix] = Righ[G, R, Ix]
  }
  trait ProductT[F[_[_], _], G[_[_], _]] {
    type Rec[R[_], Ix] = Product[F, G, R, Ix]
  }
  trait TagT[F[_[_], _], Ix0] {
    type Rec[R[_], Ix] = Tag[F, Ix0, R, Ix]
  }
  trait DT[F[_], G[_[_], _]] { type Rec[R[_], Ix] = D[F, G, R, Ix] }
  trait CT[Con, F[_[_], _]] { type Rec[R[_], Ix] = C[Con, F, R, Ix] }

  trait UnapplyH[A] {
    type F[_[_], _]
    type R[_]
    type Ix

    val proof: A === F[R, Ix]
  }

  trait UnapplyFH[A] {
    type F[_]
    type G[_[_], _]
    type R[_]
    type Ix

    val proof: A === F[G[R, Ix]]
  }

  class UnapplyFList[G0[_[_], _], R0[_], Ix0]
      extends UnapplyFH[List[G0[R0, Ix0]]] {
    type F[X] = List[X]
    type G[X[_], Y] = G0[X, Y]
    type R[X] = R0[X]
    type Ix = Ix0

    val proof = force[⊥, ⊤, List[G0[R0, Ix0]], F[G[R, Ix]]]
  }
  implicit def UnapplyFList[G0[_[_], _], R0[_], Ix] =
    new UnapplyFList[G0, R0, Ix]

  trait UnapplyH2[A, B] {
    type F[_[_], _]
    type G[_[_], _]
    type R[_]
    type Ix

    val proofA: A === F[R, Ix]
    val proofB: B === G[R, Ix]
  }

  // implicit def UnapplyH2[A, B](implicit UA: UnapplyH[A], UB: UnapplyH[B]) =
  //   new UnapplyH2[A, B]

  trait UnapplyR[A] {
    type R[_]
    type Ix

    val proof: A === R[Ix]
  }

  implicit def UnapplyRI0[A] = new UnapplyR[I0[A]] {
    type R[X] = I0[X]
    type Ix = A

    val proof = force[⊥, ⊤, I0[A], R[Ix]]
  }

  class UnapplyHI[Xi, R0[_], Ix0] extends UnapplyH[I[Xi, R0, Ix0]] {
    type F[X[_], Y] = I[Xi, X, Y]
    type R[X] = R0[X]
    type Ix = Ix0

    val proof = force[⊥, ⊤, I[Xi, R0, Ix0], F[R, Ix]]
  }
  implicit def UnapplyHI[Xi, R0[_], Ix0] = new UnapplyHI[Xi, R0, Ix0]

  class UnapplyHK[A, R0[_], Ix0] extends UnapplyH[K[A, R0, Ix0]] {
    type F[X[_], Y] = K[A, X, Y]
    type R[X] = R0[X]
    type Ix = Ix0

    val proof = force[⊥, ⊤, K[A, R0, Ix0], F[R, Ix]]
  }
  implicit def UnapplyHK[A, R0[_], Ix0] = new UnapplyHK[A, R0, Ix0]

  class UnapplyHU[R0[_], Ix0] extends UnapplyH[U[R0, Ix0]] {
    type F[X[_], Y] = U[X, Y]
    type R[X] = R0[X]
    type Ix = Ix0

    val proof = force[⊥, ⊤, U[R0, Ix0], F[R, Ix]]
  }
  implicit def UnapplyHU[R0[_], Ix0] = new UnapplyHU[R0, Ix0]

  class UnapplyHL[F0[_[_], _], R0[_], Ix0]
      extends UnapplyH[Lef[F0, R0, Ix0]] {
    type F[X[_], Y] = Lef[F0, X, Y]
    type R[X] = R0[X]
    type Ix = Ix0

    val proof = force[⊥, ⊤, Lef[F0, R0, Ix0], F[R, Ix]]
  }
  implicit def UnapplyHL[F0[_[_], _], R0[_], Ix0] =
    new UnapplyHL[F0, R0, Ix0]

  class UnapplyHR[G0[_[_], _], R0[_], Ix0]
      extends UnapplyH[Righ[G0, R0, Ix0]] {
    type F[X[_], Y] = Righ[G0, X, Y]
    type R[X] = R0[X]
    type Ix = Ix0

    val proof = force[⊥, ⊤, Righ[G0, R0, Ix0], F[R, Ix]]
  }
  implicit def UnapplyHR[G0[_[_], _], R0[_], Ix0] =
    new UnapplyHR[G0, R0, Ix0]

  class UnapplyHProduct[F0[_[_], _], G0[_[_], _], R0[_], Ix0]
    extends UnapplyH[Product[F0, G0, R0, Ix0]] {
      type F[X[_], Y] = Product[F0, G0, X, Y]
      type R[X] = R0[X]
      type Ix = Ix0

    val proof = force[⊥, ⊤, Product[F0, G0, R0, Ix0], F[R, Ix]]
    }
  implicit def UnapplyHProduct[F0[_[_], _], G0[_[_], _], R0[_], Ix0] =
    new UnapplyHProduct[F0, G0, R0, Ix0]

  class UnapplyHTag[F0[_[_], _], Ix0, R0[_], Ix1]
      extends UnapplyH[Tag[F0, Ix0, R0, Ix1]] {
    type F[X[_], Y] = Tag[F0, Ix0, X, Y]
    type R[X] = R0[X]
    type Ix = Ix1

    val proof = force[⊥, ⊤, Tag[F0, Ix0, R0, Ix1], F[R, Ix]]
  }
  implicit def UnapplyHTag[F0[_[_], _], Ix0, R0[_], Ix1] =
    new UnapplyHTag[F0, Ix0, R0, Ix1]

  class UnapplyHD[G[_], F0[_[_], _], R0[_], Ix1]
      extends UnapplyH[D[G, F0, R0, Ix1]] {
    type F[X[_], Y] = D[G, F0, X, Y]
    type R[X] = R0[X]
    type Ix = Ix1

    val proof = force[⊥, ⊤, D[G, F0, R0, Ix1], F[R, Ix]]
  }
  implicit def UnapplyHD[G[_], F0[_[_], _], R0[_], Ix1] =
    new UnapplyHD[G, F0, R0, Ix1]

  class UnapplyHC[Con, F0[_[_], _], R0[_], Ix1]
      extends UnapplyH[C[Con, F0, R0, Ix1]] {
    type F[X[_], Y] = C[Con, F0, X, Y]
    type R[X] = R0[X]
    type Ix = Ix1

    val proof = force[⊥, ⊤, C[Con, F0, R0, Ix1], F[R, Ix]]
  }
  implicit def UnapplyHC[Con, F0[_[_], _], R0[_], Ix1] =
    new UnapplyHC[Con, F0, R0, Ix1]

  def IF[R, Ix](unI: R)(implicit UR: UnapplyR[R]) =
    I[UR.Ix, UR.R, Ix](UR.proof(unI))
  def KF[A, R](unK: A)(implicit UR: UnapplyR[R]) = K[A, UR.R, UR.Ix](unK)
  def UF[R]()(implicit UR: UnapplyR[R]) = U[UR.R, UR.Ix]()
  def LF[A](unL: A)(implicit UA: UnapplyH[A]) =
    Lef[UA.F, UA.R, UA.Ix](UA.proof(unL))
  def RF[A](unR: A)(implicit UA: UnapplyH[A]) =
    Righ[UA.F, UA.R, UA.Ix](UA.proof(unR))
  // class ProductF[A, B](implicit val UA: UnapplyH[A], val UB: UnapplyH[B]) {
  //   def apply(fst: A, snd: B)(implicit LA: A === UA.F[UA.R, UA.Ix], LB: B === UB.F[UB.R, UB.Ix]) =
  //     Product[UA.F, UB.F, UA.R, UA.Ix]
  // }
  def TagF[A, Ix](unTag: A, ix: Ix)(implicit UA: UnapplyH[A]) =
    Tag[UA.F, UA.Ix, UA.R, Ix](UA.proof(unTag))
  def DF[F](unD: F)(implicit UF: UnapplyFH[F]) =
    D[UF.F, UF.G, UF.R, UF.Ix](UF.proof(unD))
  def CF[Con, A](con: Con, unC: A)(implicit UA: UnapplyH[A]) =
    C[Con, UA.F, UA.R, UA.Ix](UA.proof(unC))

  case class I0[A](unI0: A)
  case class K0[A]() { case class Rec[B](unK0: A) }

  implicit val I0Applicative: Applicative[I0] = new Applicative[I0] {
    def point[A](x: => A) = I0(x)
    def ap[A, B](fa: => I0[A])(f: => I0[A => B]): I0[B] = I0(f.unI0(fa.unI0))
  }

  implicit def K0Functor[X] = new Functor[K0[X]#Rec] {
    val K0X = K0[X]()
    def map[A, B](fa: K0[X]#Rec[A])(f: A => B) = K0X.Rec(fa.unK0)
  }

  trait PfResolver[Phi[_]] { type Pf[F[_], A] }

  trait El[Phi[_], Ix] { val proof: Phi[Ix] }

  trait Fam[Phi[_]] {
    def from[Ix](phi: Phi[Ix], index: Ix): PfResolver[Phi]#Pf[I0, Ix]
    def to[Ix](phi: Phi[Ix], pf: PfResolver[Phi]#Pf[I0, Ix]): Ix
  }

  trait EqS[Phi[_]] {
    def eqS[Ix, Ix0](a: Phi[Ix], b: Phi[Ix0]): Option[Ix === Ix0]
  }
}

sealed trait HFunctor extends HConstructor with Base {

  trait HFunctor[Phi[_], F[_[_], _]] {
    def hmapA[R[_], R0[_], Ix, A[_]]
      (p: Phi[Ix], x: F[R, Ix])
      (f: ((Phi[Ix], R[Ix]) => A[R0[Ix]]) forSome { type Ix })
      (implicit A: Applicative[A]):
        A[F[R0, Ix]]
  }

  // implicit def IHFunctor[Phi[_], Xi](implicit PEl: El[Phi, Xi]) =
  //   new HFunctor[Phi, I[Xi]#Rec] {
  //     def hmapA[R[_], R0[_], Ix, A[_]]
  //       (p: Phi[Ix], x: I[Xi]#Rec[R, Ix])
  //       (f: (Phi[Xi], R[Xi]) => A[R0[Xi]])
  //       (implicit A: Applicative[A]) =
  //       A.ap(f(PEl.proof, x.unI))(A.point((r: R0[Xi]) => I[Xi].Rec(r)))
  //   }

  implicit def KHFunctor[Phi[_], X]() = new HFunctor[Phi, KT[X]#Rec] {
    def hmapA[R[_], R0[_], Ix, A[_]]
      (p: Phi[Ix], x: K[X, R, Ix])
      (f: ((Phi[Ix], R[Ix]) => A[R0[Ix]]) forSome { type Ix })
      (implicit A: Applicative[A]) =
      A.point(K(x.unK))
  }
  

  implicit def UHFunctor[Phi[_]]() = new HFunctor[Phi, U] {
    def hmapA[R[_], R0[_], Ix, A[_]]
      (p: Phi[Ix], x: U[R, Ix])
      (f: ((Phi[Ix], R[Ix]) => A[R0[Ix]]) forSome { type Ix })
      (implicit A: Applicative[A]) =
      A.point(U())
  }

  // implicit def SumHFunctor[Phi[_], F[_[_], _], G[_[_], _]]
  //   (implicit Lh: HFunctor[Phi, F], Rh: HFunctor[Phi, G]) =
  //   new HFunctor[Phi, Sum[F, G]#Rec] {
  //     def hmapA[R[_], R0[_], Ix, A[_]]
  //       (p: Phi[Ix], x: Sum[F, G]#Rec[R, Ix])
  //       (f: ((Phi[Ix], R[Ix]) => A[R0[Ix]]) forSome { type Ix })
  //       (implicit A: Applicative[A]) = x match {
  //       case Sum[F, G].L(y) => A.ap(Lh.hmapA(p, y)(f))(A.point(L[F, R, Ix]))
  //       case Sum[F, G].R(y) => A.ap(Rh.hmapA(p, y)(f))(A.point(R[G, R, Ix]))
  //     }
  //   }

  implicit def ProductHFunctor[Phi[_], F[_[_], _], G[_[_], _]]
    (implicit Lh: HFunctor[Phi, F], Rh: HFunctor[Phi, G]) =
    new HFunctor[Phi, ProductT[F,G]#Rec] {
      def hmapA[R[_], R0[_], Ix, A[_]]
        (p: Phi[Ix], x: Product[F, G, R, Ix])
        (f: ((Phi[Ix], R[Ix]) => A[R0[Ix]]) forSome { type Ix })
        (implicit Aa: Applicative[A]) =
        (Lh.hmapA(p, x.fst)(f) |@| Rh.hmapA(p, x.snd)(f))(Product.apply _)
    }
  
  // implicit def TagHFunctor[Phi[_], F[_[_], _], Ix0]
  //   (implicit Hf: HFunctor[Phi, F]) = new HFunctor[Phi, Tag[F, Ix0]#Rec] {
  //     def hmapA[R[_], R0[_], Ix, A[_]]
  //       (p: Phi[Ix], x: Tag[F, Any]#Rec[R, Ix])
  //       (f: ((Phi[Ix], R[Ix]) => A[R0[Ix]]) forSome { type Ix })
  //       (implicit Aa: Applicative[A]) =
  //       Aa.ap(Hf.hmapA(p, x.unTag)(f))(Aa.point(Tag[F, Any].Rec.apply _))
  //   }

  implicit def DHFunctor[Phi[_], F[_], G[_[_], _]]
    (implicit Tf: Traverse[F], Hg: HFunctor[Phi, G]) =
    new HFunctor[Phi, DT[F, G]#Rec] {
      def hmapA[R[_], R0[_], Ix, A[_]]
        (p: Phi[Ix], x: D[F, G, R, Ix])
        (f: ((Phi[Ix], R[Ix]) => A[R0[Ix]]) forSome { type Ix })
        (implicit Aa: Applicative[A]) =
        Aa.ap(Tf.traverse(x.unD)(y => Hg.hmapA(p, y)(f)))(Aa.point(D(_)))
    }

  implicit def ConstructorHFunctor[Phi[_], Cp <: Constructor, F[_[_], _]]
    (implicit Hf: HFunctor[Phi, F]) = new HFunctor[Phi, CT[Cp, F]#Rec] {
    def hmapA[R[_], R0[_], Ix, A[_]]
      (p: Phi[Ix], x: C[Cp, F, R, Ix])
      (f: ((Phi[Ix], R[Ix]) => A[R0[Ix]]) forSome { type Ix })
      (implicit A: Applicative[A]) =
      A.ap(Hf.hmapA(p, x.unC)(f))(A.point(C(_)))
  }

  def hmap[Phi[_], R[_], R0[_], Ix, F[_[_], _]]
    (p: Phi[Ix], x: F[R, Ix])
    (f: (Phi[Ix], R[Ix]) => R0[Ix])
    (implicit Hf: HFunctor[Phi, F]):
      F[R0, Ix] =
    Hf.hmapA(p, x)((ix: Phi[Ix], x: R[Ix]) => I0(f(ix, x))).unI0
}

sealed trait Fold extends Base with HFunctor {

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
    Mm.bind(Hp.hmapA(p, Fp.from(p, x))((p: Phi[Ix], x: I0[Ix]) => foldM(p, x.unI0)(f)))(f(p, _))

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
        (y => Hp.hmapA(p, y)((p: Phi[Ix], x: R[Ix]) => Mm.lift((a: Ix) => I0(a))(unfoldM(p, x)(f)))))

  trait ParaAlgebra0[Phi[_], F[_[_], _], R[_]] {
    def apply[Ix](p: Phi[Ix], x: F[R, Ix], i: Ix): R[Ix]
  }
  type ParaAlgebra[Phi[_], R[_]] = ParaAlgebra0[Phi, PfResolver[Phi]#Pf, R]
  trait ParaAlgebraF0[Phi[_], F[_[_], _], G[_], R[_]] {
    def apply[Ix](p: Phi[Ix], x: F[R, Ix], i: Ix): G[R[Ix]]
  }
  type ParaAlgebraF[Phi[_], G[_], R[_]] =
    ParaAlgebraF0[Phi, PfResolver[Phi]#Pf, G, R]

  def para[Phi[_], Ix, R[_]](p: Phi[Ix], x: Ix)(f: ParaAlgebra[Phi, R])
    (implicit Fp: Fam[Phi], Hp: HFunctor[Phi, PfResolver[Phi]#Pf]):
      R[Ix] =
    f(p, hmap(p, Fp.from(p, x))((p, y) => para(p, y.unI0)(f)), x)

  def paraM[Phi[_], Ix, R[_], M[_]](p: Phi[Ix], x: Ix)(f: ParaAlgebraF[Phi, M, R])
    (implicit Fp: Fam[Phi], Hp: HFunctor[Phi, PfResolver[Phi]#Pf], Mm: Monad[M]):
      M[R[Ix]] =
    Mm.bind(Hp.hmapA(p, Fp.from(p, x))((p: Phi[Ix], y: I0[Ix]) => paraM(p, y.unI0)(f)))((r: PfResolver[Phi]#Pf[R, Ix]) => f(p, r, x))
}

sealed trait FoldK extends Base with HFunctor {

  trait Algebra0[Phi[_], F[_[_], _], R] {
    def apply[Ix](p: Phi[Ix], x: F[K0[R]#Rec, Ix]): R
  }
  type Algebra[Phi[_], R] = Algebra0[Phi, PfResolver[Phi]#Pf, R]

  trait AlgebraF0[Phi[_], F[_[_], _], G[_], R] {
    def apply[Ix](p: Phi[Ix], x: F[K0[R]#Rec, Ix]): G[R]
  }
  type AlgebraF[Phi[_], G[_], R] = AlgebraF0[Phi, PfResolver[Phi]#Pf, G, R]

  def fold[Phi[_], Ix, R](p: Phi[Ix], x: Ix)(f: Algebra[Phi, R])
    (implicit Fp: Fam[Phi], Hp: HFunctor [Phi, PfResolver[Phi]#Pf]):
      R =
    f(p, hmap(p, Fp.from(p, x))((p, x) => K0[R].Rec(fold(p, x.unI0)(f))))

  def foldM[Phi[_], Ix, R, M[_]](p: Phi[Any], x: R)(f: AlgebraF[Phi, M, R])
    (implicit Fp: Fam[Phi], Hp: HFunctor [Phi, PfResolver[Phi]#Pf], Mm: Monad[M]):
      M[R] =
    Mm.bind(Hp.hmapA(p, Fp.from(p, x))((p: Phi[_], x: I0[_]) => K0[R].Rec(foldM(p, x.unI0)(f)).liftM))(f(p, _))


}

sealed trait Show extends Base with HFunctor with FoldK {

  type ShowS = String => String

  def showParen(b: Boolean)(p: ShowS): ShowS =
    if (b) ((s: String) => '(' +: p(')' +: s)) else p

  trait HShow[Phi[_], F[_[_], _]] extends HFunctor[Phi, F] {
    val hShowsPrecAlg: Algebra0[Phi, F, List[Int => ShowS]]
  }

  implicit def ElHShow[Phi[_], Xi](implicit Ep: El[Phi, Xi]) =
    new HShow[Phi, I[Xi]#Rec] {
      val hShowsPrecAlg =
        (_: Phi[Xi], x: I[Xi]#Rec[K0[List[(Int, String) => String]]#Rec, Xi])
          => x.unI.unK0
    }

  implicit def KHShow[Phi[_], A](implicit Sa: scalaz.Show[A]) =
    new HShow[Phi, K[A]#Rec] {
      // FIXME: Should use something like `showsPrec(edence)` to handle infix
      val hShowsPrecAlg =
        (_: Phi[A], x: A) => List((n: Int) => (s: String) => Sa.show(x) ++ s)
    }

  implicit def UHShow[Phi[_]] = new HShow[Phi, U] {
    val hShowsPrecAlg = Nil
  }

  // implicit def SumHShow[Phi[_], F[_[_], _], G[_[_], _]]
  //   (implicit HSf: HShow[Phi, F], HSg: HShow[Phi, G]) =
  //   new HShow[Phi, Sum[F, G]#Rec] {
  //     val hShowsPrecAlg =
  //       (ix: Phi[Any],
  //         x: Sum[F, G]#Rec[K0[List[Int => ShowS]]#Rec, Any]) =>
  //     x match {
  //       case y: Sum[_, _]#L[_, _] => HSf.hShowsPrecAlg(ix, y.unL)
  //       case y: Sum[_, _]#R[_, _] => HSg.hShowsPrecAlg(ix, y.unR)
  //     }
  //   }

  implicit def ProductHShow[Phi[_], F[_[_], _], G[_[_], _]]
    (implicit HSf: HShow[Phi, F], HSg: HShow[Phi, G]) =
    new HShow[Phi, Sum[F, G]#Rec] {
      val hShowsPrecAlg =
        (ix: Phi[Any],
          x: Product[F, G]#Rec[K0[List[Int => ShowS]]#Rec, Any]) =>
      HSf.hShowsPrecAlg(ix, x.fst) ++ HSg.hShowsPrecAlg(ix, x.snd)
    }

  implicit def TagHShow[Phi[_], F[_[_], _], Ix](implicit HSf: HShow[Phi, F]) =
    new HShow[Phi, Tag[F, Ix]#Rec] {
      val hShowsPrecAlg =
        (ix: Phi[Ix],
          x: Tag[F, Ix]#Rec[K0[List[Int => ShowS]]#Rec, Ix]) =>
      HSf.hShowsPrecAlg(ix, x.unTag)
    }

  implicit def DHShow[Phi[_], F[_], G[_[_], _], Ix]
    (implicit Sf: Show1[F], Tf: Traverse[F], HSg: HShow[Phi, G]) =
    new HShow[Phi, D[F, G]#Rec] {
      val hShowsPrecAlg =
        (ix: Phi[Ix],
          x: D[F, G]#Rec[K0[List[Int => ShowS]]#Rec, Ix]) =>
      List((n: Int) => Sf.show1(n)(x.unD.map(HSg.hShowsPrecAlg(ix, _))))
    }

  // implicit def CHShow[Phi[_], Con <: Constructor, F[_[_], _], Ix]
  //   (implicit HSf: HShow[Phi, F]) =
  //   new HShow[Phi, C[Con, F]#Rec] {
  //     val hShowsPrecAlg =
  //       (ix: Phi[Ix],
  //         x: C[Con, F]#Rec[K0[List[Int => ShowS]]#Rec, Ix]) => {
  //         val fields = HSf.hShowsPrecAlg(ix, x)
  //         List(x.fixity match {
  //           case Prefix =>
  //             (n: Int) => showParen()()
  //           case Infix(a, p) =>
  //             (n: Int) => showParen(n > p)(spaces)
  //         })
  //       }
  //   }

  trait Show1[F[_]] {
    def show1(n: Int)(x: F[List[Int => ShowS]]): ShowS
  }

  // implicit val OptionShow1 = new Show1[Option] {
  //   def show(n: Int)(x: Option[List[Int => ShowS]]) =
  //     x match {
  //       case None    => (s: String) => "None" ++ s
  //       case Some(y) => showParen(n > 10)(spaces(((s: String) => "Some" ++ s) +: x.map(_(11))))
  //     }
  // }

  implicit val ListShow1 = new Show1[List] {
    def show1(n: Int)(x: List[List[Int => ShowS]])(implicit Ml: Monad[List]) =
      x match {
        case Nil => (s: String) => ("[]" ++ s)
        case xs  =>
          (s: String) => '[' +: commas(Ml.join(xs).map(_(0)))(']' +: s)
      }
  }

  def showsPrec[Phi[_], Ix](p: Phi[Ix], n: Int, x: Ix)
    (implicit Fp: Fam[Phi], HSp: HShow[Phi, PfResolver[Phi]#Pf]):
      ShowS =
    spaces(fold(p, x)(HSp.hShowsPrecAlg).map(_(n)))

  def show[Phi[_], Ix](ix: Phi[Ix], x: Ix)
    (implicit Fp: Fam[Phi], HSp: HShow [Phi, PfResolver[Phi]#Pf]):
      String =
    showsPrec[Phi, Ix](ix, 0, x)(Fp, HSp)("")

  def spaces(x: List[ShowS]): ShowS = intersperse(" ", x)
  def commas(x: List[ShowS]): ShowS = intersperse(", ", x)

  def intersperse(s: String, x: List[ShowS]): ShowS = x match {
    case Nil      => (s: String) => s
    case x :: Nil => x
    case x :: xs  => x compose ((str: String) => s ++ str) compose spaces(xs)
  }
}

object mutualrec extends HFix
