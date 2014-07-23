package slamdata.engine.analysis

import mutualrec._

import scalaz._
import Scalaz._

// Small use case for mutualrec, just to make sure things compile

object AST {
  sealed trait Dummy[+A]

  sealed trait Expr[+A] extends Dummy[A]
  case class Const(c: Int) extends Expr[Nothing]
  case class Add[A](l: Expr[A], r: Expr[A]) extends Expr[A]
  case class Mul[A](l: Expr[A], r: Expr[A]) extends Expr[A]
  case class Var[A](v: A) extends Expr[A]
  case class Let[A](d: Decl[A], e: Expr[A]) extends Expr[A]

  sealed trait Decl[+A] extends Dummy[A]
  case class Assign[A](v: Var[A], e: Expr[A]) extends Decl[A]
  case class Seq[A](l: List[Decl[A]]) extends Decl[A]
  case object None extends Decl[Nothing]

  case class Ast[Param]() {
    sealed trait Dummy[+Index]
    case class DummyExpr() extends Dummy[Expr[Param]]
    case class DummyDecl() extends Dummy[Decl[Param]]
    case class DummyVar() extends Dummy[Var[Param]]
  }
  type DummyAst[Param, Index] = Ast[Param]#Dummy[Index]

  case class ConstC()  extends Constructor { val name = "Const" }
  case class AddC()    extends Constructor { val name = "Add" }
  case class MulC()    extends Constructor { val name = "Mul" }
  case class VarC()    extends Constructor { val name = "Var" }
  case class LetC()    extends Constructor { val name = "Let" }

  case class AssignC() extends Constructor { val name = "Assign" }
  case class SeqC()    extends Constructor { val name = "Seq" }
  case class NoneC()   extends Constructor { val name = "None" }

  class StupidScalaHack[A] extends PfResolver[Ast[A]#Dummy] {
    type Pf[R[_], Ix] =
      SumT[
        TagT[
          SumT[CT[ConstC, KT[Int]#Rec]#Rec,
            SumT[CT[AddC, ProductT[IT[Expr[A]]#Rec, IT[Expr[A]]#Rec]#Rec]#Rec,
              SumT[CT[MulC, ProductT[IT[Expr[A]]#Rec, IT[Expr[A]]#Rec]#Rec]#Rec,
                SumT[CT[VarC, KT[A]#Rec]#Rec,
                  CT[LetC, ProductT[IT[Decl[A]]#Rec, IT[Expr[A]]#Rec]#Rec]#Rec]#Rec]#Rec]#Rec]#Rec,
          Expr[A]]#Rec,
        TagT[
          SumT[CT[AssignC, ProductT[IT[Var[A]]#Rec, IT[Expr[A]]#Rec]#Rec]#Rec,
            SumT[CT[SeqC, DT[List, IT[Decl[A]]#Rec]#Rec]#Rec,
              CT[NoneC, U]#Rec]#Rec]#Rec,
          Decl[A]]#Rec
      ]#Rec[R, Ix]
  }
  implicit def PfAst[A]() = new StupidScalaHack[A]

  implicit def ExprEl[A]() = new El[Ast[A]#Dummy, Expr[A]] {
    val AA = Ast[A]
    val proof = AA.DummyExpr()
  }
  implicit def DeclEl[A]() = new El[Ast[A]#Dummy, Decl[A]] {
    val AA = Ast[A]
    val proof = AA.DummyDecl()
  }
  implicit def VarEl[A]() = new El[Ast[A]#Dummy, Var[A]] {
    val AA = Ast[A]
    val proof = AA.DummyVar()
  }

  implicit def DummyFam[A]() = new Fam[Ast[A]#Dummy] {
    def from[Ix](phi: DummyAst[A, Ix], index: Ix) = {
      val p = new PMC[Ix]

      // phi match {
      // case _: Ast[_]#DummyExpr =>
      index match {
        case Const(i)  => LQ[TagT[SumT[CT[ConstC, KT[Int]#Rec]#Rec, Nothing]#Rec, Expr[A]]#Rec, I0, Ix](TagQ[SumT[CT[ConstC, KT[Int]#Rec]#Rec, Nothing]#Rec, Expr[A], I0, Ix] (LQ[CT[ConstC, KT[Int]#Rec]#Rec, I0, Ix](                     CQ[ConstC, KT[Int]#Rec, I0, Ix](KQ[Int, I0, Ix](i)))))
        case Add(l, r) => p.SumL(p.TagX(p.SumR(p.SumL(              p.CX(p.ProductX(p.IX(I0(l)), p.IX(I0(r))))))))
        case Mul(l, r) => p.SumL(p.TagX(p.SumR(p.SumR(p.SumL(       p.CX(p.ProductX(p.IX(I0(l)), p.IX(I0(r)))))))))
        case Var(v)    => p.SumL(p.TagX(p.SumR(p.SumR(p.SumR(p.SumL(p.CX(p.KX(v))))))))
        case Let(d, e) => p.SumL(p.TagX(p.SumR(p.SumR(p.SumR(p.SumR(p.CX(p.ProductX(p.IX(I0(d)), p.IX(I0(e))))))))))
        // }
        // case _: Ast[_]#DummyDecl => index {
        case Assign(v, e) => p.SumR(p.SumL(p.TagX(p.SumL(       p.CX(p.ProductX(p.IX(I0(v)), p.IX(I0(e))))))))
        case Seq(ds)      => p.SumR(p.SumL(p.TagX(p.SumR(p.SumL(p.CX(p.DX(ds.map((s: Decl[Any]) => p.IX(I0(s))))))))))
        case None         => p.SumR(p.SumL(p.TagX(p.SumR(p.SumR(p.CX(p.UX()))))))
          // }
          // case _: Ast[_]#DummyVar => index match {
          //   case Var(v)    => p.SumR(p.SumR(p.TagX(p.SumL(p.CX(p.KX(v))))))
          // }
      }
    }

    def to[Ix](phi: Ast[A]#Dummy[Ix], pf: PfResolver[Ast[A]#Dummy]#Pf[I0, Ix]):
        Ix =
      pf match {
        case LQ(TagQ(LQ(CQ(i)))) => Const(i)
      }
  }
}
