package slamdata.engine.analysis

import mutualrec._

import scalaz.{Tag => ZTag, _}
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

  class PfAst[A] extends PfResolver[Ast[A]#Dummy] {
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
  implicit def PfAst[A]() = new PfAst[A]

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
      phi match {
      case _: Ast[_]#DummyExpr =>
          index match {
            case Const(i) => TagF(LF(CF(ConstC(), KF(i))), index): Tag[LefT[CT[ConstC, KT[Int]#Rec]#Rec]#Rec, Expr[A], I0, Ix]
              ???
        // case Const(i)  => LF(TagF(LF(         CF(ConstC(), KF[Int, I0[Ix]](i))),                index))
        // case Add(l, r) => LF(TagF(RF(LF(      CF(AddC(),   ProductF(IF(I0(l)), IF(I0(r)))))),   index))
        // case Mul(l, r) => LF(TagF(RF(RF(LF(   CF(MulC(),   ProductF(IF(I0(l)), IF(I0(r))))))),  index))
        // case Var(v)    => LF(TagF(RF(RF(RF(LF(CF(VarC(),   KF(v)))))),                          index))
        // case Let(d, e) => LF(TagF(RF(RF(RF(RF(CF(LetC(),   ProductF(IF(I0(d)), IF(I0(e)))))))), index))
        // // // }
        // // // case _: Ast[_]#DummyDecl => index {
        // case Assign(v, e) => RF(TagF(LF(   CF(AssignC(), ProductF(IF(I0(v)), IF(I0(e))))),           index))
        // case Seq(ds)      => RF(TagF(RF(LF(CF(SeqC(),    DF[List[I[A, I0, Ix]]](ds.map((s: Decl[A]) => IF(I0(s))))))), index))
        // case None         => RF(TagF(RF(RF(CF(NoneC(),   UF()))),                                    index))
          // }
          // case _: Ast[_]#DummyVar => index match {
          //   case Var(v)    => p.SumR(p.SumR(p.TagX(p.SumL(p.CX(p.KX(v))))))
          }
      }
    }

    def to[Ix](phi: Ast[A]#Dummy[Ix], pf: PfResolver[Ast[A]#Dummy]#Pf[I0, Ix]):
        Ix =
      pf match {
        case Lef(Tag(Lef(C(K(i))))) => Const(i)
      }
  }
}
