package slamdata.engine.analysis

import mutualrec._

import scalaz.{Tag => ZTag, _}
import Scalaz._
import Leibniz._

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
    case class DummyVar()  extends Dummy[Var[Param]]
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
    // FIXME: The `Any`s in here should be `A`s.
    // FIXME: The TagT Ix should be more specific
    type Pf[R[_], Ix] =
      Sum[
        TagT[
          SumT[CT[ConstC, KT[Int]#Rec]#Rec,
            SumT[CT[AddC, ProductT[IT[Expr[Any]]#Rec, IT[Expr[Any]]#Rec]#Rec]#Rec,
              SumT[CT[MulC, ProductT[IT[Expr[Any]]#Rec, IT[Expr[Any]]#Rec]#Rec]#Rec,
                SumT[CT[VarC, KT[Any]#Rec]#Rec,
                  CT[LetC, ProductT[IT[Decl[Any]]#Rec, IT[Expr[Any]]#Rec]#Rec]#Rec]#Rec]#Rec]#Rec]#Rec,
          Ix // Expr[A]
        ]#Rec,
        SumT[
          TagT[
            SumT[CT[AssignC, ProductT[IT[Var[Any]]#Rec, IT[Expr[Any]]#Rec]#Rec]#Rec,
              SumT[CT[SeqC, DT[List, IT[Decl[Any]]#Rec]#Rec]#Rec,
                CT[NoneC, U]#Rec]#Rec]#Rec,
            Ix // Decl[A]
          ]#Rec,
          TagT[
            CT[VarC, KT[Any]#Rec]#Rec,
            Ix // Var[A]
          ]#Rec]#Rec,
      R, Ix]
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
    def from[Ix](phi: DummyAst[A, Ix], index: Ix): PfAst[A]#Pf[I0, Ix] = {
      phi match {
        case _: Ast[_]#DummyExpr => index match {
          case Const(i)  => LefT(TagT(LefT(                   CT(ConstC(), KT[Int, I0[Ix]](i))),                                                      index))
          case Add(l, r) => LefT(TagT(RighT(LefT(             CT(AddC(),   ProductT(IT[I0[Expr[Any]], Ix](I0(l)), IT[I0[Expr[Any]], Ix](I0(r)))))),   index))
          case Mul(l, r) => LefT(TagT(RighT(RighT(LefT(       CT(MulC(),   ProductT(IT[I0[Expr[Any]], Ix](I0(l)), IT[I0[Expr[Any]], Ix](I0(r))))))),  index))
          case Var(v)    => LefT(TagT(RighT(RighT(RighT(LefT( CT(VarC(),   KT[Any, I0[Ix]](v)))))),                                                   index))
          case Let(d, e) => LefT(TagT(RighT(RighT(RighT(RighT(CT(LetC(),   ProductT(IT[I0[Decl[Any]], Ix](I0(d)), IT[I0[Expr[Any]], Ix](I0(e)))))))), index))
        }
        case _: Ast[_]#DummyDecl => index match {
          case Assign(v, e) => RighT(LefT(TagT(LefT(       CT(AssignC(), ProductT(IT[I0[Var[Any]], Ix](I0(v)), IT[I0[Expr[Any]], Ix](I0(e))))), index)))
          case Seq(ds)      => RighT(LefT(TagT(RighT(LefT( CT(SeqC(),    DT(ds.map(s => IT[I0[Decl[Any]], Ix](I0(s))))))),                      index)))
          case None         => RighT(LefT(TagT(RighT(RighT(CT(NoneC(),   UT[I0[Ix]]()))),                                                       index)))
        }
        case _: Ast[_]#DummyVar => index match {
          case Var(v) => RighT(RighT(TagT(CT(VarC(), KT[Any, I0[Ix]](v)), index)))
        }
      }
    }

    def to[Ix](phi: Ast[A]#Dummy[Ix], pf: PfAst[A]#Pf[I0, Ix]):
        Ix =
      pf match {
        case Lef(Tag(Lef(C(K(i))))) => Const(i)
      }
  }

  implicit def DummyEqS[A]() = new EqS[Ast[A]#Dummy] {
    def eqS[Ix, Ix0](a: DummyAst[A, Ix], b: DummyAst[A, Ix0]) = (a, b) match {
      case (_: Ast[_]#DummyExpr, _: Ast[_]#DummyExpr) =>
        Some(force[⊥, ⊤, Ix, Ix0])
      case (_: Ast[_]#DummyDecl, _: Ast[_]#DummyDecl) =>
        Some(force[⊥, ⊤, Ix, Ix0])
      case (_: Ast[_]#DummyVar,  _: Ast[_]#DummyVar)  =>
        Some(force[⊥, ⊤, Ix, Ix0])
      case _                                          =>
        none
    }
  }
}
