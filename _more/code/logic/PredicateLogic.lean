-- Logic: 謂詞邏輯
-- 展示一階謂詞邏輯的基本概念

inductive Term : Type
  | var : String → Term
  | const : String → Term
  | app : String → List Term → Term

inductive Formula : Type
  | eq : Term → Term → Formula
  | rel : String → List Term → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | implies : Formula → Formula → Formula
  | forall : String → Formula → Formula
  | exists : String → Formula → Formula
  | true : Formula
  | false : Formula

namespace Formula

def freeVars : Formula → List String
  | eq t1 t2 => []
  | rel _ args => []
  | not f => freeVars f
  | and f1 f2 => freeVars f1 ++ freeVars f2
  | or f1 f2 => freeVars f1 ++ freeVars f2
  | implies f1 f2 => freeVars f1 ++ freeVars f2
  | forall x f => freeVars f |>.filter (x != ·)
  | exists x f => freeVars f |>.filter (x != ·)
  | true => []
  | false => []

def subst (x : String) (t : Term) : Formula → Formula
  | eq t1 t2 => eq t1 t2
  | rel r args => rel r args
  | not f => not (subst x t f)
  | and f1 f2 => and (subst x t f1) (subst x t f2)
  | or f1 f2 => or (subst x t f1) (subst x t f2)
  | implies f1 f2 => implies (subst x t f1) (subst x t f2)
  | forall y f => if y = x then forall y f else forall y (subst x t f)
  | exists y f => if y = x then exists y f else exists y (subst x t f)
  | true => true
  | false => false

end Formula

#check Formula.forall "x" (Formula.rel "P" [Term.var "x"])
#check Formula.exists "x" (Formula.eq (Term.var "x") (Term.const "a"))

#eval Formula.freeVars (Formula.forall "x" (Formula.rel "P" [Term.var "x"]))
#eval Formula.freeVars (Formula.rel "P" [Term.var "x", Term.var "y"])