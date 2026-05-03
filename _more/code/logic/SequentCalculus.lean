-- Logic:  sequent 運算
-- 展示 sequent 運算的基本概念

inductive Prop : Type
  | var : String → Prop
  | not : Prop → Prop
  | and : Prop → Prop → Prop
  | or : Prop → Prop → Prop
  | implies : Prop → Prop → Prop
  | true : Prop
  | false : Prop

structure Sequent where
  antecedent : List Prop
  consequent : Prop

namespace Sequent

def fromList (ant : List Prop) (suc : Prop) : Sequent :=
  ⟨ant, suc⟩

def init (p : Prop) : Sequent :=
  ⟨[p], p⟩

def cut (s1 s2 : Sequent) : Sequent :=
  ⟨s1.antecedent ++ s2.antecedent, s2.consequent⟩

def andLeft (s : Sequent) (p q : Prop) : Sequent :=
  ⟨p :: q :: s.antecedent, s.consequent⟩

def andRight (s : Sequent) (p q : Prop) : Sequent :=
  ⟨s.antecedent, and p q⟩

def orLeft (s : Sequent) (p q : Prop) : Sequent :=
  ⟨p :: s.antecedent, s.consequent⟩

def orRight (s : Sequent) (p q : Prop) : Sequent :=
  ⟨s.antecedent, or p q⟩

def impliesLeft (s : Sequent) (p q : Prop) : Sequent :=
  ⟨s.consequent :: s.antecedent, q⟩

def impliesRight (s : Sequent) (p q : Prop) : Sequent :=
  ⟨s.antecedent, implies p q⟩

def notLeft (s : Sequent) (p : Prop) : Sequent :=
  ⟨s.antecedent, not p⟩

def notRight (s : Sequent) (p : Prop) : Sequent :=
  ⟨p :: s.antecedent, s.consequent⟩

def weakLeft (s : Sequent) (p : Prop) : Sequent :=
  ⟨p :: s.antecedent, s.consequent⟩

def contractLeft (s : Sequent) : Sequent :=
  match s.antecedent with
  | [] => s
  | _ :: rest => ⟨rest ++ rest, s.consequent⟩

end Sequent

#check Sequent.init (Prop.var "p")
#check Sequent.andLeft (Sequent.init (Prop.var "p")) (Prop.var "q") (Prop.var "r")
#check Sequent.orRight (Sequent.init (Prop.var "p")) (Prop.var "q") (Prop.var "r")

example : Sequent :=
  Sequent.init (Prop.and (Prop.var "p") (Prop.var "q"))

example (p q : Prop) : Sequent :=
  Sequent.fromList [p, q] (Prop.and p q)