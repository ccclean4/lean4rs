-- Logic: 命題邏輯
-- 展示命題邏輯的基本概念

inductive Prop : Type
  | var : String → Prop
  | not : Prop → Prop
  | and : Prop → Prop → Prop
  | or : Prop → Prop → Prop
  | implies : Prop → Prop → Prop
  | true : Prop
  | false : Prop

namespace Prop

def eval (v : String → Bool) : Prop → Bool
  | var x => v x
  | not p => not (eval v p)
  | and p q => and (eval v p) (eval v q)
  | or p q => or (eval v p) (eval v q)
  | implies p q => (eval v p) → (eval v q)
  | true => true
  | false => false

def neg : Prop → Prop
  | not p => p
  | p => not p

def conj (p q : Prop) : Prop :=
  and p q

def disj (p q : Prop) : Prop :=
  or p q

def impl (p q : Prop) : Prop :=
  implies p q

end Prop

#check Prop.var "p"
#check Prop.not (Prop.var "p")
#check Prop.and (Prop.var "p") (Prop.var "q")

#eval Prop.eval (fun _ => false) Prop.true
#eval Prop.eval (fun _ => false) Prop.false
#eval Prop.eval (fun x => if x = "p" then true else false) (Prop.var "p")