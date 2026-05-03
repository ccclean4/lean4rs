-- Logic: 自然演繹
-- 展示自然演繹系統的證明

inductive Proof : Type
  | assume : Prop → Proof
  | andIntro : Proof → Proof → Proof
  | andElimL : Proof → Proof
  | andElimR : Proof → Proof
  | orIntroL : Proof → Prop → Proof
  | orIntroR : Prop → Proof → Proof
  | orElim : Proof → Proof → Proof → Proof
  | impliesIntro : Proof → Proof
  | impliesElim : Proof → Proof → Proof
  | notIntro : Proof → Proof
  | notElim : Proof → Proof → Proof
  | falseElim : Proof → Proof

inductive Prop : Type
  | var : String → Prop
  | not : Prop → Prop
  | and : Prop → Prop → Prop
  | or : Prop → Prop → Prop
  | implies : Prop → Prop → Prop
  | false : Prop

namespace Prop

theorem andIntro {p q : Prop} (hp : Prop) (hq : Prop) : Prop :=
  and hp hq

theorem andElimL {p q : Prop} (h : Prop) : Prop :=
  match h with
  | and hp _ => hp

theorem orIntroL (p q : Prop) : Prop :=
  or p q

theorem orIntroR (p q : Prop) : Prop :=
  or p q

theorem impliesIntro (p q : Prop) : Prop :=
  implies p q

theorem notIntro (p : Prop) : Prop :=
  not p

theorem notElim (p : Prop) : Prop :=
  implies (not p) p

theorem falseElim : Prop :=
  false

example (p q : Prop) : Prop :=
  implies (and p q) p

example (p : Prop) : Prop :=
  implies p (or p p)

example (p q : Prop) : Prop :=
  implies (not (or p q)) (and (not p) (not q))

end Prop

#check Prop.andIntro
#check Prop.andElimL