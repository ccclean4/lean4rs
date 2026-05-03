-- Logic: 自然演繹
-- 展示自然演繹系統的推理規則

inductive Proof : Type
  | hyp (n : Nat) : Proof
  | trueIntro : Proof
  | falseElim : Proof → Proof
  | andIntro : Proof → Proof → Proof
  | andElimLeft : Proof → Proof
  | andElimRight : Proof → Proof
  | orIntroLeft : Proof → Nat → Proof
  | orIntroRight : Proof → Nat → Proof
  | orElim : Proof → Proof → Proof → Proof
  | impliesIntro : Nat → Proof → Proof
  | impliesElim : Proof → Proof → Proof
  | notIntro : Nat → Proof → Proof
  | notElim : Proof → Proof → Proof
  | iffIntro : Nat → Proof → Proof → Proof
  | iffElimLeft : Proof → Proof
  | iffElimRight : Proof → Proof

structure Context := (hyps : List (Nat × Prop))

def Context.extend (Γ : Context) (n : Nat) (p : Prop) : Context := by
  sorry

def proves (Γ : Context) (p : Prop) (π : Proof) : Prop := by
  sorry

-- 自然演繹規則
namespace Rules

theorem andIntroRule {p q : Prop} (hp : proves Γ p) (hq : proves Γ q) :
  proves Γ (Prop.and p q) := by
  apply Proof.andIntro <;> assumption

theorem andElimLeftRule {p q : Prop} (h : proves Γ (Prop.and p q)) :
  proves Γ p := by
  apply Proof.andElimLeft at h
  assumption

theorem andElimRightRule {p q : Prop} (h : proves Γ (Prop.and p q)) :
  proves Γ q := by
  apply Proof.andElimRight at h
  assumption

theorem orIntroLeftRule {p q : Prop} (hp : proves Γ p) :
  proves Γ (Prop.or p q) := by
  apply Proof.orIntroLeft hp

theorem orIntroRightRule {p q : Prop} (hq : proves Γ q) :
  proves Γ (Prop.or p q) := by
  apply Proof.orIntroRight hq

theorem impliesIntroRule {p q : Prop} (n : Nat) (h : proves (Γ.extend n p) q) :
  proves Γ (Prop.implies p q) := by
  apply Proof.impliesIntro n at h
  assumption

theorem impliesElimRule {p q : Prop} (hp : proves Γ p) (h : proves Γ (Prop.implies p q)) :
  proves Γ q := by
  apply Proof.impliesElim at h
  exact h hp

theorem falseElimRule {p : Prop} (h : proves Γ Prop.false) :
  proves Γ p := by
  apply Proof.falseElim at h
  assumption

theorem notIntroRule {p : Prop} (n : Nat) (h : proves (Γ.extend n p) Prop.false) :
  proves Γ (Prop.not p) := by
  apply Proof.notIntro n at h
  assumption

theorem notElimRule {p : Prop} (hn : proves Γ (Prop.not p)) (hp : proves Γ p) :
  proves Γ Prop.false := by
  apply Proof.notElim at hn
  exact hn hp

end Rules

-- 常用定理
theorem modusPonens {p q : Prop} (h1 : proves Γ p) (h2 : proves Γ (Prop.implies p q)) :
  proves Γ q := by
  apply Rules.impliesElimRule h1 h2

theorem doubleNegation {p : Prop} : proves Γ (Prop.not (Prop.not p)) → proves Γ p := by
  intros h
  apply Rules.notElimRule
  . apply Rules.notIntroRule
    intro n
    apply Rules.notElimRule
    . exact h
    . apply Rules.impliesIntroRule n
      apply Rules.falseElimRule
      sorry
  . sorry

end