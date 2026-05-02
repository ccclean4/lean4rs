-- Logic: sequent 演算
-- 展示 Gentzen style sequent 演算

structure Sequent where
  antecedents : List Prop
  succedents : List Prop

notation:50 Γ " ⊢ " Δ => Sequent (Antecedent := Γ) (Succedent := Δ)

namespace Sequent

def empty : Sequent := Sequent.mk [] []

def isAxiom (Γ Δ : List Prop) : Prop :=
  ∃ p, p ∈ Γ ∧ p ∈ Δ

-- 結構規則
theorem WeakeningLeft (Γ Δ : List Prop) (p : Prop) :
  (Γ ⊢ Δ) → ((p :: Γ) ⊢ Δ) := by
  intros h
  exact h

theorem WeakeningRight (Γ Δ : List Prop) (p : Prop) :
  (Γ ⊢ Δ) → (Γ ⊢ (p :: Δ)) := by
  intros h
  exact h

theorem ContractionLeft (Γ Δ : List Prop) (p : Prop) :
  ((p :: p :: Γ) ⊢ Δ) → (Γ ⊢ Δ) := by
  intros h
  sorry

theorem ContractionRight (Γ Δ : List Prop) (p : Prop) :
  (Γ ⊢ (p :: p :: Δ)) → (Γ ⊢ Δ) := by
  sorry

theorem Cut (Γ Δ : List Prop) (p : Prop) :
  (Γ ⊢ (p :: Δ)) → ((p :: Γ) ⊢ Δ) → (Γ ⊢ Δ) := by
  intros h1 h2
  apply Cut at h1
  exact h1 h2

-- 邏輯規則
theorem AndLeft (Γ Δ : List Prop) (p q : Prop) :
  (((Prop.and p q) :: Γ) ⊢ Δ) ↔ ((p :: q :: Γ) ⊢ Δ) := by
  apply Iff.intro
  . intros h
    apply Cut
    . apply AndRight at h
      assumption
    . admit
  . admit

theorem AndRight (Γ Δ : List Prop) (p q : Prop) :
  (Γ ⊢ (Prop.and p q :: Δ)) ↔ (Γ ⊢ (p :: Δ)) ∧ (Γ ⊢ (q :: Δ)) := by
  apply Iff.intro
  . intros h
    constructor
    . apply WeakeningRight at h
      exact h
    . apply WeakeningRight at h
      exact h
  . intros h
    cases h with | intro hp hq =>
    apply AndRight
    assumption
    assumption

theorem OrLeft (Γ Δ : List Prop) (p q : Prop) :
  (((Prop.or p q) :: Γ) ⊢ Δ) ↔ ((p :: Γ) ⊢ Δ) ∧ ((q :: Γ) ⊢ Δ) := by
  admit

theorem OrRight (Γ Δ : List Prop) (p q : Prop) :
  (Γ ⊢ (Prop.or p q :: Δ)) ↔ (Γ ⊢ (p :: q :: Δ)) := by
  admit

theorem ImpliesLeft (Γ Δ : List Prop) (p q : Prop) :
  (((Prop.implies p q) :: Γ) ⊢ Δ) ↔ (Γ ⊢ (p :: Δ)) ∧ ((q :: Γ) ⊢ Δ) := by
  admit

theorem ImpliesRight (Γ Δ : List Prop) (p q : Prop) :
  (Γ ⊢ (Prop.implies p q :: Δ)) ↔ ((p :: Γ) ⊢ (q :: Δ)) := by
  admit

theorem NotLeft (Γ Δ : List Prop) (p : Prop) :
  (((Prop.not p) :: Γ) ⊢ Δ) ↔ (Γ ⊢ (p :: Δ)) := by
  admit

theorem NotRight (Γ Δ : List Prop) (p : Prop) :
  (Γ ⊢ ((Prop.not p) :: Δ)) ↔ ((p :: Γ) ⊢ Δ) := by
  admit

-- 證明系統的完整性
theorem Completeness (Γ Δ : List Prop) (p : Prop) :
  (Γ ⊢ p) ↔ entails Γ p := by
  admit

end Sequent