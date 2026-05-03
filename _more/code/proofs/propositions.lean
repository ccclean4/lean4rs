-- Proofs: 基本命題邏輯
-- 展示 Lean 4 中的命題邏輯證明

theorem my_and_comm {p q : Prop} : p ∧ q → q ∧ p := fun h =>
  have hp : p := h.left
  have hq : q := h.right
  And.intro hq hp

theorem my_or_comm {p q : Prop} : p ∨ q → q ∨ p := fun h =>
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)

theorem implies_trans {p q r : Prop} (h1 : p → q) (h2 : q → r) : p → r := fun hp =>
  have hq : q := h1 hp
  h2 hq

theorem contrapositive {p q : Prop} : (p → q) → (¬q → ¬p) := fun h hnq hp =>
  have hq : q := h hp
  hnq hq

theorem de_morgan_1 {p q : Prop} : ¬(p ∨ q) → ¬p ∧ ¬q := fun h =>
  have hnp : ¬p := fun hp => h (Or.inl hp)
  have hnq : ¬q := fun hq => h (Or.inr hq)
  And.intro hnp hnq

theorem de_morgan_2 {p q : Prop} : ¬p ∧ ¬q → ¬(p ∨ q) := fun h hpq =>
  Or.elim hpq h.left h.right

#check my_and_comm
#check my_or_comm
#check implies_trans
#check contrapositive
#check de_morgan_1
#check de_morgan_2