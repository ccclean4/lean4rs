-- 03_logic.lean - 邏輯運算證明

def main : IO Unit := IO.println "=== 數學證明範例：邏輯運算 ==="

theorem my_and_comm (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  exact And.intro h.right h.left

theorem my_or_comm (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h

theorem imp_trans (p q r : Prop) : (p → q) → (q → r) → (p → r) := by
  intros hpq hqr hp
  exact hqr (hpq hp)

#eval main
#eval IO.println s!"my_and_comm True False : True ∧ False → False ∧ True"
#eval IO.println s!"my_or_comm True False : True ∨ False → False ∨ True"