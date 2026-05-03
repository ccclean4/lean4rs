-- Tactics: 結構化證明
-- 展示 calc, show, have, let 的使用

theorem calc_example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  calc
    a = b := h1
    _ = c := h2

theorem calc_chain (a b c d : Nat) (h1 : a = b) (h2 : b < c) (h3 : c ≤ d) : a < d := by
  calc
    a = b := h1
    _ < c := h2
    _ ≤ d := h3

theorem show_example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  show p from hp
  show q from hq

theorem show_example2 (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

theorem have_show (n : Nat) (h : n > 0) : n * n > 0 := by
  have hn : n ≥ 1 := Nat.lt_of_succ_le (Nat.succ_le_of_lt h)
  calc
    n * n ≥ 1 * n := Nat.mul_le_mul hn (Nat.le_refl n)
    _ = n := Nat.one_mul n
    _ > 0 := h

theorem let_proof (a b : Nat) : a + b = b + a := by
  let sum := a + b
  show sum = b + a from Nat.add_comm a b

-- 嵌套 have
theorem nested_have (n : Nat) : n * 1 = n := by
  have h1 : n * 1 = n * 1 := rfl
  have h2 : n * 1 = n := Nat.mul_one n
  have h3 : n = n := rfl
  exact h2

-- 結構化遞迴證明
theorem list_length_append (as bs : List Nat) : (as ++ bs).length = as.length + bs.length := by
  induction as with
  | nil => simp [List.append]
  | cons a as ih =>
    simp [List.append, List.length]
    calc
      (a :: as ++ bs).length = (as ++ bs).length + 1 := rfl
        _ = as.length + bs.length + 1 := by rw [ih]
        _ = as.length + 1 + bs.length := by rw [Nat.add_assoc]
        _ = (a :: as).length + bs.length := rfl

-- 逆向思考
theorem reverse_thinking (p q : Prop) : (p → q) → (¬q → ¬p) := by
  intros h hnq hp
  have hq : q := h hp
  exact hnq hq