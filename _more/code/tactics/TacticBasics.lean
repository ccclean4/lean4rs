-- Tactics: 證明策略
-- 展示常見 tactic 的使用模式

-- basic
theorem basic_refl : ∀ (n : Nat), n = n := by
  intros n
  rfl

theorem basic_exact : 1 + 1 = 2 := by
  exact Eq.refl 2

-- apply
theorem apply_example (p q r : Prop) (hp : p) (h : p → q) (h2 : q → r) : r := by
  apply h2
  apply h
  exact hp

-- rewrite
theorem rw_example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]

theorem rw_symm (a b : Nat) (h : a = b) : b = a := by
  rw [← h]

-- simp
@[simp]
theorem simp_fact (n : Nat) : n + 0 = n := by
  simp

theorem simp_example : ∀ n : Nat, n + 0 + 0 = n := by
  intros n
  simp

-- split (用於 if 或 match)
theorem split_example (n : Nat) : (if n > 0 then n else 0) ≥ 0 := by
  cases h : n > 0 with
  | true => simp [h]
  | false => simp [h]

-- constructor (用於 And, Or, Eq)
theorem constructor_and (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor <;> assumption

theorem constructor_or_left (p q : Prop) (hp : p) : p ∨ q := by
  left
  assumption

theorem constructor_or_right (p q : Prop) (hq : q) : p ∨ q := by
  right
  assumption

-- use (用於 exists)
theorem use_example : ∃ n : Nat, n > 5 := by
  use 10

-- cases
theorem cases_example (n : Nat) : n = 0 ∨ n > 0 := by
  cases n with
  | zero => left; rfl
  | succ n => right; exact Nat.succ_pos n

-- rcases (解構模式)
theorem rcases_example {p q : Prop} (h : p ∧ q) : q ∧ p := by
  rcases h with ⟨hp, hq⟩
  constructor <;> assumption

-- have 與 let
theorem have_example (n : Nat) : n + 0 = n := by
  have h : n + 0 = n := Nat.add_zero n
  exact h

theorem let_example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  let ha := Eq.symm h
  rw [ha]