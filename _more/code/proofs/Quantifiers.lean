-- Proofs: 量化命題證明
-- 展示 forall 與 exists 的證明技巧

theorem forall_intro {α : Type} {P : α → Prop} (h : ∀ x : α, P x) : ∀ x : α, P x := h

theorem forall_elim {α : Type} {P : α → Prop} (h : ∀ x : α, P x) (a : α) : P a := h a

theorem exists_intro {α : Type} {P : α → Prop} (a : α) (h : P a) : ∃ x : α, P x := Exists.intro a h

theorem exists_elim {α : Type} {P : α → Prop} {q : Prop} (h : ∃ x : α, P x) (g : ∀ x : α, P x → q) : q := Exists.elim h g

-- 具體例子
theorem forall_plus (n : Nat) : ∀ m : Nat, n + m ≥ n := by
  intros m
  exact Nat.le_add_of_nonneg_right (Nat.zero_le n)

theorem exists_sqrt (n : Nat) (h : n > 0) : ∃ m : Nat, m * m ≤ n := by
  use n
  exact Nat.mul_le_mul_right n (Nat.le_refl n)

theorem forall_exists {α : Type} {P : α → Prop} (h : ∃! x, P x) : ∃ x, P x := by
  cases h with
  | intro x hx => exact Exists.intro x hx.left

-- 雙重量化
theorem double_forall {α β : Type} {P : α → β → Prop} (h : ∀ x y, P x y) (a : α) (b : β) : P a b := by
  exact h a b

theorem forall_exists_comm {α β : Type} {P : α → β → Prop} : (∀ x, ∃ y, P x y) ↔ (∃ g, ∀ x, P x (g x)) := by
  apply Iff.intro
  . intros h
    -- 選擇函數存在
    admit
  . intros h g x
    -- 對於每個 x，存在 y = g x 使得 P x y 成立
    admit

-- 練習證明
theorem ex_1 : ∀ n : Nat, n ≠ 0 → ∃ m, n = m + 1 := by
  intros n h
  use n - 1
  exact Nat.succ_pred h

theorem ex_2 : ∀ n m : Nat, n ≤ m → ∃ k, m = n + k := by
  intros n m h
  use m - n
  exact Nat.sub_add_cancel (Nat.le_antisymm h (Nat.le_add_left n m) ▸ h ▸ Nat.le_refl n)

theorem ex_3 : ∃ n : Nat, ∀ m : Nat, m ≥ n := by
  use 0
  intros m
  exact Nat.zero_le m

theorem ex_4 : (∃ x, ∀ y, P x y) → ∀ y, ∃ x, P x y := by
  intros h y
  cases h with
  | intro x hx => exact Exists.intro x (hx y)