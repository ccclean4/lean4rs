# 12 - 結構化證明

## calc（計算證明）

```lean
theorem calc_example (a b c : Nat) (h1 : a = b + 1) (h2 : b = c - 1) : a > c := by
  calc
    a     = b + 1 := h1
      _   = c - 1 + 1 := by rw [h2]
      _   = c := Nat.sub_add_cancel (by omega)
    a > c := Nat.lt_of_sub_eq_succ rfl
```

## show（顯示目標）

```lean
theorem show_example (p q : Prop) (h : p ∧ q) : q ∧ p := by
  have ⟨hp, hq⟩ := h
  constructor
  show q from hq
  show p from hp
```

## have（輔助事實）

```lean
theorem have_example (n : Nat) : n + 0 = n := by
  have h : n = n := rfl
  exact Nat.add_zero n
```

## let（區域綁定）

```lean
theorem let_example (n m : Nat) : (n + m) + 0 = n + m := by
  let sum := n + m
  show sum = n + m from rfl
```

## 結構化遞迴證明

```lean
theorem nat_induction (P : Nat → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) (n : Nat) : P n := by
  induction n with
  | zero => exact h0
  | succ n ih => exact hs n ih
```

## 練習

1. 用 calc 證明：`∀ a b c, a = b → b = c → a = c`
2. 用結構化證明重寫命題邏輯章節的定理
3. 證明加法交換律
4. 證明列表 append 的結合律