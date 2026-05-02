# 13 - 自動化證明

## simp

### 基本用法

```lean
theorem simp_basic : ∀ n : Nat, n + 0 = n := by
  simp
```

### 自訂簡化規則

```lean
@[simp]
theorem triple_eq_three_mul (n : Nat) : n + n + n = 3 * n := by
  ring
```

## ring（環運算）

```lean
theorem ring_example (a b c : Int) : (a + b) * c = a * c + b * c := by
  ring
```

## linarith（線性運算）

```lean
theorem linarith_example (x y z : Int) (h1 : x + y = z) (h2 : z = 2) : x + y = 2 := by
  linarith
```

## omega（ Presburger 算術）

```lean
theorem omega_example (n : Nat) : n ≥ 0 := by
  omega

theorem omega_example2 (n m : Nat) (h : n ≤ m) : n - m ≤ 0 := by
  omega
```

## finish（自動證明）

```lean
theorem finish_example : ∀ n : Nat, n ≥ 0 ∧ n ≤ n := by
  finish
```

## aesop（自動策略）

```lean
theorem aesop_example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  aesop
```

## 綜合範例

```lean
theorem综合_example (n : Nat) : n * 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      n.succ * 0 = n * 0 + 0 := Nat.mul_succ n 0
                _ = 0 + 0 := by rw [ih]
                _ = 0 := rfl
```

## 練習

1. 使用 `simp` 簡化表達式
2. 使用 `ring` 證明多項式恆等式
3. 使用 `omega` 證明整數不等式
4. 比較 `finish` 和 `decide` 的使用場景