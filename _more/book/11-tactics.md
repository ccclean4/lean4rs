# 11 - Tactic 基礎

## tactic 模式

在 `by` 之後編寫證明腳本：

```lean
theorem example : 1 + 1 = 2 := by
  rfl
```

## 常用 tactic

### rfl（反射性）

```lean
theorem refl_example : ∀ n : Nat, n = n := by
  intros
  rfl
```

### intros（引入假設）

```lean
theorem implies_example : ∀ (p q : Prop), p → q → p := by
  intros p q hp hq
  exact hp
```

### exact（指定目標證據）

```lean
theorem simple : 1 + 1 = 2 := by
  exact Eq.refl 2
```

### apply（應用函數）

```lean
theorem apply_example (p q : Prop) (h : p → q) (hp : p) : q := by
  apply h
  exact hp
```

### rewrite（重寫）

```lean
theorem rewrite_example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  rw [h]
```

### simp（簡化）

```lean
theorem simp_example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp [h]
```

### contradiction（矛盾）

```lean
theorem contra_example (p : Prop) (h1 : p) (h2 : ¬p) : False := by
  contradiction
```

## 結構化 tactic

```lean
have h : P := by tactic
· -- 打開新目標
```

## 練習

使用 tactic 證明：
1. `∀ n, n + 0 = n`
2. `∀ p, p ∧ true ↔ p`
3. `∀ p, p ∨ false ↔ p`
4. `∀ p q r, (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)`