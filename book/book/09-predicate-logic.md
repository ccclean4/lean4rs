# 09 - 謂詞邏輯與量化

## 全稱量化

```lean
-- ∀ x : α, P x
-- 是 (x : α) → P x 的語法糖

theorem allIntro {α : Type} {P : α → Prop} (h : ∀ x : α, P x) : ∀ x : α, P x := h

theorem allElim {α : Type} {P : α → Prop} (h : ∀ x : α, P x) (a : α) : P a := h a
```

### 具體例子

```lean
theorem allPos {n : Nat} : n > 0 → ∀ m : Nat, m + n > m := fun _ m => Nat.lt_add_of_pos_right (Nat.lt_of_succ_le (Nat.le_of_eq (Nat.add_zero n ▸ rfl)))
```

## 存在量化

```lean
-- ∃ x : α, P x
-- 是 Σ x : α, P x 的語法糖

theorem existsIntro {α : Type} {P : α → Prop} (a : α) (h : P a) : ∃ x : α, P x := Exists.intro a h

theorem existsElim {α : Type} {P : α → Prop} (h : ∃ x : α, P x) (g : ∀ x : α, P x → q) : q := Exists.elim h g
```

## 量化與邏輯

```lean
-- 全稱與蘊含
theoremforallImp {α : Type} {P Q : α → Prop} : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x)
  | h₁, h₂, x => h₁ x (h₂ x)

-- 存在與合取
theorem existsAnd {α : Type} {P Q : α → Prop} : (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) :=
  fun h => match h with
    | ⟨a, ⟨hp, hq⟩⟩ => And.intro (Exists.intro a hp) (Exists.intro a hq)
```

## 唯一性

```lean
-- ∃! x, P x 表示存在唯一 x 使得 P x 成立
-- ∃! x, P x := ∃ x, P x ∧ ∀ y, P y → y = x

theorem existsUnique {α : Type} {P : α → Prop} (h : ∃! x, P x) : ∃ x, P x := Exists.elim h (fun x hx => Exists.intro x hx.left)
```

## 練習

1. 證明：`∀ n : Nat, n ≠ 0 → ∃ m, n = m + 1`
2. 證明：`∃ n : Nat, n > 5 ∧ n < 10`
3. 證明：`∀ p q : Prop, (∀ x, p ∨ q) ↔ p ∨ ∀ x, q`（假設 x 不在 p 中自由出現）
4. 證明：唯一性蘊含存在性