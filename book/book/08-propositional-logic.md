# 08 - 命題邏輯與連結詞

## 邏輯連結詞

Lean 4 內建常見的邏輯連結詞：

```lean
-- 否定
#check ¬p          -- Not p = p → False

-- 連言（且）
#check p ∧ q       -- And p q

-- 選言（或）
#check p ∨ q       -- Or p q

-- 雙蘊含
#check p ↔ q       -- Iff p q = (p → q) ∧ (q → p)
```

## 證明建構

### And（且）

```lean
theorem andIntro {p q : Prop} (hp : p) (hq : q) : p ∧ q := And.intro hp hq

theorem andElimLeft {p q : Prop} (h : p ∧ q) : p := h.left

theorem andElimRight {p q : Prop} (h : p ∧ q) : q := h.right
```

### Or（或）

```lean
theorem orIntroLeft {p q : Prop} (hp : p) : p ∨ q := Or.inl hp

theorem orIntroRight {p q : Prop} (hq : q) : p ∨ q := Or.inr hq

theorem orElim {p q r : Prop} (h : p ∨ q) (hp : p → r) (hq : q → r) : r :=
  Or.elim h hp hq
```

### Not（否定）

```lean
theorem notIntro {p : Prop} (h : p → False) : ¬p := h

theorem notElim {p : Prop} (h : ¬p) (hp : p) : False := h hp
```

### Iff（雙蘊含）

```lean
theorem iffIntro {p q : Prop} (hpq : p → q) (hqp : q → p) : p ↔ q := Iff.intro hpq hqp

theorem iffElimLeft {p q : Prop} (h : p ↔ q) : p → q := Iff.mp h

theorem iffElimRight {p q : Prop} (h : p ↔ q) : q → p := Iff.mpr h
```

## 命題邏輯定律

```lean
-- 交換律
theorem andComm {p q : Prop} : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h => And.intro h.right h.left)
    (fun h => And.intro h.right h.left)

theorem orComm {p q : Prop} : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h => Or.elim h Or.inr Or.inl)
    (fun h => Or.elim h Or.inr Or.inl)

-- 分配律
theorem andOrDist {p q r : Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := ...
```

## 練習

1. 證明 De Morgan 定律：`¬(p ∨ q) ↔ ¬p ∧ ¬q`
2. 證明蘊含分配：`(p → (q ∧ r)) ↔ (p → q) ∧ (p → r)`
3. 證明排中律：`p ∨ ¬p`
4. 證明逆否命題：`(p → q) ↔ (¬q → ¬p)`