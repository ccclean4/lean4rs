# 07 - 命題與證據

## Prop 類型

在 Lean 4 中，命題也是類型：

```lean
-- 命題是 Type 1（Type 0 的類型）
#check Prop  -- Type

-- 證據是命題的項
theorem example : 1 + 1 = 2 := rfl

-- rfl 是反射性證據
#check rfl : ∀ {α : Sort ?u}, α = α
```

## 證據作為值

```lean
-- 命題可以像值一樣操作
def proof_of_true : True := trivial

def proof_of_and (p : Prop) (hp : p) (q : Prop) (hq : q) : p ∧ q :=
  And.intro hp hq

-- 提取成分
#check proof_of_and 5 = 5 rfl 3 = 3 (fun _ => rfl)  -- 5 = 5 ∧ 3 = 3
```

## 蘊含

```lean
-- p → q 表示「若 p 則 q」
-- 也是函數類型：接收 p 的證據，返回 q 的證據

theorem modusPonens (p q : Prop) (hp : p) (h : p → q) : q := h hp
```

## 恆真式

```lean
theorem trivial : ∀ (p : Prop), p → p := fun p hp => hp

theorem not_not (p : Prop) (hp : p) : ¬¬p := fun hnp => hnp hp
```

## 矛盾

```lean
theorem explosion (p : Prop) (h : False) : p := False.elim h
```

## 練習

1. 證明：`∀ p, p ∨ p = p`
2. 證明：`∀ p, p ∧ p = p`
3. 證明：`∀ p q, p → q → p`
4. 證明：`∀ p, ¬¬p → p`（需要額外假設）