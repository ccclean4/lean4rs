# Induction.lean

## 數學原理

### 自然數的結構

自然數的皮亞諾公理：

1. $0$ 是自然數
2. 每個自然數 $n$ 有後繼 $S(n)$
3. $S$ 是單射
4. $S(n) \neq 0$ 對所有 $n$
5. 數學歸納法原理

Lean 4 的歸納定義：

```lean
inductive Nat : Type
  | zero : Nat
  | succ : Nat → Nat
```

### 加法的交換律證明

數學陳述：$\forall a, b \in \mathbb{N}, a + b = b + a$

對 $a$ 進行歸納：
- 基底：$a = 0$，需證 $0 + b = b + 0$
  - $0 + b = b$（加法定義）
  - $b + 0 = b$（加法性質）
- 歸納步驟：假設 $a + b = b + a$，需證 $(a+1) + b = b + (a+1)$
  - $(a+1) + b = (a+b) + 1$（加法結合律）
  - $b + (a+1) = (b+a) + 1$（歸納假設）

### 乘法對加法的分配律

$$\forall a, b, c \in \mathbb{N}, a \times (b + c) = a \times b + a \times c$$

對 $a$ 歸納：
- 基底：$0 \times (b+c) = 0 = 0 \times b + 0 \times c$
- 歸納步驟：$(a+1) \times (b+c) = a \times (b+c) + (b+c)$

## 程式意義

### 結構遞迴

Lean 4 的 `induction` tactic 自動產生歸納假設：

```lean
theorem natAddComm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero =>
    have : b = b + 0 := (Nat.add_zero b).symm
    simp [this]
  | succ a ih =>
    calc
      a.succ + b = (a + b).succ := rfl
        _ = (b + a).succ := by rw [ih]
        _ = b + a.succ := Nat.add_succ b a ▸ rfl
```

### 計算性證明

`calc` 區塊允許逐步代數推導，每行可以是不同的表達式或已知事實。

### 無窮下降法

```lean
theorem infiniteDescent (P : Nat → Prop) (h : ∀ n, (∀ m < n, P m) → P n) : ∀ n, P n
```

這是證明不存在時常用的方法：假設存在最小反例，導出矛盾。

## 教學重點

1. 數學歸納法作為結構遞迴的對偶
2. 歸納假設的自動化產生
3. `calc` 區塊的靈活性