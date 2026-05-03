# Peano.lean

## 數學原理

### 皮亞諾公理系統

皮亞諾公理是自然數的標準公理化定義：

1. $0$ 是自然數
2. 每個自然數 $n$ 有唯一的後繼 $S(n)$
3. $S$ 是單射（不同輸入有不同輸出）
4. $S(n) \neq 0$（0 不是任何數的後繼）
5. **數學歸納法公理**：若 $P(0)$ 成立且 $P(n) \to P(S(n))$，則 $P(n)$ 對所有 $n$ 成立

### Lean 4 的形式化

```lean
inductive MyNat : Type
  | zero : MyNat
  | succ : MyNat → MyNat
```

這完全對應皮亞諾公理。

### 加法的定義

加法 $+$ 的遞迴定義：
$$a + 0 = a$$
$$a + S(b) = S(a + b)$$

```lean
def add : MyNat → MyNat → MyNat
  | a, .zero => a
  | a, .succ b => .succ (add a b)
```

### 乘法的定義

乘法 $\times$ 的遞迴定義：
$$a \times 0 = 0$$
$$a \times S(b) = a \times b + a$$

```lean
def mul : MyNat → MyNat → MyNat
  | _, .zero => .zero
  | a, .succ b => add (mul a b) a
```

## 程式意義

### 定理證明

皮亞諾系統中的核心定理：

1. **加法單位元**
   - $n + 0 = n$（右單位元）
   - $0 + n = n$（左單位元，需歸納證明）

2. **加法交換律**
   $$a + b = b + a$$
   需對 $b$ 歸納。

3. **加法結合律**
   $$(a + b) + c = a + (b + c)$$
   需對 $c$ 歸納。

4. **乘法對加法的分配律**
   $$a \times (b + c) = a \times b + a \times c$$

### 歸納法的形式

```lean
theorem induction (P : MyNat → Prop) (h0 : P .zero) (hs : ∀ n, P n → P (.succ n)) (n : MyNat) : P n
```

這是皮亞諾第五公理的形式化表達。

## 教學重點

1. 自然數的公理化定義
2. 運算的遞迴定義模式
3. 數學歸納法作為元定理
4. 從公理建立算術理論