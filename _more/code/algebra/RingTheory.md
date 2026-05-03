# RingTheory.lean

## 數學原理

### 環的定義

環 $(R, +, 0, -, \times, 1)$ 滿足：

1. $(R, +, 0, -)$ 是阿貝爾群
2. $(R, \times, 1)$ 是么半群
3. 乘法對加法的分配律：
   - $a \times (b + c) = a \times b + a \times c$
   - $(a + b) \times c = a \times c + b \times c$

### 環的類型層級

```
環 → 交換環 → 整域 → 場
```

| 類型 |額外條件 |
|------|---------|
| 交換環 | $ab = ba$ |
| 整域 | 無零因子：$ab = 0 \implies a = 0 \lor b = 0$ |
| 場 | 乘法逆元存在 |

### 經典例子

| 環 | 是否交換 | 是否整域 | 是否場 |
|----|---------|---------|--------|
| $\mathbb{Z}$ | 是 | 是 | 否 |
| $\mathbb{Q}$ | 是 | 是 | 是 |
| $\mathbb{R}$ | 是 | 是 | 是 |
| $\mathbb{C}$ | 是 | 是 | 是 |
| $M_n(\mathbb{R})$ | 否 | 否 | 否 |

## 程式意義

### 類別定義

```lean
class Ring (α : Type) where
  add : α → α → α
  zero : α
  neg : α → α
  mul : α → α → α
  one : α
  -- 公理...
```

### 定理證明

```lean
theorem ring_neg_unique {α : Type} [Ring α] (a b : α) (h : add a b = zero) : b = neg a
```

利用消去律證明逆元的唯一性。

### 有理數場

```lean
instance : Field Rat where
  inv := Rat.inv
  mulInv := Rat.mul_inv_cancel
```

## 教學重點

1. 環的公理化定義
2. 從整數到有理數的結構擴展
3. 無零因子的重要性（整域）
4. 場的刻畫：每個非零元素都有乘法逆元