# GroupTheory.lean

## 數學原理

### 群的定義

群 $(G, \cdot, e, {}^{-1})$ 是配備二元運算 $\cdot$、單位元 $e$ 和逆元 ${}^{-1}$ 的集合，滿足：

1. **結合律**：$(a \cdot b) \cdot c = a \cdot (b \cdot c)$
2. **單位元**：$e \cdot a = a = a \cdot e$
3. **逆元**：$a^{-1} \cdot a = e = a \cdot a^{-1}$

### 群的例子

| 群 | 運算 | 單位元 | 逆元 |
|----|------|--------|------|
| $(\mathbb{Z}, +)$ | 加法 | 0 | $-a$ |
| $(\mathbb{Q} \setminus \{0\}, \times)$ | 乘法 | 1 | $1/a$ |
| $S_n$（置換群） | 複合 | 恆等置換 | 逆置換 |

### 基本性質

1. **唯一性**：群中任何元素的逆元唯一
2. **消去律**：若 $ab = ac$，則 $b = c$
3. **阿貝爾群**：若還滿足交換律，則為阿貝爾群

### 同態與同構

- **同態**：保持運算的映射 $f(ab) = f(a)f(b)$
- **同構**：雙射的同態

## 程式意義

### 類別層級設計

```lean
class Group (α : Type) extends Monoid α where
  inv : α → α
  inv_left : ∀ a, mul (inv a) a = one
  inv_right : ∀ a, mul a (inv a) = one
```

使用繼承建立類別層級：Magma → Semigroup → Monoid → Group。

### 定理證明

```lean
theorem group_cancel_left {α : Type} [Group α] (a b c : α)
  (h : mul a b = mul a c) : b = c
```

利用逆元進行消去，展現代數推理。

### 形式化驗證的價值

群論的形式化確保：
1. 公理系統的無矛盾性
2. 定理證明的機械化檢驗
3. 抽象代數的計算機輔助研究