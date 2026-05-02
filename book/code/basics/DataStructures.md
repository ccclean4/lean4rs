# DataStructures.lean

## 數學原理

### 列表 (List)

列表是常見的抽象資料結構，在數學上相當於有限序列：

$$\text{List } \alpha \cong [\alpha] = \alpha^0 \cup \alpha^1 \cup \alpha^2 \cup \cdots$$

Lean 4 的列表定義：

```lean
inductive List (α : Type) : Type
  | nil : List α
  | cons : α → List α → List α
```

### 選項類型 (Option)

Option 類型對應數學中的「可能失敗的計算」：

$$\text{Option } \alpha \cong \alpha \cup \{ \text{None} \}$$

### 和類型 (Sum)

Sum 類型（又稱 Coproduct 或 Either）：

$$\text{Sum } \alpha \, \beta \cong \alpha + \beta$$

表示「要么是 α，要么是 β」。

## 程式意義

### List 的 fold

```lean
def sum (xs : List Nat) : Nat := xs.foldl (· + ·) 0
```

`foldl` 對應數學中的廣義乘積運算：

$$\sum_{i=1}^{n} a_i = (\cdots ((a_1 + a_2) + a_3) + \cdots + a_n)$$

### filter 與 map

```lean
def doubled := nums.map (· * 2)
def filtered := nums.filter (· > 2)
```

- `map` 對應泛函分析中的映射概念
- `filter` 對應集合論中的子集選擇

### 列表推導式

```lean
def list_comprehension : List Nat :=
  [i * j | i ∈ [1, 2, 3], j ∈ [1, 2, 3]]
```

這是集合 builder notation 的計算機實現。

## 教學重點

1. 代數資料類型（ADT）的表示
2. fold 的普遍性（catamorphism）
3. Option 類型如何優雅地處理失敗情況