# Recursion.lean

## 數學原理

### 遞迴與數學歸納法

遞迴程式的正確性與數學歸納法密切相關。費波那契數列：

$$f(0) = 0, \quad f(1) = 1, \quad f(n+2) = f(n) + f(n+1)$$

Lean 4 的模式匹配直接對應數學定義：

```lean
def fib (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
```

### 尾遞迴與迭代

尾遞迴是迭代的函數式表示：

$$f(n) = \text{iter}(0, 1, n)$$

其中 $\text{iter}(a, b, 0) = a$，$\text{iter}(a, b, n+1) = \text{iter}(b, a+b, n)$

### 樹狀遞迴

二元樹的遞迴定義對應拓撲學中的胞腔複形：

```lean
inductive Tree (α : Type) : Type
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
```

## 程式意義

### 線性遞迴 (fib)

```lean
def fib (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
```

時間複雜度 $O(\phi^n)$，其中 $\phi = \frac{1+\sqrt{5}}{2}$ 是黃金比例。

### 尾遞迴優化 (fibTail)

```lean
def fibTail (n : Nat) : Nat :=
  let rec go (a b : Nat) : Nat → Nat
    | 0 => a
    | 1 => b
    | n + 2 => go b (a + b) n
  go 0 1 n
```

時間複雜度 $O(n)$，空間複雜度 $O(1)$。

### 樹狀遞迴

```lean
def treeSize (t : Tree Nat) : Nat :=
  match t with
  | Tree.leaf _ => 1
  | Tree.node l r => 1 + treeSize l + treeSize r
```

## 互遞迴

奇偶判斷展示互遞迴：

```lean
def isEven (n : Nat) : Bool :=
  match n with
  | 0 => true
  | n + 1 => isOdd n

and isOdd (n : Nat) : Bool :=
  match n with
  | 0 => false
  | n + 1 => isEven n
```

這對應數學中的命題邏輯互推導。

## 教學重點

1. 結構遞迴原則（每個 inductive 類型都有唯一的遞迴原理）
2. 尾遞迴的執行效率優勢
3. 互遞迴作為狀態機的模型