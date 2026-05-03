# Collections.lean

## 數學原理

### 佇列 (Queue)

佇列是 FIFO（先進先出）資料結構，數學上是一個有限序列：

$$Q = \langle q_1, q_2, \ldots, q_n \rangle$$

操作：
- `enqueue`：在末尾添加
- `dequeue`：從頭部移除

### 棧 (Stack)

棧是 LIFO（後進先出）資料結構：

$$S = \langle s_1, s_2, \ldots, s_n \rangle \quad \text{其中 } s_n \text{ 是 top}$$

操作：
- `push`：壓入
- `pop`：彈出

### 樹 (Tree)

二元樹的遞迴定義：

$$T ::= \text{leaf}(a) \mid \text{node}(T_1, T_2)$$

對應數學中的根系結構。

## 程式意義

### 佇列的雙棧實現

```lean
inductive Queue (α : Type) where
  | mk : List α → List α → Queue α
```

利用兩個棧模擬佇列：
- `front`：出隊端的棧
- `back`：入隊端的棧

攤銷複雜度 $O(1)$。

### 棧的函數式實現

```lean
inductive Stack (α : Type) where
  | empty : Stack α
  | push : α → Stack α → Stack α
```

完全函數式，無需可變狀態。

### 樹的函數式操作

```lean
def Tree.map (f : α → β) : Tree α → Tree β
  | .leaf a => .leaf (f a)
  | .node l r => .node (map f l) (map f r)

def Tree.fold (f : α → β → β) (b : β) : Tree α → β
  | .leaf a => f a b
  | .node l r => fold f (fold f b r) l
```

`fold` 對應數學中的路徑積分概念。

## 教學重點

1. 代數資料類型（ADT）的設計
2. 資料結構的慣用實現方式
3. 函數式 vs 命令式實現
4. fold 的普遍性