# SearchTrees.lean

## 數學原理

### 二元搜尋樹的定義

二元搜尋樹（BST）是滿足以下條件的二元樹：

對所有節點 $v$，若左子樹存在，則左子樹所有節點 $< v$；若右子樹存在，則右子樹所有節點 $> v$。

### BST 的數學性質

搜尋樹的中序遍歷產生有序序列：

$$\text{inorder}(\text{BST}) = \text{sorted sequence}$$

### 高度與節點關係

對於高度為 $h$ 的 BST：
- 最小節點數：$h + 1$（完全樹）
- 最大節點數：$2^{h+1} - 1$

### 搜索複雜度

搜索時間為 $O(h)$，平衡樹為 $O(\log n)$。

## 程式意義

### BST 定義

```lean
inductive BST (α : Type) : Type
  | empty : BST α
  | node : α → BST α → BST α → BST α
```

### 搜索

```lean
def BST.contains [Ord α] : BST α → α → Bool
  | .empty, _ => false
  | .node v l r, x =>
    match cmp x v with
    | .lt => contains l x
    | .eq => true
    | .gt => contains r x
```

### 插入

```lean
def BST.insert [Ord α] : α → BST α → BST α
  | x, .empty => .node x .empty .empty
  | x, (.node v l r) =>
    match cmp x v with
    | .lt => .node v (insert x l) r
    | .eq => .node v l r
    | .gt => .node v l (insert x r)
```

### 中序遍歷

```lean
def BST.toList : BST α → List α
  | .empty => []
  | .node v l r => l.toList ++ [v] ++ r.toList
```

## 教學重點

1. BST 的遞迴定義
2. 搜索與插入的邏輯
3. 中序遍歷的性質
4. BST 性質的形式化證明