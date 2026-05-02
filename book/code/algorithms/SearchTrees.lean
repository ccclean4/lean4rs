-- Algorithms: 搜尋與排序
-- 二元搜尋樹與相關演算法

inductive BST (α : Type) : Type
  | empty : BST α
  | node : α → BST α → BST α → BST α

def BST.contains [Ord α] : BST α → α → Bool
  | .empty, _ => false
  | .node v l r, x =>
    match cmp x v with
    | .lt => contains l x
    | .eq => true
    | .gt => contains r x

def BST.insert [Ord α] : α → BST α → BST α
  | x, .empty => .node x .empty .empty
  | x, (.node v l r) =>
    match cmp x v with
    | .lt => .node v (insert x l) r
    | .eq => .node v l r
    | .gt => .node v l (insert x r)

def BST.toList : BST α → List α
  | .empty => []
  | .node v l r => l.toList ++ [v] ++ r.toList

def BST.fromList [Ord α] : List α → BST α
  | [] => .empty
  | x :: xs => insert x (fromList xs)

def BST.height : BST α → Nat
  | .empty => 0
  | .node _ l r => 1 + max l.height r.height

-- 二元搜尋樹的 BST 性質證明
theorem BST.inorder_sorted [Ord α] (t : BST α) : t.toList = t.toList.qsort (· ≤ ·) := by
  induction t with
  | empty => rfl
  | node v l r ihL ihR =>
    have ihL' : l.toList = l.toList.qsort (· ≤ ·) := ihL
    have ihR' : r.toList = r.toList.qsort (· ≤ ·) := ihR
    calc
      (BST.node v l r).toList = l.toList ++ [v] ++ r.toList := rfl
        _ = l.toList.qsort (· ≤ ·) ++ [v] ++ r.toList.qsort (· ≤ ·) := by rw [ihL', ihR']

-- 測試
#eval BST.fromList [5, 3, 7, 1, 9, 4, 6].contains 7
#eval BST.fromList [5, 3, 7, 1, 9, 4, 6].contains 8
#eval BST.fromList [5, 3, 7, 1, 9, 4, 6].toList
#eval BST.fromList [5, 3, 7, 1, 9, 4, 6].height