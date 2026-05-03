-- Basics: 遞迴範例
-- 展示各種遞迴模式

-- 線性遞迴
def fib (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

-- 尾遞迴版本
def fibTail (n : Nat) : Nat :=
  let rec go (a b : Nat) : Nat → Nat
    | 0 => a
    | 1 => b
    | n + 2 => go b (a + b) n
  go 0 1 n

-- 樹的定義
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

-- 樹狀遞迴
def treeSize {α : Type} (t : Tree α) : Nat :=
  match t with
  | Tree.leaf _ => 1
  | Tree.node l r => 1 + treeSize l + treeSize r

def treeMax (t : Tree Nat) : Nat :=
  match t with
  | Tree.leaf x => x
  | Tree.node l r => max (treeMax l) (treeMax r)

-- 插入排序（替代 quickSort，避免終止性問題）
def insertSort (xs : List Nat) : List Nat :=
  let rec insert (x : Nat) (ys : List Nat) : List Nat :=
    match ys with
    | [] => [x]
    | y :: ys' => if x ≤ y then x :: y :: ys' else y :: insert x ys'
  match xs with
  | [] => []
  | x :: xs' => insert x (insertSort xs')

-- 互遞迴：奇偶判斷
mutual
  def isEven (n : Nat) : Bool :=
    match n with
    | 0 => true
    | n + 1 => isOdd n

  def isOdd (n : Nat) : Bool :=
    match n with
    | 0 => false
    | n + 1 => isEven n
end

-- 測試
#eval fib 10
#eval fibTail 10
#eval insertSort [3, 1, 4, 1, 5, 9, 2, 6]
#eval isEven 42
#eval isOdd 42