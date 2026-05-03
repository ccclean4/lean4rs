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

-- 樹狀遞迴
def treeSize (t : Tree Nat) : Nat :=
  match t with
  | Tree.leaf _ => 1
  | Tree.node l r => 1 + treeSize l + treeSize r

def treeMax (t : Tree Nat) : Nat :=
  match t with
  | Tree.leaf x => x
  | Tree.node l r => max (treeMax l) (treeMax r)

-- 雙遞迴
def quickSort (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | x :: xs =>
    let smaller := xs.filter (· < x)
    let larger := xs.filter (· > x)
    quickSort smaller ++ [x] ++ quickSort larger

-- 互遞迴：奇偶判斷
def isEven (n : Nat) : Bool :=
  match n with
  | 0 => true
  | n + 1 => isOdd n

and isOdd (n : Nat) : Bool :=
  match n with
  | 0 => false
  | n + 1 => isEven n

-- 測試
#eval fib 10
#eval fibTail 10
#eval quickSort [3, 1, 4, 1, 5, 9, 2, 6]
#eval isEven 42
#eval isOdd 42