# 14 - 編寫正確的排序演算法

## 插入排序

```lean
def insert (a : Nat) (xs : List Nat) : List Nat :=
  match xs with
  | [] => [a]
  | x :: ys =>
    if a ≤ x then a :: x :: ys
    else x :: insert a ys

def insertionSort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (insertionSort xs)

-- 正確性證明
theorem insert_preserves_length (a : Nat) (xs : List Nat) :
  (insert a xs).length = xs.length + 1 := by
  induction xs with
  | nil => simp [insert]
  | cons x xs ih =>
    simp [insert]
    split
    case h_1 => rfl
    case h_2 => simp [ih]
```

## 合併排序

```lean
def merge : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: merge xs (y :: ys)
    else y :: merge (x :: xs) ys

def mergeSort : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | xs =>
    let mid := xs.length / 2
    let (left, right) := xs.splitAt mid
    merge (mergeSort left) (mergeSort right)

-- 交換性證明
theorem merge_comm (xs ys : List Nat) : merge xs ys = merge ys xs := by
  induction xs generalizing ys with
  | nil => simp [merge]
  | cons x xs ih =>
    cases ys with
    | nil => simp [merge]
    | cons y ys =>
      simp [merge]
      split <;> split <;> simp
      . case h_1 => apply ih
      . case h_2 => simp at *
      . case h_3 => simp at *
      . case h_4 => simp at ih; apply ih
```

## 練習

1. 證明 `insertionSort` 輸出是排序的
2. 證明 `mergeSort` 的正確性
3. 實作快速排序並證明其正確性
4. 實作堆疊排序並證明其正確性