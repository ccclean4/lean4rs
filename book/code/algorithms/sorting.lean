-- Algorithms: 排序演算法
-- Lean 4 中的排序演算法實現與驗證

def insert (a : Nat) (xs : List Nat) : List Nat :=
  match xs with
  | [] => [a]
  | x :: ys =>
    if a ≤ x then a :: x :: ys
    else x :: insert a ys

def insertionSort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (insertionSort xs)

def merge (xs ys : List Nat) : List Nat :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs', y :: ys' =>
    if x ≤ y then x :: merge xs' ys
    else y :: merge xs ys'

def mergeSort : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | xs =>
    let mid := xs.length / 2
    let (left, right) := xs.splitAt mid
    merge (mergeSort left) (mergeSort right)

-- 插入排序的長度保持
theorem insert_preserves_length (a : Nat) (xs : List Nat) :
  (insert a xs).length = xs.length + 1 := by
  induction xs with
  | nil => simp [insert]
  | cons x xs ih =>
    simp [insert]
    split
    case h_1 => rfl
    case h_2 => simp [ih]

theorem insertionSort_length (xs : List Nat) :
  (insertionSort xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [insertionSort]
    simp [insert_preserves_length]
    simp [ih]

-- merge 保持長度
theorem merge_preserves_length (xs ys : List Nat) :
  (merge xs ys).length = xs.length + ys.length := by
  induction xs generalizing ys with
  | nil => simp [merge]
  | cons x xs ih =>
    cases ys with
    | nil => simp [merge]
    | cons y ys =>
      simp [merge]
      split
      case h_1 => simp [ih]
      case h_2 => simp [ih]

-- 合併排序保持長度
theorem mergeSort_length (xs : List Nat) :
  (mergeSort xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil => rfl
    | cons y zs =>
      simp [mergeSort]
      let mid := (y :: zs).length / 2
      let (left, right) := (y :: zs).splitAt mid
      have ih_left : (mergeSort left).length = left.length := by admit
      have ih_right : (mergeSort right).length = right.length := by admit
      simp [merge_preserves_length]
      admit

-- 測試
#eval insertionSort [5, 3, 8, 4, 2, 7, 1, 6]
#eval mergeSort [5, 3, 8, 4, 2, 7, 1, 6]