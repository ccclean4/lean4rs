-- 05_list.lean - 列表處理

def isEven (n : Nat) : Bool := n % 2 == 0

def sum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: ys => x + sum ys

def product (xs : List Nat) : Nat :=
  match xs with
  | [] => 1
  | x :: ys => x * product ys

def length (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => 1 + length ys

def append (xs ys : List α) : List α :=
  match xs with
  | [] => ys
  | x :: zs => x :: append zs ys

def reverse (xs : List α) : List α :=
  match xs with
  | [] => []
  | x :: ys => reverse ys ++ [x]

def doubleAll (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | x :: ys => (x * 2) :: doubleAll ys

def filterEven (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | x :: ys => if isEven x then x :: filterEven ys else filterEven ys

def allEven (xs : List Nat) : Bool :=
  match xs with
  | [] => true
  | x :: ys => isEven x && allEven ys

def anyEven (xs : List Nat) : Bool :=
  match xs with
  | [] => false
  | x :: ys => isEven x || anyEven ys

#eval IO.println s!"sum [1, 2, 3, 4, 5] = {sum [1, 2, 3, 4, 5]}"
#eval IO.println s!"product [1, 2, 3, 4, 5] = {product [1, 2, 3, 4, 5]}"
#eval IO.println s!"length [a, b, c, d] = {length (["a", "b", "c", "d"])}"
#eval IO.println s!"append [1, 2] [3, 4, 5] = {append [1, 2] [3, 4, 5]}"
#eval IO.println s!"reverse [1, 2, 3, 4, 5] = {reverse [1, 2, 3, 4, 5]}"
#eval IO.println s!"doubleAll [1, 2, 3] = {doubleAll [1, 2, 3]}"
#eval IO.println s!"filterEven [1, 2, 3, 4, 5, 6] = {filterEven [1, 2, 3, 4, 5, 6]}"
#eval IO.println s!"allEven [2, 4, 6] = {allEven [2, 4, 6]}"
#eval IO.println s!"anyEven [1, 3, 5, 6] = {anyEven [1, 3, 5, 6]}"