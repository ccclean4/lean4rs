-- Basics: 高階函數
-- 展示 map, filter, fold, zip 等高階函數

def double := fun x : Nat => x * 2

def isEven (n : Nat) : Bool := n % 2 == 0

def isOdd (n : Nat) : Bool := n % 2 == 1

def sum (xs : List Nat) : Nat := xs.foldl (· + ·) 0

def product (xs : List Nat) : Nat := xs.foldl (· * ·) 1

def zipWith {α β γ : Type} (f : α → β → γ) (xs : List α) (ys : List β) : List γ :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xs', y :: ys' => f x y :: zipWith f xs' ys'

def unzip {α β : Type} (xys : List (α × β)) : List α × List β :=
  xys.foldr (fun (x, y) (xs, ys) => (x :: xs, y :: ys)) ([], [])

def compose (f : β → γ) (g : α → β) (x : α) : γ := f (g x)

def curry (f : α × β → γ) (a : α) (b : β) : γ := f (a, b)

def uncurry (f : α → β → γ) (ab : α × β) : γ := f ab.1 ab.2

#eval [1, 2, 3, 4, 5].map double
#eval [1, 2, 3, 4, 5].filter isEven
#eval sum [1, 2, 3, 4, 5]
#eval product [1, 2, 3, 4, 5]
#eval zipWith (· + ·) [1, 2, 3] [10, 20, 30]
#eval unzip [(1, 'a'), (2, 'b'), (3, 'c')]