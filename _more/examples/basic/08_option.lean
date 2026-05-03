-- 08_option.lean - Option 與 Sum

def isEven (n : Nat) : Bool := n % 2 == 0

def findFirstEven (xs : List Nat) : Option Nat :=
  match xs with
  | [] => none
  | x :: ys => if isEven x then some x else findFirstEven ys

def safeDiv (a b : Nat) : Option Nat :=
  if b == 0 then none else some (a / b)

def divideOrError (a b : Nat) : Sum String Nat :=
  if b == 0 then .inl "Division by zero" else .inr (a / b)

#eval IO.println s!"findFirstEven [1, 3, 5, 6, 7] = {findFirstEven [1, 3, 5, 6, 7]}"
#eval IO.println s!"safeDiv 10 2 = {safeDiv 10 2}"
#eval IO.println s!"safeDiv 10 0 = {safeDiv 10 0}"
#eval IO.println s!"divideOrError 10 3 = {divideOrError 10 3}"
#eval IO.println s!"divideOrError 10 0 = {divideOrError 10 0}"