-- 04_recursion.lean - 遞迴

def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def fib (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

def sumUpTo (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => n + 1 + sumUpTo n

#eval IO.println s!"factorial 5 = {factorial 5}"
#eval IO.println s!"fib 10 = {fib 10}"
#eval IO.println s!"sumUpTo 100 = {sumUpTo 100}"