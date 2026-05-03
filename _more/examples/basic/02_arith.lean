-- 02_arith.lean - 算術運算

def add (a b : Nat) : Nat := a + b
def sub (a b : Nat) : Nat := a - b
def mul (a b : Nat) : Nat := a * b
def div (a b : Nat) : Nat := a / b
def mod (a b : Nat) : Nat := a % b
def pow (base exp : Nat) : Nat := base ^ exp

#eval IO.println s!"add 3 5 = {add 3 5}"
#eval IO.println s!"sub 10 3 = {sub 10 3}"
#eval IO.println s!"mul 4 7 = {mul 4 7}"
#eval IO.println s!"div 20 4 = {div 20 4}"
#eval IO.println s!"mod 17 5 = {mod 17 5}"
#eval IO.println s!"pow 2 10 = {pow 2 10}"