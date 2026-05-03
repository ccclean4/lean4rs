-- 03_condition.lean - 條件表達式

def myMax (a b : Nat) : Nat := if a > b then a else b
def myMin (a b : Nat) : Nat := if a < b then a else b
def abs (n : Int) : Int := if n > 0 then n else -n
def sign (n : Int) : Int := if n > 0 then 1 else if n < 0 then -1 else 0

#eval IO.println s!"myMax 15 8 = {myMax 15 8}"
#eval IO.println s!"myMin 15 8 = {myMin 15 8}"
#eval IO.println s!"abs (-5) = {abs (-5)}"
#eval IO.println s!"sign (-3) = {sign (-3)}"