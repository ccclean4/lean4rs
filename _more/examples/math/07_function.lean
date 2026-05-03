-- 07_function.lean - 函數性質

def main : IO Unit := IO.println "=== 數學證明範例：函數性質 ==="

def inc (x : Nat) : Nat := x + 1
def double (x : Nat) : Nat := x * 2

#eval main
#eval IO.println s!"inc 3 = {inc 3}"
#eval IO.println s!"double 4 = {double 4}"
#eval IO.println s!"(inc ∘ double) 4 = {inc (double 4)}"
#eval IO.println s!"(double ∘ inc) 4 = {double (inc 4)}"