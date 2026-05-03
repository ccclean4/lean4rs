-- 06_relation.lean - 關係與順序

def main : IO Unit := IO.println "=== 數學證明範例：關係與順序 ==="

def le (a b : Nat) : Bool := a ≤ b
def lt (a b : Nat) : Bool := a < b
def ge (a b : Nat) : Bool := a ≥ b
def gt (a b : Nat) : Bool := a > b

#eval main
#eval IO.println s!"le 5 5 = {le 5 5}"
#eval IO.println s!"lt 5 5 = {lt 5 5}"
#eval IO.println s!"ge 5 3 = {ge 5 3}"
#eval IO.println s!"gt 5 3 = {gt 5 3}"