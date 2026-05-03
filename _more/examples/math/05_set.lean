-- 05_set.lean - 集合證明

def main : IO Unit := IO.println "=== 數學證明範例：集合 ==="

def containsEvens (n : Nat) : Bool := n % 2 == 0
def containsOdds (n : Nat) : Bool := n % 2 == 1

#eval main
#eval IO.println s!"containsEvens 4 = {containsEvens 4}"
#eval IO.println s!"containsOdds 5 = {containsOdds 5}"
#eval IO.println s!"4 是偶數，5 是奇數"