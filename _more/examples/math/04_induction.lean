-- 04_induction.lean - 數學歸納法

def main : IO Unit := IO.println "=== 數學證明範例：數學歸納法 ==="

def sumUpTo (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => n + 1 + sumUpTo n

def sumFormula (n : Nat) : Nat := n * (n + 1) / 2

#eval main
#eval IO.println s!"sumUpTo 10 = {sumUpTo 10} = sumFormula 10 = {sumFormula 10}"
#eval IO.println s!"sumUpTo 100 = {sumUpTo 100} = sumFormula 100 = {sumFormula 100}"