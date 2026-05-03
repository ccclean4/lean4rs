-- 01_equal.lean - 相等性證明

def main : IO Unit := IO.println "=== 數學證明範例：相等性 ==="

theorem add_zero (n : Nat) : n + 0 = n := Nat.add_zero n

theorem zero_add (n : Nat) : 0 + n = n := Nat.zero_add n

theorem add_comm (a b : Nat) : a + b = b + a := Nat.add_comm a b

theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := Nat.add_assoc a b c

#eval main
#eval IO.println s!"add_zero 5 : 5 + 0 = {5 + 0}"
#eval IO.println s!"zero_add 5 : 0 + 5 = {0 + 5}"
#eval IO.println s!"add_comm 3 5 : 3 + 5 = {3 + 5} = {5 + 3}"
#eval IO.println s!"add_assoc 1 2 3 : (1+2)+3 = {(1+2)+3} = {1+(2+3)}"