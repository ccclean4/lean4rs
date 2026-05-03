-- 02_nat_prop.lean - 自然數性質

def main : IO Unit := IO.println "=== 數學證明範例：自然數性質 ==="

theorem mul_zero (n : Nat) : n * 0 = 0 := Nat.mul_zero n

theorem zero_mul (n : Nat) : 0 * n = 0 := Nat.zero_mul n

theorem mul_one (n : Nat) : n * 1 = n := Nat.mul_one n

theorem one_mul (n : Nat) : 1 * n = n := Nat.one_mul n

theorem mul_comm (a b : Nat) : a * b = b * a := Nat.mul_comm a b

theorem mul_assoc (a b c : Nat) : (a * b) * c = a * (b * c) := Nat.mul_assoc a b c

theorem dist_l (a b c : Nat) : a * (b + c) = a * b + a * c := Nat.left_distrib a b c

#eval main
#eval IO.println s!"mul_zero 5 : 5 * 0 = {5 * 0}"
#eval IO.println s!"zero_mul 5 : 0 * 5 = {0 * 5}"
#eval IO.println s!"mul_one 5 : 5 * 1 = {5 * 1}"
#eval IO.println s!"mul_comm 3 4 : 3 * 4 = {3 * 4} = {4 * 3}"
#eval IO.println s!"dist_l 2 3 4 : 2*(3+4) = {2*(3+4)} = {2*3 + 2*4}"