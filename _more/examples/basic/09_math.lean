-- 09_math.lean - 計算性質

def main : IO Unit := IO.println "=== 基本範例：計算性質 ==="

#eval main
#eval IO.println s!"Nat.gcd 48 18 = {Nat.gcd 48 18}"
#eval IO.println s!"48 * 18 / Nat.gcd 48 18 = {48 * 18 / Nat.gcd 48 18}"