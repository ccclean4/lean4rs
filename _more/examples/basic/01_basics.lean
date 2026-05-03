-- 01_basics.lean - 基本輸出與資料型態

def main : IO Unit :=
  IO.println "=== Lean 4 基本範例 ==="

def isEven (n : Nat) : Bool := n % 2 == 0

def greet (name : String) : String := "Hello, " ++ name ++ "!"

#eval main
#eval IO.println s!"isEven 4 = {isEven 4}"
#eval IO.println s!"isEven 5 = {isEven 5}"
#eval IO.println s!"greet \"Lean\" = \"{greet "Lean"}\""