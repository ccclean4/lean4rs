def main : IO Unit :=
  IO.println "Hello, World!"

def add (a b : Nat) : Nat := a + b

#eval add 3 5
#eval main