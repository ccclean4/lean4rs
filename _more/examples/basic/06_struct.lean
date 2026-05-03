-- 06_struct.lean - 結構體

structure Point where
  x : Int
  y : Int

def pointAdd (p q : Point) : Point :=
  { x := p.x + q.x, y := p.y + q.y }

def pointScale (p : Point) (s : Int) : Point :=
  { x := p.x * s, y := p.y * s }

def main : IO Unit := do
  let p1 : Point := { x := 1, y := 2 }
  let p2 : Point := { x := 3, y := 4 }
  let p3 := pointAdd p1 p2
  IO.println s!"pointAdd (1,2) (3,4) = ({p3.x}, {p3.y})"
  let p4 := pointScale p1 5
  IO.println s!"pointScale (1,2) 5 = ({p4.x}, {p4.y})"

#eval main