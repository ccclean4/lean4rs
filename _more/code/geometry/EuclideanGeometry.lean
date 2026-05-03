-- Geometry: 歐氏幾何
-- 展示歐氏幾何的基本概念

structure Point where
  x : Float
  y : Float

structure Line where
  a : Float
  b : Float
  c : Float

namespace Point

def distance (p1 p2 : Point) : Float :=
  let dx := p2.x - p1.x
  let dy := p2.y - p1.y
  Float.sqrt (dx * dx + dy * dy)

def midpoint (p1 p2 : Point) : Point :=
  ⟨ (p1.x + p2.x) / 2.0, (p1.y + p2.y) / 2.0 ⟩

def collinear (p1 p2 p3 : Point) : Bool :=
  let area := (p2.x - p1.x) * (p3.y - p1.y) - (p3.x - p1.x) * (p2.y - p1.y)
  Float.abs area < 0.0001

end Point

namespace Line

def fromPoints (p1 p2 : Point) : Line :=
  let a := p2.y - p1.y
  let b := p1.x - p2.x
  let c := a * p1.x + b * p1.y
  ⟨ a, b, -c ⟩

def distanceToPoint (l : Line) (p : Point) : Float :=
  Float.abs (l.a * p.x + l.b * p.y + l.c) / Float.sqrt (l.a * l.a + l.b * l.b)

def intersect (l1 l2 : Line) : Option Point :=
  let det := l1.a * l2.b - l2.a * l1.b
  if Float.abs det < 0.0001 then none
  else
    let x := (l2.b * (-l1.c) - l1.b * (-l2.c)) / det
    let y := (l1.a * (-l2.c) - l2.a * (-l1.c)) / det
    some ⟨ x, y ⟩

end Line

#eval Point.distance ⟨0.0, 0.0⟩ ⟨3.0, 4.0⟩
#eval Point.midpoint ⟨0.0, 0.0⟩ ⟨4.0, 6.0⟩

#eval Line.fromPoints ⟨0.0, 0.0⟩ ⟨1.0, 1.0⟩

example : Point := ⟨ 1.0, 2.0 ⟩
example : Line := ⟨ 1.0, -1.0, 0.0 ⟩