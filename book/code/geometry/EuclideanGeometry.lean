-- Geometry: 平面幾何定理
-- 展示幾何命題的形式化證明

structure Triangle where
  A : Point
  B : Point
  C : Point
  nonDegenerate : B ≠ A ∧ C ≠ A ∧ B ≠ C

def Triangle.sideLengths (t : Triangle) : Float × Float × Float :=
  (Point.distance t.B t.C,
   Point.distance t.A t.C,
   Point.distance t.A t.B)

def Triangle.perimeter (t : Triangle) : Float :=
  let (a, b, c) := sideLengths t
  a + b + c

def Triangle.area (t : Triangle) : Float := do
  let (a, b, c) := sideLengths t
  let s := (a + b + c) / 2
  sqrt (s * (s - a) * (s - b) * (s - c))

def Triangle.isEquilateral (t : Triangle) : Bool := do
  let (a, b, c) := sideLengths t
  a ≈ b ∧ b ≈ c

def Triangle.isIsosceles (t : Triangle) : Bool := do
  let (a, b, c) := sideLengths t
  a ≈ b ∨ b ≈ c ∨ a ≈ c

def Triangle.isRight (t : Triangle) : Bool := do
  let (a, b, c) := sideLengths t
  a^2 + b^2 ≈ c^2 ∨ b^2 + c^2 ≈ a^2 ∨ a^2 + c^2 ≈ b^2

structure Circle where
  center : Point
  radius : Float
  valid : radius > 0

def Circle.contains (γ : Circle) (p : Point) : Bool :=
  Point.distance p γ.center ≤ γ.radius

def Circle.area (γ : Circle) : Float :=
  Float.pi * γ.radius^2

def Circle.circumference (γ : Circle) : Float :=
  2 * Float.pi * γ.radius

def Circle.intersectsLine (γ : Circle) (l : Line) : Bool := do
  let d := abs (l.a * γ.center.x + l.b * γ.center.y + l.c) / sqrt (l.a^2 + l.b^2)
  d ≤ γ.radius

structure Polygon where
  vertices : List Point
  simple : ∀ i j, i ≠ j → vertices[i] ≠ vertices[j]

def Polygon.perimeter (P : Polygon) : Float := do
  let n := P.vertices.length
  let rec loop (i : Nat) (acc : Float) : Float :=
    if i = n then acc
    else loop (i + 1) (acc + Point.distance P.vertices[i] P.vertices[(i+1) % n])
  loop 0 0

def Point.inTriangle (p : Triangle) : Bool := do
  let (a, b, c) := (p.x, p.y, 1)
  let (a1, b1, c1) := (t.A.x, t.A.y, 1)
  let (a2, b2, c2) := (t.B.x, t.B.y, 1)
  let (a3, b3, c3) := (t.C.x, t.C.y, 1)
  let d1 := a * (b1 - c1) + b * (c1 - a1) + c * (a1 - b1)
  let d2 := a * (b2 - c2) + b * (c2 - a2) + c * (a2 - b2)
  let d3 := a * (b3 - c3) + b * (c3 - a3) + c * (a3 - b3)
  (d1 ≥ 0 ∧ d2 ≥ 0 ∧ d3 ≥ 0) ∨ (d1 ≤ 0 ∧ d2 ≤ 0 ∧ d3 ≤ 0)

end