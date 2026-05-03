-- Geometry: 點與線
-- 平面幾何的基本元素

structure Point where
  x : Float
  y : Float

structure Line where
  a : Float
  b : Float
  c : Float
  valid : a ≠ 0 ∨ b ≠ 0

def Point.mk (x y : Float) : Point := ⟨x, y⟩

def Point.origin : Point := ⟨0, 0⟩

def Point.distance (p q : Point) : Float :=
  sqrt ((p.x - q.x)^2 + (p.y - q.y)^2)

def Point.add (p q : Point) : Point := ⟨p.x + q.x, p.y + q.y⟩

def Point.sub (p q : Point) : Point := ⟨p.x - q.x, p.y - q.y⟩

def Point.scale (p : Point) (k : Float) : Point := ⟨k * p.x, k * p.y⟩

def Line.through (p q : Point) (h : p ≠ q) : Line := do
  let a := q.y - p.y
  let b := p.x - q.x
  let c := a * p.x + b * p.y
  ⟨a, b, -c, by simp [a, b]⟩

def Line.slope (l : Line) : Float :=
  if l.a = 0 then 0 else -l.b / l.a

def Line.yIntercept (l : Line) : Float :=
  if l.b = 0 then 0 else -l.c / l.b

def Line.contains (l : Line) (p : Point) : Bool :=
  l.a * p.x + l.b * p.y + l.c = 0

def Line.intersection (l1 l2 : Line) : Option Point := do
  let det := l1.a * l2.b - l2.a * l1.b
  guard (det ≠ 0)
  let x := (l2.c * l1.b - l1.c * l2.b) / det
  let y := (l1.c * l2.a - l2.c * l1.a) / det
  pure ⟨x, y⟩

def Line.parallel (l1 l2 : Line) : Bool :=
  l1.a * l2.b = l2.a * l1.b

def Line.perpendicular (l1 l2 : Line) : Bool :=
  l1.a * l2.a + l1.b * l2.b = 0

def Line.perpendicularThrough (p : Point) (l : Line) : Line := do
  let a' := l.b
  let b' := -l.a
  let c' := -(a' * p.x + b' * p.y)
  ⟨a', b', c', by simp⟩

def Point.reflect (p : Point) (l : Line) : Point := do
  let perp := Line.perpendicularThrough p l
  let intersection := Line.intersection l perp
  match intersection with
  | some m => Point.add p (Point.scale (Point.sub p m) 2)
  | none => p

def Point.rotate (p : Point) (θ : Float) : Point := do
  let cosθ := cos θ
  let sinθ := sin θ
  ⟨p.x * cosθ - p.y * sinθ, p.x * sinθ + p.y * cosθ⟩

-- 測試
#eval Point.distance (Point.mk 0 0) (Point.mk 3 4)
#eval Point.distance (Point.mk 1 1) (Point.mk 4 5)