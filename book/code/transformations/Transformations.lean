-- Transformations: 幾何變換
-- 展示平面幾何的剛體變換與仿射變換

structure Point2D where
  x : Float
  y : Float
  deriving Repr

structure Vector2D where
  dx : Float
  dy : Float
  deriving Repr

structure Matrix2D where
  a11 : Float
  a12 : Float
  a21 : Float
  a22 : Float
  deriving Repr

namespace Point2D

def origin : Point2D := ⟨0, 0⟩

def add (p : Point2D) (v : Vector2D) : Point2D := ⟨p.x + v.dx, p.y + v.dy⟩

def sub (p q : Point2D) : Vector2D := ⟨p.x - q.x, p.y - q.y⟩

def distance (p q : Point2D) : Float := do
  let v := p - q
  Float.sqrt (v.dx^2 + v.dy^2)

end Point2D

namespace Vector2D

def zero : Vector2D := ⟨0, 0⟩

def add (u v : Vector2D) : Vector2D := ⟨u.dx + v.dx, u.dy + v.dy⟩

def sub (u v : Vector2D) : Vector2D := ⟨u.dx - v.dx, u.dy - v.dy⟩

def scale (v : Vector2D) (s : Float) : Vector2D := ⟨v.dx * s, v.dy * s⟩

def dot (u v : Vector2D) : Float := u.dx * v.dx + u.dy * v.dy

def cross (u v : Vector2D) : Float := u.dx * v.dy - u.dy * v.dx

def norm (v : Vector2D) : Float := Float.sqrt (v.dot v)

def normalize (v : Vector2D) : Vector2D := do
  let n := v.norm
  if n > 0 then v.scale (1 / n) else v

end Vector2D

namespace Matrix2D

def identity : Matrix2D := ⟨1, 0, 0, 1⟩

def mul (A B : Matrix2D) : Matrix2D := ⟨
  A.a11 * B.a11 + A.a12 * B.a21,
  A.a11 * B.a12 + A.a12 * B.a22,
  A.a21 * B.a11 + A.a22 * B.a21,
  A.a21 * B.a12 + A.a22 * B.a22
⟩

def apply (M : Matrix2D) (v : Vector2D) : Vector2D := ⟨
  M.a11 * v.dx + M.a12 * v.dy,
  M.a21 * v.dx + M.a22 * v.dy
⟩

end Matrix2D

inductive Transformation where
  | rigid : Matrix2D → Vector2D → Transformation
  | affine : Matrix2D → Vector2D → Transformation

def Transformation.apply (T : Transformation) (p : Point2D) : Point2D := do
  match T with
  | .rigid M v => Point2D.add (Point2D.origin.add (Matrix2D.apply M (p - Point2D.origin))) v
  | .affine M v => Point2D.add (Point2D.origin.add (Matrix2D.apply M (p - Point2D.origin))) v

def Transformation.translate (v : Vector2D) : Transformation := do
  .rigid Matrix2D.identity v

def Transformation.rotate (θ : Float) : Transformation := do
  let cosθ := Float.cos θ
  let sinθ := Float.sin θ
  .rigid ⟨cosθ, -sinθ, sinθ, cosθ⟩ Vector2D.zero

def Transformation.scale (s : Float) : Transformation := do
  .affine ⟨s, 0, 0, s⟩ Vector2D.zero

def Transformation.shear (kx ky : Float) : Transformation := do
  .affine ⟨1, kx, ky, 1⟩ Vector2D.zero

def Transformation.compose (T1 T2 : Transformation) : Transformation := do
  match T1, T2 with
  | .rigid M1 v1, .rigid M2 v2 => .rigid (M2.mul M1) (Matrix2D.apply M2 v1 + v2)
  | .rigid M1 v1, .affine M2 v2 => .affine (M2.mul M1) (Matrix2D.apply M2 v1 + v2)
  | .affine M1 v1, .rigid M2 v2 => .affine (M2.mul M1) (Matrix2D.apply M2 v1 + v2)
  | .affine M1 v1, .affine M2 v2 => .affine (M2.mul M1) (Matrix2D.apply M2 v1 + v2)

def Transformation.inverse (T : Transformation) : Transformation := do
  match T with
  | .rigid M v =>
    let Minv := ⟨M.a22, -M.a12, -M.a21, M.a11⟩  -- 假設正交矩陣
    .rigid Minv (Matrix2D.apply Minv (-v))
  | .affine M v =>
    .affine M v  -- 簡化版本

def Transformation.isometry (T : Transformation) : Bool := do
  match T with
  | .rigid M v =>
    let c1 := Vector2D ⟨M.a11, M.a21⟩
    let c2 := Vector2D ⟨M.a12, M.a22⟩
    (c1.norm ≈ 1) ∧ (c2.norm ≈ 1) ∧ (c1.dot c2 ≈ 0)
  | .affine _ _ => false

structure Frame where
  origin : Point2D
  e1 : Vector2D
  e2 : Vector2D

def Frame.changeCoordinates (F : Frame) (p : Point2D) : Float × Float := do
  let v := p - F.origin
  let x := v.dot F.e1
  let y := v.dot F.e2
  (x, y)

def Frame.toGlobal (F : Frame) (local : Float × Float) : Point2D := do
  let (x, y) := local
  F.origin.add (F.e1.scale x).add (F.e2.scale y)

end