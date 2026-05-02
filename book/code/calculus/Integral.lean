-- Calculus: 積分
-- 定積分與不定積分

structure Partition (a b : Float) (n : Nat) where
  points : List Float
  valid : points.length = n + 1
  start : points[0] = a
  end : points[n] = b
  increasing : ∀ i < n, points[i] < points[i+1]

def Partition.mesh (p : Partition a b n) : Float :=
  match p.points with
  | [] => 0
  | x :: xs =>
    let widths := List.zipWith (· - ·) xs p.points
    List.foldl max 0 widths

def Partition.tagged (p : Partition a b n) : List (Float × Float) :=
  match p.points with
  | [] => []
  | [x] => []
  | x :: xs =>
    let widths := List.zipWith (· - ·) xs (x :: List.dropLast xs)
    List.zip widths (List.dropLast p.points)

def RiemannSum (f : Float → Float) (p : Partition a b n) : Float :=
  let tagged := p.tagged
  List.foldl (· + ·) 0 (tagged.map (fun (dx, ξ) => f ξ * dx))

def integrable (f : Float → Float) (a b : Float) : Prop :=
  ∃ L, ∀ ε > 0, ∃ δ > 0, ∀ p, p.partition a b → p.mesh < δ →
    abs (RiemannSum f p - L) < ε

def definiteIntegral (f : Float → Float) (a b : Float) (h : integrable f a b) : Float :=
  Classical.choose h

-- 不定積分（原始函數）
def antiderivative (f F : Float → Float) : Prop :=
  ∀ x, hasDerivative F x (f x)

-- 基本積分表
theorem integral_const (c : Float) (a b : Float) : integrable (fun _ => c) a b := by
  use c * (b - a)
  intros ε hε
  use (ε / (abs c + 1)).sqrt
  intros p hp
  have := calc
    abs (RiemannSum (fun _ => c) p - c * (b - a))
      = abs (c * (p.points.back - p.points.front) - c * (b - a)) := by sorry
  exact this

theorem integral_linearity (f g : Float → Float) (a b : Float)
  (hf : integrable f a b) (hg : integrable g a b) :
  integrable (fun x => f x + g x) a b := by
  sorry

theorem integral_bounds (f : Float → Float) (a b c : Float)
  (hab : integrable f a b) (hbc : integrable f b c) :
  integrable f a c := by
  sorry

-- 微積分基本定理
theorem fundamentalTheorem (f : Float → Float) (F : Float → Float)
  (hF : antiderivative f F) (a b : Float) : integrable f a b := by
  exists F b - F a
  intros ε hε
  use ε / 2
  intros p hp
  sorry

-- 指數函數與對數函數
def exp (x : Float) : Float := Float.exp x

def ln (x : Float) : Float := Float.log x

theorem derivative_exp (x : Float) : hasDerivative exp x (exp x) := by
  intros ε hε
  use 1
  intros h hh
  sorry

theorem integral_exp (a b : Float) : integrable exp a b := by
  use exp b - exp a
  intros ε hε
  sorry

-- 常用積分公式
theorem integral_x_pow (n : Nat) (a b : Float) (ha : a ≥ 0 ∨ n > 0) :
  integrable (fun x => x^n) a b := by
  use (b^(n+1) - a^(n+1)) / (n + 1)
  intros ε hε
  sorry

end