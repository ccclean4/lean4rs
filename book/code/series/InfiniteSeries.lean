-- Series: 無限級數
-- 展示收斂級數、冪級數與傅立葉級數

structure Series where
  term : Nat → Float

def Series.sum (s : Series) (n : Nat) : Float :=
  List.sum (List.take n (List.map s.term (List.range n)))

def Series.partialSums (s : Series) : List Float :=
  List.scanl (· + ·) 0 (List.map s.term (List.range ∞))

def Series.converges (s : Series) (L : Float) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s.sum n - L) < ε

def Series.convergesAbsolutely (s : Series) : Prop :=
  Series.converges s (fun n => abs (s.term n)) 0

-- 幾何級數
def geometricSeries (r : Float) : Series := ⟨fun n => r^n⟩

theorem geometricSeriesSum (r : Float) (h : abs r < 1) (n : Nat) :
  geometricSeries r |>.sum n = (1 - r^n) / (1 - r) := by
  induction n with
  | zero => simp [geometricSeries, Series.sum]
  | succ n ih =>
    calc
      geometricSeries r |>.sum (n + 1)
        = geometricSeries r |>.sum n + r^(n+1) := by simp [Series.sum]
        _ = (1 - r^n) / (1 - r) + r^(n+1) := by rw [ih]
        _ = (1 - r^(n+1)) / (1 - r) := by ring

-- p-級數
def pSeries (p : Float) : Series := ⟨fun n => 1 / (n+1)^p⟩

theorem pSeriesConverges (p : Float) (h : p > 1) : converges (pSeries p) := by
  sorry

-- 交錯級數
def alternatingSeries (s : Series) : Series := ⟨fun n => (-1)^n * s.term n⟩

theorem alternatingSeriesTest (s : Series)
  (h1 : ∀ n, s.term n ≥ 0)
  (h2 : ∀ n, s.term (n+1) ≤ s.term n)
  (h3 : limit (Series.mk s.term) 0) :
  converges (alternatingSeries s) := by
  sorry

-- 冪級數
structure PowerSeries where
  coefficients : List Float

def PowerSeries.evaluate (ps : PowerSeries) (x : Float) (n : Nat) : Float :=
  List.sum (List.take n (List.mapIdx (fun k a => a * x^k) ps.coefficients))

def PowerSeries.radiusOfConvergence (ps : PowerSeries) : Float := by
  admit

-- 常見冪級數
def expSeries : PowerSeries := ⟨List.replicate ∞ 1⟩
def sinSeries : PowerSeries := ⟨fun i => if i % 2 = 0 then 0 else (-1)^(i/2) / Float.factorial i⟩
def cosSeries : PowerSeries := ⟨fun i => if i % 2 = 1 then 0 else (-1)^(i/2) / Float.factorial i⟩

-- 傅立葉級數
structure FourierCoefficients where
  a0 : Float
  an : Nat → Float
  bn : Nat → Float

def FourierSeries.evaluate (fc : FourierCoefficients) (x : Float) (n : Nat) : Float :=
  let a0 := fc.a0 / 2
  let rec sum (acc : Float) (k : Nat) : Float :=
    if k > n then acc
    else
      let ak := fc.an k
      let bk := fc.bn k
      sum (acc + ak * Float.cos (k * x) + bk * Float.sin (k * x)) (k + 1)
  a0 + sum 0 1

-- 傅立葉收斂定理
theorem fourierConvergence (fc : FourierCoefficients) (f : Float → Float) :
  (∀ x, f x = FourierSeries.evaluate fc x ∞) ↔ f 連續 := by
  admit

-- 級數運算
def Series.add (s1 s2 : Series) : Series := ⟨fun n => s1.term n + s2.term n⟩

def Series.mul (s1 s2 : Series) : Series := ⟨fun n =>
  List.sum (List.mapIdx (fun k a => a * s2.term k) (List.take (n+1) (List.map s1.term (List.range (n+1)))))⟩

-- 比較審斂法
theorem comparisonTest (s1 s2 : Series)
  (h : ∀ n, abs (s1.term n) ≤ s2.term n)
  (hconv : converges (Series.mk s2.term)) :
  converges s1 := by
  sorry

-- 比值審斂法
theorem ratioTest (s : Series) (L : Float) :
  limit (Series.mk (fun n => abs (s.term (n+1) / s.term n))) L →
  (L < 1 → converges s) ∧ (L > 1 → diverges s) := by
  sorry

-- 根值審斂法
theorem rootTest (s : Series) (L : Float) :
  limit (Series.mk (fun n => abs (s.term n)^(1/n))) L →
  (L < 1 → converges s) ∧ (L > 1 → diverges s) := by
  sorry

end