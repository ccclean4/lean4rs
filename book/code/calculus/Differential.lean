-- Calculus: 微分
-- 導數的定義與微分法則

def DifferentiableAt (f : Float → Float) (x : Float) : Prop :=
  ∃ L, ∀ ε > 0, ∃ δ > 0, ∀ h, 0 < abs h ∧ abs h < δ →
    abs ((f (x + h) - f x) / h - L) < ε

def derivative (f : Float → Float) (x : Float) : Float → Prop := fun L =>
  ∀ ε > 0, ∃ δ > 0, ∀ h, 0 < abs h ∧ abs h < δ →
    abs ((f (x + h) - f x) / h - L) < ε

def hasDerivative (f : Float → Float) (x : Float) (L : Float) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ h, 0 < abs h ∧ abs h < δ →
    abs ((f (x + h) - f x) / h - L) < ε

-- 基本函數的導數
theorem derivative_const (c : Float) (x : Float) : hasDerivative (fun _ => c) x 0 := by
  intros ε hε
  use 1
  intros h hh
  calc
    abs (((fun _ => c) (x + h) - (fun _ => c) x) / h - 0)
      = abs (0 / h) := by simp
      = 0 := by simp
      < ε := hε

theorem derivative_id (x : Float) : hasDerivative (fun x => x) x 1 := by
  intros ε hε
  use 1
  intros h hh
  calc
    abs (((fun x => x) (x + h) - (fun x => x) x) / h - 1)
      = abs ((x + h - x) / h - 1) := by simp
      = abs (h / h - 1) := by simp
      = abs (1 - 1) := by simp
      = 0 := rfl
      < ε := hε

theorem derivative_pow (n : Nat) (x : Float) : hasDerivative (fun x => x^n) x (n : Float) * x^(n-1) := by
  sorry

-- 微分法則
theorem derivative_sum (f g : Float → Float) (x : Float) (Lf Lg : Float)
  (hf : hasDerivative f x Lf) (hg : hasDerivative g x Lg) :
  hasDerivative (fun x => f x + g x) x (Lf + Lg) := by
  intros ε hε
  have δ1 := hf (ε / 2) (by linarith)
  have δ2 := hg (ε / 2) (by linarith)
  use min δ1 δ2
  intros h hh
  have := calc
    abs (((fun x => f x + g x) (x + h) - (fun x => f x + g x) x) / h - (Lf + Lg))
      = abs ((f (x + h) - f x) / h - Lf + (g (x + h) - g x) / h - Lg) := by simp; ring
      _ ≤ abs ((f (x + h) - f x) / h - Lf) + abs ((g (x + h) - g x) / h - Lg) := abs_add _ _
  have := calc
    this < ε / 2 + ε / 2 := by linarith [hf (ε/2) (by linarith) h (by linarith), hg (ε/2) (by linarith) h (by linarith)]
    this = ε := by ring
  exact this

theorem derivative_product (f g : Float → Float) (x : Float) (Lf Lg : Float)
  (hf : hasDerivative f x Lf) (hg : hasDerivative g x Lg) :
  hasDerivative (fun x => f x * g x) x (Lf * g x + f x * Lg) := by
  sorry

theorem derivative_chain (f g : Float → Float) (x : Float) (Lf Lg : Float)
  (hf : hasDerivative f x Lf) (hg : hasDerivative g (f x) Lg) :
  hasDerivative (fun x => g (f x)) x (Lf * Lg) := by
  sorry

theorem derivative_inverse (f : Float → Float) (x : Float) (Lf : Float)
  (hf : hasDerivative f x Lf) (hLf : Lf ≠ 0) :
  hasDerivative (fun y => (f y - f x) / (y - x)) x (1 / Lf) := by
  sorry

-- 導數的應用
theorem stationary_point (f : Float → Float) (x : Float)
  (hf : hasDerivative f x 0) : x 是 f 的穩定點 := by
  exact Stationary

def isLocalMax (f : Float → Float) (x : Float) : Prop :=
  ∃ δ > 0, ∀ h, abs h < δ → f (x + h) ≤ f x

def isLocalMin (f : Float → Float) (x : Float) : Prop :=
  ∃ δ > 0, ∀ h, abs h < δ → f (x + h) ≥ f x

end