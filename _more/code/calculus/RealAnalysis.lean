-- Calculus: 實數序列與極限
-- 展示序列的極限收斂性證明

structure Sequence where
  term : Nat → Float

def Sequence.limit (a : Sequence) (L : Float) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (a.term n - L) < ε

def Sequence.converges (a : Sequence) : Prop :=
  ∃ L, limit a L

def Sequence.bounded (a : Sequence) : Prop :=
  ∃ M, ∀ n, abs (a.term n) ≤ M

def Sequence.monotone (a : Sequence) : Prop :=
  ∀ n, a.term n ≤ a.term (n + 1)

def Sequence.strictlyIncreasing (a : Sequence) : Prop :=
  ∀ n, a.term n < a.term (n + 1)

-- 極限的唯一性
theorem limit_unique (a : Sequence) (L1 L2 : Float)
  (h1 : limit a L1) (h2 : limit a L2) : L1 = L2 := by
  intros ε hε
  have := h1 (ε / 2) (by linarith)
  have := h2 (ε / 2) (by linarith)
  obtain ⟨N1, hN1⟩ := this
  obtain ⟨N2, hN2⟩ := this
  let N := max N1 N2
  have := abs_triangle (a.term N - L1) (L1 - L2) (a.term N - L2)
  have := calc
    abs (L1 - L2) = abs ((a.term N - L2) - (a.term N - L1)) := by ring
      _ ≤ abs (a.term N - L2) + abs (a.term N - L1) := abs_triangle _ _ _
      _ < ε / 2 + ε / 2 := by linarith [hN1 N (le_max_left _ _), hN2 N (le_max_right _ _)]
      _ = ε := by ring
  have ε_pos : ε > 0 := hε
  have abs (L1 - L2) < ε := this
  exact Float.noconfusion (by linarith)

-- 收斂序列有界
theorem converges_bounded (a : Sequence) (h : converges a) : bounded a := by
  obtain ⟨L, hL⟩ := h
  have := hL 1 (by linarith)
  obtain ⟨N, hN⟩ := this
  use max (max L 1) (List.max (List.map (fun n => abs (a.term n)) (List.range N)))
  intros n
  cases (Nat.lt_or_ge n N) with
  | inl hn => sorry
  | inr hn => sorry

-- 單調有界序列收斂（實數完备性）
theorem monotone_converges (a : Sequence)
  (hm : monotone a) (hb : bounded a) : converges a := by
  let L := sup (Set.range a.term)
  exists L
  intros ε hε
  sorry

-- 常見序列
def seq_constant (c : Float) : Sequence := ⟨fun _ => c⟩

def seq_linear (a : Float) : Sequence := ⟨fun n => a * n⟩

def seq_geometric (r : Float) : Sequence := ⟨fun n => r^n⟩

def seq_harmonic : Sequence := ⟨fun n => 1 / (n + 1)⟩

def seq_factorial_inv : Sequence := ⟨fun n => 1 / Float.factorial (n + 1)⟩

-- 極限計算
theorem limit_constant (c : Float) : limit (seq_constant c) c := by
  intros ε hε
  use 0
  intros n hn
  simp [seq_constant, Sequence.term]
  exact hε

theorem limit_harmonic : limit seq_harmonic 0 := by
  intros ε hε
  use (1 / ε).toNat + 1
  intros n hn
  have : n ≥ (1 / ε).toNat := by linarith
  have : 1 / (n + 1) ≤ 1 / n := by sorry
  have : 1 / n < ε := by sorry
  sorry

end