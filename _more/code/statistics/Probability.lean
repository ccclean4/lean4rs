-- Statistics: 機率論基礎
-- 隨機變數、期望值、變異數

def SampleSpace (Ω : Type) := Ω

def Event (Ω : Type) := Ω → Prop

structure ProbabilitySpace where
  space : Type
  Pr : Event space → Float
  nonempty : ∃ ω : space, True
  measure_one : Pr (fun _ => True) = 1
  countable_additivity : ∀ (events : List (Event space)),
    (∀ i j, i ≠ j → Disjoint (events[i]) (events[j])) →
    Pr (Union events) = List.sum (events.map Pr)

def RandomVariable (Ω : Type) (P : ProbabilitySpace) (α : Type) :=
  Ω → α

def expectation {Ω : Type} {P : ProbabilitySpace} (X : RandomVariable Ω P Float) : Float :=
  sorry

def variance {Ω : Type} {P : ProbabilitySpace} (X : RandomVariable Ω P Float) : Float :=
  expectation (fun ω => (X ω - expectation X)^2)

def stdDev {Ω : Type} {P : ProbabilitySpace} (X : RandomVariable Ω P Float) : Float :=
  Float.sqrt (variance X)

-- 常見分布
inductive Bernoulli (p : Float) : Type
  | success : Bernoulli p
  | failure : Bernoulli p

def Bernoulli.mean (p : Float) : Float := p

def Bernoulli.variance (p : Float) : Float := p * (1 - p)

inductive Binomial (n : Nat) (p : Float) : Type

def Binomial.mean (n : Nat) (p : Float) : Float := n * p

def Binomial.variance (n : Nat) (p : Float) : Float := n * p * (1 - p)

inductive Poisson (λ : Float) : Type

def Poisson.mean (λ : Float) : Float := λ

def Poisson.variance (λ : Float) : Float := λ

-- 大數定律
theorem weakLawLargeNumbers {Ω : Type} {P : ProbabilitySpace}
  (X : Nat → RandomVariable Ω P Float)
  (iid : ∀ i, mean (X i) = μ ∧ variance (X i) = σ²)
  (ε : Float) (hε : ε > 0) :
  limit (fun n =>
    expectation (fun ω =>
      abs ((List.range n |>.map X)[n] - μ))) 0 := by
  sorry

-- 中央極限定理（敘述）
theorem centralLimitTheorem {Ω : Type} {P : ProbabilitySpace}
  (X : Nat → RandomVariable Ω P Float)
  (iid : ∀ i, mean (X i) = 0 ∧ variance (X i) = 1) :
  ∀ a b, a < b →
    limit (fun n =>
      probability (fun ω =>
        a ≤ (List.sum (List.take n (X ·))) / (Float.sqrt n) ∧
        (List.sum (List.take n (X ·))) / (Float.sqrt n) ≤ b))
    (Float.normalCDF b - Float.normalCDF a) := by
  sorry

-- 條件機率
def conditionalProbability {Ω : Type} {P : ProbabilitySpace}
  (A B : Event Ω) (hB : P B > 0) : Float :=
  P (fun ω => A ω ∧ B ω) / P B

-- 貝葉斯定理
theorem bayesTheorem {Ω : Type} {P : ProbabilitySpace}
  (A B : Event Ω) (hA : P A > 0) (hB : P B > 0) :
  conditionalProbability A B hB = conditionalProbability B A hA * P A / P B := by
  calc
    conditionalProbability A B hB
      = P (fun ω => A ω ∧ B ω) / P B := rfl
      _ = conditionalProbability B A hA * P A / P B := by sorry

end