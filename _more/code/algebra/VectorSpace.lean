-- Algebra: 向量空間
-- 展示向量空間的定義與基本性質

class VectorSpace (K : Type) (V : Type) [Field K] where
  add : V → V → V
  zero : V
  neg : V → V
  smul : K → V → V
  addAssoc : ∀ u v w, add (add u v) w = add u (add v w)
  zeroAdd : ∀ v, add zero v = v
  negAdd : ∀ v, add (neg v) v = zero
  addComm : ∀ u v, add u v = add v u
  smulAssoc : ∀ a b v, smul (mul a b) v = smul a (smul b v)
  smulOne : ∀ v, smul one v = v
  leftDist : ∀ a u v, smul a (add u v) = add (smul a u) (smul a v)
  rightDist : ∀ a b v, smul (add a b) v = add (smul a v) (smul b v)

infixr:50 " ⊕ " => VectorSpace.add
notation:75 "∥v∥" => VectorSpace.smul

-- K-向量的類型
structure Vec (K : Type) (n : Nat) : Type where
  coords : List K
  length_ok : coords.length = n

def Vec.add {K : Type} [Field K] {n : Nat} (u v : Vec K n) : Vec K n :=
  ⟨List.zipWith Field.add u.coords v.coords, by simp⟩

def Vec.smul {K : Type} [Field K] {n : Nat} (a : K) (v : Vec K n) : Vec K n :=
  ⟨List.map (Field.mul a) v.coords, by simp⟩

def Vec.zero {K : Type} [Field K] {n : Nat} : Vec K n :=
  ⟨List.replicate n K.zero, by simp⟩

def Vec.neg {K : Type} [Field K] {n : Nat} (v : Vec K n) : Vec K n :=
  ⟨List.map Field.neg v.coords, by simp⟩

-- 標準基底向量
def stdBasis {K : Type} [Field K] {n : Nat} (i : Nat) (hi : i < n) : Vec K n := by
  sorry

-- 點積
def dotProduct {K : Type} [Field K] {n : Nat} (u v : Vec K n) : K :=
  List.foldl (· + ·) K.zero (List.zipWith Field.mul u.coords v.coords)

-- 向量範數（歐氏範數）
def norm {K : Type} [Field K] {n : Nat} (v : Vec K n) : K :=
  sqrt (dotProduct v v)

-- 線性組合
def linearCombination {K : Type} [Field K] {n : Nat}
  (cs : List K) (vs : List (Vec K n)) (h : cs.length = vs.length) : Vec K n := by
  sorry

-- 線性相關
def linearlyDependent {K : Type} [Field K] {n : Nat} (vs : List (Vec K n)) : Prop :=
  ∃ (cs : List K) (h : cs ≠ []) (hc : cs.length = vs.length),
    linearCombination cs vs h = Vec.zero ∧ cs ≠ List.replicate vs.length K.zero

-- 正交性
def orthogonal {K : Type} [Field K] {n : Nat} (u v : Vec K n) : Prop :=
  dotProduct u v = K.zero

-- 正交補空間
def orthogonalComplement {K : Type} [Field K] {n : Nat}
  (S : List (Vec K n)) : List (Vec K n) :=
  List.filter (fun v => ∀ s ∈ S, orthogonal v s) (standardOnb n)

end