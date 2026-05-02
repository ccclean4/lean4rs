-- Algebra: 環論基礎
-- 展示環、整域、場的定義與性質

class Ring (α : Type) where
  add : α → α → α
  zero : α
  neg : α → α
  mul : α → α → α
  one : α
  addAssoc : ∀ a b c, add (add a b) c = add a (add b c)
  zeroAdd : ∀ a, add zero a = a
  negAdd : ∀ a, add (neg a) a = zero
  addComm : ∀ a b, add a b = add b a
  mulAssoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mulOne : ∀ a, mul one a = a
  oneMul : ∀ a, mul a one = a
  leftDist : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  rightDist : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)

class CommRing (α : Type) extends Ring α where
  mulComm : ∀ a b, mul a b = mul b a

class IntegralDomain (α : Type) extends CommRing α where
  noZeroDivisors : ∀ a b, mul a b = zero → a = zero ∨ b = zero

class Field (α : Type) extends IntegralDomain α where
  inv : α → α
  mulInv : ∀ a, a ≠ zero → mul a (inv a) = one

-- 整數是交換環
instance : Ring Int where
  add := Int.add
  zero := 0
  neg := Int.neg
  mul := Int.mul
  one := 1
  addAssoc := Int.add_assoc
  zeroAdd := Int.zero_add
  negAdd := Int.add_neg_cancel_left
  addComm := Int.add_comm
  mulAssoc := Int.mul_assoc
  mulOne := Int.mul_one
  oneMul := Int.one_mul
  leftDist := Int.mul_add
  rightDist := Int.add_mul

instance : CommRing Int := {}
instance : IntegralDomain Int := {}
instance (a b : Int) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 := Int.mul_ne_zero

-- 有理數是場
instance : Field Rat where
  add := Rat.add
  zero := 0
  neg := Rat.neg
  mul := Rat.mul
  one := 1
  inv := Rat.inv
  addAssoc := Rat.add_assoc
  zeroAdd := Rat.zero_add
  negAdd := by simp [Rat.add_neg_cancel]
  addComm := Rat.add_comm
  mulAssoc := Rat.mul_assoc
  mulOne := Rat.mul_one
  oneMul := Rat.one_mul
  leftDist := Rat.mul_add
  rightDist := Rat.add_mul
  mulComm := Rat.mul_comm
  noZeroDivisors := by simp [Rat.mul_ne_zero]
  mulInv := Rat.mul_inv_cancel

-- 環的基本性質
theorem ring_unique_zero {α : Type} [Ring α] (z : α) (h : ∀ a, add z a = a) : z = Ring.zero α := by
  calc
    z = add z zero := (Ring.zeroAdd z).symm
      _ = zero := h zero

theorem ring_unique_one {α : Type} [Ring α] (u : α) (h : ∀ a, mul u a = a) : u = Ring.one α := by
  calc
    u = mul u one := (Ring.mulOne u).symm
      _ = one := h one

theorem ring_neg_unique {α : Type} [Ring α] (a b : α) (h : add a b = zero) : b = neg a := by
  calc
    b = add zero b := (Ring.zeroAdd b).symm
      _ = add (add (neg a) a) b := by rw [Ring.negAdd]
      _ = add (neg a) (add a b) := Ring.addAssoc (neg a) a b
      _ = add (neg a) zero := by rw [h]
      _ = neg a := Ring.zeroAdd (neg a)

-- 場中 a / a = 1 (a ≠ 0)
theorem field_div_eq_one {α : Type} [Field α] (a : α) (ha : a ≠ zero) : mul a (inv a ha) = one := by
  apply Field.mulInv

-- (a + b)(a - b) = a² - b²
theorem ring_sq_diff {α : Type} [CommRing α] (a b : α) :
  mul (add a b) (add a (neg b)) = add (mul a a) (neg (mul b b)) := by
  calc
    mul (add a b) (add a (neg b))
      = add (mul a a) (mul a (neg b)) ⊕ add (mul b a) (mul b (neg b)) := by sorry
    -- 簡化版本
    sorry

end