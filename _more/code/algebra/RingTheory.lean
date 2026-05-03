-- Algebra: 環論
-- 展示環的基本定義與性質

class Ring (α : Type) where
  add : α → α → α
  mul : α → α → α
  zero : α
  one : α
  neg : α → α
  addAssoc : ∀ a b c : α, add (add a b) c = add a (add b c)
  addComm : ∀ a b : α, add a b = add b a
  zeroAdd : ∀ a : α, add zero a = a
  addZero : ∀ a : α, add a zero = a
  negAdd : ∀ a : α, add (neg a) a = zero
  mulAssoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)
  oneMul : ∀ a : α, mul one a = a
  mulOne : ∀ a : α, mul a one = a
  mulAddDist : ∀ a b c : α, mul a (add b c) = add (mul a b) (mul a c)
  addMulDist : ∀ a b c : α, mul (add a b) c = add (mul a c) (mul b c)

namespace Ring

def sub (α : Type) [Ring α] (a b : α) : α :=
  add a (neg b)

theorem addNeg (α : Type) [Ring α] (a : α) : a + (-a) = 0 := by
  sorry

theorem subAdd (α : Type) [Ring α] (a b : α) : (a - b) + b = a := by
  sorry

end Ring

instance : Ring Int where
  add := Int.add
  mul := Int.mul
  zero := 0
  one := 1
  neg := Int.neg
  addAssoc := Int.add_assoc
  addComm := Int.add_comm
  zeroAdd := Int.zero_add
  addZero := Int.add_zero
  negAdd := Int.add_neg_cancel_left
  mulAssoc := Int.mul_assoc
  oneMul := Int.mul_one
  mulOne := Int.one_mul
  mulAddDist := Int.mul_add_distrib_left
  addMulDist := Int.add_mul_distrib_left

#check Ring
#check Ring.add
#check Ring.mul

example : Ring Int := inferInstance