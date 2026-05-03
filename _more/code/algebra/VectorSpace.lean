-- Algebra: 向量空間
-- 展示向量空間的基本定義與性質

class VectorSpace (α : Type) [Field α] where
  add : α → α → α
  zero : α
  neg : α → α
  smul : α → α → α
  one : α
  addAssoc : ∀ u v w : α, add (add u v) w = add u (add v w)
  addComm : ∀ u v : α, add u v = add v u
  zeroAdd : ∀ u : α, add zero u = u
  addZero : ∀ u : α, add u zero = u
  negAdd : ∀ u : α, add (neg u) u = zero
  smulDist : ∀ r s u : α, smul (r * s) u = smul r (smul s u)
  smulOne : ∀ u : α, smul one u = u
  smulAddDist : ∀ r u v : α, smul r (add u v) = add (smul r u) (smul r v)
  addSmulDist : ∀ r s u : α, smul (r + s) u = add (smul r u) (smul s u)

class Field (α : Type) where
  add : α → α → α
  mul : α → α → α
  zero : α
  one : α
  neg : α → α
  inv : α → α
  addAssoc : ∀ a b c : α, add (add a b) c = add a (add b c)
  addComm : ∀ a b : α, add a b = add b a
  zeroAdd : ∀ a : α, add zero a = a
  negAdd : ∀ a : α, add (neg a) a = zero
  mulAssoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)
  mulComm : ∀ a b : α, mul a b = mul b a
  oneMul : ∀ a : α, mul one a = a
  mulInv : ∀ a : α, a ≠ zero → mul a (inv a) = one
  mulAddDist : ∀ a b c : α, mul a (add b c) = add (mul a b) (mul a c)

namespace Field

def sub (α : Type) [Field α] (a b : α) : α :=
  add a (neg b)

def div (α : Type) [Field α] (a b : α) : α :=
  mul a (inv b)

end Field

instance : Field Float where
  add := Float.add
  mul := Float.mul
  zero := 0.0
  one := 1.0
  neg := Float.neg
  inv a := 1.0 / a
  addAssoc := Float.add_assoc
  addComm := Float.add_comm
  zeroAdd := Float.zero_add
  negAdd := Float.add_neg_cancel
  mulAssoc := Float.mul_assoc
  mulComm := Float.mul_comm
  oneMul := Float.one_mul
  mulInv _ := Float.div_mul_cancel
  mulAddDist := Float.mul_add_distrib_left

#check Field
#check VectorSpace

example : Field Float := inferInstance