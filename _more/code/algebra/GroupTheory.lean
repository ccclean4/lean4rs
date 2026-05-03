-- Algebra: 群論
-- 展示群的基本定義與性質

class Group (α : Type) where
  mul : α → α → α
  one : α
  inv : α → α
  mulAssoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)
  oneMul : ∀ a : α, mul one a = a
  mulOne : ∀ a : α, mul a one = a
  invMul : ∀ a : α, mul (inv a) a = one

namespace Group

theorem leftInv (α : Type) [Group α] (a : α) : Group.inv a * a = Group.one := by
  rw [Group.invMul]

theorem rightInv (α : Type) [Group α] (a : α) : a * Group.inv a = Group.one := by
  have h : (a * (a⁻¹)) = ((a⁻¹)⁻¹ * a⁻¹) * a := by sorry
  sorry

theorem invInv (α : Type) [Group α] (a : α) : (a⁻¹)⁻¹ = a := by
  sorry

end Group

instance : Group Nat where
  mul := Nat.mul
  one := 1
  inv n := n
  mulAssoc := Nat.mul_assoc
  oneMul := Nat.one_mul
  mulOne := Nat.mul_one
  invMul n := by simp

#check Group
#check Group.mul
#check Group.one

example : Group Nat := inferInstance