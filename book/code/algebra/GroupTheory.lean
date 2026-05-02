-- Algebra: 群論基礎
-- 展示群的定義與基本性質

class Magma (α : Type) where
  mul : α → α → α

class Semigroup (α : Type) extends Magma α where
  assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

class Monoid (α : Type) extends Semigroup α where
  one : α
  one_left : ∀ a, mul one a = a
  one_right : ∀ a, mul a one = a

class Group (α : Type) extends Monoid α where
  inv : α → α
  inv_left : ∀ a, mul (inv a) a = one
  inv_right : ∀ a, mul a (inv a) = one

class AbelianGroup (α : Type) extends Group α where
  comm : ∀ a b, mul a b = mul b a

-- 群的例子：整數加法
instance : Magma Int where mul := Int.add
instance : Semigroup Int where assoc := Int.add_assoc
instance : Monoid Int where one := 0
instance : Group Int where inv := Int.neg
instance : AbelianGroup Int where comm := Int.add_comm

-- 群的例子：模 n 剩餘類
def Zmod (n : Nat) := {x : Nat // x < n}

def Zmod.add {n : Nat} (a b : Zmod n) : Zmod n :=
  ⟨(a.val + b.val) % n, Nat.mod_lt _ (Nat.zero_lt_succ n)⟩

def Zmod.zero {n : Nat} : Zmod n := ⟨0, Nat.zero_lt_succ n⟩

def Zmod.neg {n : Nat} (a : Zmod n) : Zmod n :=
  ⟨(n - a.val) % n, Nat.mod_lt _ (Nat.zero_lt_succ n)⟩

-- 群的基本性質
theorem group_unique_inv {α : Type} [Group α] (a : α) (x y : α)
  (hx : mul x a = one) (hy : mul a y = one) : x = y := by
  calc
    x = mul x one := (one_right x).symm
      _ = mul x (mul a y) := by rw [hy]
      _ = mul (mul x a) y := (assoc x a y).symm
      _ = mul one y := by rw [hx]
      _ = y := one_left y

theorem group_cancel_left {α : Type} [Group α] (a b c : α) (h : mul a b = mul a c) : b = c := by
  have ha : mul (inv a) (mul a b) = mul (inv a) (mul a c) := congrArg (mul (inv a)) h
  calc
    b = mul one b := (one_left b).symm
      _ = mul (mul (inv a) a) b := by rw [inv_left]
      _ = mul (inv a) (mul a b) := assoc (inv a) a b
    _ = mul (inv a) (mul a c) := by rw [ha]
      _ = mul (mul (inv a) a) c := (assoc (inv a) a c).symm
      _ = mul one c := by rw [inv_left]
      _ = c := one_left c

-- 群同態
def isHomomorphism {α β : Type} [Group α] [Group β] (f : α → β) : Prop :=
  ∀ a b, f (mul a b) = mul (f a) (f b)

def isIsomorphism {α β : Type} [Group α] [Group β] (f : α → β) : Prop :=
  isHomomorphism f ∧ ∃ g, isHomomorphism g ∧ ∀ a, f (g a) = a ∧ g (f a) = a

-- 凱萊定理：每個有限群是置換群的子群
-- （略，這需要置換群的定義）