# 10 - 數學結構：Group, Ring, Field

## 類別定義

```lean
-- 群 (Group)
class Group (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  leftIdent : ∀ a, mul one a = a
  leftInv : ∀ a, mul (inv a) a = one

-- 阿貝爾群 (Abelian Group)
class AbelianGroup (G : Type) extends Group G where
  comm : ∀ a b, mul a b = mul b a
```

## 環 (Ring)

```lean
class Ring (R : Type) where
  add : R → R → R
  zero : R
  neg : R → R
  mul : R → R → R
  one : R
  addAssoc : ∀ a b c, add (add a b) c = add a (add b c)
  addIdent : ∀ a, add zero a = a
  addInv : ∀ a, add (neg a) a = zero
  addComm : ∀ a b, add a b = add b a
  mulAssoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  leftDistrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  rightDistrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
  mulIdent : ∀ a, mul one a = a
```

## 場 (Field)

```lean
class Field (F : Type) extends Ring F where
  inv : F → F
  div : F → F → F
  invDef : ∀ a ≠ 0, mul a (inv a) = one
  divDef : ∀ a b ≠ 0, div a b = mul a (inv b)
  nonzero : 0 ≠ 1
```

## 實例：整數

```lean
instance : Group Int where
  mul := Int.mul
  one := 1
  inv := Int.neg
  assoc := Int.mul_assoc
  leftIdent := Int.one_mul
  leftInv := Int.mul_left_inv

instance : Ring Int := ...
```

## 性質證明

```lean
theorem groupCancelLeft {G : Type} [Group G] (a b c : G) : mul a b = mul a c → b = c := do
  let h : mul (inv a) (mul a b) = mul (inv a) (mul a c) := congrArg (mul (inv a)) h
  have := calc
    b = mul one b := (leftIdent b).symm
    _ = mul (mul (inv a) a) b := (leftInv a).symm ▸ rfl
    _ = mul (inv a) (mul a b) := (assoc (inv a) a b).symm
  this.trans h |>.trans (assoc _ _ _).symm ▸ (leftIdent c)
```

## 練習

1. 定義並實例化 `Monoid`
2. 證明群的逆元唯一性
3. 定義 `VectorSpace` 類別
4. 證明場中 `a / a = 1`（當 a ≠ 0）