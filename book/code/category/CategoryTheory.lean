-- Category: 範疇論基礎
-- 展示範疇、函子、自然變換的定義

class Category (C : Type) where
  Hom : C → C → Type
  id : ∀ x : C, Hom x x
  compose : ∀ {x y z : C}, Hom y z → Hom x y → Hom x z
  idLeft : ∀ {x y : C} (f : Hom x y), compose (id y) f = f
  idRight : ∀ {x y : C} (f : Hom x y), compose f (id x) = f
  assoc : ∀ {w x y z} (f : Hom w x) (g : Hom x y) (h : Hom y z),
    compose h (compose g f) = compose (compose h g) f

infixr:80 " ⟶ " => Category.Hom
infixr:60 " ≫ " => Category.compose

namespace Category

-- 集合範疇
instance : Category Type where
  Hom := fun A B => A → B
  id := fun x => x
  compose := fun g f x => g (f x)
  idLeft := by intros; rfl
  idRight := by intros; rfl
  assoc := by intros; rfl

-- 群範疇
def GroupHom (G H : Type) [Group G] [Group H] := G → H

instance [Group G] [Group H] : Category (FinGroup G H) where
  sorry

-- 預序範疇
class Preorder (α : Type) where
  le : α → α → Prop
  refl : ∀ a, le a a
  trans : ∀ a b c, le a b → le b c → le a c

instance [Preorder α] : Category α where
  Hom := fun a b => {f : Unit // Preorder.le a b}
  id := fun a => ⟨(), Preorder.refl a⟩
  compose := fun _ _ _ => ⟨(), Preorder.trans _ _ _⟩

-- 離散範疇
def Discrete (α : Type) : Category α where
  Hom x y := if x = y then Unit else Empty
  id x := if h : x = x then ⟨()⟩ else nomatch h
  compose := by intros _ _ _; admit
  idLeft := by intros; admit
  idRight := by intros; admit
  assoc := by intros; admit

end Category

-- 函子
class Functor (C D : Type) [Category C] [Category D] where
  obj : C → D
  map : ∀ {x y : C}, (x ⟶ y) → (obj x ⟶ obj y)
  identity : ∀ x, map (Category.id x) = Category.id (obj x)
  compose : ∀ {x y z} (f : y ⟶ z) (g : x ⟶ y), map (f ≫ g) = map f ≫ map g

infixr:50 " →ᵐ " => Functor

namespace Functor

-- 遺忘函子
def forget [Category C] : C →ᵐ Type := {
  obj := fun c => c
  map := fun f => f
  identity := by rfl
  compose := by rfl
}

-- 常值函子
def const (C D : Type) [Category C] [Category D] (d : D) : C →ᵐ D := {
  obj := fun _ => d
  map := fun _ => Category.id d
  identity := by intros; exact (Category.idLeft (Category.id d)).symm
  compose := by intros; exact (Category.idLeft (Category.id d)).symm
}

end Functor

-- 自然變換
class NaturalTransformation {C D : Type} [Category C] [Category D]
  (F G : C →ᵐ D) where
  component : ∀ x, F.obj x ⟶ G.obj x
  naturality : ∀ {x y} (f : x ⟶ y), component y ≫ G.map f = F.map f ≫ component x

infixr:50 " ⟹ " => NaturalTransformation

-- 函子範疇
def FunctorCategory (C D : Type) [Category C] [Category D] : Type :=
  {F : C →ᵐ D // ∀ x y, F.map {x := x, y := y} = F.map}

-- 通用構造
def TerminalObject (C : Type) [Category C] : Type :=
  {t : C // ∀ c, ∃! f, f : c ⟶ t}

def InitialObject (C : Type) [Category C] : Type :=
  {i : C // ∀ c, ∃! f, f : i ⟶ c}

def Product {C : Type} [Category C] (a b : C) : Type :=
  {p : C // ∀ z, ∃! f, f : z ⟶ a × f : z ⟶ b}

def Coproduct {C : Type} [Category C] (a b : C) : Type :=
  {c : C // ∀ z, ∃! f, f : a ⟶ c × f : b ⟶ c}

-- 米田引理（Yoneda Lemma）的陳述
theorem yoneda {C : Type} [Category C] (F : C →ᵐ Type) (c : C) :
  (c ⟶ _) ≅ F.obj c := by
  admit

end