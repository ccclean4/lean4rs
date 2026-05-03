-- Proofs: 布爾代數系統 (Boolean Algebra)
-- 展示布爾代數的公理化定義與性質證明

inductive Bool : Type
  | false : Bool
  | true : Bool

namespace Bool

def and : Bool → Bool → Bool
  | .true, b => b
  | .false, _ => .false

def or : Bool → Bool → Bool
  | .true, _ => .true
  | .false, b => b

def not : Bool → Bool
  | .true => .false
  | .false => .true

def xor : Bool → Bool → Bool
  | .true, .true => .false
  | .false, .false => .false
  | _, _ => .true

def implies : Bool → Bool → Bool
  | .true, .false => .false
  | _, _ => .true

theorem andTrueId (b : Bool) : and .true b = b := by
  cases b with
  | true => rfl
  | false => rfl

theorem andFalseAbsorb (b : Bool) : and .false b = .false := rfl

theorem orTrueAbsorb (b : Bool) : or .true b = .true := rfl

theorem orFalseId (b : Bool) : or .false b = b := by
  cases b with
  | true => rfl
  | false => rfl

theorem andComm (a b : Bool) : and a b = and b a := by
  cases a with
  | true => cases b with | true => rfl | false => rfl
  | false => cases b with | true => rfl | false => rfl

theorem orComm (a b : Bool) : or a b = or b a := by
  cases a with
  | true => cases b with | true => rfl | false => rfl
  | false => cases b with | true => rfl | false => rfl

theorem andAssoc (a b c : Bool) : and (and a b) c = and a (and b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem orAssoc (a b c : Bool) : or (or a b) c = or a (or b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem andOrDist (a b c : Bool) : and a (or b c) = or (and a b) (and a c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem orAndDist (a b c : Bool) : or a (and b c) = and (or a b) (or a c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem doubleNegation (b : Bool) : not (not b) = b := by
  cases b with
  | true => rfl
  | false => rfl

theorem contrapositive (a b : Bool) : implies a b = implies (not b) (not a) := by
  cases a <;> cases b <;> rfl

theorem impliesTrans (a b c : Bool) : implies (implies a b) (implies b c) = implies a c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem xorDef (a b : Bool) : xor a b = and (or a b) (not (and a b)) := by
  cases a <;> cases b <;> rfl

end Bool