-- Proofs: 布爾代數系統 (Boolean Algebra)
-- 展示布爾代數的公理化定義與性質證明

inductive MyBool : Type
  | false : MyBool
  | true : MyBool

namespace MyBool

def and : MyBool → MyBool → MyBool
  | .true, b => b
  | .false, _ => .false

def or : MyBool → MyBool → MyBool
  | .true, _ => .true
  | .false, b => b

def not : MyBool → MyBool
  | .true => .false
  | .false => .true

def xor : MyBool → MyBool → MyBool
  | .true, .true => .false
  | .false, .false => .false
  | _, _ => .true

def implies : MyBool → MyBool → MyBool
  | .true, .false => .false
  | _, _ => .true

theorem andTrueId (b : MyBool) : and .true b = b := by
  cases b with
  | true => rfl
  | false => rfl

theorem andFalseAbsorb (b : MyBool) : and .false b = .false := rfl

theorem orTrueAbsorb (b : MyBool) : or .true b = .true := rfl

theorem orFalseId (b : MyBool) : or .false b = b := by
  cases b with
  | true => rfl
  | false => rfl

theorem andComm (a b : MyBool) : and a b = and b a := by
  cases a with
  | true => cases b with | true => rfl | false => rfl
  | false => cases b with | true => rfl | false => rfl

theorem orComm (a b : MyBool) : or a b = or b a := by
  cases a with
  | true => cases b with | true => rfl | false => rfl
  | false => cases b with | true => rfl | false => rfl

theorem andAssoc (a b c : MyBool) : and (and a b) c = and a (and b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem orAssoc (a b c : MyBool) : or (or a b) c = or a (or b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem andOrDist (a b c : MyBool) : and a (or b c) = or (and a b) (and a c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem orAndDist (a b c : MyBool) : or a (and b c) = and (or a b) (or a c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem doubleNegation (b : MyBool) : not (not b) = b := by
  cases b <;> rfl

theorem contrapositive (a b : MyBool) : implies a b = implies (not b) (not a) := by
  cases a <;> cases b <;> rfl

-- 注意: (a → b) → (b → c) = a → c 在布爾代數中不成立
-- theorem impliesTrans (a b c : MyBool) : implies (implies a b) (implies b c) = implies a c

theorem xorDef (a b : MyBool) : xor a b = and (or a b) (not (and a b)) := by
  cases a <;> cases b <;> rfl

end MyBool