-- Logic: 命題邏輯
-- 展示命題邏輯的語法與語義

inductive Prop : Type
  | var : String → Prop
  | true : Prop
  | false : Prop
  | and : Prop → Prop → Prop
  | or : Prop → Prop → Prop
  | implies : Prop → Prop → Prop
  | not : Prop → Prop

namespace Prop

def not (p : Prop) : Prop := Prop.not p

def iff (p q : Prop) : Prop := Prop.and (Prop.implies p q) (Prop.implies q p)

-- 賦值（解釋）
def Assignment := String → Bool

def eval (γ : Assignment) : Prop → Bool
  | .var x => γ x
  | .true => true
  | .false => false
  | .and p q => eval γ p && eval γ q
  | .or p q => eval γ p || eval γ q
  | .implies p q => !eval γ p || eval γ q
  | .not p => !eval γ p

def sat (p : Prop) : Prop := ∃ γ, eval γ p = true

def unsat (p : Prop) : Prop := ∀ γ, eval γ p = false

def valid (p : Prop) : Prop := ∀ γ, eval γ p = true

-- 語義後承
def entails (Γ : List Prop) (p : Prop) : Prop := ∀ γ,
  (∀ q ∈ Γ, eval γ q = true) → eval γ p = true

-- 重言式
def tautology (p : Prop) : Prop := valid p

-- 矛盾式
def contradiction (p : Prop) : Prop := unsat p

-- 可滿足時，返回一個滿足賦值
def satisfyingAssignment (p : Prop) (h : sat p) : Assignment := by
  admit

-- 範例
def p := Prop.var "p"
def q := Prop.var "q"
def r := Prop.var "r"

def example1 : Prop := Prop.and p q
def example2 : Prop := Prop.or p (Prop.not p)
def example3 : Prop := Prop.implies (Prop.and p q) p
def example4 : Prop := Prop.not (Prop.or p q)

-- 測試
#check example1
#check example2
#check example3
#check example4

end Prop