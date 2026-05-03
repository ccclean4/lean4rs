-- Logic: 謂詞邏輯
-- 展示一階謂詞邏輯的語法與推理

inductive Term : Type
  | var : String → Term
  | func : String → List Term → Term

inductive Formula : Type
  | pred : String → List Term → Formula
  | true : Formula
  | false : Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | implies : Formula → Formula → Formula
  | not : Formula → Formula
  | forall : String → Formula → Formula
  | exists : String → Formula → Formula

namespace Formula

def not (φ : Formula) : Formula := Formula.not φ

def exists (x : String) (φ : Formula) : Formula := Formula.exists x φ

def forall (x : String) (φ : Formula) : Formula := Formula.forall x φ

-- 自由變數
def freeVars : Term → List String
  | .var x => [x]
  | .func _ args => args >>= freeVars

def freeVarsFormula : Formula → List String
  | .pred _ args => args >>= freeVars
  | .true => []
  | .false => []
  | .and φ ψ => freeVarsFormula φ ∪ freeVarsFormula ψ
  | .or φ ψ => freeVarsFormula φ ∪ freeVarsFormula ψ
  | .implies φ ψ => freeVarsFormula φ ∪ freeVarsFormula ψ
  | .not φ => freeVarsFormula φ
  | .forall x φ => freeVarsFormula φ |>.erase x
  | .exists x φ => freeVarsFormula φ |>.erase x

-- 閉式（無自由變數）
def closed (φ : Formula) : Prop := freeVarsFormula φ = []

-- 代換
def substitute (φ : Formula) (x : String) (t : Term) : Formula := by
  sorry

-- 論域
structure Structure where
  domain : Type
  interpretations : String → (List Term → domain) → domain

-- 模型關係
inductive satisfies {M : Structure} (γ : String → M.domain) : Formula → Prop
  | true : satisfies Formula.true
  | pred {name args} : sorry → satisfies (Formula.pred name args)
  | and {φ ψ} : satisfies φ → satisfies ψ → satisfies (Formula.and φ ψ)
  | orLeft {φ ψ} : satisfies φ → satisfies (Formula.or φ ψ)
  | orRight {φ ψ} : satisfies ψ → satisfies (Formula.or φ ψ)
  | implies {φ ψ} : (¬satisfies φ ∨ satisfies ψ) → satisfies (Formula.implies φ ψ)
  | not {φ} : ¬satisfies φ → satisfies (Formula.not φ)
  | forall {x φ} : ∀ d : M.domain, satisfies (update γ x d) φ → satisfies (Formula.forall x φ)
  | exists {x φ} : ∃ d : M.domain, satisfies (update γ x d) φ → satisfies (Formula.exists x φ)

def models (M : Structure) (φ : Formula) : Prop := ∀ γ, satisfies γ φ

def valid (φ : Formula) : Prop := ∀ M γ, satisfies γ φ

-- 範例
def greater (x y : String) : Formula := Formula.pred ">" [Term.var x, Term.var y]

def isEven (x : String) : Formula := Formula.pred "Even" [Term.var x]

def example_forall : Formula := Formula.forall "x" (Formula.forall "y" (greater "y" "x" → Formula.false))

def example_exists : Formula := Formula.exists "x" (Formula.pred "Prime" [Term.var x])

-- 自然數結構
def NatStructure : Structure := {
  domain := Nat,
  interpretations := fun ">" args => args[0] > args[1]
}

end Formula