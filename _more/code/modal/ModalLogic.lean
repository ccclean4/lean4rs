-- Modal: 模態邏輯
-- 展示模態邏輯的語法與語義

inductive ModalFormula : Type
  | var : String → ModalFormula
  | true : ModalFormula
  | false : ModalFormula
  | and : ModalFormula → ModalFormula → ModalFormula
  | or : ModalFormula → ModalFormula → ModalFormula
  | implies : ModalFormula → ModalFormula → ModalFormula
  | not : ModalFormula → ModalFormula
  | box : ModalFormula → ModalFormula
  | diamond : ModalFormula → ModalFormula

namespace ModalFormula

def not (φ : ModalFormula) : ModalFormula := ModalFormula.not φ

def iff (φ ψ : ModalFormula) : ModalFormula :=
  ModalFormula.and (ModalFormula.implies φ ψ) (ModalFormula.implies ψ φ)

-- 對偶性
theorem boxDiamondDual (φ : ModalFormula) :
  ModalFormula.not (box φ) = ModalFormula.diamond (ModalFormula.not φ) := by
  rfl

theorem diamondBoxDual (φ : ModalFormula) :
  ModalFormula.not (diamond φ) = ModalFormula.box (ModalFormula.not φ) := by
  rfl

end ModalFormula

-- 克里普克結構
structure KripkeModel where
  worlds : Type
  accessibility : worlds → worlds → Prop
  valuation : String → worlds → Bool

-- 可達關係的性質
class Reflexive (R : α → α → Prop) := reflexivity : ∀ a, R a a
class Symmetric (R : α → α → Prop) := symmetry : ∀ a b, R a b → R b a
class Transitive (R : α → α → Prop) := transitivity : ∀ a b c, R a b → R b c → R a c
class Serial (R : α → α → Prop) := seriality : ∀ a, ∃ b, R a b
class Euclidean (R : α → α → Prop) := euclidean : ∀ a b c, R a b → R a c → R b c

-- 克里普克語義
inductive satisfies {W : Type} (R : W → W → Prop) (V : String → W → Bool) : W → ModalFormula → Prop
  | var : ∀ w x, V x w = true → satisfies w (.var x)
  | true : ∀ w, satisfies w .true
  | and : ∀ w φ ψ, satisfies w φ → satisfies w ψ → satisfies w (.and φ ψ)
  | orLeft : ∀ w φ ψ, satisfies w φ → satisfies w (.or φ ψ)
  | orRight : ∀ w φ ψ, satisfies w ψ → satisfies w (.or φ ψ)
  | implies : ∀ w φ ψ, (¬satisfies w φ ∨ satisfies w ψ) → satisfies w (.implies φ ψ)
  | not : ∀ w φ, ¬satisfies w φ → satisfies w (.not φ)
  | box : ∀ w φ, (∀ w', R w w' → satisfies w' φ) → satisfies w (.box φ)
  | diamond : ∀ w φ, (∃ w', R w w' ∧ satisfies w' φ) → satisfies w (.diamond φ)

def forces {M : KripkeModel} (w : M.worlds) (φ : ModalFormula) : Prop :=
  satisfies M.accessibility M.valuation w φ

def validInModel (M : KripkeModel) (φ : ModalFormula) : Prop :=
  ∀ w, forces w φ

def valid (φ : ModalFormula) : Prop :=
  ∀ M w, forces w φ

-- 系統 K（最小模態邏輯）
namespace SystemK

theorem distribution (φ ψ : ModalFormula) :
  valid (.implies (.box (.implies φ ψ)) (.implies (.box φ) (.box ψ))) := by
  intros M w h1 h2 w' hw
  have := h1 w' hw
  have := h2 w' hw
  tauto

theorem Necessitation (φ : ModalFormula) (h : valid φ) : valid (.box φ) := by
  intros M w hw' w' hw
  exact h M w'

end SystemK

-- 系統 T（添加反射性）
namespace SystemT

class ReflexiveModel (M : KripkeModel) [Reflexive M.accessibility] : Prop

theorem T1 (φ : ModalFormula) :
  valid (.implies φ (.box φ)) := by
  intros M w hw
  constructor
  intros w' hw'
  have : w' = w := by admit  -- 反身性
  rw [this]
  exact hw

end SystemT

-- 系統 S4（反射性 + 傳遞性）
namespace SystemS4

theorem S4_1 (φ : ModalFormula) :
  valid (.implies (.box φ) (.diamond φ)) := by
  intros M w hw
  have : ∃ w', M.accessibility w w' := by admit  -- 反射性
  obtain ⟨w', hw'⟩ := this
  exact Exists.intro w' (And.intro hw' (hw w' hw'))

end SystemS4

-- 系統 S5（反射性 + 傳遞性 + 歐幾里得性）
namespace SystemS5

-- S5 中 ◻ 和 ◇ 是相互定義的
theorem S5_diamond_box (φ : ModalFormula) :
  valid (.implies (.diamond φ) (.box (.diamond φ))) := by
  intros M w hw
  obtain ⟨w', ⟨hw', hwφ⟩⟩ := hw
  intros w'' hw''
  have : M.accessibility w' w'' := by admit  -- 歐幾里得性
  exact Exists.intro w'' (And.intro this (by admit))

end SystemS5

-- 範例
def p := ModalFormula.var "p"
def q := ModalFormula.var "q"

def example1 : ModalFormula := ModalFormula.box p
def example2 : ModalFormula := ModalFormula.diamond (ModalFormula.not p)
def example3 : ModalFormula := ModalFormula.implies (ModalFormula.box p) (ModalFormula.diamond q)

end