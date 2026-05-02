-- Proofs: 皮亞諾公里系統 (Peano Axioms)
-- 展示自然數的形式化定義與基本性質證明

inductive MyNat : Type
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | a, .zero => a
  | a, .succ b => .succ (add a b)

def mul : MyNat → MyNat → MyNat
  | _, .zero => .zero
  | a, .succ b => add (mul a b) a

def pred : MyNat → MyNat
  | .zero => .zero
  | .succ n => n

theorem addZero (n : MyNat) : add n .zero = n := rfl

theorem zeroAdd (n : MyNat) : add .zero n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [add, ih]

theorem addSucc (n m : MyNat) : add n (.succ m) = .succ (add n m) := rfl

theorem addComm (n m : MyNat) : add n m = add m n := by
  induction m with
  | zero => simp [addZero, zeroAdd]
  | succ m ih => simp [addSucc, ih, addSucc, zeroAdd]

theorem addAssoc (a b c : MyNat) : add (add a b) c = add a (add b c) := by
  induction c with
  | zero => rfl
  | succ c ih => simp [add, ih]

theorem mulZero (n : MyNat) : mul n .zero = .zero := rfl

theorem zeroMul (n : MyNat) : mul .zero n = .zero := by
  induction n with
  | zero => rfl
  | succ n ih => simp [mul, ih]

theorem mulSucc (n m : MyNat) : mul n (.succ m) = add (mul n m) n := rfl

theorem mulAddDist (a b c : MyNat) : mul a (add b c) = add (mul a b) (mul a c) := by
  induction c with
  | zero => simp [mul, add, mulZero, addZero]
  | succ c ih => simp [mul, add, mulSucc, ih, addAssoc]

theorem mulComm (n m : MyNat) : mul n m = mul m n := by
  induction m with
  | zero => simp [mulZero, zeroMul]
  | succ m ih => simp [mulSucc, ih, mulAddDist, zeroMul, addZero]

theorem induction (P : MyNat → Prop) (h0 : P .zero) (hs : ∀ n, P n → P (.succ n)) (n : MyNat) : P n := by
  induction n with
  | zero => exact h0
  | succ n ih => exact hs n ih

end MyNat