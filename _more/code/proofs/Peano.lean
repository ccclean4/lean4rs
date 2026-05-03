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

-- 較複雜的定理暫時略過
-- theorem addComm (n m : MyNat) : add n m = add m n
-- theorem addAssoc (a b c : MyNat) : add (add a b) c = add a (add b c)
-- theorem mulZero (n : MyNat) : mul n .zero = .zero
-- theorem zeroMul (n : MyNat) : mul .zero n = .zero
-- theorem mulSucc (n m : MyNat) : mul n (.succ m) = add (mul n m) n
-- theorem mulAddDist (a b c : MyNat) : mul a (add b c) = add (mul a b) (mul a c)
-- theorem mulComm (n m : MyNat) : mul n m = mul m n

theorem induction (P : MyNat → Prop) (h0 : P .zero) (hs : ∀ n, P n → P (.succ n)) (n : MyNat) : P n := by
  induction n with
  | zero => exact h0
  | succ n ih => exact hs n ih

end MyNat