-- Proofs: 數學歸納法
-- 展示自然數歸納法的各種形式

theorem natZeroAdd (n : Nat) : 0 + n = n := rfl

theorem natAddAssoc (a b c : Nat) : a + b + c = a + (b + c) := by
  induction a with
  | zero => rfl
  | succ a ih => simp [Nat.add_succ, ih]

theorem natAddComm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero =>
    have : b = b + 0 := (Nat.add_zero b).symm
    simp [this]
  | succ a ih =>
    calc
      a.succ + b = (a + b).succ := rfl
        _ = (b + a).succ := by rw [ih]
        _ = b + a.succ := Nat.add_succ b a ▸ rfl

theorem natMulDist (a b c : Nat) : a * (b + c) = a * b + a * c := by
  induction a with
  | zero => rfl
  | succ a ih =>
    calc
      a.succ * (b + c) = (b + c) + a * (b + c) := rfl
        _ = (b + c) + (a * b + a * c) := by rw [ih]
        _ = b + a * b + (c + a * c) := by repeat rw [Nat.add_assoc]
        _ = a.succ * b + a.succ * c := rfl

theorem natPowTwo (n : Nat) : 2 ^ n = Nat.pow 2 n := rfl

theorem sumFirstN (n : Nat) : (List.range n).foldl (· + ·) 0 = n * (n - 1) / 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have : List.range n.succ = List.range n ++ [n] := by simp
    have : (List.range n ++ [n]).foldl (· + ·) 0 = (List.range n).foldl (· + ·) 0 + n := by simp
    rw [this, ih]
    have : n * (n - 1) / 2 + n = n * (n + 1) / 2 := by omega
    rw [this]

-- 強化歸納法
theorem infiniteDescent (P : Nat → Prop) (h : ∀ n, (∀ m < n, P m) → P n) : ∀ n, P n
  | 0 => h 0 (fun m h => absurd h (Nat.not_lt_zero m))
  | n + 1 => h (n + 1) fun m hm => infiniteDescent P h m (Nat.lt_of_succ_lt hm)