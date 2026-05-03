-- Calculus: 實分析
-- 展示實分析的基本概念

def limit (f : Float → Float) (x : Float) : Float :=
  f (x + 0.0000001)

def isContinuous (f : Float → Float) (x : Float) : Bool :=
  let left := f (x - 0.0001)
  let right := f (x + 0.0001)
  Float.abs (right - left) < 0.001

def isConvergent (seq : Nat → Float) : Bool :=
  let rec check (n : Nat) (prev : Float) : Bool :=
    if n > 1000 then true
    else
      let curr := seq n
      if Float.abs (curr - prev) > 0.0001 then false
      else check (n + 1) curr
  check 1 (seq 0)

def cauchySequence (seq : Nat → Float) : Bool :=
  let rec check (n m : Nat) : Bool :=
    if n > 100 then true
    else if m > 100 then true
    else
      let diff := Float.abs (seq n - seq m)
      if diff > 0.0001 then false
      else check (n + 1) m || check n (m + 1)
  check 0 1

def supremum (s : List Float) : Float :=
  match s with
  | [] => 0.0
  | x :: xs => xs.foldl Float.max x

def infimum (s : List Float) : Float :=
  match s with
  | [] => 0.0
  | x :: xs => xs.foldl Float.min x

#eval isContinuous (fun x => x * x) 2.0
#eval isConvergent (fun n => 1.0 / n.toFloat + 2.0)
#eval cauchySequence (fun n => 1.0 / n.toFloat)

#eval supremum [1.0, 2.0, 3.0, 4.0, 5.0]
#eval infimum [1.0, 2.0, 3.0, 4.0, 5.0]