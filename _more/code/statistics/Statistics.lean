-- Statistics: 描述統計
-- 集中趨勢、變異、相關

def mean (xs : List Float) : Float :=
  if xs.isEmpty then 0 else List.sum xs / xs.length.toFloat

def median (xs : List Float) : Float :=
  let sorted := xs.qsort (· ≤ ·)
  let n := sorted.length
  if n % 2 = 0 then
    (sorted[n/2 - 1] + sorted[n/2]) / 2
  else
    sorted[n/2]

def mode (xs : List Float) : Float := by
  sorry

def variance (xs : List Float) : Float := do
  let m := mean xs
  let squaredDiffs := xs.map (fun x => (x - m)^2)
  mean squaredDiffs

def stdDev (xs : List Float) : Float := Float.sqrt (variance xs)

def range (xs : List Float) : Float := do
  let min := xs.min?.getD 0
  let max := xs.max?.getD 0
  max - min

def quartile (xs : List Float) (q : Float) : Float := do
  let sorted := xs.qsort (· ≤ ·)
  let pos := q * sorted.length.toFloat
  let idx := pos.floor.toNat
  let frac := pos - idx.floor.toFloat
  if idx < sorted.length - 1 then
    sorted[idx] * (1 - frac) + sorted[idx + 1] * frac
  else
    sorted.back

def iqr (xs : List Float) : Float := quartile xs 0.75 - quartile xs 0.25

def covariance (xs ys : List Float) : Float := do
  let mx := mean xs
  let my := mean ys
  let n := xs.length.toFloat
  let rec go (acc : Float) (xs ys : List Float) : Float :=
    match xs, ys with
    | [], [] => acc / n
    | x :: xs', y :: ys' => go (acc + (x - mx) * (y - my)) xs' ys'
    | _, _ => acc / n
  go 0 xs ys

def correlation (xs ys : List Float) : Float := do
  let cov := covariance xs ys
  let sx := stdDev xs
  let sy := stdDev ys
  if sx > 0 ∧ sy > 0 then cov / (sx * sy) else 0

def percentile (xs : List Float) (p : Float) : Float := do
  let sorted := xs.qsort (· ≤ ·)
  let pos := p * sorted.length.toFloat / 100
  let idx := pos.floor.toNat
  let frac := pos - idx.floor.toFloat
  if idx < sorted.length - 1 then
    sorted[idx] * (1 - frac) + sorted[idx + 1] * frac
  else
    sorted.back

def zScore (x : Float) (xs : List Float) : Float := do
  let m := mean xs
  let s := stdDev xs
  if s > 0 then (x - m) / s else 0

def standardize (xs : List Float) : List Float :=
  let m := mean xs
  let s := stdDev xs
  if s > 0 then xs.map (fun x => (x - m) / s) else xs

-- 測試
#eval mean [1, 2, 3, 4, 5]
#eval median [1, 2, 3, 4, 5]
#eval variance [1, 2, 3, 4, 5]
#eval stdDev [1, 2, 3, 4, 5]
#eval range [1, 2, 3, 4, 5]
#eval iqr [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]