-- Calculus: 積分
-- 展示積分的基本概念

def riemannSum (f : Float → Float) (a b : Float) (n : Nat) : Float :=
  let dx := (b - a) / n.toFloat
  let rec sum (i : Nat) (acc : Float) : Float :=
    if i >= n then acc
    else sum (i + 1) (acc + f (a + dx * i.toFloat) * dx)
  sum 0 0.0

def trapezoidRule (f : Float → Float) (a b : Float) (n : Nat) : Float :=
  let dx := (b - a) / n.toFloat
  let rec sum (i : Nat) (acc : Float) : Float :=
    if i >= n then acc
    else
      let x := a + dx * i.toFloat
      let xNext := a + dx * (i + 1).toFloat
      sum (i + 1) (acc + (f x + f xNext) / 2.0 * dx)
  sum 0 0.0

def simpsonRule (f : Float → Float) (a b : Float) : Float :=
  let c := (a + b) / 2.0
  (b - a) / 6.0 * (f a + 4.0 * f c + f b)

def integrate (f : Float → Float) (a b : Float) : Float :=
  trapezoidRule f a b 1000

def antideriv (f : Float → Float) (x : Float) : Float :=
  x * x * x / 3.0

#eval riemannSum (fun x => x * x) 0.0 1.0 100
#eval trapezoidRule (fun x => x * x) 0.0 1.0 100
#eval simpsonRule (fun x => x * x) 0.0 1.0
#eval integrate (fun x => x * x) 0.0 1.0

example : Float := riemannSum (fun x => x) 0.0 1.0 10