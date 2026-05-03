-- Calculus: 微分
-- 展示微分的基本概念

def deriv (f : Float → Float) (x : Float) (h : Float) : Float :=
  (f (x + h) - f x) / h

def deriv2 (f : Float → Float) (x : Float) (h : Float) : Float :=
  (f (x + h) - 2 * f x + f (x - h)) / (h * h)

def d/dx (f : Float → Float) (x : Float) : Float :=
  (f (x + 0.001) - f x) / 0.001

def d²/dx² (f : Float → Float) (x : Float) : Float :=
  (f (x + 0.001) - 2 * f x + f (x - 0.001)) / 0.000001

def pow (n : Nat) (x : Float) : Float :=
  match n with
  | 0 => 1.0
  | n + 1 => x * pow n x

def sin' (x : Float) : Float := Float.cos x
def cos' (x : Float) : Float := -Float.sin x
def exp' (x : Float) : Float := Float.exp x
def log' (x : Float) : Float := 1.0 / x

#eval d/dx (fun x => x * x) 2.0
#eval d²/dx² (fun x => x * x * x) 1.0
#eval sin' 0.0
#eval cos' 0.0
#eval exp' 1.0
#eval log' 2.718281828