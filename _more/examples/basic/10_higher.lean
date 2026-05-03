-- 10_higher.lean - 高階函式與匿名函式

def twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)
def thrice (f : Nat → Nat) (x : Nat) : Nat := f (f (f x))
def compose (f : α → β) (g : β → γ) (x : α) : γ := g (f x)

def square (x : Nat) : Nat := x * x
def cube (x : Nat) : Nat := x * x * x

#eval IO.println s!"twice square 3 = {twice square 3}"
#eval IO.println s!"thrice cube 2 = {thrice cube 2}"
#eval IO.println s!"compose (fun x => x + 1) (fun x => x * 2) 5 = {compose (fun x => x + 1) (fun x => x * 2) 5}"