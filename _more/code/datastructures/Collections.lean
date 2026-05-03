-- DataStructures: 常用資料結構
-- 展示 Queue, Stack, Tree 等結構的實現

inductive Queue (α : Type) where
  | mk : List α → List α → Queue α

def Queue.empty : Queue α := .mk [] []

def Queue.enqueue (q : Queue α) (x : α) : Queue α :=
  match q with
  | .mk front back => .mk front (x :: back)

def Queue.dequeue (q : Queue α) : Option (α × Queue α) :=
  match q with
  | .mk [] [] => none
  | .mk [] back => reverseAndDequeue back
  | .mk (x :: front) back => some (x, .mk front back)
where
  reverseAndDequeue (xs : List α) : Option (α × Queue α) :=
    match xs.reverse with
    | [] => none
    | x :: front => some (x, .mk front [])

def Queue.toList (q : Queue α) : List α :=
  match q with
  | .mk front back => front ++ back.reverse

def Queue.size (q : Queue α) : Nat :=
  match q with
  | .mk front back => front.length + back.length

-- Stack
inductive Stack (α : Type) where
  | empty : Stack α
  | push : α → Stack α → Stack α

def Stack.push (s : Stack α) (x : α) : Stack α := .push x s

def Stack.pop (s : Stack α) : Option (α × Stack α) :=
  match s with
  | .empty => none
  | .push x rest => some (x, rest)

def Stack.top (s : Stack α) : Option α :=
  match s with
  | .empty => none
  | .push x _ => some x

def Stack.toList (s : Stack α) : List α :=
  match s with
  | .empty => []
  | .push x rest => x :: toList rest

-- Tree
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

def Tree.map (f : α → β) : Tree α → Tree β
  | .leaf a => .leaf (f a)
  | .node l r => .node (map f l) (map f r)

def Tree.fold (f : α → β → β) (b : β) : Tree α → β
  | .leaf a => f a b
  | .node l r => fold f (fold f b r) l

def Tree.flatten : Tree α → List α
  | .leaf a => [a]
  | .node l r => flatten l ++ flatten r

-- 測試
#eval Queue.empty.enqueue 1.enqueue 2.enqueue 3 |> Queue.toList
#eval Stack.empty.push 1.push 2.push 3 |> Stack.toList
#eval Tree.node (Tree.node (Tree.leaf 1) (Tree.leaf 2)) (Tree.leaf 3) |> Tree.flatten