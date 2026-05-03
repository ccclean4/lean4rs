-- 07_inductive.lean - 枚舉與代數資料型態

inductive Color where
  | red
  | green
  | blue

def colorName (c : Color) : String :=
  match c with
  | Color.red => "Red"
  | Color.green => "Green"
  | Color.blue => "Blue"

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : α → Tree α → Tree α → Tree α

def treeSize : Tree α → Nat
  | Tree.leaf => 0
  | Tree.node _ l r => 1 + treeSize l + treeSize r

#eval IO.println s!"colorName Color.blue = \"{colorName Color.blue}\""
#eval IO.println s!"treeSize (Tree.node 1 Tree.leaf Tree.leaf) = {treeSize (Tree.node 1 Tree.leaf Tree.leaf)}"