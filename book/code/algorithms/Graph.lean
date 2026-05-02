-- Algorithms: 圖論基礎
-- 展示圖的表示與常見演算法

inductive Graph (α : Type) where
  | empty : Graph α
  | addEdge : α → α → Graph α → Graph α

def Graph.vertices (g : Graph α) : List α :=
  match g with
  | .empty => []
  | .addEdge u v g =>
    let vs := vertices g
    if u ∈ vs then
      if v ∈ vs then vs else v :: vs
    else
      u :: (if v ∈ vs then vs else v :: vs)

def Graph.edges (g : Graph α) : List (α × α) :=
  match g with
  | .empty => []
  | .addEdge u v g => (u, v) :: edges g

def Graph.hasEdge (g : Graph α) (u v : α) : Bool :=
  match g with
  | .empty => false
  | .addEdge a b g' =>
    if u == a ∧ v == b then true else hasEdge g' u v

-- DFS
def Graph.dfs (g : Graph α) (start : α) : List α :=
  let rec visit (seen : List α) (current : α) : List α :=
    if current ∈ seen then seen
    else
      let seen' := current :: seen
      visitAdjacent seen' (adjacent current)
  and visitAdjacent (seen : List α) (adj : List α) : List α :=
    match adj with
    | [] => seen
    | a :: as => visit (visitAdjacent seen as) a
  and adjacent (v : α) : List α :=
    match g with
    | .empty => []
    | .addEdge u w g' =>
      let adj' := adjacent v
      if u == v then w :: adj' else adj'
  visit [] start

-- BFS
def Graph.bfs (g : Graph α) (start : α) : List α :=
  let rec loop (queue : List α) (seen : List α) : List α :=
    match queue with
    | [] => seen.reverse
    | v :: queue' =>
      if v ∈ seen then
        loop queue' seen
      else
        loop (queue' ++ adjacent v) (v :: seen)
  and adjacent (v : α) : List α :=
    match g with
    | .empty => []
    | .addEdge u w g' =>
      let adj' := adjacent v
      if u == v then w :: adj' else adj'
  loop [start] []

-- 測試
def exampleGraph : Graph Nat :=
  Graph.empty
    |>.addEdge 1 2
    |>.addEdge 2 3
    |>.addEdge 3 4
    |>.addEdge 1 3

#eval exampleGraph.vertices
#eval exampleGraph.edges
#eval exampleGraph.hasEdge 1 2
#eval exampleGraph.hasEdge 2 1