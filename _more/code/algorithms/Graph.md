# Graph.lean

## 數學原理

### 圖的定義

圖 $G = (V, E)$ 由頂點集 $V$ 和邊集 $E \subseteq V \times V$ 組成。

### 圖的表示

- 鄰接表：對每個頂點儲存其相鄰頂點
- 鄰接矩輯：$n \times n$ 布爾矩陣

### 深度優先搜索 (DFS)

DFS 使用棧（隱式或顯式）：

$$DFS(v) = v \cdot \bigcup_{u \in \text{adj}(v)} DFS(u)$$

核心思想：沿路徑深入，直到無路可走再回溯。

### 廣度優先搜索 (BFS)

BFS 使用佇列：

$$BFS(v) = \text{visit}(v), \text{visit}(\text{adj}(v)), \text{visit}(\text{adj}(\text{adj}(v)))\ldots$$

核心思想：按層次順序訪問節點。

## 程式意義

### 圖的表示

```lean
inductive Graph (α : Type) where
  | empty : Graph α
  | addEdge : α → α → Graph α → Graph α
```

函數式表示，邊的添加是持久化的。

### DFS 實現

```lean
def Graph.dfs (g : Graph α) (start : α) : List α :=
  let rec visit (seen : List α) (current : α) : List α :=
    if current ∈ seen then seen
    else
      let seen' := current :: seen
      visitAdjacent seen' (adjacent current)
  visit [] start
```

### BFS 實現

```lean
def Graph.bfs (g : Graph α) (start : α) : List α :=
  let rec loop (queue : List α) (seen : List α) : List α :=
    match queue with
    | [] => seen.reverse
    | v :: queue' =>
      if v ∈ seen then loop queue' seen
      else loop (queue' ++ adjacent v) (v :: seen)
  loop [start] []
```

### 查找相鄰頂點

```lean
def adjacent (v : α) : List α :=
  match g with
  | .empty => []
  | .addEdge u w g' =>
    let adj' := adjacent v
    if u == v then w :: adj' else adj'
```

## 教學重點

1. 圖的函數式表示
2. DFS 與 BFS 的核心區別
3. 互遞迴的運用
4. 狀態管理（visited 集合）