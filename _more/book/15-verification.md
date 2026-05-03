# 15 - 形式化驗證範例

## 棧（Stack）驗證

```lean
-- 棧介面
class Stack (α : Type) where
  empty : α
  push : α → α → α
  pop : α → Option (α × α)
  top : α → Option α

-- 規範：pop 後再 push 恢復原值
theorem stackRecover (s : α) (x : α) (h : Stack.pop s = some (x, s')) :
  Stack.pop (Stack.push x s') = some (x, s') := by
  simp [Stack.push, Stack.pop] at h
  exact h
```

## 佇列（Queue）驗證

```lean
-- 雙端佇列用兩個棧模擬
structure Queue (α : Type) where
  front : List α
  back : List α

def enqueue (q : Queue α) (x : α) : Queue α :=
  { q with back := x :: q.back }

def dequeue (q : Queue α) : Option (α × Queue α) :=
  match q.front with
  | [] =>
    match q.back.reverse with
    | [] => none
    | x :: front' => some (x, { front := front', back := [] })
  | x :: front' => some (x, { q with front := front' })

theorem dequeue_enqueue (q : Queue α) (x : α) :
  dequeue (enqueue q x) = some (x, q) := by
  simp [enqueue, dequeue]
  cases q.back <;> simp
```

## 記憶體安全

```lean
-- 界檢查陣列存取
def safeGet {α : Type} (xs : List α) (i : Nat) (h : i < xs.length) : α :=
  match h with
  | Nat.lt_succ_self _ => xs[i]

theorem safeGet_inbound {α : Type} (xs : List α) (i : Nat) (h : i < xs.length) :
  safeGet xs i h ∈ xs := by
  simp [safeGet, List.get]
```

## 練習

1. 驗證二元搜尋樹的 `insert` 維持 BST 性質
2. 驗證 `dequeue` 的公平性
3. 驗證並髏式記憶體管理器的配置/釋放
4. 驗證簡單的解析器組合子