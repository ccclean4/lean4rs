# 06 - 歸納類型與遞迴

## 歸納定義

Lean 4 使用 `inductive` 關鍵字定義歸納類型：

```lean
inductive Bool : Type
  | false : Bool
  | true : Bool

inductive Nat : Type
  | zero : Nat
  | succ : Nat → Nat

inductive List (α : Type) : Type
  | nil : List α
  | cons : α → List α → List α
```

## 結構遞迴原則

每個歸納類型配套唯一的遞迴原理：

```lean
-- Nat 的遞迴原理
def natRec {C : Nat → Type} (h0 : C 0) (hs : (n : Nat) → C n → C (n + 1)) : (n : Nat) → C n

-- 等同於
def natRec (h0 : C 0) (hs : ∀ n, C n → C (n+1)) : ∀ n, C n
```

## 樹狀結構

```lean
inductive Tree (α : Type) : Type
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

def treeSize : Tree α → Nat
  | Tree.leaf _ => 1
  | Tree.node l r => 1 + treeSize l + treeSize r

def treeDepth : Tree α → Nat
  | Tree.leaf _ => 0
  | Tree.node l r => 1 + max (treeDepth l) (treeDepth r)
```

## 互遞歸類型

```lean
inductive Expr
  | num : Nat → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | lam : String → Expr → Expr
  | app : Expr → Expr → Expr

inductive Value
  | numV : Nat → Value
  | closureV : String → Expr → Env → Value

-- 環境
def Env := List (String × Value)
```

## 屬性證明

```lean
theorem treeSize_pos : ∀ t : Tree α, treeSize t > 0
  | Tree.leaf _ => Nat.lt_succ_self 0
  | Tree.node l r => Nat.add_pos (Nat.lt_succ_self 0)
                      (Nat.lt_of_lt_of_le (Nat.lt_succ_self 0)
                        (Nat.le_add_right _ _))
```

## 練習

1. 定義 `BST α`（二元搜尋樹）
2. 實作 `insert` 和 `contains`
3. 實作 `Expr` 的求值器
4. 證明 `contains` 的正確性