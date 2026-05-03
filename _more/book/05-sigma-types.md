# 05 - Sigma 類型與資料對

## Sigma 類型

Sigma 類型 (`Σ`) 是依賴的積類型：

```lean
-- Σ x : A, B(x)
-- 表示一個對：(x : A) × B(x)
-- 第一個成分是 A 類型，第二個成分的類型依賴於第一個成分

def mySigma : Σ n : Nat, Vec Nat n :=
  ⟨3, [1, 2, 3]⟩

-- 存取成分
#eval mySigma.fst  -- 3
#eval mySigma.snd  -- [1, 2, 3]
```

## 結構化存取

```lean
-- 更一般地
#eval mySigma.1  -- 3
#eval mySigma.2  -- [1, 2, 3]
```

## 資料對 (DProd)

非依賴版本的 Sigma：

```lean
-- DProd α β 等同於 α × β
def myPair : DProd Nat (fun _ => Nat) := ⟨5, 10⟩

#eval myPair.1  -- 5
#eval myPair.2  -- 10
```

## { || } 語法

```lean
-- { x // P } 是 Sigma 類型的特例
-- { x : A // P } = Σ x : A, P
-- 例如：Fin n = { i : Nat // i < n }

def three : Fin 5 := ⟨3, Nat.lt_succ_self 2⟩
```

## 模式匹配

```lean
def first {α : Type} {β : α → Type} (p : Σ x : α, β x) : α :=
  match p with
  | ⟨a, b⟩ => a

def second {α : Type} {β : α → Type} (p : Σ x : α, β x) : β p.fst :=
  match p with
  | ⟨a, b⟩ => b
```

## 練習

1. 定義函數：`swap : Σ x : α, β x → Σ x : α, γ x`
2. 定義：`MkFin : (n : Nat) → Fin (n + 1)`
3. 實作二元搜尋樹節點：`Tree α = Σ left : Tree α, Σ value : α, Σ right : Tree α`