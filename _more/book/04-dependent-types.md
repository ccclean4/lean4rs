# 04 - 依賴類型與 Pi 類型

## 依賴類型簡介

Lean 4 的核心特色是**依賴類型**：類型可以依賴值。

```lean
-- Vec : Type → Nat → Type
-- Vec α n 表示長度為 n 的向量，元素類型為 α
```

## Pi 類型（函數類型）

Pi 類型表示依賴函數：

```lean
-- 普通函數：Nat → Nat
-- 依賴函數：(n : Nat) → Vec Nat n
--           ^^^^
--           參數名稱使類型依賴於值
```

### 語法

```lean
-- 明確依賴
def foo : (n : Nat) → Type := fun n => Vec Nat n

-- 隱含依賴（常見）
def bar : {n : Nat} → Vec Nat n := fun => Vec.nil
```

## 依值類型

```lean
-- Fin n 是 {x : Nat // x < n}
-- 長度為 n 的列表的元素類型
def getElement {n : Nat} (v : Vec α n) (i : Fin n) : α := ...
```

## Vector（固定長度向量）

```lean
inductive Vec (α : Type) : Nat → Type
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

def v123 : Vec Nat 3 := Vec.cons 1 (Vec.cons 2 (Vec.cons 3 Vec.nil))
```

## 依賴函數範例

```lean
-- length-indexed append
def append {n m : Nat} (v1 : Vec α n) (v2 : Vec α m) : Vec α (n + m)
  | Vec.nil, v2 => v2
  | Vec.cons x xs, v2 => Vec.cons x (append xs v2)
```

## 練習

1. 定義 `head` 函數取得 `Vec α (n+1)` 的第一個元素
2. 定義 `replicate : (n : Nat) → α → Vec α n`
3. 定義 `zip : Vec α n → Vec β n → Vec (α × β) n`