# HigherOrder.lean

## 數學原理

### 函數作為一級公民

在數學中，函數是集合之間的映射。在 Lean 4 中，函數也是值：

$$\text{Type} \ni f : \alpha \to \beta$$

### 高階函數

高階函數以其他函數為輸入或輸出：

- `map : (α → β) → (List α → List β)`
- `filter : (α → Bool) → (List α → List α)`
- `fold : (β → α → β) → β → List α → β`

### Kleisli 合成

`compose (f : β → γ) (g : α → β) (x : α) : γ` 等同於數學中的函數合成：

$$(f \circ g)(x) = f(g(x))$$

### Currying

Currying 將多元函數轉換為一系列單參數函數：

$$\alpha \times \beta \to \gamma \cong \alpha \to (\beta \to \gamma)$$

## 程式意義

### map（映射）

```lean
def double := fun x : Nat => x * 2
#eval [1, 2, 3, 4, 5].map double  -- [2, 4, 6, 8, 10]
```

數學含義：對列表每個元素應用函數，產生新列表。

### filter（過濾）

```lean
def isEven (n : Nat) : Bool := n % 2 == 0
#eval [1, 2, 3, 4, 5].filter isEven  -- [2, 4]
```

數學含義：從集合中選擇滿足述詞的元素。

### fold（折疊）

```lean
def sum (xs : List Nat) : Nat := xs.foldl (· + ·) 0
```

數學含義：廣義結合運算的迭代應用。

### zipWith

```lean
def zipWith {α β γ : Type} (f : α → β → γ) (xs : List α) (ys : List β) : List γ
```

數學含義：兩個列表的笛卡爾積在 f 下的像。

## 範疇論視角

這些高階函數對應範疇論中的重要概念：

| 函數 | 範疇論概念 |
|------|-----------|
| `map` | 函子（Functor） |
| `fold` | 餘積（Catamorphism） |
| `compose` | 合成（Composition） |

## 教學重點

1. 函數式思維：資料變換而非狀態修改
2. `·` 語法（anonymous function syntax）
3. fold 的普遍性