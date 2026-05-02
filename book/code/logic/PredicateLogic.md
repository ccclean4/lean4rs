# PredicateLogic.lean

## 數學原理

### 一階謂詞邏輯的語法

$$\varphi ::= P(t_1, \ldots, t_n) \mid \top \mid \bot \mid \varphi \land \varphi \mid \varphi \lor \varphi \mid \varphi \to \varphi \mid \neg\varphi \mid \forall x \ \varphi \mid \exists x \ \varphi$$

其中：
- $P$ 是 $n$ 元謂詞符號
- $t_i$ 是項（變元或函數應用）
- $x$ 是變元

### 項的定義

$$t ::= x \mid f(t_1, \ldots, t_n)$$

其中 $f$ 是函數符號。

### 自由變數與約束變數

- **自由變數**：不在任何量詞作用域內的變元
- **約束變數**：被量詞綁定的變元

### 量詞規則

| 規則 | 名稱 |
|------|------|
| $\forall$-intro | 從 $\varphi$ 在 $x$ 不自由出現於假設中，推出 $\forall x \ \varphi$ |
| $\forall$-elim | 從 $\forall x \ \varphi$ 得出 $\varphi[t/x]$（代換） |
| $\exists$-intro | 從 $\varphi[t/x]$ 得出 $\exists x \ \varphi$ |
| $\exists$-elim | 從 $\exists x \ \varphi$ 和 $\varphi \vdash \psi$（$x$ 不在假設中自由出現）得出 $\psi$ |

## 程式意義

### Term 和 Formula 類型

```lean
inductive Term : Type
  | var : String → Term
  | func : String → List Term → Term

inductive Formula : Type
  | pred : String → List Term → Formula
  | forall : String → Formula → Formula
  | exists : String → Formula → Formula
  ...
```

### 自由變數計算

```lean
def freeVarsFormula : Formula → List String
  | .forall x φ => freeVarsFormula φ |>.erase x
  | .exists x φ => freeVarsFormula φ |>.erase x
```

約束變數從自由變數集合中移除。

### 模型論語義

```lean
inductive satisfies {M : Structure} (γ : String → M.domain) : Formula → Prop
  | forall {x φ} : ∀ d : M.domain, satisfies (update γ x d) φ → satisfies (Formula.forall x φ)
  | exists {x φ} : ∃ d : M.domain, satisfies (update γ x d) φ → satisfies (Formula.exists x φ)
```

## 教學重點

1. 一階邏輯的語法層次
2. 自由變數與約束變數的區別
3. 代換的正確實現
4. 模型論語義的基本思想