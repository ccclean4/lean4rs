# PropositionalLogic.lean

## 數學原理

### 命題邏輯的語法

命題邏輯的 BNF 語法：

$$\varphi ::= p \mid \top \mid \bot \mid \varphi \land \varphi \mid \varphi \lor \varphi \mid \varphi \to \varphi \mid \neg\varphi$$

其中 $p$ 是命題變元。

### 語義（布爾賦值）

| 公式 | 語義 |
|------|------|
| $\top$ | 永遠為真 |
| $\bot$ | 永遠為假 |
| $\varphi \land \psi$ | 當兩者皆為真時為真 |
| $\varphi \lor \psi$ | 當兩者至少一者為真時為真 |
| $\varphi \to \psi$ | 當 $\varphi$ 為假或 $\psi$ 為真時為真 |
| $\neg \varphi$ | 當 $\varphi$ 為假時為真 |

### 重要概念

| 概念 | 定義 |
|------|------|
| 可滿足（sat） | 存在賦值使公式為真 |
| 重言式（valid） | 所有賦值都使公式為真 |
| 矛盾式（unsat） | 沒有賦值使公式為真 |
| 語義後承（entails） | $\Gamma \models \varphi$ 當且僅當所有滿足 $\Gamma$ 的賦值也滿足 $\varphi$ |

## 程式意義

### Prop 歸納類型

```lean
inductive Prop : Type
  | var : String → Prop
  | true : Prop
  | false : Prop
  | and : Prop → Prop → Prop
  | or : Prop → Prop → Prop
  | implies : Prop → Prop → Prop
  | not : Prop → Prop
```

這是命題邏輯公式的抽象語法樹（AST）。

### 語義評估

```lean
def eval (γ : Assignment) : Prop → Bool
  | .var x => γ x
  | .and p q => eval γ p && eval γ q
  | .or p q => eval γ p || eval γ q
  | .implies p q => !eval γ p || eval γ q
  | .not p => !eval γ p
```

賦值（Assignment）是從命題變元到布爾值的函數。

### 有效性檢查

```lean
def valid (p : Prop) : Prop := ∀ γ, eval γ p = true
```

枚舉所有可能的賦值來檢查有效性。

## 教學重點

1. 命題邏輯的形式語法
2. 布爾賦值與語義
3. 可滿足性問題（SAT）的計算複雜性
4. 語義後承與推論的區別