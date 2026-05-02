# ModalLogic.lean

## 數學原理

### 模態邏輯的語法

在命題邏輯基礎上添加兩個模態算子：
- $\square \varphi$：必然 $\varphi$
- $\diamond \varphi$：可能 $\varphi$

對偶關係：
- $\square \varphi \iff \neg \diamond \neg \varphi$
- $\diamond \varphi \iff \neg \square \neg \varphi$

### 克里普克語義

模態公式在克里普克模型 $M = (W, R, V)$ 中評価：
- $W$：可能世界集合
- $R \subseteq W \times W$：可達關係
- $V$：賦值函數

$$M, w \models \square \varphi \iff \forall w' (Rww' \to M, w' \models \varphi)$$
$$M, w \models \diamond \varphi \iff \exists w' (Rww' \wedge M, w' \models \varphi)$$

### 系統層次

| 系統 | 額外公理 | 可達關係性質 |
|------|---------|-------------|
| K | 無 | 無限制 |
| T | $p \to \square p$ | 反射性 |
| S4 | $p \to \square p$, $\square p \to \square \square p$ | 反射性、傳遞性 |
| S5 | $p \to \square p$, $\square p \to \square \square p$, $\diamond p \to \square \diamond p$ | 反射性、傳遞性、歐幾里得性 |

## 程式意義

### ModalFormula 歸納類型

```lean
inductive ModalFormula : Type
  | var : String → ModalFormula
  | box : ModalFormula → ModalFormula
  | diamond : ModalFormula → ModalFormula
  ...
```

### 克里普克模型

```lean
structure KripkeModel where
  worlds : Type
  accessibility : worlds → worlds → Prop
  valuation : String → worlds → Bool
```

### 滿足關係

```lean
inductive satisfies {W : Type} (R : W → W → Prop) (V : String → W → Bool) : W → ModalFormula → Prop
  | box : ∀ w φ, (∀ w', R w w' → satisfies w' φ) → satisfies w (.box φ)
  | diamond : ∀ w φ, (∃ w', R w w' ∧ satisfies w' φ) → satisfies w (.diamond φ)
```

## 教學重點

1. 模態算子的直觀意義
2. 克里普克框架與模型
3. 必然性與可能性的對偶性
4. 不同系統對應的結構性質