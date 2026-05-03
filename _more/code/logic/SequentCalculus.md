# SequentCalculus.lean

## 數學原理

### Sequent 的定義

 sequent 形式為 $\Gamma \vdash \Delta$，讀作「由 $\Gamma$ 推出 $\Delta$」：

$$\Gamma \vdash \Delta \iff \bigwedge_{\varphi \in \Gamma} \varphi \implies \bigvee_{\psi \in \Delta} \psi$$

當 $\Delta$ 為空時，相當於 $\Gamma$ 導出矛盾；當 $\Gamma$ 為空時，相當於導出 $\bigvee \Delta$。

### 結構規則

| 規則 | 名稱 |
|------|------|
| Weakening | $\Gamma \vdash \Delta \implies \Gamma, p \vdash \Delta$ |
| Contraction | $\Gamma, p, p \vdash \Delta \iff \Gamma, p \vdash \Delta$ |
| Cut | $\Gamma \vdash p, \Delta \quad \Sigma, p \vdash \Theta \implies \Gamma, \Sigma \vdash \Delta, \Theta$ |

### 邏輯規則

#### And ($\land$)

$$\frac{\Gamma, p, q \vdash \Delta}{\Gamma, p \land q \vdash \Delta} \land\text{-left} \quad \frac{\Gamma \vdash p \quad \Gamma \vdash q}{\Gamma \vdash p \land q} \land\text{-right}$$

#### Or ($\lor$)

$$\frac{\Gamma, p \vdash \Delta \quad \Gamma, q \vdash \Delta}{\Gamma, p \lor q \vdash \Delta} \lor\text{-left} \quad \frac{\Gamma \vdash p, q}{\Gamma \vdash p \lor q} \lor\text{-right}$$

#### Implies ($\to$)

$$\frac{\Gamma \vdash p, \Delta \quad \Gamma, q \vdash \Delta}{\Gamma, p \to q \vdash \Delta} \to\text{-left} \quad \frac{\Gamma, p \vdash q}{\Gamma \vdash p \to q} \to\text{-right}$$

### 內定理定理

每個命題邏輯的重言式都在 sequent 演算中可證：

$$\models \varphi \iff \vdash \varphi$$

## 程式意義

### Sequent 結構

```lean
structure Sequent where
  antecedents : List Prop
  succedents : List Prop
```

左邊是前提（假設），右邊是結論（目標）。

### 規則的實現

```lean
theorem AndRight (Γ Δ : List Prop) (p q : Prop) :
  (Γ ⊢ (Prop.and p q :: Δ)) ↔ (Γ ⊢ (p :: Δ)) ∧ (Γ ⊢ (q :: Δ))
```

And-Right 規則將目標拆分為兩個子目標。

### 證明搜索

sequent 演算可用於自動化定理證明：
- 從目標開始，反向應用規則
- 直到所有分支都是公理或失敗

## 教學重點

1. sequent 與自然演繹的關係
2. 左規則與右規則的對偶性
3. Cut Elimination 定理的重要性
4. 證明系統的完整性與soundness