# NaturalDeduction.lean

## 數學原理

### 自然演繹系統

自然演繹是一種從前提推出結論的證明系統，使用推論規則而非公理。

### 核心規則

#### 引入規則（Introduction）

| 規則 | 名稱 |
|------|------|
| $\land$-intro | 從 $p, q$ 推出 $p \land q$ |
| $\lor$-intro-left | 從 $p$ 推出 $p \lor q$ |
| $\lor$-intro-right | 從 $q$ 推出 $p \lor q$ |
| $\to$-intro | 從假設 $p$ 下推出 $q$，得出 $p \to q$ |
| $\neg$-intro | 從假設 $p$ 下推出 $\bot$，得出 $\neg p$ |
| $\top$-intro | 直接得出 $\top$ |

#### 消去規則（Elimination）

| 規則 | 名稱 |
|------|------|
| $\land$-elim-left | 從 $p \land q$ 得出 $p$ |
| $\land$-elim-right | 從 $p \land q$ 得出 $q$ |
| $\lor$-elim | 從 $p \lor q$、從 $p$ 推出 $r$、從 $q$ 推出 $r$，得出 $r$ |
| $\to$-elim | 從 $p$ 和 $p \to q$ 得出 $q$（modus ponens） |
| $\neg$-elim | 從 $\neg p$ 和 $p$ 得出 $\bot$（反證法） |
| $\bot$-elim | 從 $\bot$ 得出任意 $p$（爆炸原理） |

### 重要定理

- **肯定前件（Modus Ponens）**：$p \to q, p \vdash q$
- **雙重否定消除**：$\neg\neg p \vdash p$
- **排中律**：$p \lor \neg p$

## 程式意義

### Proof 類型

```lean
inductive Proof : Type
  | hyp (n : Nat) : Proof
  | trueIntro : Proof
  | falseElim : Proof → Proof
  | andIntro : Proof → Proof → Proof
  | andElimLeft : Proof → Proof
  | andElimRight : Proof → Proof
  | orIntroLeft : Proof → Nat → Proof
  | orIntroRight : Proof → Nat → Proof
  | orElim : Proof → Proof → Proof → Proof
  | impliesIntro : Nat → Proof → Proof
  | impliesElim : Proof → Proof → Proof
  ...
```

每個建構子對應一條推論規則。

### 證據作為第一級物件

在 Curry-Howard 對應下：
- 命題是類型
- 證明是terms
- 推論規則是typed abstraction/Application

### 規則的實現

```lean
theorem andIntroRule {p q : Prop} (hp : proves Γ p) (hq : proves Γ q) :
  proves Γ (Prop.and p q) := by
  apply Proof.andIntro <;> assumption
```

## 教學重點

1. 自然演繹的規則系統
2. 引入規則與消去規則的對偶性
3. 假設管理（context）
4. 形式證明的結構