# propositions.lean

## 數學原理

### 命題邏輯

本檔案展示命題邏輯的基本定律。命題是具有真值的陳述。

| 連接詞 | 符號 | 數學含義 |
|--------|------|----------|
| 且 | `∧` | $p \land q$ |
| 或 | `∨` | $p \lor q$ |
| 蘊含 | `→` | $p \to q$ |
| 雙蘊含 | `↔` | $p \leftrightarrow q$ |
| 否定 | `¬` | $\neg p$ |

### 交換律

$$p \land q \leftrightarrow q \land p$$
$$p \lor q \leftrightarrow q \lor p$$

在 Lean 4 中作為函數證明：

```lean
theorem and_comm {p q : Prop} : p ∧ q → q ∧ p := fun h =>
  have hp : p := h.left
  have hq : q := h.right
  And.intro hq hp
```

### 傳遞性

$$(p \to q) \to (q \to r) \to (p \to r)$$

```lean
theorem implies_trans {p q r : Prop} (h1 : p → q) (h2 : q → r) : p → r := fun hp =>
  have hq : q := h1 hp
  h2 hq
```

### 逆否命題

$$(p \to q) \leftrightarrow (\neg q \to \neg p)$$

```lean
theorem contrapositive {p q : Prop} : (p → q) → (¬q → ¬p) := fun h hnq hp =>
  have hq : q := h hp
  hnq hq
```

### De Morgan 定律

$$\neg(p \lor q) \leftrightarrow (\neg p \land \neg q)$$
$$\neg(p \land q) \leftrightarrow (\neg p \lor \neg q)$$

## 程式意義

### 證據作為值

在直覺主義邏輯中，證明就是物件。`p : Prop` 的證據 `hp : p` 是：
- `And.intro hp hq` 構建 `p ∧ q` 的證據
- `Or.elim h hp hq` 從 `p ∨ q` 提取 `p` 或 `q` 的證據

### 函數式證明

每個定理都是一個函數，輸入前提輸出結論：

```lean
theorem contrapositive : (p → q) → (¬q → ¬p)
```

這是 Curry-Howard 對應的核心：命題即類型，證明即程式。

## 教學重點

1. 命題邏輯的語法與語義
2. 自然演繹系統的推論規則
3. 證據作為第一級物件