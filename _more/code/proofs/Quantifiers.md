# Quantifiers.lean

## 數學原理

### 謂詞邏輯的量化

一階邏輯的兩個核心量化符：

| 符號 | 名稱 | 數學含義 |
|------|------|----------|
| `∀` | 全稱量化 | 「對所有...成立」 |
| `∃` | 存在量化 | 「存在...使得」 |

### 全稱量化的證明

要證明 $\forall x, P(x)$，需展示對任意輸入 $x$ 都能構造 $P(x)$ 的證據：

```lean
theorem forall_intro {α : Type} {P : α → Prop} (h : ∀ x : α, P x) : ∀ x : α, P x := h
```

應用（使用）全稱命題：
```lean
theorem forall_elim {α : Type} {P : α → Prop} (h : ∀ x : α, P x) (a : α) : P a := h a
```

### 存在量化的證明

要證明 $\exists x, P(x)$，需找到具體的 $a$ 並證明 $P(a)$：

```lean
theorem exists_intro {α : Type} {P : α → Prop} (a : α) (h : P a) : ∃ x : α, P x := Exists.intro a h
```

使用（消除）存在命題：
```lean
theorem exists_elim {α : Type} {P : α → Prop} {q : Prop} (h : ∃ x : α, P x) (g : ∀ x : α, P x → q) : q := Exists.elim h g
```

### 雙重量化

$$(\forall x, \exists y, P(x,y)) \leftrightarrow (\exists f, \forall x, P(x, f(x)))$$

這是選擇公理的另一種表述。

## 程式意義

### 對應關係

在 Curry-Howard 對應下：
- 全稱量化 $\forall x, P(x)$ 對應依賴函數類型 $(x : \alpha) \to P(x)$
- 存在量化 $\exists x, P(x)$ 對應 Sigma 類型 $\Sigma x : \alpha, P(x)$

### 量化與資料結構

```lean
theorem forall_plus (n : Nat) : ∀ m : Nat, n + m ≥ n
```

這表達了加法保持下界的不變性。

### 唯一性量化

$$\exists! x, P(x) \iff \exists x, P(x) \land \forall y, P(y) \to y = x$$

## 教學重點

1. 全稱量化的 intro/elim 規則
2. 存在量化的 intro/elim 規則
3. 雙重量化的交換律成立條件
4. 選擇公理的邏輯地位