# StructuredProofs.lean

## 數學原理

### 結構化證明的動機

傳統的 tactic 腳本難以閱讀，結構化證明允許以數學風格撰寫證明。

### calc 區塊

`calc` 允許鏈式代數推導：

$$\frac{a = b \quad b = c}{a = c}$$

```lean
theorem calc_example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  calc
    a = b := h1
    _ = c := h2
```

每行目標是建立等式關係。

### show 子句

`show` 明確指出當前目標：

```lean
theorem show_example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  show p from hp   -- 明確這是 p 目標
  show q from hq   -- 明確這是 q 目標
```

### have 與 let

- `have` 建立可證明的輔助事實
- `let` 建立計算性綁定

```lean
theorem have_show (n : Nat) (h : n > 0) : n * n > 0 := by
  have hn : n ≥ 1 := Nat.lt_of_succ_le (Nat.succ_le_of_lt h)
  calc
    n * n ≥ 1 * n := Nat.mul_le_mul hn (Nat.le_refl n)
```

## 程式意義

### 計算性推理

結構化證明結合計算與邏輯：

```lean
theorem list_length_append (as bs : List Nat) : (as ++ bs).length = as.length + bs.length := by
  induction as with
  | nil => simp [List.append]
  | cons a as ih =>
    simp [List.append, List.length]
    calc
      (a :: as ++ bs).length = (as ++ bs).length + 1 := rfl
        _ = as.length + bs.length + 1 := by rw [ih]
```

### 逆向思考

有時從結論往回推更自然：

```lean
theorem reverse_thinking (p q : Prop) : (p → q) → (¬q → ¬p) := by
  intros h hnq hp      -- 假設
  have hq : q := h hp  -- 需要 q
  exact hnq hq         -- 矛盾
```

### 證明的可讀性

結構化證明的優勢：
1. 數學表達式清晰
2. 輔助事實有名字
3. 推理步驟一目了然

## 教學重點

1. `calc` 的靈活性（可混合 tactic）
2. `have` vs `let` 的選擇
3. 結構化遞迴證明的寫法
4. 閱讀與維護結構化證明