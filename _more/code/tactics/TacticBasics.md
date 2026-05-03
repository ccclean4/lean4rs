# TacticBasics.lean

## 數學原理

### 策略（ tactic ）的意義

Tactic 是 Lean 4 證明引擎的核心概念。每個 tactic 代表一個推理步驟：

| Tactic | 數學含義 |
|--------|----------|
| `rfl` | 反射性：$t = t$ |
| `exact h` | 直接應用：使用已知證據 |
| `apply h` | 逆流應用：匹配目標 |
| `intro` | 引入前提：$\to$ 規則 |

### 自然演繹系統

Lean 4 的 tactic 系統實現了自然演繹：

$$\frac{}{\Gamma \vdash p \to p} \text{(假言推理)}$$

```lean
theorem simple (p : Prop) (hp : p) : p := by exact hp
```

## 程式意義

### 基本 tactic

```lean
theorem basic_refl : ∀ (n : Nat), n = n := by
  intros n
  rfl
```

- `intros` 引入全稱量化的變數
- `rfl` 證明目標是反射性的

### 應用與逆流

```lean
theorem apply_example (p q r : Prop) (hp : p) (h : p → q) (h2 : q → r) : r := by
  apply h2    -- 目標：r，從結論往前提
  apply h     -- 目標：q
  exact hp    -- 目標：p
```

### 重寫戰略

`rw` 使用等式進行代換：

```lean
theorem rw_example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]  -- 依序應用等式
```

`←` 反向使用等式：
```lean
theorem rw_symm (a b : Nat) (h : a = b) : b = a := by
  rw [← h]
```

### 模式匹配

`cases` 對歸納類型進行分支：
```lean
theorem cases_example (n : Nat) : n = 0 ∨ n > 0 := by
  cases n with
  | zero => left; rfl
  | succ n => right; exact Nat.succ_pos n
```

### 結構化解構

`rcases` 使用模式解構複合值：
```lean
theorem rcases_example {p q : Prop} (h : p ∧ q) : q ∧ p := by
  rcases h with ⟨hp, hq⟩
  constructor <;> assumption
```

## 教學重點

1. tactic 的組合使用
2. `·` 語法開啟子目標
3. `simp` 與 `rw` 的區別
4. 結構化 tactic 寫法