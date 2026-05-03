# EuclideanGeometry.lean

## 數學原理

### 三角形

三角形由三個不共線的點確定：

$$T = \triangle ABC, \quad A, B, C \in \mathbb{R}^2, \quad A \neq B \neq C$$

#### 海龍公式（Heron's Formula）

已知三邊 $a, b, c$，面積為：

$$S = \sqrt{s(s-a)(s-b)(s-c)}, \quad s = \frac{a+b+c}{2}$$

#### 勾股定理

直角三角形：$a^2 + b^2 = c^2$

### 圓

圓 $\gamma = (O, r)$ 是滿足 $|OP| = r$ 的點集：

$$|OP| = r \iff (x - x_0)^2 + (y - y_0)^2 = r^2$$

### 多邊形

簡單多邊形由頂點序列定義，滿足：
- 邊不交叉
- 連續頂點不同

## 程式意義

### Triangle 結構

```lean
structure Triangle where
  A : Point
  B : Point
  C : Point
  nonDegenerate : B ≠ A ∧ C ≠ A ∧ B ≠ C
```

`nonDegenerate` 確保不是退化三角形。

### 三角形類型判斷

```lean
def Triangle.isEquilateral (t : Triangle) : Bool := do
  let (a, b, c) := sideLengths t
  a ≈ b ∧ b ≈ c

def Triangle.isRight (t : Triangle) : Bool := do
  let (a, b, c) := sideLengths t
  a^2 + b^2 ≈ c^2 ∨ b^2 + c^2 ≈ a^2 ∨ a^2 + c^2 ≈ b^2
```

### 內點判斷

點在三角形內的判斷（重心座標）：

```lean
def Point.inTriangle (p : Triangle) : Bool := do
  -- 計算重心座標的符號一致性
```

## 教學重點

1. 幾何結構的依賴類型表示
2. 海龍公式的形式化
3. 幾何性質的形式驗證
4. 浮點數比較的問題（`≈`）