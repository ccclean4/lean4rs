# PointsAndLines.lean

## 數學原理

### 點的代數表示

平面上的點 $(x, y)$ 是二維歐氏空間 $\mathbb{R}^2$ 的元素：

$$P = (x, y) \in \mathbb{R}^2$$

### 直線的方程

一般式：$ax + by + c = 0$（其中 $a, b$ 不同時為零）

向量形式：$\vec{n} \cdot \vec{x} + c = 0$，其中 $\vec{n} = (a, b)$ 是法向量。

### 距離公式

點到點的距離（歐氏距離）：

$$d(P, Q) = \sqrt{(x_1 - x_2)^2 + (y_1 - y_2)^2}$$

點到直線的距離：

$$d(P, l) = \frac{|ax_0 + by_0 + c|}{\sqrt{a^2 + b^2}}$$

### 直線間的關係

- **平行**：法向量成比例，$a_1 b_2 = a_2 b_1$
- **垂直**：法向量內積為零，$a_1 a_2 + b_1 b_2 = 0$

## 程式意義

### Point 結構

```lean
structure Point where
  x : Float
  y : Float
```

### Line 結構

```lean
structure Line where
  a : Float
  b : Float
  c : Float
  valid : a ≠ 0 ∨ b ≠ 0
```

`valid` 欄位確保直線不是退化的。

### 交點計算

```lean
def Line.intersection (l1 l2 : Line) : Option Point := do
  let det := l1.a * l2.b - l2.a * l1.b
  guard (det ≠ 0)
  let x := (l2.c * l1.b - l1.c * l2.b) / det
  let y := (l1.c * l2.a - l2.c * l1.a) / det
  pure ⟨x, y⟩
```

使用行列式（克拉默法則）求交點。

### 對稱變換

點關於直線的反射：

```lean
def Point.reflect (p : Point) (l : Line) : Point := do
  let perp := Line.perpendicularThrough p l
  let intersection := Line.intersection l perp
  match intersection with
  | some m => Point.add p (Point.scale (Point.sub p m) 2)
  | none => p
```

## 教學重點

1. 解析幾何的基本表示
2. 從幾何到代數的轉換
3. 不確定性處理（Option）
4. 幾何變換的代數描述