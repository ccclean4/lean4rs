# Transformations.lean

## 數學原理

### 平面幾何變換

平面變換是 $\mathbb{R}^2$ 到自身的雙射。

#### 剛體變換（等距變換）
- 保持距離
- 包括：平移、旋轉、反射

#### 仿射變換
- 保持直線與平行線
- 可表示為 $T(x) = Ax + b$，其中 $A$ 是可逆矩陣

### 變換的代數表示

$$T(x) = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \begin{pmatrix} x \\ y \end{pmatrix} + \begin{pmatrix} e \\ f \end{pmatrix}$$

### 變換群

- **歐幾里得群** $E(2)$：剛體變換組成的群
- **仿射群** $Aff(2)$：所有可逆仿射變換

### 變換的性質

| 變換 | 矩陣 | 性質 |
|------|------|------|
| 恆等 | $I$ | 所有距離不變 |
| 旋轉 | $\begin{pmatrix} \cos\theta & -\sin\theta \\ \sin\theta & \cos\theta \end{pmatrix}$ | 保持距離、方向 |
| 反射 | 正交矩陣（$\det = -1$） | 保持距離、反轉方向 |
| 縮放 | $sI$ | 保持角度 |

## 程式意義

### Point2D 結構

```lean
structure Point2D where
  x : Float
  y : Float
```

### 變換的複合

```lean
def Transformation.compose (T1 T2 : Transformation) : Transformation := do
  match T1, T2 with
  | .rigid M1 v1, .rigid M2 v2 => .rigid (M2.mul M1) (Matrix2D.apply M2 v1 + v2)
  ...
```

使用匹配來處理不同類型的變換。

### 正交性檢測

```lean
def Transformation.isometry (T : Transformation) : Bool := do
  match T with
  | .rigid M v =>
    let c1 := Vector2D ⟨M.a11, M.a21⟩
    let c2 := Vector2D ⟨M.a12, M.a22⟩
    (c1.norm ≈ 1) ∧ (c2.norm ≈ 1) ∧ (c1.dot c2 ≈ 0)
```

## 教學重點

1. 變換的分類與性質
2. 矩陣作為線性變換的表示
3. 剛體變換與仿射變換的區別
4. 變換群的結構