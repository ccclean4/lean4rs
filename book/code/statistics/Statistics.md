# Statistics.lean

## 數學原理

### 集中趨勢

| 統計量 | 定義 |
|--------|------|
| 均值（Mean） | $\bar{x} = \frac{1}{n}\sum_{i=1}^n x_i$ |
| 中位數（Median） | 排序後的中間值 |
| 眾數（Mode） | 出現次數最多的值 |

### 變異程度

| 統計量 | 定義 |
|--------|------|
| 方差（Variance） | $\sigma^2 = \frac{1}{n}\sum(x_i - \bar{x})^2$ |
| 標準差（Std Dev） | $\sigma = \sqrt{\sigma^2}$ |
| 全距（Range） | $\max - \min$ |
| 四分位距（IQR） | $Q_3 - Q_1$ |

### 相關性

**共變異數**：
$$\text{Cov}(X,Y) = \frac{1}{n}\sum(x_i - \bar{x})(y_i - \bar{y})$$

**相關係數**：
$$\rho_{XY} = \frac{\text{Cov}(X,Y)}{\sigma_X \sigma_Y}$$

## 程式意義

### 基本統計量

```lean
def mean (xs : List Float) : Float :=
  if xs.isEmpty then 0 else List.sum xs / xs.length.toFloat

def median (xs : List Float) : Float := ...
def variance (xs : List Float) : Float := ...
def stdDev (xs : List Float) : Float := ...
```

### 分位數

```lean
def quartile (xs : List Float) (q : Float) : Float := ...
def percentile (xs : List Float) (p : Float) : Float := ...
```

### 標準化

```lean
def zScore (x : Float) (xs : List Float) : Float := do
  let m := mean xs
  let s := stdDev xs
  if s > 0 then (x - m) / s else 0

def standardize (xs : List Float) : List Float := ...
```

Z-score 將資料標準化為均值為 0、標準差為 1 的分布。

### 相關係數

```lean
def correlation (xs ys : List Float) : Float := do
  let cov := covariance xs ys
  let sx := stdDev xs
  let sy := stdDev ys
  if sx > 0 ∧ sy > 0 then cov / (sx * sy) else 0
```

## 教學重點

1. 描述統計與推論統計的區別
2. 各種集中趨勢量數的適用場景
3. 變異性量數的計算
4. 相關係數的解釋