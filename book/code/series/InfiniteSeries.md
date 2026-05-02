# InfiniteSeries.lean

## 數學原理

### 無限級數

序列 $(a_n)$ 的無窮級數：

$$\sum_{n=0}^{\infty} a_n = \lim_{N \to \infty} \sum_{n=0}^{N} a_n$$

### 收斂判別法

#### 比較審斂法

若 $0 \leq a_n \leq b_n$ 且 $\sum b_n$ 收斂，則 $\sum a_n$ 收斂。

#### 比值審斂法

$$L = \lim_{n \to \infty} \left|\frac{a_{n+1}}{a_n}\right|$$

- $L < 1$：絕對收斂
- $L > 1$：發散
- $L = 1$：不定

#### 根值審斂法

$$L = \lim_{n \to \infty} \sqrt[n]{|a_n|}$$

### 重要級數

| 級數 | 公式 | 收斂條件 |
|------|------|----------|
| 幾何級數 | $\sum r^n$ | $|r| < 1$ |
| p-級數 | $\sum \frac{1}{n^p}$ | $p > 1$ |
| 交錯級數 | $\sum (-1)^n a_n$ | $a_n \downarrow 0$ |

### 冪級數

$$\sum_{n=0}^{\infty} a_n (x - x_0)^n$$

收斂半徑 $R$ 由係數決定。

### 傅立葉級數

$$f(x) = \frac{a_0}{2} + \sum_{n=1}^{\infty} (a_n \cos nx + b_n \sin nx)$$

## 程式意義

### Series 結構

```lean
structure Series where
  term : Nat → Float
```

### 部分和

```lean
def Series.sum (s : Series) (n : Nat) : Float :=
  List.sum (List.take n (List.map s.term (List.range n)))
```

### 幾何級數求和公式

```lean
theorem geometricSeriesSum (r : Float) (h : abs r < 1) (n : Nat) :
  geometricSeries r |>.sum n = (1 - r^n) / (1 - r)
```

## 教學重點

1. 級數收斂的嚴格定義
2. 各種審斂法的應用條件
3. 冪級數的收斂半徑
4. 傅立葉級數的物理意義