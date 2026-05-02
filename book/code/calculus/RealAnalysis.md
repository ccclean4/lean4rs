# RealAnalysis.lean

## 數學原理

### 序列的極限

序列 $(a_n)$ 收斂於 $L$：

$$\lim_{n \to \infty} a_n = L \iff \forall \varepsilon > 0, \exists N, \forall n \geq N, |a_n - L| < \varepsilon$$

### 極限的性質

1. **唯一性**：若極限存在，則唯一
2. **有界性**：收斂序列必為有界
3. **保號性**：收斂於正數的序列最終為正

### 單調收斂定理

若序列單調遞增且有上界，則必收斂於其上確界。

### 重要序列

| 序列 | 極限 |
|------|------|
| $c$（常數） | $c$ |
| $\frac{1}{n}$ | $0$ |
| $r^n$（$|r| < 1$） | $0$ |
| $\frac{n}{n+1}$ | $1$ |

## 程式意義

### Sequence 結構

```lean
structure Sequence where
  term : Nat → Float
```

### 極限定義

```lean
def Sequence.limit (a : Sequence) (L : Float) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (a.term n - L) < ε
```

這是 $\varepsilon$-$N$ 定義的形式化。

### 收斂有界定理

```lean
theorem converges_bounded (a : Sequence) (h : converges a) : bounded a
```

每個收斂序列都是有界的。

### 極限定義的應用

```lean
theorem limit_harmonic : limit seq_harmonic 0
```

$\lim_{n \to \infty} \frac{1}{n} = 0$

## 教學重點

1. 極限的 $\varepsilon$-$N$ 定義
2. 極限唯一性的證明
3. 單調收斂定理
4. 實數完备性的刻畫