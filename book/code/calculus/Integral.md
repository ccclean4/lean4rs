# Integral.lean

## 數學原理

### 黎曼積分

函數 $f$ 在 $[a,b]$ 上可積：

$$\int_a^b f(x)\,dx = \lim_{\|\Delta\| \to 0} \sum_{i=1}^n f(\xi_i) \Delta x_i$$

其中 $\Delta$ 是分割，$\|\Delta\|$ 是分割的 mesh（最大子區間長度）。

### 定積分的性質

1. **線性性**：$\int (af + bg) = a\int f + b\int g$
2. **區間可加性**：$\int_a^c = \int_a^b + \int_b^c$
3. **保序性**：若 $f \leq g$，則 $\int f \leq \int g$

### 微積分基本定理

若 $F' = f$，則：

$$\int_a^b f(x)\,dx = F(b) - F(a)$$

這建立了微分與積分的對偶關係。

## 程式意義

### Partition 結構

```lean
structure Partition (a b : Float) (n : Nat) where
  points : List Float
  valid : points.length = n + 1
  start : points[0] = a
  end : points[n] = b
```

分割由端點列表定義，確保長度正確且端點正確。

### Riemann 和

```lean
def RiemannSum (f : Float → Float) (p : Partition a b n) : Float :=
  let tagged := p.tagged
  List.foldl (· + ·) 0 (tagged.map (fun (dx, ξ) => f ξ * dx))
```

對每個子區間，用標記點的值乘以區間寬度求和。

### 可積性

```lean
def integrable (f : Float → Float) (a b : Float) : Prop :=
  ∃ L, ∀ ε > 0, ∃ δ > 0, ∀ p, p.partition a b → p.mesh < δ →
    abs (RiemannSum f p - L) < ε
```

存在唯一的黎曼和極限。

## 教學重點

1. 分割與黎曼和的概念
2. 可積性的嚴格定義
3. 微積分基本定理的重要性
4. 常見函數的積分公式