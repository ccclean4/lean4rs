# Probability.lean

## 數學原理

### 機率空間

三元組 $(\Omega, \mathcal{F}, P)$：
- $\Omega$：樣本空間
- $\mathcal{F}$：事件域（$\Omega$ 的子集族）
- $P$：機率測度

### 機率測度的性質

1. **非負性**：$P(A) \geq 0$
2. **正規化**：$P(\Omega) = 1$
3. **可數可加性**：互斥事件的可數並的機率等於機率之和

### 條件機率

$$P(A|B) = \frac{P(A \cap B)}{P(B)}$$

### 貝葉斯定理

$$P(A|B) = \frac{P(B|A)P(A)}{P(B)}$$

### 常見分布

| 分布 | 參數 | 均值 | 方差 |
|------|------|------|------|
| Bernoulli | $p$ | $p$ | $p(1-p)$ |
| Binomial | $n, p$ | $np$ | $np(1-p)$ |
| Poisson | $\lambda$ | $\lambda$ | $\lambda$ |

### 極限定理

- **大數定律**：樣本均值依概率收斂於期望值
- **中央極限定理**：標準化和趨近於標準常態分布

## 程式意義

### ProbabilitySpace 結構

```lean
structure ProbabilitySpace where
  space : Type
  Pr : Event space → Float
  nonempty : ∃ ω : space, True
  measure_one : Pr (fun _ => True) = 1
  countable_additivity : ...
```

### 隨機變數

```lean
def RandomVariable (Ω : Type) (P : ProbabilitySpace) (α : Type) :=
  Ω → α
```

隨機變數是樣本空間到值空間的函數。

### 期望值與變異數

```lean
def expectation {Ω : Type} {P : ProbabilitySpace} (X : RandomVariable Ω P Float) : Float

def variance {Ω : Type} {P : ProbabilitySpace} (X : RandomVariable Ω P Float) : Float
```

## 教學重點

1. 機率論的公理化構造
2. 條件機率與獨立性
3. 貝葉斯推斷的基礎
4. 大數定律與中央極限定理