# Differential.lean

## 數學原理

### 導數的定義

函數 $f$ 在點 $x$ 處可導：

$$f'(x) = \lim_{h \to 0} \frac{f(x+h) - f(x)}{h}$$

### 基本微分法則

| 函數 | 導數 |
|------|------|
| $c$（常數） | $0$ |
| $x^n$ | $nx^{n-1}$ |
| $e^x$ | $e^x$ |
| $\ln x$ | $\frac{1}{x}$ |
| $\sin x$ | $\cos x$ |
| $\cos x$ | $-\sin x$ |

### 微分法則

1. **和法則**：$(f + g)' = f' + g'$
2. **積法則**：$(fg)' = f'g + fg'$
3. **商法則**：$(\frac{f}{g})' = \frac{f'g - fg'}{g^2}$
4. **鏈式法則**：$(f \circ g)' = (f' \circ g) \cdot g'$

## 程式意義

### 可導性定義

```lean
def DifferentiableAt (f : Float → Float) (x : Float) : Prop :=
  ∃ L, ∀ ε > 0, ∃ δ > 0, ∀ h, 0 < abs h ∧ abs h < δ →
    abs ((f (x + h) - f x) / h - L) < ε
```

### 基本導數的證明

```lean
theorem derivative_const (c : Float) (x : Float) : hasDerivative (fun _ => c) x 0
```

常數函數的導數為零。

### 和法則的證明

```lean
theorem derivative_sum (f g : Float → Float) (x : Float) (Lf Lg : Float)
  (hf : hasDerivative f x Lf) (hg : hasDerivative g x Lg) :
  hasDerivative (fun x => f x + g x) x (Lf + Lg)
```

利用極限的加法性質。

## 教學重點

1. 導數的嚴格定義
2. 基本函數導數的推導
3. 微分法則的形式化
4. 導數的幾何意義（切線斜率）