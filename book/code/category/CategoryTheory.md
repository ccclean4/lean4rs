# CategoryTheory.lean

## 數學原理

### 範疇的定義

範疇 $\mathcal{C}$ 由以下組成：
- **對象**（Objects）：$\text{Ob}(\mathcal{C})$
- **態射**（Morphisms）：$f : A \to B$ 或 $A \xrightarrow{f} B$
- **複合**：$g \circ f$
- **單位態射**：$\text{id}_A$

滿足：
1. **結合律**：$(f \circ g) \circ h = f \circ (g \circ h)$
2. **單位律**：$\text{id} \circ f = f = f \circ \text{id}$

### 函子

函子 $F : \mathcal{C} \to \mathcal{D}$ 包含：
- 對象映射：$F : \text{Ob}(\mathcal{C}) \to \text{Ob}(\mathcal{D})$
- 態射映射：$F : (A \xrightarrow{f} B) \to (FA \xrightarrow{Ff} FB)$

保持：
- $F(\text{id}_A) = \text{id}_{FA}$
- $F(g \circ f) = Fg \circ Ff$

### 自然變換

自然變換 $\eta : F \Rightarrow G$ 對每個對象 $A$ 給出態射 $\eta_A : FA \to GA$，使得：

$$\eta_B \circ Ff = Gf \circ \eta_A$$

## 程式意義

### Category 類別

```lean
class Category (C : Type) where
  Hom : C → C → Type
  id : ∀ x : C, Hom x x
  compose : ∀ {x y z : C}, Hom y z → Hom x y → Hom x z
```

這是對範疇的抽象定義。

### 集合範疇

```lean
instance : Category Type where
  Hom := fun A B => A → B
  id := fun x => x
  compose := fun g f x => g (f x)
```

類型作為對象，函數作為態射。

### 米田引理

$$\text{Hom}(c, F) \cong F(c)$$

這是範疇論中最深刻的结果之一。

## 教學重點

1. 範疇作為數學結構的統一框架
2. 函子作為範疇之間的映射
3. 自然變換作為函子之間的映射
4. 通用構造（終對象、積、余積）