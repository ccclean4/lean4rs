# VectorSpace.lean

## 數學原理

### 向量空間的定義

向量空間 $V$ over field $K$ 配備：
- 向量加法：$V \times V \to V$
- 純量乘法：$K \times V \to V$

滿足 8 條公理：
1. $u + (v + w) = (u + v) + w$（加法結合）
2. $u + v = v + u$（加法交換）
3. $0 + v = v$（零向量）
4. $v + (-v) = 0$（加法逆元）
5. $a(bv) = (ab)v$（純量結合）
6. $1v = v$（純量單位）
7. $a(u + v) = au + av$（左分配）
8. $(a + b)v = av + bv$（右分配）

### 基本概念

- **線性組合**：$v = \sum c_i v_i$
- **線性相關**：存在非平凡線性組合使和為零
- **基底**：極大線性無關集
- **維度**：基底中向量個數

### 內積空間

當 $K = \mathbb{R}$ 或 $\mathbb{C}$，可定義內積：

$$\langle u, v \rangle = \sum u_i \overline{v_i}$$

## 程式意義

### VectorSpace 類別

```lean
class VectorSpace (K : Type) (V : Type) [Field K] where
  add : V → V → V
  zero : V
  neg : V → V
  smul : K → V → V
  -- 公理...
```

### Vec 結構

```lean
structure Vec (K : Type) (n : Nat) : Type where
  coords : List K
  length_ok : coords.length = n
```

使用長度類型確保維度在類型層面保證。

### 點積

```lean
def dotProduct {K : Type} [Field K] {n : Nat} (u v : Vec K n) : K :=
  List.foldl (· + ·) K.zero (List.zipWith Field.mul u.coords v.coords)
```

## 教學重點

1. 向量空間的抽象定義
2. 純量乘法與向量加法的區別
3. 維度作為類型參數
4. 形式化代數的好處