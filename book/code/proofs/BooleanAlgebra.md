# BooleanAlgebra.lean

## 數學原理

### 布爾代數的定義

布爾代數是一個集合 $B$ 配備兩個二元運算 $\land$（AND）、$\lor$（OR）和一元運算 $\neg$（NOT），滿足以下公理：

| 公理 | 名稱 |
|------|------|
| $a \land a = a$ | 冪等律 |
| $a \lor a = a$ | 冪等律 |
| $a \land b = b \land a$ | 交換律 |
| $a \lor b = b \lor a$ | 交換律 |
| $a \land (b \land c) = (a \land b) \land c$ | 結合律 |
| $a \lor (b \lor c) = (a \lor b) \lor c$ | 結合律 |
| $a \land (a \lor b) = a$ | 吸收律 |
| $a \lor (a \land b) = a$ | 吸收律 |
| $a \land (b \lor c) = (a \land b) \lor (a \land c)$ | 分配律 |
| $a \lor (b \land c) = (a \lor b) \land (a \lor c)$ | 分配律 |
| $\neg(\neg a) = a$ | 雙重否定 |
| $\neg a \land a = \bot$ | 矛盾 |
| $\neg a \lor a = \top$ | 排中 |

### 布爾代數與邏輯

布爾代數與命題邏輯完全對應：
- $\land$ 對應命題的「且」
- $\lor$ 對應命題的「或」
- $\neg$ 對應命題的「否定」

## 程式意義

### 基本運算的實現

```lean
def and : Bool → Bool → Bool
  | .true, b => b
  | .false, _ => .false

def or : Bool → Bool → Bool
  | .true, _ => .true
  | .false, b => b

def not : Bool → Bool
  | .true => .false
  | .false => .true
```

真值表实现，直接对应逻辑联结词。

### 交換律證明

```lean
theorem andComm (a b : Bool) : and a b = and b a
```

通过情况分析（cases）证明所有组合都满足交换性。

### 結合律證明

```lean
theorem andAssoc (a b c : Bool) : and (and a b) c = and a (and b c)
```

通過對 $a, b, c$ 的所有 $2^3 = 8$ 種組合進行枚舉證明。

### 分配律證明

```lean
theorem andOrDist (a b c : Bool) : and a (or b c) = or (and a b) (and a c)
```

同樣通過枚舉證明。

## 教學重點

1. 布爾代數的公理系統
2. 命題邏輯與布爾代數的對應
3. 透過枚舉證明有限域的性质
4. 布爾代數與集合代數的類比