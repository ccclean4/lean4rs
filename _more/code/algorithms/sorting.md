# sorting.lean

## 數學原理

### 排序的數學定義

對列表 $xs$ 排序得到 $ys$，需滿足：
1. $ys$ 是 $xs$ 的排列（permutation）
2. $ys$ 是有序的（ordered）

### 插入排序

插入排序的數學描述：

對列表 $xs = [x_1, x_2, \ldots, x_n]$：
$$\text{insertionSort}(xs) = \text{insert}(x_1, \text{insert}(x_2, \ldots \text{insert}(x_n, [])\ldots))$$

其中 `insert` 將元素插入已排序列表的正確位置。

### 合併排序

分治策略：
1. 分割：將列表從中點分開
2. 征服：遞迴排序兩半
3. 合併：合併兩個有序列表

合併的數學定義：
$$\text{merge}(xs, ys) = \begin{cases}
ys & \text{if } xs = [] \\
xs & \text{if } ys = [] \\
x :: \text{merge}(xs', ys) & \text{if } x \leq y \\
y :: \text{merge}(xs, ys') & \text{if } x > y
\end{cases}$$

## 程式意義

### 插入

```lean
def insert (a : Nat) (xs : List Nat) : List Nat :=
  match xs with
  | [] => [a]
  | x :: ys =>
    if a ≤ x then a :: x :: ys
    else x :: insert a ys
```

### 合併

```lean
def merge (xs ys : List Nat) : List Nat :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs', y :: ys' =>
    if x ≤ y then x :: merge xs' ys
    else y :: merge xs ys
```

### 正確性證明

```lean
theorem insert_preserves_length (a : Nat) (xs : List Nat) :
  (insert a xs).length = xs.length + 1
```

證明插入不改變元素個數。

## 教學重點

1. 排序的兩個條件：排列 + 有序
2. 結構遞迴原則的應用
3. 正確性證明的策略
4. 時間複雜度分析