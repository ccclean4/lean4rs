# 03 - 函數與閉包

## 匿名函數（Lambda）

```lean
def add := fun x y => x + y

#eval add 3 4  -- 7

def square := fun x => x * x

#eval square 5  -- 25
```

## 多參數函數

```lean
def add := fun (x y : Nat) => x + y

def curriedAdd (x : Nat) (y : Nat) : Nat := x + y

#eval curriedAdd 3 4  -- 7
```

## 閉包

```lean
def makeAdder (n : Nat) : Nat → Nat := fun m => m + n

def add5 := makeAdder 5

#eval add5 3   -- 8
#eval add5 10  -- 15
```

## 高階函數

### map

```lean
def doubleAll (xs : List Nat) : List Nat :=
  xs.map (fun x => x * 2)

#eval doubleAll [1, 2, 3]  -- [2, 4, 6]
```

### filter

```lean
def evens (xs : List Nat) : List Nat :=
  xs.filter (fun x => x % 2 == 0)

#eval evens [1, 2, 3, 4, 5]  -- [2, 4]
```

### fold

```lean
def sum (xs : List Nat) : Nat :=
  xs.foldl (fun acc x => acc + x) 0

#eval sum [1, 2, 3, 4]  -- 10
```

## 函數合成

```lean
def inc := fun x => x + 1
def double := fun x => x * 2

def incThenDouble := double ∘ inc

#eval incThenDouble 5  -- 12 ( (5+1)*2 )
```

## 部分應用

```lean
def add (a b : Nat) : Nat := a + b

def add5 := add 5  -- 填入第一個參數

#eval add5 3  -- 8
```

## 遞迴函數

```lean
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 5  -- 120
```

## 尾遞迴

```lean
def factorialTail (n : Nat) : Nat → Nat
  | acc, 0 => acc
  | acc, n + 1 => factorialTail (acc * (n + 1)) n

def factorial' (n : Nat) : Nat := factorialTail 1 n
```

## 練習

1. 實作 `map` 對 List 每個元素加 1
2. 實作 `foldr`（從右邊折疊）
3. 實作 `compose` 函數合成
4. 實作快速排序