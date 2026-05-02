# 02 - 基本語法與資料結構

## 變數與類型

Lean 4 是靜態類型語言，每個表達式都有確定的類型。

```lean
def x : Nat := 42        -- 自然數
def y : Int := -7        -- 整數
def z : Float := 3.14    -- 浮點數
def b : Bool := true     -- 布林值
```

## 基本資料結構

### 單位類型 (Unit)

```lean
def unit : Unit := ()
```

### 布林 (Bool)

```lean
def myTrue : Bool := true
def myFalse : Bool := false
```

### 自然數 (Nat)

```lean
def zero : Nat := 0
def five : Nat := 5
def add_example : Nat := 5 + 3  -- 8
```

### 字串與字元

```lean
def greeting : String := "Hello"
def letter : Char := 'A'
```

## 函數定義

```lean
def add (a b : Nat) : Nat := a + b

def double (n : Nat) : Nat := n * 2

def isZero (n : Nat) : Bool := n == 0
```

## 區域變數

```lean
def example : Nat := do
  let a := 5
  let b := 3
  a + b  -- 8
```

## List（列表）

```lean
def nums : List Nat := [1, 2, 3, 4, 5]

def head (xs : List α) : α := xs.head!

def tail (xs : List α) : List α := xs.tail!
```

## Option（選項）

```lean
def findPositive (n : Nat) : Option Nat :=
  if n > 0 then some n else none
```

## 基本運算

```lean
#eval 5 + 3        -- 8
#eval 10 - 3       -- 7
#eval 4 * 2        -- 8
#eval 10 / 3       -- 3 (整數除法)
#eval 10 % 3       -- 1
```

## 比較運算

```lean
#eval 5 < 3       -- false
#eval 5 > 3       -- true
#eval 5 == 5      -- true
#eval 5 ≠ 3       -- true
```

## 迴圈與遞迴

Lean 4 沒有迴圈語法，使用遞迴：

```lean
def factorial (n : Nat) : Nat :=
  if n == 0 then 1 else n * factorial (n - 1)

#eval factorial 5  -- 120
```

## where 子句

```lean
def isPrime (n : Nat) : Bool := do
  if n < 2 then false
  else not (hasDivisor n 2)
where
  hasDivisor (d : Nat) : Bool :=
    if d * d > n then false
    else if n % d == 0 then true
    else hasDivisor (d + 1)

#eval isPrime 7   -- true
#eval isPrime 10  -- false
```

## 練習

1. 定義函數計算兩數最大值
2. 定義遞迴函數計算第 n 個費波那契數
3. 定義函數反轉 List