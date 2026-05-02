# HelloWorld.lean

## 數學原理

本程式展示 Lean 4 的基本 IO 功能，是學習 Lean 4 的第一個程式。

## 程式意義

```lean
def main : IO Unit := do
  IO.println "======================================"
  IO.println "       Lean 4 Basics - Hello World    "
  IO.println "======================================"
```

- `main` 是程式入口點，回傳 `IO Unit`（相當於 IO 單元類型）
- `do` 區塊用於撰寫命令式程式碼
- `IO.println` 輸出字串到標準輸出

## 基本運算展示

```lean
IO.println s!"5 + 3 = {5 + 3}"
```

字串插值 `s!"..."` 允許在字串中嵌入 Lean 4 表達式的值。

## 列表操作

```lean
let nums := [1, 2, 3, 4, 5]
IO.println s!"nums = {nums}"
IO.println s!"nums.head! = {nums.head!}"
IO.println s!"nums.tail! = {nums.tail!}"
```

- `List.head!` 取得第一個元素（不安全）
- `List.tail!` 取得剩餘元素（不安全）

## 教學重點

1. Lean 4 的 `def` 關鍵字用於定義函數
2. `IO` 單子是處理副作用的方式
3. 字串插值語法 `s!"..."`