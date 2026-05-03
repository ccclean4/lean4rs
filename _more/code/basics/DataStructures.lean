-- Basics: 資料結構
-- 展示 List, Option, Sum 等常見資料結構

-- List 操作
def list_examples : List Nat :=
  let nums := [1, 2, 3, 4, 5]
  let doubled := nums.map (· * 2)
  let filtered := nums.filter (· > 2)
  let summed := nums.foldl (· + ·) 0
  nums

-- 列表推導式
def list_comprehension : List Nat :=
  Id.run do
    let mut result := []
    for i in [1, 2, 3] do
      for j in [1, 2, 3] do
        result := result ++ [i * j]
    result

-- Option 類型
def safeDiv (a b : Nat) : Option Nat :=
  if b == 0 then none else some (a / b)

def findFirst (xs : List Nat) (p : Nat → Bool) : Option Nat :=
  xs.find? p

-- Sum 類型（Either）
def tryParse : String → Sum String Nat
  | "42" => .inr 42
  | s => .inl s!"無法解析: {s}"

-- 測試函數
def main : IO Unit := do
  IO.println s!"列表: {list_examples}"
  IO.println s!"列表推導: {list_comprehension}"
  IO.println s!"safeDiv 10 2 = {safeDiv 10 2}"
  IO.println s!"safeDiv 10 0 = {safeDiv 10 0}"
  IO.println s!"findFirst [1,2,3,4] (· > 2) = {[1,2,3,4].find? (· > 2)}"
  IO.println s!"tryParse \"42\" = {tryParse "42"}"
  IO.println s!"tryParse \"hello\" = {tryParse "hello"}"