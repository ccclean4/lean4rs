-- Basics: Hello World
-- 展示 Lean 4 的基本輸出功能

def main : IO Unit := do
  IO.println "======================================"
  IO.println "       Lean 4 Basics - Hello World    "
  IO.println "======================================"
  IO.println ""
  IO.println "基本運算："
  IO.println s!"5 + 3 = {5 + 3}"
  IO.println s!"10 - 3 = {10 - 3}"
  IO.println s!"4 * 2 = {4 * 2}"
  IO.println ""
  IO.println "布林運算："
  IO.println s!"5 < 3 = {if 5 < 3 then "true" else "false"}"
  IO.println s!"5 > 3 = {if 5 > 3 then "true" else "false"}"
  IO.println s!"5 == 5 = {if 5 == 5 then "true" else "false"}"
  IO.println ""
  IO.println "列表操作："
  let nums := [1, 2, 3, 4, 5]
  IO.println s!"nums = {nums}"
  IO.println s!"nums.head! = {nums.head!}"
  IO.println s!"nums.tail! = {nums.tail!}"
  IO.println s!"nums.length = {nums.length}"
  IO.println ""
  IO.println "完成！"