# 01 - 安裝與環境設定

Lean 4 是微軟研究院開發的互動式定理證明器，同時也是一門函數式程式語言。本書將帶領讀者從零開始學習 Lean 4。

## 安裝方式

### 方式一：Elan（推薦）

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

或手動下載：[https://github.com/leanprover/elan/releases](https://github.com/leanprover/elan/releases)

### 方式二：pip 安裝

```bash
pip install lean4
```

### 方式三：原始碼編譯

```bash
git clone https://github.com/leanprover/lean4.git
cd lean4
 Lakefile: build
```

## 編輯器設定

### VS Code（推薦）

1. 安裝 VS Code
2. 安裝擴充套件：`Lean 4`（by Sebastian Ullrich）
3. 開啟 `.lean` 檔案即可開始

### Neovim

使用 `lean.nvim` 外掛：

```lua
use({ "Julian/lean.nvim" })
```

## 專案建立

```bash
lean4_toolchain install 4.0.0
lake new my_project
cd my_project
lake build
```

## 驗證安裝

建立 `hello.lean`：

```lean
def main : IO Unit := do
  IO.println "Hello, Lean 4!"
```

執行：

```bash
lake exe my_project hello
```

輸出：`Hello, Lean 4!`

## 學習資源

- [Lean 4 官方文件](https://lean-lang.org/lean4/doc/)
- [Lean 4 GitHub](https://github.com/leanprover/lean4)
- [Functional Programming in Lean](https://leanprover.github.io/functional_programming_in_lean/)