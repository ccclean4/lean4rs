# 16 - 與 Python 互操作

## 為何需要互操作

Lean 4 是 theorem prover，主要用於形式化驗證。Python 是廣泛使用的程式語言，有豐富的生態系統。互操作讓我們能：
- 在 Python 中使用 Lean 4 的驗證引擎
- 將 Lean 4 證明的結果整合到 Python 應用

## 匯出 Lean 4 函數

### Lake 專案設定

```bash
lake new lean_python_interop
cd lean_python_interop
```

### `Native` 模組

對於簡單計算，可以使用 `@[export]` 屬性：

```lean
@[export]
def add_nat (a b : Nat) : Nat := a + b

@[export]
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
```

### C 共享函式庫

```bash
lake build
# 產生 .so 檔案
```

## Python FFI

使用 `cppyy` 或 ctypes：

```python
import ctypes

# 載入 Lean 產生的 C 函式庫
lib = ctypes.CDLL("./build/lib/mylib.so")

# 呼叫 Lean 函數
result = lib.lean_add_nat(3, 5)
print(f"3 + 5 = {result}")
```

## 資料轉換

```lean
-- 轉換 List 為 C 陣列指標
@[export]
def list_to_array (xs : List Float) : List Float :=
  xs
```

## 整合範例

```lean
-- Lean 端：驗證矩陣乘法
@[export]
def verify_matrix_multiply (a b c : List (List Float)) : Bool :=
  matrixMultiply a b = c

-- Python 端：使用 Lean 驗證結果
import ctypes

lib = ctypes.CDLL("./build/lib/matrix_verify.so")
lib.lean_verify_matrix_multiply.restype = ctypes.c_bool

result = lib.lean_verify_matrix_multiply(a_data, b_data, c_data)
```

## 練習

1. 建立 Lake 專案並匯出簡單函數
2. 從 Python 呼叫 Lean 函數
3. 實現矩陣驗證的 FFI
4. 處理資料結構轉換