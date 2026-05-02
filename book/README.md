# Lean 4 書籍

一本關於 Lean 4 定理證明器與函數式編程語言的教材。

## 課程內容

### 第一部分：基礎入門

- [安裝與環境設定](book/01-installation.md)
- [基本語法與資料結構](book/02-basic-syntax.md)
- [函數與閉包](book/03-functions.md)

### 第二部分：類型理論

- [依賴類型與 Pi 類型](book/04-dependent-types.md)
- [Sigma 類型與資料對](book/05-sigma-types.md)
- [歸納類型與遞迴](book/06-inductive-types.md)

### 第三部分：命題與證明

- [命題與證據](book/07-propositions.md)
- [命題邏輯與連結詞](book/08-propositional-logic.md)
- [謂詞邏輯與量化](book/09-predicate-logic.md)
- [數學結構：Group, Ring, Field](book/10-math-structures.md)

### 第四部分：證明策略

- [tactic 基礎](book/11-tactics.md)
- [結構化證明](book/12-structured-proofs.md)
- [自動化證明](book/13-automation.md)

### 第五部分：實際應用

- [編寫正確的排序演算法](book/14-sorting.md)
- [形式化驗證範例](book/15-verification.md)
- [與 Python 互操作](book/16-interop.md)

## 程式碼範例

### basics/ - 基礎範例

| 檔案 | 說明 |
|------|------|
| [HelloWorld.lean](code/basics/HelloWorld.lean) | 基本 IO 輸出 |
| [DataStructures.lean](code/basics/DataStructures.lean) | List, Option, Sum 資料結構 |
| [Recursion.lean](code/basics/Recursion.lean) | 線性/尾/樹狀/互遞迴 |
| [HigherOrder.lean](code/basics/HigherOrder.lean) | map, filter, fold, compose |

### proofs/ - 證明範例

| 檔案 | 說明 |
|------|------|
| [propositions.lean](code/proofs/propositions.lean) | 命題邏輯基本定律 |
| [Induction.lean](code/proofs/Induction.lean) | 數學歸納法 |
| [Quantifiers.lean](code/proofs/Quantifiers.lean) | 全稱與存在量化 |
| [Peano.lean](code/proofs/Peano.lean) | 皮亞諾公理系統 |
| [BooleanAlgebra.lean](code/proofs/BooleanAlgebra.lean) | 布爾代數系統 |

### algorithms/ - 演算法實作

| 檔案 | 說明 |
|------|------|
| [sorting.lean](code/algorithms/sorting.lean) | 插入排序、合併排序 |
| [SearchTrees.lean](code/algorithms/SearchTrees.lean) | 二元搜尋樹 |
| [Graph.lean](code/algorithms/Graph.lean) | 圖論基礎、DFS、BFS |

### tactics/ - 證明策略

| 檔案 | 說明 |
|------|------|
| [TacticBasics.lean](code/tactics/TacticBasics.lean) | 基本 tactic 操作 |
| [StructuredProofs.lean](code/tactics/StructuredProofs.lean) | calc, show, have, let |

### datastructures/ - 資料結構

| 檔案 | 說明 |
|------|------|
| [Collections.lean](code/datastructures/Collections.lean) | Queue, Stack, Tree |

### algebra/ - 代數

| 檔案 | 說明 |
|------|------|
| [GroupTheory.lean](code/algebra/GroupTheory.lean) | 群論基礎定義與性質 |
| [RingTheory.lean](code/algebra/RingTheory.lean) | 環、整域、場 |
| [VectorSpace.lean](code/algebra/VectorSpace.lean) | 向量空間與線性代數 |

### geometry/ - 幾何

| 檔案 | 說明 |
|------|------|
| [PointsAndLines.lean](code/geometry/PointsAndLines.lean) | 點、直線、距離 |
| [EuclideanGeometry.lean](code/geometry/EuclideanGeometry.lean) | 三角形、圓、多邊形 |

### calculus/ - 微積分

| 檔案 | 說明 |
|------|------|
| [RealAnalysis.lean](code/calculus/RealAnalysis.lean) | 序列極限與收斂 |
| [Differential.lean](code/calculus/Differential.lean) | 導數與微分法則 |
| [Integral.lean](code/calculus/Integral.lean) | 黎曼積分與微積分基本定理 |

### statistics/ - 統計

| 檔案 | 說明 |
|------|------|
| [Probability.lean](code/statistics/Probability.lean) | 機率論基礎、大數定律 |
| [Statistics.lean](code/statistics/Statistics.lean) | 描述統計、集中趨勢、變異 |

### logic/ - 數理邏輯

| 檔案 | 說明 |
|------|------|
| [PropositionalLogic.lean](code/logic/PropositionalLogic.lean) | 命題邏輯語法與語義 |
| [NaturalDeduction.lean](code/logic/NaturalDeduction.lean) | 自然演繹系統 |
| [PredicateLogic.lean](code/logic/PredicateLogic.lean) | 一階謂詞邏輯 |
| [SequentCalculus.lean](code/logic/SequentCalculus.lean) | Sequent 演算 |

### category/ - 範疇論

| 檔案 | 說明 |
|------|------|
| [CategoryTheory.lean](code/category/CategoryTheory.lean) | 範疇、函子、自然變換 |

### transformations/ - 幾何變換

| 檔案 | 說明 |
|------|------|
| [Transformations.lean](code/transformations/Transformations.lean) | 剛體變換、仿射變換 |

### series/ - 無限級數

| 檔案 | 說明 |
|------|------|
| [InfiniteSeries.lean](code/series/InfiniteSeries.lean) | 幾何級數、p-級數、傅立葉級數 |

### modal/ - 模態邏輯

| 檔案 | 說明 |
|------|------|
| [ModalLogic.lean](code/modal/ModalLogic.lean) | 克里普克語義、系統 K/T/S4/S5 |

## 對應文檔

每個 `.lean` 檔案都有對應的 `.md` 說明文件，解釋其數學原理與程式意義。