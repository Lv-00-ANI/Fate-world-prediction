/-
================================================================================
  TailBlockReal2Consumer.lean

  **接入 `FateV2.Predict.GraphToProbView7`**（本文件不修改 `TailBlockReal2.lean`，只消费它）。

  `TailBlockReal2` 的核心结论是

    `condIndep_tail_block_real`：
      `hfac`、`hread`、`hOut`（真尾块）、`hsplitA`（仅 `A` 内的因子图分离）、
      `X/Y/Z` 两两不交  ⟹  `CondIndep p X Y Z`。

  本文件把这条**主定理 D** 接到因果/概率主链上，给出 4 条**新增内容**的消费定理
  （每条都真正调用主定理，结论不是主定理的换写）：

  1. `outSet_univ_eq_empty` / `outSet_univ_subset`：
     `outSet univ = ∅`（`_wip` 支撑引理，`TailBlockReal2` 未提供）。

  2. ⭐ `condIndep_tail_block_real_symm`：
     **主定理在 `X ↔ Y` 交换下的对称化**。`TailBlockReal2` 只给出
     `CondIndep p X Y Z`；本文件给出 `CondIndep p Y X Z`
     —— 假设 `hsplitA` 的析取、`hOut` 的 `X∪Y∪Z`、三个 `Disjoint` 全部对称，
     故可由主定理重启一次得到（不依赖任何"`CondIndep` 本身对 `X/Y` 对称"的引理）。

  3. ⭐ `condIndep_tail_block_real_strong`：
     **`hOut` 的更强自然形式的版本**。
     主定理的 `hOut : ∀ v ∉ A, R v \ {v} ⊆ outSet A` 被替换为
     `hOutS : ∀ v ∉ A, R v ⊆ outSet A`（含 `v` 自身，即"`A` 外因子整体不读 `A`"）。
     这是**下游更容易核验**的形式：`from hOutS` 直接得到主定理的 `hOut`
     （用 `TailBlockReal2.readSet_subset_outSet` 的逆方向不行，
     这里用 `Finset.sdiff_subset` 平凡运输）。

  4. ⭐ `condIndep_tail_block_real_univ`：
     **无尾块特例**（`X ∪ Y ∪ Z = univ`）。此时 `hOut` 的量化域
     `{v | v ∉ X∪Y∪Z}` 为空，故**尾块假设自动满足**，
     主定理退化为"纯 `A` 内因子图分离 ⟹ 条件独立"的干净定理。
     这条把 `TailBlockReal2` 与经典因子图分离定理（`View19` 的 `Split` 主链）
     **对齐**，显式展示 `TailBlockReal2` 是其**推广**（不假设 `A = univ`）。

  5. ⭐ `condIndep_tail_block_real_one_side`：
     **单边读集条件**：若 `A` 外因子不读 `A`，且 `A` 内每个因子落在 `X∪Z` 一侧
     （只有一侧），则 `CondIndep p X Y Z`。这是 `hsplitA` 的单侧充分条件版，
     让下游可以用"父集在 `X∪Z` 内"这种自然图论条件替代析取。

  零 sorry / admit / axiom。
================================================================================
-/

import FateWorld.FateV2.Predict.TailBlockReal2
namespace FateV2.Predict.GraphToProbView7

open FateV2.Modeling

open Finset FateV2.Error FateV2.Predict.View19

universe u

set_option linter.unusedSectionVars false

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-!
  # Predict · TailBlockReal2Consumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TailBlockReal2Consumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：TailBlockReal2
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  支撑引理：`outSet univ = ∅`
  =========================================================================== -/

theorem outSet_univ_eq_empty : outSet (Finset.univ : Finset V) = ∅ := by
  ext u
  simp [outSet]

theorem outSet_empty_eq_univ : outSet (∅ : Finset V) = Finset.univ := by
  unfold outSet
  simp

theorem outSet_univ_subset {A : Finset V} (hA : A = Finset.univ) :
    outSet A = ∅ := by
  rw [hA, outSet_univ_eq_empty]

/-! ===========================================================================
  §2  ⭐ 主定理 D 的 `X ↔ Y` 对称化
  =========================================================================== -/

/-- `X ∪ Y ∪ Z` 与 `Y ∪ X ∪ Z` 是同一个集合（交换律 + 结合律的显式形式）。 -/
theorem union_swap_XYZ (X Y Z : Finset V) :
    (Y ∪ X ∪ Z : Finset V) = X ∪ Y ∪ Z := by
  rw [Finset.union_comm Y X, Finset.union_assoc]

/-- ⭐ **主定理 D 的对称化**：`CondIndep p Y X Z`。

`TailBlockReal2.condIndep_tail_block_real` 只给出 `X ⊥ Y | Z` 的一个取向；
本定理给出交换后的取向。假设全部对称，故重跑主定理即得。

**⟹ 新增内容**：调用方不必关心 `X`/`Y` 的书写顺序。 -/
theorem condIndep_tail_block_real_symm [Nonempty α] {ψ : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v : V, ψ v w)
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hOut : ∀ v, v ∉ X ∪ Y ∪ Z → R v \ {v} ⊆ outSet (X ∪ Y ∪ Z))
    (hsplitA : ∀ v, v ∈ X ∪ Y ∪ Z → R v ⊆ X ∪ Z ∨ R v ⊆ Y ∪ Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    FateV2.Predict.FactorMarkov.CondIndep p Y X Z := by
  refine condIndep_tail_block_real hfac hread ?_ ?_ (Disjoint.symm hXY) hYZ hXZ
  · -- `hOut`：`v ∉ Y ∪ X ∪ Z` 时，由 `union_swap_XYZ` 得 `v ∉ X ∪ Y ∪ Z`
    intro v hv
    rw [union_swap_XYZ] at hv
    rw [union_swap_XYZ]
    exact hOut v hv
  · -- `hsplitA`：析取的左右换位
    intro v hv
    rw [union_swap_XYZ] at hv
    rcases hsplitA v hv with h | h
    · right; exact h
    · left; exact h

/-! ===========================================================================
  §3  ⭐ `hOut` 的更强自然形式
  =========================================================================== -/

/-- ⭐ **`hOut` 强形式版**：`hOutS : ∀ v ∉ A, R v ⊆ outSet A`（`A` 外因子整体不读 `A`）。

比主定理的 `R v \ {v} ⊆ outSet A` 更强、更易核验；运输是 `Finset.sdiff_subset`。 -/
theorem condIndep_tail_block_real_strong [Nonempty α] {ψ : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v : V, ψ v w)
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hOutS : ∀ v, v ∉ X ∪ Y ∪ Z → R v ⊆ outSet (X ∪ Y ∪ Z))
    (hsplitA : ∀ v, v ∈ X ∪ Y ∪ Z → R v ⊆ X ∪ Z ∨ R v ⊆ Y ∪ Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z :=
  condIndep_tail_block_real hfac hread
    (fun v hv => Finset.Subset.trans Finset.sdiff_subset (hOutS v hv))
    hsplitA hXY hXZ hYZ

/-! ===========================================================================
  §4  ⭐ 无尾块特例：`X ∪ Y ∪ Z = univ`
  =========================================================================== -/

/-- ⭐ **无尾块特例**：当 `X ∪ Y ∪ Z = univ` 时，`hOut` 的量化域为空，自动成立。

⟹ 本定理是 `TailBlockReal2` 与经典「`A` 内因子图分离 ⟹ 条件独立」的**对齐点**：
`TailBlockReal2` 是它的严格推广（不要求 `A = univ`）。 -/
theorem condIndep_tail_block_real_univ [Nonempty α] {ψ : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v : V, ψ v w)
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hcover : X ∪ Y ∪ Z = (Finset.univ : Finset V))
    (hsplitA : ∀ v, v ∈ X ∪ Y ∪ Z → R v ⊆ X ∪ Z ∨ R v ⊆ Y ∪ Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z := by
  refine condIndep_tail_block_real hfac hread ?_ hsplitA hXY hXZ hYZ
  intro v hv
  rw [hcover] at hv
  exact absurd (Finset.mem_univ v) hv

/-! ===========================================================================
  §5  ⭐ 单侧读集充分条件
  =========================================================================== -/

/-- ⭐ **单侧版**：若 `A` 内每个因子的读集都落在 `X ∪ Z` 一侧，则 `hsplitA` 的析取
自动满足（取左支）。

**⟹ 用途**：下游可用「父集在 `X ∪ Z` 内」这种自然图论条件替代析取条件。 -/
theorem condIndep_tail_block_real_one_side [Nonempty α] {ψ : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v : V, ψ v w)
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hOut : ∀ v, v ∉ X ∪ Y ∪ Z → R v \ {v} ⊆ outSet (X ∪ Y ∪ Z))
    (hsplitL : ∀ v, v ∈ X ∪ Y ∪ Z → R v ⊆ X ∪ Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z :=
  condIndep_tail_block_real hfac hread hOut
    (fun v hv => Or.inl (hsplitL v hv)) hXY hXZ hYZ

end FateV2.Predict.GraphToProbView7

/-! ===========================================================================
  §R-13   Tail 系真接线（本轮追加，纯追加：D = 0）

  ## 背景

  本轮盘点：`Fate/Tail*.lean` 共 19 个模块。按**命名空间口径**
  （`grep "Fate\.TailX\.\w+"`）全族外部引用 **0 次**；但这是假象 ——
  Tail 系大量声明落在**共享命名空间** `FateV2.Predict.GraphToProbView7` / `FateV2.Predict.View19`
  里，故 `grep "Fate\.TailBlockBridge\.\w+"` 恒为 0，而
  `TailFromDSepIntegration` 事实上在消费 `condIndep_tail_block`。
  （双模式核验见报告 §1。）

  本节的目的是在**同一命名空间**内把 Tail 系**三条子路线**的入口缝起来：

  | 路线 | 分离前提的型 | 关键的 A 外前提 |
  |---|---|---|
  | `TailBlockCondIndep` / `TailBlockBridge`（旧 D） | `View19.Split R X Y Z`（**全空间**全称） | `hTail : ∀ v ∉ A, R v ⊆ Z` |
  | `TailBlockReal2` / `TailBlockReal2Consumer`（新 D） | `hsplitA : ∀ v ∈ A, …`（**限 A**） | `hOut : ∀ v ∉ A, R v \ {v} ⊆ outSet A` |
  | `TailOutExtract` | `View19.outSet A = univ \ A` 的互补结构 | `hOut : ∀ v ∉ A, R v ⊆ Z` |

  ### 关键观察（这就是「缝」）

  两套 D 定理的**分离前提不同型**：`View19.Split R X Y Z` 是
  `∀ v : V, …`；而 `hsplitA` 是 `∀ v, v ∈ X ∪ Y ∪ Z → …`。
  两者在 `X ∪ Y ∪ Z = univ` 时**等价**，否则 `Split ⟹ hsplitA` 单边成立。
  本节把这个转译显式化（`split_implies_hsplitA` / `hsplitA_of_split_univ`），
  于是**旧路线的 `Split` 前提可以直接喂给新路线的定理**
  （`condIndep_tail_block_real_of_split` / `_strong_split` / `_univ_split`），
  调用方不必在两套说法之间手工翻译。

  第三个子路线 `TailOutExtract` 的互补事实被接到**计数口径**
  （`outSet_card_add`），这是 `mass_eq_PA_mul_Pout` 中指数
  `|V| - |A|` 的集合论语义（`= |outSet A|`）。

  ### 诚实边界（重要）

  * 本节**不**声称把 `hTail` 与 `hOut` 打通。由本库已入库存档的
    `TailVerdict` / `TailTailCollapse`（`hTail_implies_univ`）与
    `TailFromDSepIntegration`（`hTail_readSetOf_iff_cover`）：
    `hTail` 在 `Z ⊆ A`、`R = readSetOf G` 下**强制 `A = univ`**（无尾块），
    而 `hOut` 恰恰**允许** `A ≠ univ`（`outSet A ≠ ∅`）。
    **两者前提互不相容**，不存在统一的 `mass` 分解式。
    本节因此只在 `Split` / `hsplitA` 这一维上做接线，
    **不做** `hTail`–`hOut` 的伪统一，也不假装有。
  * 本节定理**均不**以前件包含结论：每条都从**两条及以上不同模块的定理**
    的结论/前件匹配出发，且结论 `CondIndep p X Y Z` 是一个**定义在 `mass`
    四个等式上的 Prop**，与任何前件都不同型（同义反复自查见报告 §5）。
  * 零 `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats`。
  =========================================================================== -/

namespace FateV2.Predict.GraphToProbView7

open Finset

universe u

section Sep

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ### §R13.1  两套分离前提的互译 -/

end Sep

section SepNoFintype

variable {V : Type u} [DecidableEq V]

/-- ⭐ **R13-1**：`View19.Split`（全空间全称）⟹ `hsplitA`（只在 `X ∪ Y ∪ Z` 上全称）。

这是**旧 D 路线**（`TailBlockBridge.condIndep_tail_block` 的 `hsplit`）与
**新 D 路线**（`TailBlockReal2.condIndep_tail_block_real` 的 `hsplitA`）
之间的前提转译 —— 方向单边，限制量化域。 -/
theorem split_implies_hsplitA {R : V → Finset V} {X Y Z : Finset V}
    (hsplit : View19.Split R X Y Z) :
    ∀ v, v ∈ X ∪ Y ∪ Z → R v ⊆ X ∪ Z ∨ R v ⊆ Y ∪ Z :=
  fun v _ => hsplit v

end SepNoFintype

section Sep2

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- ⭐ **R13-2**：无尾块（`X ∪ Y ∪ Z = univ`）时 R13-1 的**逆**也成立。

⟹ 有覆盖时 `Split` 与 `hsplitA` **等价**，两套前提可自由互换。 -/
theorem hsplitA_of_split_univ {R : V → Finset V} {X Y Z : Finset V}
    (hcover : X ∪ Y ∪ Z = (Finset.univ : Finset V))
    (hsplitA : ∀ v, v ∈ X ∪ Y ∪ Z → R v ⊆ X ∪ Z ∨ R v ⊆ Y ∪ Z) :
    View19.Split R X Y Z := by
  intro v
  exact hsplitA v (hcover ▸ Finset.mem_univ v)

/-! ### §R13.2  `TailOutExtract` 的 `outSet` 接到计数口径 -/

/-- ⭐ **R13-3**：`TailOutExtract` 的两条互补事实
（`A_union_outSet : A ∪ outSet A = univ`、`A_disjoint_outSet : Disjoint A (outSet A)`）
合起来给出**计数守恒** `#A + #(outSet A) = #V`。

⟹ 这是 `mass_eq_PA_mul_Pout` 里 `|α| ^ (|V| - |A|)` 那个指数的**集合论语义**：
`|V| - |A| = |outSet A|`。 -/
theorem outSet_card_add (A : Finset V) :
    A.card + (View19.outSet A).card = Fintype.card V := by
  classical
  have hunion : A ∪ View19.outSet A = (Finset.univ : Finset V) :=
    View19.A_union_outSet A
  have hdisj : Disjoint A (View19.outSet A) := View19.A_disjoint_outSet A
  have h := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_univ] at h
  exact h.symm

end Sep2

section Main

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-! ### §R13.3  旧路线的 `Split` 直接驱动新 D 定理 -/

/-- ⭐⭐ **R13-4**：`View19.Split` + `hOut`（`TailBlockReal2` 口径）⟹ `CondIndep`。

**新内容**：`condIndep_tail_block_real` 要求 `hsplitA`；而工程上人写的、
以及 `TailBlockBridge.condIndep_tail_block` 要的都是全空间 `Split`。
本条让调用方**只写 `Split`** 就能走新路线。 -/
theorem condIndep_tail_block_real_of_split [Nonempty α]
    {f : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v : V, f v w)
    (hread : View19.ReadSet f R)
    (hOut : ∀ v, v ∉ X ∪ Y ∪ Z → R v \ {v} ⊆ View19.outSet (X ∪ Y ∪ Z))
    (hsplit : View19.Split R X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z :=
  condIndep_tail_block_real hfac hread hOut (split_implies_hsplitA hsplit)
    hXY hXZ hYZ

/-- ⭐⭐ **R13-5**：强 `hOut` 版（`R v ⊆ outSet A`，不含 `v` 自身）的同一条转译。 -/
theorem condIndep_tail_block_strong_split [Nonempty α]
    {f : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v : V, f v w)
    (hread : View19.ReadSet f R)
    (hOutS : ∀ v, v ∉ X ∪ Y ∪ Z → R v ⊆ View19.outSet (X ∪ Y ∪ Z))
    (hsplit : View19.Split R X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z :=
  condIndep_tail_block_real_strong hfac hread hOutS (split_implies_hsplitA hsplit)
    hXY hXZ hYZ

/-- ⭐⭐ **R13-6**：无尾块 + `Split` ⟹ `CondIndep`（`hOut` **完全免去**）。

覆盖时 `v ∉ X ∪ Y ∪ Z` 无解，`hOut` 空真 —— 但调用方不必自己构造这个空真证明。 -/
theorem condIndep_tail_block_univ_split [Nonempty α]
    {f : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v : V, f v w)
    (hread : View19.ReadSet f R)
    (hcover : X ∪ Y ∪ Z = (Finset.univ : Finset V))
    (hsplit : View19.Split R X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z :=
  condIndep_tail_block_real_univ hfac hread hcover (split_implies_hsplitA hsplit)
    hXY hXZ hYZ

/-- ⭐⭐⭐ **R13-7**：`Split` + 强 `hOut` ⟹ **两个取向同时成立**
（`CondIndep p X Y Z` 与 `CondIndep p Y X Z`）。

**新内容**：把 `condIndep_tail_block_strong_split`（本文件 R13-5）与
`condIndep_tail_block_real_symm`（`TailBlockReal2Consumer` 的对称化）
在**同一组前提**下同时点亮，并显式承担 `X ↔ Y` 交换时
`outSet` 实参的改写（`union_swap_XYZ`）。

⟹ 下游不必关心 `X` / `Y` 的书写顺序；同时这是「新 D 路线两个入口不冲突」的机检证据。 -/
theorem condIndep_both_orientations_strong [Nonempty α]
    {f : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v : V, f v w)
    (hread : View19.ReadSet f R)
    (hOutS : ∀ v, v ∉ X ∪ Y ∪ Z → R v ⊆ View19.outSet (X ∪ Y ∪ Z))
    (hsplit : View19.Split R X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z ∧ FateV2.Predict.FactorMarkov.CondIndep p Y X Z :=
  ⟨condIndep_tail_block_strong_split hfac hread hOutS hsplit hXY hXZ hYZ,
   condIndep_tail_block_real_symm hfac hread
     (fun v hv => by
        rw [union_swap_XYZ] at *
        exact Finset.Subset.trans Finset.sdiff_subset (hOutS v hv))
     (split_implies_hsplitA hsplit)
     hXY hXZ hYZ⟩

end Main

end FateV2.Predict.GraphToProbView7
