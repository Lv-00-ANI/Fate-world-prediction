import FateWorld.FateV2.Predict.View19FactorGraphSplit
/-!
  # Predict · ProdSplitSides

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ProdSplitSides.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：View19FactorGraphSplit
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `prod_split_sides`：乘积拆分引理（幽灵定理的实质实现）

  ## 背景

  `Fate/View19FactorGraphSplit.lean:60` 声称：
  > **\* §5 乘积拆分引理（`prod_split_sides`）**

  **但该定理在 Lean 里不存在**（审计确认）。

  **⚠ 且该文件自己承诺「无 `sorry`。未能证明者一律登记为显式 `def … _Gap : Prop`」，
  却既未证明也未登记 ⟹ 这是**双重缺失**。**

  ## 本节做什么

  **补上「乘积的读集」这一关键引理**：

  ```lean
  theorem prod_reads : (∀ v, R v ⊆ S) → (∏ v, ψ v ·) 只读 S
  ```

  **⟹ 这是 §6 主定理的必需中间步**：`Split` 保证每个 `R v` 落在某侧，
  于是乘积在对应侧上「读集被覆盖」，从而可用 `mass_mul` 整体提出。

  ## 技术路线

  `ReadSet ψ R`（文件既有）给出每个 `ψ v` 只读 `R v`。
  若 `∀ v, R v ⊆ S`，则每个 `ψ v` 只读 `S`，故 `∏ v ψ v` 只读 `S`（`Finset.prod_congr`）。

  ## 诚实边界

  * **本节只证「乘积的读集」这一步**，不做 §6 主定理的完整组装。
  * **`Split` 到「两侧各自覆盖」的转换留给下一步**（它需要按因子分组）。
  =========================================================================== -/

namespace FateV2.Predict.View19

open FateV2.Modeling

open Finset
open FateV2.Error
open Fate.DAGFactorization

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-! ### §0.1 ⭐ 乘积的读集 -/

/-- ⭐⭐ **乘积的读集**：若每个 `ψ v` 只读 `R v` 且 `∀ v, R v ⊆ S`，
则 `∏ v, ψ v` 只读 `S`。

**⟹ 这是 `prod_split_sides` 的核心：`Split` 把每个 `R v` 放进某一侧，
于是乘积在该侧上「读集被覆盖」。** -/
theorem prod_reads (ψ : V → (V → α) → ℝ) {R : V → Finset V}
    (hread : ReadSet ψ R) {S : Finset V} (hcover : ∀ v, R v ⊆ S) :
    ∀ w w', (∀ u ∈ S, w u = w' u) → (∏ v, ψ v w) = (∏ v, ψ v w') := by
  intro w w' h
  refine Finset.prod_congr rfl ?_
  intro v _
  exact hread v w w' (fun u hu => h u (hcover v hu))

/-! ### §0.2 ⭐⭐ `Split` 下 `X∪Y∪Z` 覆盖全部因子

**`Split R X Y Z : ∀ v, R v ⊆ X∪Z ∨ R v ⊆ Y∪Z`。**

**⟹ 两半都在 `X∪Y∪Z` 内 ⟹ 全部因子被 `X∪Y∪Z` 覆盖。** -/

/-- ⭐⭐ **`X∪Y∪Z` 覆盖全部因子**（`Split` 的直接推论）。 -/
theorem split_covers_XYZ {R : V → Finset V} {X Y Z : Finset V}
    (hsplit : Split R X Y Z) : ∀ v, R v ⊆ X ∪ Y ∪ Z := by
  intro v u hu
  rcases hsplit v with h | h
  · have h1 : u ∈ X ∪ Z := h hu
    rcases Finset.mem_union.mp h1 with hx | hz
    · simp [Finset.mem_union, hx]
    · simp [Finset.mem_union, hz]
  · have h1 : u ∈ Y ∪ Z := h hu
    rcases Finset.mem_union.mp h1 with hy | hz
    · simp [Finset.mem_union, hy]
    · simp [Finset.mem_union, hz]

/-- ⭐ **`X∪Z` 覆盖 X 侧的因子**（`Split` 给出哪侧就覆盖哪侧）。 -/
theorem split_covers_XZ {R : V → Finset V} {X Y Z : Finset V}
    (hsplit : Split R X Y Z) {v : V} (h : R v ⊆ X ∪ Z) : R v ⊆ X ∪ Z := h

/-! ### §0.3 ⭐⭐⭐ `mass (X∪Y∪Z) p` 的因子提出

**`HyperFactorizes ψ p` + `ReadSet ψ R` + `Split R X Y Z` ⟹
`mass (X∪Y∪Z) p x = (∏ v, ψ v x) · mass (X∪Y∪Z) 1 x`。**

**⚠ 这一步需要 `mass_mul`（`Fate/DAGFactorization`）与 `prod_reads` 配合。
本文件只给到 `prod_reads`，组装留待下一步。** -/

/-- ⭐⭐⭐ **`mass (X∪Y∪Z) p` 的值**（因子化形式，待组装）。

**⚠ 本节只陈述，组装未做** —— 需把 `∏ v, ψ v` 当作 `mass_mul` 的 `f`，
且需要 `mass (X∪Y∪Z) 1 x` 的显式值（纤维基数）。**登记为缺口。** -/
theorem prod_split_sides_XYZ_statement
    (ψ : V → (V → α) → ℝ) (p : (V → α) → ℝ)
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : ReadSet ψ R) {X Y Z : Finset V} (hsplit : Split R X Y Z) (x : V → α) :
    mass (X ∪ Y ∪ Z) p x
      = (∏ v, ψ v x) * mass (X ∪ Y ∪ Z) (fun _ => (1 : ℝ)) x := by
  have hc := split_covers_XYZ hsplit
  have h1 : (∀ w, p w = (∏ v, ψ v w) * 1) := fun w => by rw [hfac w]; ring
  have hfun : p = fun w => (∏ v, ψ v w) * (1 : ℝ) := by
    funext w; rw [hfac w]; ring
  rw [hfun]
  exact mass_mul (X ∪ Y ∪ Z) (fun w => ∏ v, ψ v w) (fun _ => (1 : ℝ)) x
          (prod_reads ψ hread hc)

end FateV2.Predict.View19
