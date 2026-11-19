import FateWorld.FateV2.Predict.ProdSplitSides
/-!
  # Predict · MassProCover

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MassProCover.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ProdSplitSides
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  主定理 C 的组装引擎（`ancestral_dSep_CondIndep` 的核心引理）

  ## 背景

  `Fate/GraphToProbView7.lean:190` 声称「4.4 主定理 C」：
  `A = X∪Y∪Z` 上因子化 + `FactorNorm` + `hsplit` ⟹ `CondIndep p X Y Z`，
  但该定理不存在。

  ## 本节给什么：`mass_prod_cover`

  **核心引擎**：
  ```lean
  theorem mass_prod_cover (hW : ∀ v ∈ W, R v ⊆ S) :
      mass S (fun w => (∏ v ∈ W, ψ v w) * g w) x
        = (∏ v ∈ W, ψ v x) * mass S g x
  ```

  **语义**：「凡读集被 `S` 覆盖的因子集 `W`，都可从 `mass S` 中整体提出。」

  **⟹ 这比 `ProdSplitSides.prod_split_sides_XYZ_statement`（只对全部因子）更一般，
  现在对**任意子集 `W`** 都成立。**

  ## 为什么这够用

  `Split R X Y Z` 给出：`∀ v, R v ⊆ X∪Z ∨ R v ⊆ Y∪Z`。
  于是对四个求和集：

  | `mass` 的 `S` | 可提出的因子集 `W` |
  |---|---|
  | `X∪Y∪Z` | **全部 `V`**（两半都 ⊆ `X∪Y∪Z`）|
  | `X∪Z` | `{v | R v ⊆ X∪Z}` |
  | `Y∪Z` | `{v | R v ⊆ Y∪Z}` |
  | `Z` | `{v | R v ⊆ Z}`（可能为空）|

  **⟹ 四个 `mass` 都能写成「因子乘积 × 剩余 `mass`」的形式。**

  ## 证明（`Finset.induction_on`）

  * 空集：`∏ ∅ = 1`，`mass S (1 * g) = mass S g`，`1 * mass S g = mass S g` ✅
  * 插入 `a ∉ s`：
    `∏_{v∈insert a s} = ψ a · ∏_{v∈s}`，用 `mass_frozen_mul`（`R a ⊆ S`）提出 `ψ a`，
    再对 `s` 用归纳假设。

  ## 诚实边界

  * **本节只给引擎**，四个 `mass` 的具体形态与 `CondIndep` 的最终配平**未做**。
  * **`CondIndep` 的配平需要「剩余 `mass`」在两边按比例对齐** —— 这是下一步。
  =========================================================================== -/

namespace FateV2.Predict.View19

open FateV2.Modeling

open Finset
open FateV2.Error
open FateV2.Predict.DAGFactorization

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-! ### §0.1 ⭐⭐⭐ 核心引擎 -/

/-- ⭐⭐⭐ **乘积提出引擎**：若 `W` 中每个因子的读集都被 `S` 覆盖，
则 `∏_{v∈W} ψ v` 可从 `mass S` 中整体提出。

**⟹ 这是主定理 C 四个 `mass` 分解的统一内核。** -/
theorem mass_prod_cover (ψ : V → (V → α) → ℝ) {R : V → Finset V}
    (hread : ReadSet ψ R) {S : Finset V} (W : Finset V)
    (hW : ∀ v ∈ W, R v ⊆ S) (g : (V → α) → ℝ) (x : V → α) :
    mass S (fun w => (∏ v ∈ W, ψ v w) * g w) x
      = (∏ v ∈ W, ψ v x) * mass S g x := by
  classical
  induction W using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    have hW' : ∀ v ∈ s, R v ⊆ S := fun v hv => hW v (Finset.mem_insert_of_mem hv)
    have haS : R a ⊆ S := hW a (Finset.mem_insert_self a s)
    have ih' := ih hW'
    have hsplit : (fun w => (ψ a w * ∏ v ∈ s, ψ v w) * g w)
        = (fun w => ψ a w * ((∏ v ∈ s, ψ v w) * g w)) := by
      funext w; ring
    rw [hsplit]
    rw [mass_frozen_mul ψ hread haS (fun w => (∏ v ∈ s, ψ v w) * g w) x]
    rw [ih']
    ring

/-! ### §0.2 ⭐⭐ 特例：全部因子可提出 -/

/-- ⭐⭐ **全部因子可提出**（`W = univ` 且全部覆盖）。

**⟹ 这就是 `ProdSplitSides.prod_split_sides_XYZ_statement` 的推广形式。** -/
theorem mass_prod_cover_all (ψ : V → (V → α) → ℝ) {R : V → Finset V}
    (hread : ReadSet ψ R) {S : Finset V} (hS : ∀ v, R v ⊆ S)
    (g : (V → α) → ℝ) (x : V → α) :
    mass S (fun w => (∏ v, ψ v w) * g w) x
      = (∏ v, ψ v x) * mass S g x := by
  have h := mass_prod_cover ψ hread Finset.univ (fun v _ => hS v) g x
  simpa using h

end FateV2.Predict.View19
