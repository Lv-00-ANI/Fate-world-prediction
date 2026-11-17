import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.FactorMarkov
/-!
  # Predict · BarCorrected

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BarCorrected.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：DAGFactorization, FactorMarkov
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `bar_univ` 的**正确版本**（原版为假）

  ## 背景

  `Fate/Strategy9SinkPeelNorm.lean` 定义
  ```lean
  def tail (f) (T) : (V → α) → ℝ := fun w => ∏ v ∈ (univ \ T), f v w
  def bar (T) (f) (x) : ℝ := mass T (tail f T) x
  ```
  并声称 `bar_univ : bar univ f x = ∏ v, f v x`。

  **这是假的**：`T = univ` 时 `tail f univ = ∏ v ∈ ∅ = 1`，
  故 `bar univ f x = mass univ 1 x = 1`，而非 `∏ v, f v x`。

  ## 正确版本

  `bar_univ_correct`：`bar univ f x = 1`
  `bar_empty_correct`：`bar ∅ f x = ∑ w, ∏ v, f v w`

  ⟹ 这是本会话第 11 处真实数学错误。
  =========================================================================== -/

namespace FateV2.Predict.S9Fixed

open FateV2.Modeling
open Finset Fate.DAGFactorization
open FateV2.Modeling.Graph
universe u
variable {V : Type u} {α : Type u} [DecidableEq V] [Fintype V] [DecidableEq α] [Fintype α]

noncomputable def tail (f : V → (V → α) → ℝ) (T : Finset V) : (V → α) → ℝ :=
  fun w => ∏ v ∈ (univ \ T), f v w

noncomputable def bar (T : Finset V) (f : V → (V → α) → ℝ) (x : V → α) : ℝ :=
  mass T (tail f T) x

-- ⭐ 正确版本：bar univ f x = 1（因 tail f univ = ∏ ∅ = 1）
theorem bar_univ_correct (f : V → (V → α) → ℝ) (x : V → α) :
    bar univ f x = 1 := by
  unfold bar tail
  simp only [Finset.sdiff_self, Finset.prod_empty]
  rw [Fate.DAGFactorization.mass_univ]

-- ⭐ bar ∅ f x = ∑ w, ∏ v, f v w（tail f ∅ = ∏ v ∈ univ, f v）
theorem bar_empty_correct (f : V → (V → α) → ℝ) (x : V → α) :
    bar ∅ f x = ∑ w, ∏ v, f v w := by
  unfold bar tail
  rw [Finset.sdiff_empty, Fate.DAGFactorization.mass_empty]

end FateV2.Predict.S9Fixed
