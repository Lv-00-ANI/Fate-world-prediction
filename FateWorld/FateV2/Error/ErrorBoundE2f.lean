import FateWorld.FateV2.Error.ErrorBoundE2
import FateWorld.FateV2.Error.ErrorBoundE2b
import FateWorld.FateV2.Predict.ErrorBoundE2e
import Mathlib.Tactic

namespace FateV2.Error.Stage2.ErrorBoundE2f

open FateV2.Predict

open Finset

/-!
  # Error · ErrorBoundE2f

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ErrorBoundE2f.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Stage2.ErrorBoundE2, Stage2.ErrorBoundE2b, Stage2.ErrorBoundE2e
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-- ⭐⭐⭐ **`exp` 的二次上界对 `t ∈ [0,1]` 的推论**：

$$\exp t \le 1 + t + t^2 \le 1 + 2t$$（`t ∈ [0,1]`）

**⚠ 这是把 `eᵗ-1` 控制成 `2t` 的关键。** -/
theorem exp_le_one_add_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp t ≤ 1 + 2 * t := by
  have h := FateV2.Predict.Stage2.ErrorBoundE2e.exp_le_quadratic_upper ht0 ht1
  nlinarith [sq_nonneg t, ht0, ht1]

/-- ⭐⭐⭐⭐ **`eᵗ - 1 ≤ 2t`**（`t ∈ [0,1]`）。 -/
theorem exp_sub_one_le_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp t - 1 ≤ 2 * t := by
  have h := exp_le_one_add_two_mul ht0 ht1
  linarith

/-- ⭐⭐⭐⭐ **Hoeffding 的显式指数界**（`t ∈ [0,1]`）：

$$\exp\left(t\sum_i x_i\right) \le \exp\left(2t\sum_i x_i\right)$$

**⚠ 由 `hoeffding_prod_to_exp` 与 `eᵗ-1 ≤ 2t` 组合得到。** -/
theorem hoeffding_explicit_bound (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    Real.exp (t * ∑ i, x i) ≤ Real.exp (2 * t * ∑ i, x i) := by
  have h1 := FateV2.Error.Stage2.ErrorBoundE2b.hoeffding_prod_to_exp n t ht0 x hx
  -- h1 : exp(t * Σx) ≤ exp((eᵗ-1) * Σx)
  have h2 : Real.exp t - 1 ≤ 2 * t := exp_sub_one_le_two_mul ht0 ht1
  have hsum : 0 ≤ ∑ i, x i := by
    apply Finset.sum_nonneg
    intro i _
    exact (hx i).1
  have h3 : (Real.exp t - 1) * ∑ i, x i ≤ 2 * t * ∑ i, x i := by
    nlinarith [h2, hsum]
  have h4 : Real.exp ((Real.exp t - 1) * ∑ i, x i) ≤ Real.exp (2 * t * ∑ i, x i) := by
    apply Real.exp_le_exp.mpr
    exact h3
  linarith

-- 公理审计
#print axioms exp_le_one_add_two_mul
#print axioms exp_sub_one_le_two_mul
#print axioms hoeffding_explicit_bound

end FateV2.Error.Stage2.ErrorBoundE2f
