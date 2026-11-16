import FateWorld.FateV2.Error.ErrorBoundE5
import Mathlib.Tactic

namespace FateV2.Predict.Stage2.ErrorBoundE5Full

open FateV2.Error

open Finset
open FateV2.Error.Stage2.ErrorBoundE5

variable {ι : Type*} [Fintype ι]

/-!
  # Predict · ErrorBoundE5Full

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ErrorBoundE5Full.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Stage2.ErrorBoundE5
  - 补充 open 域：FateV2.Error
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-- ⭐⭐⭐⭐ **期望差 = 中心化损失 × 权重差**：

$$\sum_i \ell_i q_i - \sum_i \ell_i p_i = \sum_i \ell_i (q_i - p_i)$$

**⚠ 这是 `E5` 的**核心恒等式**。 -/
theorem expected_diff_eq
    (ell p q : ι → ℝ) :
    ∑ i, ell i * q i - ∑ i, ell i * p i = ∑ i, ell i * (q i - p i) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- ⭐⭐⭐⭐⭐ **`E5` 的完整形式**：

若 `ℓ` 以 `e₀` 为参照 `L`-Lipschitz，`p`、`q` 是概率分布，
则
$$\left|\sum_i \ell_i q_i - \sum_i \ell_i p_i\right| \le L \cdot \sum_i |q_i - p_i|.$$

**⚠ 这是 `E5` 的**主定理**（`∑|q-p|` 是 `W₁` 的上界）。** -/
theorem e5_main
    (ell : ι → ℝ) (p q : ι → ℝ) (e0 L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ i, |ell i - e0| ≤ L)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1) :
    |∑ i, ell i * q i - ∑ i, ell i * p i| ≤ L * ∑ i, |q i - p i| := by
  rw [expected_diff_eq]
  -- 用 `∑(q-p) = 0` 把 `ℓ` 换成 `ℓ - e₀`
  have h0 := weight_diff_sum_zero p q hpsum hqsum
  have hshift : ∑ i, (ell i - e0) * (q i - p i) = ∑ i, ell i * (q i - p i) := by
    have hsplit : ∑ i, (ell i - e0) * (q i - p i)
        = ∑ i, ell i * (q i - p i) - ∑ i, e0 * (q i - p i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hconst : ∑ i, e0 * (q i - p i) = 0 := by
      have hfac : ∑ i, e0 * (q i - p i) = e0 * ∑ i, (q i - p i) := by
        rw [Finset.mul_sum]
      rw [hfac, h0, mul_zero]
    rw [hsplit, hconst, sub_zero]
  rw [← hshift]
  exact distribution_shift_bound ell q p e0 L hL hlip

end FateV2.Predict.Stage2.ErrorBoundE5Full

-- 公理审计
#print axioms FateV2.Predict.Stage2.ErrorBoundE5Full.expected_diff_eq
#print axioms FateV2.Predict.Stage2.ErrorBoundE5Full.e5_main
