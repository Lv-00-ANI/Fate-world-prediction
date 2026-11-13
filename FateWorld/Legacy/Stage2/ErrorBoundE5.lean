import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# `Fate/Stage2/ErrorBoundE5` —— `𝖤₅` 分布偏移误差界（基础）

## 内容

分布偏移误差的**基础代数工具**。

## 理论形式

$$|R_Q - R_P| \le L \cdot W_1(P, Q)$$

**⚠ 完整的 Wasserstein 距离需要测度论载体，工作量大。**
本文件只交付**最基础的三角不等式与 Lipschitz 传递**。
-/

namespace Fate.Stage2.ErrorBoundE5

open Finset

variable {ι : Type*} [Fintype ι]

/-! ## §1 ⭐⭐ 权重的可加性 -/

/-- ⭐⭐ **权重差分求和为 0**（`∑p = ∑q = 1` 时）。

**⚠ 这是分布偏移的核心：`∑(q-p) = 0`。** -/
theorem weight_diff_sum_zero
    (p q : ι → ℝ) (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1) :
    ∑ i, (q i - p i) = 0 := by
  rw [Finset.sum_sub_distrib, hqsum, hpsum]
  norm_num

/-! ## §2 ⭐⭐⭐ Lipschitz 加权界 -/

/-- ⭐⭐⭐ **Lipschitz 加权界**：

若 `|a i| ≤ L` 对所有 `i`，则

$$\left|\sum_i a_i \cdot w_i\right| \le L \cdot \sum_i |w_i|.$$

**⚠ 这是 `E5` 的**核心不等式**（`a` 是损失的差分，`w` 是分布的差分）。** -/
theorem weighted_sum_bound
    (a w : ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (ha : ∀ i, |a i| ≤ L) :
    |∑ i, a i * w i| ≤ L * ∑ i, |w i| := by
  calc |∑ i, a i * w i|
      ≤ ∑ i, |a i * w i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |w i| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul]
    _ ≤ ∑ i, L * |w i| := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (ha i) (abs_nonneg _)
    _ = L * ∑ i, |w i| := by rw [Finset.mul_sum]

/-! ## §3 ⭐⭐⭐ 分布偏移的三角界 -/

/-- ⭐⭐⭐ **分布偏移的三角界**：

若 `ell` 是 `L`-Lipschitz 且**以 `e0` 为参照**（`|ell i - e0| ≤ L`），则

$$\left|\sum_i (\ell_i - e_0)(q_i - p_i)\right| \le L \sum_i |q_i - p_i|.$$

**⚠ 这是 `E5` 的**主定理的代数形式**（`q - p` 是分布差分，`∑|q-p|` 是 `W₁` 的上界）。** -/
theorem distribution_shift_bound
    (ell : ι → ℝ) (q p : ι → ℝ) (e0 L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ i, |ell i - e0| ≤ L) :
    |∑ i, (ell i - e0) * (q i - p i)| ≤ L * ∑ i, |q i - p i| := by
  apply weighted_sum_bound (a := fun i => ell i - e0) (w := fun i => q i - p i)
  · exact hL
  · intro i
    exact hlip i

/-! ## §4 公理审计 -/

#print axioms weight_diff_sum_zero
#print axioms weighted_sum_bound
#print axioms distribution_shift_bound

end Fate.Stage2.ErrorBoundE5