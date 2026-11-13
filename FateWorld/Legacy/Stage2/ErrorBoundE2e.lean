import FateWorld.Legacy.Stage2.ErrorBoundE2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# `exp` 的二次上界

辅助引理放在 `Fate` 命名空间之外计算（`Fate` 命名空间中的 `linarith` 在
`k * x` 形式的系数匹配上表现异常），随后在 `Fate.Stage2.ErrorBoundE2e`
中以完全限定名引用。
-/

/-- 辅助：`x ≥ 1` 时 `1 + x + x² ≥ 3`（避免在 `Fate` 命名空间内使用 `linarith`）。 -/
theorem exp_quad_aux_ge_one {x : ℝ} (h : (2 : ℝ) ≤ x + x) :
    (3 : ℝ) ≤ 1 + x + x^2 := by
  rw [show (1 : ℝ) + x + x^2 = 1 + x * (1 + x) by ring]
  have h1 : (1 : ℝ) ≤ x := by linarith
  have h2 : (1 : ℝ) ≤ 1 + x := by linarith
  have hz : (0 : ℝ) ≤ 1 + x := by linarith
  have hm : (1 : ℝ) * (1 + x) ≤ x * (1 + x) := mul_le_mul_of_nonneg_right h1 hz
  linarith [hm]

namespace Fate.Stage2.ErrorBoundE2e

/-- ⭐⭐⭐⭐ **`exp` 的二次上界**（`0 ≤ x ≤ 1`）：

$$\exp x \le 1 + x + x^2$$

**⚠ 这是 `psi_symmetric` 缺失的关键引理。** -/
theorem exp_le_quadratic_upper {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x^2 := by
  rcases lt_or_ge (x + x) 2 with h | h
  · -- case `x < 1/2` : Taylor expansion at order 3 via `Real.exp_bound'`
    have hb := Real.exp_bound' (x := x) hx0 hx1 (n := 3) (by norm_num)
    have hsum : (∑ m ∈ Finset.range 3, x ^ m / (↑m.factorial : ℝ))
        = 1 + x + x^2/2 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    have hfact : (Nat.factorial 3 : ℝ) = 6 := by norm_num
    have hxx : (0:ℝ) ≤ x ^ 2 := sq_nonneg x
    have hxx2 : (0:ℝ) ≤ x * (2 - (x + x)) := mul_nonneg hx0 (by linarith)
    rw [hsum] at hb
    rw [hfact] at hb
    nlinarith [hb, hxx, hxx2]
  · -- case `x ≥ 1/2` : `1 + x + x² ≥ 3 > exp 1 ≥ exp x`
    have h3 : (3 : ℝ) ≤ 1 + x + x^2 := exp_quad_aux_ge_one h
    have h4 : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hx1
    have h5 : Real.exp 1 < 3 := Real.exp_one_lt_three
    linarith

end Fate.Stage2.ErrorBoundE2e

-- ⭐ **公理审计**
#print axioms Fate.Stage2.ErrorBoundE2e.exp_le_quadratic_upper
