/-
  第2层 · 全称性审计（反例：某些 ∃ 不可升级为 ∀）

  ⚠ 零 `sorry` / `admit` / `axiom`。
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic
import FateWorld.Legacy.ObsEstimationStrong

namespace Fate
namespace AudUniv2

/-! ### 1. `estimator_error_bound` 的「无前像」∀ 升级是**假**的

若省略 `h x' = h x + η` 这条前提，而把 x' 任意量化，
则结论 `dist x' x ≤ L * ηmax` 失败（取 x' 远离 x）。 -/

theorem id_lipschitzInvertibleOn_one :
    RA14Strong.LipschitzInvertibleOn (fun x : ℝ => x) 1 := by
  intro a b
  show dist a b ≥ dist a b / 1
  rw [div_one]

/-- 反例：去掉「x' 是 hx+η 的原像」后，∀ 形式不成立。 -/
theorem no_univ_error_bound_without_preimage :
    ¬ (∀ (h : ℝ → ℝ) (L ηmax : ℝ), 0 < L → Function.Injective h →
        RA14Strong.LipschitzInvertibleOn h L →
        ∀ x η x' : ℝ, dist η 0 ≤ ηmax → dist x' x ≤ L * ηmax) := by
  intro H
  have key := H (fun x : ℝ => x) 1 0 one_pos Function.injective_id
    id_lipschitzInvertibleOn_one 0 0 1 (by rw [Real.dist_eq]; norm_num : dist (0:ℝ) 0 ≤ 0)
  simp only [Real.dist_eq, sub_zero, abs_one] at key
  norm_num at key

/-- `bound_attained_by_scaled_estimator` 的 ∀-外壳：对**所有** L>0 有取等实例。
（这是能把该 ∃ 提升到的**最强**全称形式：量化在 L 上。） -/
theorem univ_bound_attained (L : ℝ) (hL : 0 < L) :
    ∃ (xhat : ℝ → ℝ) (x η ηmax : ℝ),
      dist η 0 ≤ ηmax ∧ dist (xhat (x + η)) x = L * ηmax ∧ 0 < ηmax :=
  RA14Strong.bound_attained_by_scaled_estimator L hL

end AudUniv2
end Fate
