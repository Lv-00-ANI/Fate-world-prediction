import FateWorld.FateV2.Modeling.NaryConnect3
import FateWorld.FateV2.Modeling.NaryCancel
import FateWorld.FateV2.Modeling.NaryProduct
import FateWorld.FateV2.Modeling.NaryFinalBridge
import FateWorld.FateV2.Modeling.NaryBridge
import FateWorld.FateV2.Modeling.NaryMassLink
import Mathlib.Data.Fintype.Pi

/-!
  # Modeling · NaryBridgeFinal

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NaryBridgeFinal.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NaryConnect3, NaryCancel, NaryProduct, NaryFinalBridge, NaryBridge, NaryMassLink
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenNFinalBridge  ⭐⭐⭐⭐⭐ THE N-ARY BRIDGE, FINAL FORM (round 203)

  ## Target

  With `M = (weightedCountN p).real (fiberN a.2)`, `t_i = coordSet i (Sf i : Set _)`,
  `t = iInter i, t_i`, and `kappa_a = condExpKernel (weightedCountN p) (comap snd)`:

      kappa_a(t) = prod i, kappa_a(t_i)

  ## Assembly (all pieces already proven in earlier rounds)

  | step | statement | source |
  |---|---|---|
  | 1 | `kappa(t) * M = mu.real(t ∩ fiberN z)` | `kernelValue_iInter_coordSet_mul` (r190) |
  | 1' | `mu.real(t ∩ fiberN z) = ∑ xs, [∀i, xs i ∈ Sf i] p (xs,z)` | `joint_real_eq_indicator_sum` (r202) |
  | 2 | `kappa(t_i) * M = mu.real(t_i ∩ fiberN z)` | `kernelValue_coordSet_mul` (r188) |
  | 2' | `mu.real(t_i ∩ fiberN z) = ∑ a∈Sf i, marg pN i a z` | `coordSet_real_eq_marg_sum` (r202) |
  | 3 | `(∑ xs, [...]) * M^n = ∏ i, (∑ a∈Sf i, marg i a z)` | `product_factorize` (r198) |
  | 4 | `A * M^n = ∏ i,(B i * M) -> A = ∏ i, B i` | `cancel_mass_pow` (r201) |

  This module gives the **closing algebraic step** in exactly the shape the
  bridge produces: `bridge_close`.
  =========================================================================== -/

namespace FateV2.Modeling.GenN

open MeasureTheory ProbabilityTheory

section Assembly

variable {ι : Type*} [Fintype ι]

/-- ⭐⭐⭐⭐ **the closing algebraic step of the N-ary bridge**.

Given per-`i` kernel identities `kappa_i * M = b_i`, the joint one
`kappa * M^n = prod i, b_i`, and `M ≠ 0`, conclude `kappa = prod i, kappa_i`.

**⭐ This is the exact shape in which the bridge delivers its result**:
step (1)/(2) supply the `kappa_i * M = b_i`, step (3) plus (1')/(2') supply
the joint identity, and `cancel_mass_pow` finishes. -/
theorem bridge_close
    (kappa : ℝ) (kappa_i : ι → ℝ) (b : ι → ℝ) (M : ℝ)
    (hM : M ≠ 0)
    (hi : ∀ i, kappa_i i * M = b i)
    (hj : kappa * M ^ Fintype.card ι = ∏ i, b i) :
    kappa = ∏ i, kappa_i i := by
  apply cancel_mass_pow kappa kappa_i M hM
  rw [hj]
  exact Finset.prod_congr rfl (fun i _ => (hi i).symm)

end Assembly

end FateV2.Modeling.GenN
