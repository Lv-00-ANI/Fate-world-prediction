import FateWorld.FateV2.Modeling.NaryFiberDecomp
import FateWorld.FateV2.Modeling.NaryMargSum
import FateWorld.FateV2.Modeling.NaryFinalBridge
import FateWorld.FateV2.Modeling.NaryAlgebra
/-!
  # Modeling · NaryAssembly

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NaryAssembly.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NaryFiberDecomp, NaryMargSum, NaryFinalBridge, NaryAlgebra
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenNAssembly  N-ary bridge: fiber mass identity (round 196)

  ## Result

    mu.real(fiberN z) = sum w, p (w, z)

  the mass of the `Z = z` fiber equals the sum of `p` over that fiber.

  ## How

  Corollary of `real_eq_sum_of_fiber` (round 195); the slice-avoidance
  hypothesis is **trivial**: `(w, z')` with `z' ≠ z` is not in `fiberN z`
  by definition.

  ## Instance note

  `fiberN` is a `def` and Lean does not unfold it while searching for a
  `DecidablePred` instance, so `[DecidablePred (· ∈ fiberN z)]` is an
  **explicit binder**; `fiberNDec` produces a witness.
  =========================================================================== -/

namespace FateV2.Modeling.GenN

open MeasureTheory ProbabilityTheory

section Witness

variable {ι : Type*} {fam : ι → Type*} {γ : Type*}

/-- Witness for `DecidablePred (· ∈ fiberN z)` (unfolds first). -/
@[instance_reducible]
def fiberNDec [DecidableEq γ] (z : γ) :
    DecidablePred (· ∈ (fiberN z : Set ((∀ j, fam j) × γ))) :=
  fun w => by unfold fiberN; infer_instance

end Witness

section FiberNMass

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*} [Fintype γ] [DecidableEq γ]
variable [MeasurableSpace γ]
variable [MeasurableSpace ((∀ j, fam j) × γ)]
variable [MeasurableSingletonClass ((∀ j, fam j) × γ)]

omit [DecidableEq γ] [MeasurableSpace γ] in
/-- ⭐⭐⭐ **mass of `fiberN z` = sum of `p` over that fiber** (needs `hp`). -/
theorem fiberN_real_eq_sum'
    (p : ((∀ j, fam j) × γ) → ℝ) (hp : ∀ w, 0 ≤ p w) (z : γ)
    [dec : DecidablePred (· ∈ (fiberN z : Set ((∀ j, fam j) × γ)))] :
    (weightedCountN p).real (fiberN z) = ∑ w : (∀ j, fam j), p (w, z) := by
  have h := real_eq_sum_of_fiber p hp (fiberN z) z
    (fun w z' hz' => by
      simp only [fiberN, Set.mem_setOf_eq]
      exact hz')
  rw [h]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  exact if_pos (by simp only [fiberN, Set.mem_setOf_eq])

end FiberNMass

end FateV2.Modeling.GenN
