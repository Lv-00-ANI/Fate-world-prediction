import FateWorld.FateV2.Modeling.NaryMargSum
import FateWorld.FateV2.Modeling.NaryRealSum
import FateWorld.FateV2.Modeling.NaryFinalBridge
import FateWorld.FateV2.Modeling.NaryAlgebra
/-!
  # Modeling · NaryFiberDecomp

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NaryFiberDecomp.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NaryMargSum, NaryRealSum, NaryFinalBridge, NaryAlgebra
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenNFiber  fiber decomposition of `mu.real` (round 195)

  ## The general form

    mu.real t = sum w, [ (w, z) in t ] * p (w, z)

  whenever `t` avoids every other slice `(w, z')` with `z' != z`.

  ## Consequences

  - `t = fiberN z`: the hypothesis is trivial
  - `t = coordSet i S`: also trivial (`coordSet` does not depend on `z`)

  ## Instances traps diagnosed here

  1. `fiberN z` is a `def` and Lean's tc search **does not unfold it**.
  2. `classical` / `haveI` inside `by` are **too late** (the failure happens
     during statement elaboration).
  Keep `t` abstract and pass the "slice-avoidance" hypothesis instead.
  =========================================================================== -/

namespace FateV2.Modeling.GenN

open MeasureTheory ProbabilityTheory

section FiberDecomp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)] [∀ i, DecidableEq (fam i)]
variable {γ : Type*} [Fintype γ] [DecidableEq γ]
variable [MeasurableSpace γ]
variable [MeasurableSpace ((∀ j, fam j) × γ)]
variable [MeasurableSingletonClass ((∀ j, fam j) × γ)]

omit [(i : ι) → DecidableEq (fam i)] [DecidableEq γ] [MeasurableSpace γ] in
/-- ⭐⭐ **Fiber decomposition of `mu.real`** (needs `hp`).

If `t` avoids every slice `(w, z')` with `z' ≠ z`, then `mu.real t` is the sum
of `p` over the `z`-slice of `t`. -/
theorem real_eq_sum_of_fiber
    (p : ((∀ j, fam j) × γ) → ℝ) (hp : ∀ w, 0 ≤ p w)
    (t : Set ((∀ j, fam j) × γ)) [DecidablePred (· ∈ t)]
    (z : γ)
    (h : ∀ w : (∀ j, fam j), ∀ z' : γ, z' ≠ z → (w, z') ∉ t) :
    (weightedCountN p).real t = ∑ w : (∀ j, fam j), (if (w, z) ∈ t then p (w, z) else 0) := by
  rw [weightedCountN_real_eq_sum p hp]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  refine Finset.sum_eq_single z ?_ ?_
  · intro z' _ hz'
    rw [if_neg (h w z' hz')]
  · intro hz
    exact absurd (Finset.mem_univ z) hz

end FiberDecomp

end FateV2.Modeling.GenN
