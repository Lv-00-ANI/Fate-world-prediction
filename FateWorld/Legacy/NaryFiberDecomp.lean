import FateWorld.Legacy.NaryMargSum
import FateWorld.Legacy.NaryRealSum
import FateWorld.Legacy.NaryFinalBridge
import FateWorld.Legacy.NaryAlgebra

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

namespace Fate.GenN

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

end Fate.GenN
