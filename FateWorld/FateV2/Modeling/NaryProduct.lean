import FateWorld.FateV2.Modeling.NaryAssembly
import FateWorld.FateV2.Modeling.NaryMargSum
import FateWorld.FateV2.Modeling.NaryMassLink
import FateWorld.FateV2.Modeling.NaryFinalBridge
import FateWorld.FateV2.Modeling.NaryAlgebra
import Mathlib.Data.Fintype.Pi

/-!
  # Modeling · NaryProduct

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NaryProduct.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NaryAssembly, NaryMargSum, NaryMassLink, NaryFinalBridge, NaryAlgebra
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenNProduct  THE KEY ALGEBRAIC STEP of the N-ary bridge (round 198)

  ## Result

    (sum xs, [all xs i in Sf i] * p xs z) * M^(n-1)
      = prod i, sum a in Sf i, marg p i a z

  where `M = NMass p z`.

  ## Why the earlier attempts failed (diagnosed by agent M0)

  `Finset.prod_univ_sum` has direction

      prod i, sum j in t i, f i j  =  sum x in piFinset t, prod i, f i (x i)

  i.e. it turns the **product of sums into a sum over the product index set**,
  *not* the other way round.  So one must

  1. first rewrite the left-hand `if`-sum over `univ` into a sum over
     `Fintype.piFinset Sf` (via `← Finset.sum_filter` + `Fintype.mem_piFinset`), then
  2. apply `Finset.prod_univ_sum` **forwards** on the right.

  ## Instance note

  The `if ∀ i, xs i ∈ Sf i` guard needs `[∀ i, DecidableEq (fam i)]` at
  *elaboration* time, so it must be a section variable (not just `classical`).
  =========================================================================== -/

namespace FateV2.Modeling.GenN

open MeasureTheory ProbabilityTheory
open FateV2.Modeling.GenC3

section ProductFactorize

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)] [∀ i, DecidableEq (fam i)]
variable {γ : Type*} [Fintype γ] [DecidableEq γ]

omit [Fintype γ] [DecidableEq γ] in
/-- ⭐⭐⭐⭐ **THE KEY ALGEBRAIC STEP** (finset-indexed form).

This is `condIndepN_sum_factorize` rewritten so that both sides are ready to
meet the measure-theoretic identities of `NaryRealSum` / `NaryFiberDecomp`. -/
theorem product_factorize
    (p : FateV2.Modeling.GenC3.NJoint (ι := ι) fam γ)
    (h : FateV2.Modeling.GenC3.CondIndepN p)
    (Sf : ∀ i, Finset (fam i))
    (z : γ) :
    (∑ xs : (∀ j, fam j), (if ∀ i, xs i ∈ Sf i then p xs z else 0))
        * (NMass p z) ^ (Fintype.card ι - 1) =
      ∏ i, ∑ a ∈ Sf i, marg p i a z := by
  classical
  have key : ∀ xs : (∀ i, fam i), p xs z * (NMass p z) ^ (Fintype.card ι - 1)
      = ∏ i, marg p i (xs i) z := fun xs => (FateV2.Modeling.GenC3.condIndepN_iff p).mp h xs z
  rw [Finset.sum_mul]
  have hL : ∀ xs : (∀ i, fam i),
      (if ∀ i, xs i ∈ Sf i then p xs z else 0) * (NMass p z) ^ (Fintype.card ι - 1)
      = if ∀ i, xs i ∈ Sf i then ∏ i, marg p i (xs i) z else 0 := by
    intro xs
    by_cases hxs : ∀ i, xs i ∈ Sf i
    · rw [if_pos hxs, if_pos hxs]; exact key xs
    · rw [if_neg hxs, if_neg hxs, zero_mul]
  rw [Finset.sum_congr rfl (fun xs _ => hL xs)]
  have hpi : ∀ g : (∀ j, fam j) → ℝ,
      (∑ xs : (∀ j, fam j), (if ∀ i, xs i ∈ Sf i then g xs else 0))
        = ∑ xs ∈ Fintype.piFinset Sf, g xs := by
    intro g
    rw [← Finset.sum_filter]
    congr 1
    ext xs
    simp [Fintype.mem_piFinset]
  rw [hpi (fun xs => ∏ i, marg p i (xs i) z)]
  rw [Finset.prod_univ_sum (t := Sf) (f := fun i a => marg p i a z)]

end ProductFactorize

end FateV2.Modeling.GenN
