import FateWorld.FateV2.Modeling.NaryLink
import FateWorld.FateV2.Modeling.NaryFiberDecomp
import FateWorld.FateV2.Modeling.NaryMargSum
/-!
  # Modeling · NaryConnect3

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NaryConnect3.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NaryLink, NaryFiberDecomp, NaryMargSum
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenNConnect2  THE TWO CONNECTION LEMMAS (a) and (b) (round 202)

  Agent P1's verification (round 201) showed the N-ary bridge closes through

      kappa(t) * M^n = prod i, (kappa(t_i) * M)

  provided these two links exist:

  **(a)** `joint_real_eq_indicator_sum`:
      `mu.real((iInter i, coordSet i (Sf i)) intersect fiberN z)`
      `  = sum xs, [all xs i in Sf i] * p (xs, z)`
      -- turns the measure-side numerator into exactly the left-hand side of
      `product_factorize` (round 198).

  **(b)** `coordSet_real_eq_marg_sum`:
      `mu.real(coordSet i (Sf i) intersect fiberN z)`
      `  = sum a in Sf i, marg pN i a z`
      -- turns each single-coordinate numerator into the marginal sum, i.e. the
      matching right-hand factor of `product_factorize`.

  Both are corollaries of `real_eq_sum_of_fiber` (round 195) plus
  `mem_iInter_coordSet_finset` (round 201) and `sum_marg_eq_fiberwise` (round 193).
  =========================================================================== -/

namespace FateV2.Modeling.GenN

open MeasureTheory ProbabilityTheory

section ConnA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)] [∀ i, DecidableEq (fam i)]
variable {γ : Type*} [Fintype γ] [DecidableEq γ] [MeasurableSpace γ]
variable [MeasurableSpace ((∀ j, fam j) × γ)]
variable [MeasurableSingletonClass ((∀ j, fam j) × γ)]

omit [MeasurableSpace γ] in
omit [∀ i, DecidableEq (fam i)] [DecidableEq γ] in
/-- ⭐⭐⭐ **(a)**: the joint numerator as an indicator sum. -/
theorem joint_real_eq_indicator_sum
    (p : ((∀ j, fam j) × γ) → ℝ) (hp : ∀ w, 0 ≤ p w)
    (Sf : ∀ i, Finset (fam i)) (z : γ)
    [dec : DecidablePred (· ∈ ((⋂ i, coordSet i ((Sf i : Set (fam i))))
      ∩ fiberN z : Set ((∀ j, fam j) × γ)))]
    [_dec2 : DecidablePred (fun xs : (∀ j, fam j) => ∀ i, xs i ∈ Sf i)] :
    (weightedCountN p).real ((⋂ i, coordSet i ((Sf i : Set (fam i)))) ∩ fiberN z)
      = ∑ xs : (∀ j, fam j), (if ∀ i, xs i ∈ Sf i then p (xs, z) else 0) := by
  have hslices : ∀ w : (∀ j, fam j), ∀ z' : γ, z' ≠ z →
      (w, z') ∉ ((⋂ i, coordSet i ((Sf i : Set (fam i)))) ∩ fiberN z) := by
    intro w z' hz' hmem
    exact hz' (by simpa only [fiberN, Set.mem_setOf_eq] using hmem.2)
  rw [real_eq_sum_of_fiber p hp _ z hslices]
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  have hmemiff : ((xs, z) ∈ (⋂ i, coordSet i ((Sf i : Set (fam i)))) ∩ fiberN z)
      ↔ ∀ i, xs i ∈ Sf i := by
    constructor
    · intro h; exact (mem_iInter_coordSet_finset xs z).mp h.1
    · intro h
      exact ⟨(mem_iInter_coordSet_finset xs z).mpr h,
        by simp only [fiberN, Set.mem_setOf_eq]⟩
  by_cases h : ∀ i, xs i ∈ Sf i
  · rw [if_pos h, if_pos (hmemiff.mpr h)]
  · rw [if_neg h, if_neg (fun hc => h (hmemiff.mp hc))]

end ConnA

section ConnB

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)] [∀ i, DecidableEq (fam i)]
variable {γ : Type*} [Fintype γ] [DecidableEq γ] [MeasurableSpace γ]
variable [MeasurableSpace ((∀ j, fam j) × γ)]
variable [MeasurableSingletonClass ((∀ j, fam j) × γ)]

omit [MeasurableSpace γ] in
omit [DecidableEq γ] in
/-- ⭐⭐⭐ **(b)**: the single-coordinate numerator equals the marginal sum. -/
theorem coordSet_real_eq_marg_sum
    (pN : Fate.GenC3.NJoint (ι := ι) fam γ)
    (p : ((∀ j, fam j) × γ) → ℝ)
    (hp : ∀ w, 0 ≤ p w)
    (hlink : ∀ xs z, pN xs z = p (xs, z))
    (i : ι) (Sf : Finset (fam i)) (z : γ)
    [dec : DecidablePred (· ∈ (coordSet i ((Sf : Set (fam i))) ∩ fiberN z
      : Set ((∀ j, fam j) × γ)))]
    [_dec2 : DecidablePred (· ∈ (coordSet i ((Sf : Set (fam i)))
      : Set ((∀ j, fam j) × γ)))] :
    (weightedCountN p).real (coordSet i ((Sf : Set (fam i))) ∩ fiberN z)
      = ∑ a ∈ Sf, Fate.GenC3.marg pN i a z := by
  have hslices : ∀ w : (∀ j, fam j), ∀ z' : γ, z' ≠ z →
      (w, z') ∉ (coordSet i ((Sf : Set (fam i))) ∩ fiberN z) := by
    intro w z' hz' hmem
    exact hz' (by simpa only [fiberN, Set.mem_setOf_eq] using hmem.2)
  rw [real_eq_sum_of_fiber p hp _ z hslices]
  have hstep : ∀ w : (∀ j, fam j),
      (if (w, z) ∈ (coordSet i ((Sf : Set (fam i))) ∩ fiberN z) then p (w, z) else 0)
        = (if w i ∈ Sf then pN w z else 0) := by
    intro w
    have hmemiff : ((w, z) ∈ (coordSet i ((Sf : Set (fam i))) ∩ fiberN z))
        ↔ w i ∈ Sf := by
      constructor
      · intro h
        exact Finset.mem_coe.mp (by
          simpa only [coordSet, Set.mem_inter_iff, Set.mem_setOf_eq] using h.1)
      · intro h
        exact ⟨by simp only [coordSet, Set.mem_setOf_eq]; exact Finset.mem_coe.mpr h,
               by simp only [fiberN, Set.mem_setOf_eq]⟩
    by_cases h : w i ∈ Sf
    · rw [if_pos h, if_pos (hmemiff.mpr h), hlink]
    · rw [if_neg h, if_neg (fun hc => h (hmemiff.mp hc))]
  rw [Finset.sum_congr rfl (fun w _ => hstep w)]
  have hfiber := sum_marg_eq_fiberwise (p := pN) i Sf z
  -- convert the LHS into the filter form matching `hfiber`'s RHS
  rw [← Finset.sum_filter]
  rw [← hfiber]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  by_cases h : xs i = a
  · rw [if_pos h]
  · rw [if_neg h]

end ConnB

end FateV2.Modeling.GenN
