import FateWorld.Legacy.NaryConnect
open MeasureTheory ProbabilityTheory
namespace Fate.GenN

/-- ⭐ **`coordSet` 上的可判定性**。 -/
instance coordSet_decidablePred {ι : Type*} {fam : ι → Type*} {γ : Type*}
    (i : ι) (S : Set (fam i)) [DecidablePred (· ∈ S)] :
    DecidablePred (· ∈ (coordSet i S : Set ((∀ j, fam j) × γ))) :=
  fun w => inferInstanceAs (Decidable (w.1 i ∈ S))

section WeightedCountOnCoordSet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*} [Fintype γ] [MeasurableSpace γ]
variable [MeasurableSpace ((∀ j, fam j) × γ)]
variable [MeasurableSingletonClass ((∀ j, fam j) × γ)]

omit [MeasurableSpace γ] in
/-- ⭐⭐ **`weightedCountN` 在 `coordSet` 上的显式求值**（**填补缺口 1**）。 -/
theorem weightedCountN_coordSet
    (p : ((∀ j, fam j) × γ) → ℝ)
    (i : ι) (S : Set (fam i)) [DecidablePred (· ∈ S)] :
    weightedCountN p (coordSet i S) =
      ∑ xs : (∀ j, fam j), ∑ z : γ,
        (if xs i ∈ S then ENNReal.ofReal (p (xs, z)) else 0) := by
  rw [weightedCountN_apply]
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  refine Finset.sum_congr rfl (fun z _ => ?_)
  show (if (xs i ∈ S) then ENNReal.ofReal (p (xs, z)) else 0)
      = (if xs i ∈ S then ENNReal.ofReal (p (xs, z)) else 0)
  rfl

end WeightedCountOnCoordSet

end Fate.GenN
