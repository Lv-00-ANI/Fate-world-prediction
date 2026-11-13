import FateWorld.Legacy.NaryFinalBridge
import FateWorld.Legacy.NaryAlgebra
import Mathlib.Data.Fintype.Pi

/-! ===========================================================================
  §GenNMargSum  marginal sums (round 193)

  ## The key intermediate lemma (last blocking point of the N-ary bridge)

    sum a in S, marg p i a z  =  sum xs, [xs i in S] * p xs z

  ## How it was finally proven (after 8 failed attempts in round 192)

  The trick is `filter_filter_absorb`: for `a in Sf`, the fiber
  `{xs | xs i = a}` is **already** contained in `{xs | xs i in Sf}`,
  so the extra guard in `sum_fiberwise_of_maps_to` is redundant.
  =========================================================================== -/

namespace Fate.GenN

open MeasureTheory ProbabilityTheory

section MargSum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)] [∀ i, DecidableEq (fam i)]
variable {γ : Type*}

/-- ⭐ double filter absorbs when the second condition implies the first. -/
theorem filter_filter_absorb {Sf : Finset (fam i)} {a : fam i} (ha : a ∈ Sf) :
    (Finset.univ.filter (fun xs : (∀ j, fam j) => xs i ∈ Sf)).filter
      (fun xs : (∀ j, fam j) => xs i = a)
      = (Finset.univ.filter (fun xs : (∀ j, fam j) => xs i = a)) := by
  ext xs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, h2⟩
    exact h2
  · intro h2
    exact ⟨by rw [h2]; exact ha, h2⟩

/-- ⭐⭐⭐ **the key marginal-sum identity** (Finset version).

This was the last blocking point of the N-ary bridge:
`sum a in S, marg p i a z = sum xs, [xs i in S] * p xs z`.

**Proof**: rewrite each inner sum as a filter-sum, then apply
`sum_fiberwise_of_maps_to` with `s = univ.filter (xs i in Sf)`, `t = Sf`;
finally use `filter_filter_absorb` for the redundant guard. -/
theorem sum_marg_eq_fiberwise {p : Fate.GenC3.NJoint (ι := ι) fam γ}
    (i : ι) (Sf : Finset (fam i)) (z : γ) :
    (∑ a ∈ Sf, ∑ xs : (∀ j, fam j), (if xs i = a then p xs z else 0))
      = ∑ xs ∈ (Finset.univ.filter (fun xs : (∀ j, fam j) => xs i ∈ Sf)), p xs z := by
  classical
  have inner : ∀ a : fam i,
      (∑ xs : (∀ j, fam j), (if xs i = a then p xs z else 0))
      = ∑ xs ∈ (Finset.univ.filter (fun xs : (∀ j, fam j) => xs i = a)), p xs z := by
    intro a
    rw [Finset.sum_filter]
  simp only [inner]
  have h := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ.filter (fun xs : (∀ j, fam j) => xs i ∈ Sf)))
    (t := Sf) (g := fun xs => xs i) (f := fun xs => p xs z)
    (fun xs hxs => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxs
      exact hxs)
  rw [← h]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [filter_filter_absorb ha]

end MargSum

end Fate.GenN
