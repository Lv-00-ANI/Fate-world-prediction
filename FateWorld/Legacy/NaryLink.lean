import FateWorld.Legacy.NaryCancel
import FateWorld.Legacy.NaryFiberDecomp
import FateWorld.Legacy.NaryMargSum
import FateWorld.Legacy.NaryFinalBridge
import FateWorld.Legacy.NaryBridge

/-! ===========================================================================
  §GenNLink  set identity for the joint set (round 201)

  Agent P1's verification of the bridge chain identified the connection lemma

  **(c)** `(xs, z) in iInter i, coordSet i (S i)  <=>  forall i, xs i in S i`

  which turns the measure-theoretic sum
  `sum w, [(w, z) in iInter i, coordSet i (S i)] * p (w, z)`
  (obtained from `real_eq_sum_of_fiber`) into the indicator sum
  `sum xs, [forall i, xs i in S i] * p (xs, z)`
  that `product_factorize` (round 198) consumes.

  Both the `Set` and the `Finset`-indexed versions are recorded.
  =========================================================================== -/

namespace Fate.GenN

open MeasureTheory ProbabilityTheory

section SetIdentity

variable {ι : Type*}
variable {fam : ι → Type*}
variable {γ : Type*}

/-- ⭐⭐⭐ **(c)** the membership identity for the joint set.

`(xs, z) in iInter i, coordSet i (S i)  <=>  forall i, xs i in S i`. -/
theorem mem_iInter_coordSet {S : ∀ i, Set (fam i)} (xs : ∀ j, fam j) (z : γ) :
    ((xs, z) ∈ (⋂ i, coordSet i (S i) : Set ((∀ j, fam j) × γ)))
      ↔ ∀ i, xs i ∈ S i := by
  simp [coordSet, Set.mem_iInter]

end SetIdentity

section FinsetIdentity

variable {ι : Type*} [Fintype ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*}

omit [Fintype ι] [∀ i, Fintype (fam i)] in
/-- ⭐ **(c')** the `Finset`-indexed membership. -/
theorem mem_iInter_coordSet_finset {Sf : ∀ i, Finset (fam i)} (xs : ∀ j, fam j) (z : γ) :
    ((xs, z) ∈ (⋂ i, coordSet i ((Sf i : Set (fam i))) : Set ((∀ j, fam j) × γ)))
      ↔ ∀ i, xs i ∈ Sf i := by
  rw [mem_iInter_coordSet]
  constructor
  · intro h i; exact Finset.mem_coe.mpr (h i)
  · intro h i; exact Finset.mem_coe.mp (h i)

end FinsetIdentity

end Fate.GenN
