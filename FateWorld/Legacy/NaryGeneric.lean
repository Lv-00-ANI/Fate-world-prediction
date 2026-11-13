import FateWorld.Legacy.NaryPointwise
import Mathlib.Data.Fintype.Pi

/-! ===========================================================================
  §GenNGeneric  general (Set-indexed) form of the N-ary bridge (round 207)

  `nary_bridge_pointwise_all` is stated for **finset-indexed** families
  `Sf : ∀ i, Finset (fam i)`.  Since every `fam i` is a `Fintype`, every subset
  is finite, so the `Finset` restriction loses no generality.  This module
  removes it, addressing semantic audit R0's "gap 1".
  =========================================================================== -/

namespace Fate.GenN

open MeasureTheory ProbabilityTheory

section Aux

variable {ι : Type*}
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*}

/-- ⭐ a `Set` and the corresponding finite set give the same `coordSet`. -/
theorem coordSet_set_eq_coordSet_finite (i : ι) (S : Set (fam i)) :
    (coordSet i S : Set ((∀ j, fam j) × γ))
      = coordSet i (((S.toFinite).toFinset : Finset (fam i)) : Set (fam i)) := by
  ext w
  simp only [coordSet, Set.mem_setOf_eq]
  rw [Set.Finite.coe_toFinset]

end Aux

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)] [∀ i, DecidableEq (fam i)]
variable {γ : Type*} [Fintype γ] [DecidableEq γ] [MeasurableSpace γ]
  [MeasurableSingletonClass γ]
variable [∀ i, MeasurableSpace (fam i)] [∀ i, MeasurableSingletonClass (fam i)]
variable [MeasurableSpace ((∀ j, fam j) × γ)]
variable [MeasurableSingletonClass ((∀ j, fam j) × γ)]
variable [StandardBorelSpace ((∀ j, fam j) × γ)]

/-- ⭐⭐⭐⭐⭐ **N-ary bridge, general (Set-indexed) form**.

Same content as `nary_bridge_pointwise_all`, but each per-coordinate parameter
is an **arbitrary set** instead of a finset. -/
theorem nary_bridge_generic
    (p : ((∀ j, fam j) × γ) → ℝ) (hp : ∀ w, 0 ≤ p w)
    (pN : Fate.GenC3.NJoint (ι := ι) fam γ)
    (hpN : ∀ xs z, pN xs z = p (xs, z))
    (hcond : Fate.GenC3.CondIndepN pN)
    (hproj : ∀ i, Measurable (fun w : (∀ j, fam j) × γ => w.1 i))
    (hsnd : Measurable (fun w : (∀ j, fam j) × γ => w.2))
    (S : ∀ i, Set (fam i)) :
    letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
    ∀ a : (∀ j, fam j) × γ,
      (weightedCountN p) {a} ≠ 0 →
      (weightedCountN p).real (fiberN a.2) ≠ 0 →
      ((condExpKernel (Ω := (∀ j, fam j) × γ) (weightedCountN p)
        (MeasurableSpace.comap (fun w : (∀ j, fam j) × γ => w.2) inferInstance)) a).real
          (⋂ i, coordSet (fam := fam) (γ := γ) i (S i))
        = ∏ i, ((condExpKernel (Ω := (∀ j, fam j) × γ) (weightedCountN p)
        (MeasurableSpace.comap (fun w : (∀ j, fam j) × γ => w.2) inferInstance)) a).real
          (coordSet (fam := fam) (γ := γ) i (S i)) := by
  intro a hμa hM
  have hrew : ∀ i, (coordSet (fam := fam) (γ := γ) i (S i) : Set ((∀ j, fam j) × γ))
      = coordSet (fam := fam) (γ := γ) i
          ((((S i).toFinite).toFinset : Finset (fam i)) : Set (fam i)) :=
    fun i => coordSet_set_eq_coordSet_finite i (S i)
  simp only [hrew]
  exact nary_bridge_pointwise_all p hp pN hpN hcond hproj hsnd
    (fun i => (S i).toFinite.toFinset) a hμa hM

end Generic

end Fate.GenN
