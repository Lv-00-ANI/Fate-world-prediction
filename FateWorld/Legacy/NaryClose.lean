import FateWorld.Legacy.NaryBridgeFinal
import Mathlib.Data.Fintype.Pi

/-! ===========================================================================
  §GenNClose  closing lemma in the shape the bridge actually produces (round 205)

  Agent Q3's adversarial review (round 204) observed that no bridge component
  produces `kappa * M^n` directly: the joint kernel value gives `kappa * M = A`
  and the algebraic factorization gives `A * M^(n-1) = B`.  In round 204 the
  `M^n` form was derived inside `kernel_iInter_mul_eq_prod_marg_sum`, so the
  result is sound; a lemma in the *produced* shape is more faithful to the
  assembly.
  =========================================================================== -/

namespace Fate.GenN

open MeasureTheory ProbabilityTheory

section ProducedShape

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- `M^n = M^(n-1) * M` for `n = Fintype.card ι > 0`. -/
theorem pow_card_eq_pred_mul (M : ℝ) :
    M ^ Fintype.card ι = M ^ (Fintype.card ι - 1) * M := by
  have hpos : 0 < Fintype.card ι := Fintype.card_pos
  conv_lhs => rw [show Fintype.card ι = (Fintype.card ι - 1) + 1 by omega]
  rw [pow_succ]

/-- ⭐⭐⭐⭐ **closing lemma in the shape the bridge actually produces**.

`kappa * M = A`, `A * M^(n-1) = B`, `B = prod i, (kappa_i i * M)`, `M ≠ 0`
  ==>  `kappa = prod i, kappa_i i`. -/
theorem bridge_close_produced
    (kappa A B : ℝ) (kappa_i : ι → ℝ)
    (M : ℝ) (hM : M ≠ 0)
    (hκM : kappa * M = A)
    (hAB : A * M ^ (Fintype.card ι - 1) = B)
    (hB : B = ∏ i, (kappa_i i * M)) :
    kappa = ∏ i, kappa_i i := by
  set n := Fintype.card ι with hn
  set P := ∏ i, kappa_i i with hP
  have hn1 : 1 ≤ n := Fintype.card_pos
  have hMk : M ^ (n - 1) ≠ 0 := pow_ne_zero _ hM
  -- kappa * M^(n-1) * M = P * M^(n-1) * M
  have hkey : kappa * M ^ (n - 1) * M = P * M ^ (n - 1) * M := by
    calc kappa * M ^ (n - 1) * M
        = (kappa * M) * M ^ (n - 1) := by ring
      _ = A * M ^ (n - 1) := by rw [hκM]
      _ = B := hAB
      _ = ∏ i, (kappa_i i * M) := hB
      _ = P * M ^ n := prod_mul_const_eq' kappa_i M
      _ = P * M ^ (n - 1) * M := by
          rw [pow_card_eq_pred_mul (M := M)]; ring
  have hMk' : M ^ (n - 1) ≠ 0 := hMk
  exact mul_right_cancel₀ hMk' (mul_right_cancel₀ hM hkey)

end ProducedShape

end Fate.GenN
