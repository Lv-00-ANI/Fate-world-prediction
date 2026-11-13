import FateWorld.Legacy.NaryProduct
import Mathlib.Data.Fintype.Pi

/-! ===========================================================================
  §GenNCancel  pure real-algebra core of the N-ary bridge's final step (round 201)

  ## History of this statement (both corrections are recorded on purpose)

  - **Round 199** conjectured `A * M^(n-1) = prod i, (B i * M) -> A * M = (prod i, B i) * M`.
    **FALSE** (counterexample: `ι = Fin 2`, `B = (3,5)`, `M = 2`, `A = 30`).
  - **Round 200** corrected it to `A = (prod i, B i) * M`.
  - **Round 201** (agent P1) showed that is **not the shape the bridge produces
    either**.  Each `B i = kappa(t_i)` already carries one factor `M`
    (`kappa(t_i) * M = mu.real(...)`), so the correct intermediate identity is

        kappa(t) * M^n = prod i, (kappa(t_i) * M)

    i.e. **`A * M^n = (prod i, B i) * M^n`**, whence `A = prod i, B i`
    when `M != 0`.

  ## The correct algebraic core

      A * M^n = (prod i, B i) * M^n ,  M != 0   ->   A = prod i, B i
  =========================================================================== -/

namespace Fate.GenN

open MeasureTheory ProbabilityTheory

section Cancel

variable {ι : Type*} [Fintype ι]

/-- ⭐ `prod i, (B i * M) = (prod i, B i) * M^n`. -/
theorem prod_mul_const_eq' (B : ι → ℝ) (M : ℝ) :
    ∏ i, (B i * M) = (∏ i, B i) * M ^ Fintype.card ι := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- ⭐⭐⭐⭐ **pure real-algebra core of the N-ary bridge's final step**.

If `A * M^n = (prod i, B i) * M^n` and `M ≠ 0`, then `A = prod i, B i`.

This is exactly the cancellation needed at the end of the bridge: the joint
kernel value `A = kappa(t)` and the product `prod i, kappa(t_i)` agree once the
common factor `M^n` is removed. -/
theorem cancel_pow_eq
    (A : ℝ) (B : ι → ℝ) (M : ℝ)
    (hM : M ≠ 0)
    (h : A * M ^ Fintype.card ι = (∏ i, B i) * M ^ Fintype.card ι) :
    A = ∏ i, B i := by
  have hpow : M ^ Fintype.card ι ≠ 0 := pow_ne_zero _ hM
  exact mul_right_cancel₀ hpow h

/-- ⭐⭐⭐ **the exact shape produced by the bridge**.

If `A * M^n = prod i, (B i * M)` and `M ≠ 0`, then `A = prod i, B i`. -/
theorem cancel_mass_pow
    (A : ℝ) (B : ι → ℝ) (M : ℝ)
    (hM : M ≠ 0)
    (h : A * M ^ Fintype.card ι = ∏ i, (B i * M)) :
    A = ∏ i, B i := by
  rw [prod_mul_const_eq' B M] at h
  exact cancel_pow_eq A B M hM h

end Cancel

end Fate.GenN
