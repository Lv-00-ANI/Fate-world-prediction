import FateWorld.Legacy.ArrowEquivA
import FateWorld.Legacy.RebaseSplit

/-! ===========================================================================
  § mass 的 A-分解

  `mass S p x`（`S ⊆ A`，`p` 只依赖 `A` 上的坐标）= `|α|^(|V|-|A|) * ∑_{wA} …`

  证明即「用 `arrowEquivA` 换元 + 对补集坐标求和是常数倍的 `∑_t 1`」。
  零 sorry / admit / axiom。
  =========================================================================== -/

namespace Fate.GraphToProbView7
open Finset Fate
universe u
set_option linter.unusedSectionVars false

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-- `p` 只依赖 `A` 上的坐标 ⟹ 在 `A` 上与 `wA` 一致的 `w`，其 `p` 值与
`extEnd A ω₀ wA` 的 `p` 值相同。 -/
theorem p_eq_of_agree_on_A {A : Finset V} {p : (V → α) → ℝ}
    (hp : ∀ w w', (∀ u ∈ A, w u = w' u) → p w = p w')
    (ω₀ : V → α) {wA : ↥A → α} {w : V → α}
    (hw : ∀ u : ↥A, w u.1 = wA u) :
    p w = p (extEnd A ω₀ wA) := by
  refine hp w _ (fun u hu => ?_)
  rw [extEnd_of_mem A ω₀ wA u hu]
  exact hw ⟨u, hu⟩

theorem mass_eq_card_mul_massA {A S : Finset V} (hSA : S ⊆ A)
    {p : (V → α) → ℝ}
    (hp : ∀ w w', (∀ u ∈ A, w u = w' u) → p w = p w')
    (ω₀ : V → α) (x : V → α) :
    Fate.DAGFactorization.mass S p x
      = ((Fintype.card α : ℝ) ^ (Fintype.card V - A.card))
        * ∑ wA : (↥A → α),
            if (∀ u ∈ sub A S hSA, wA u = x u.1) then p (extEnd A ω₀ wA) else 0 := by
  classical
  unfold Fate.DAGFactorization.mass
  -- 步骤 2/3：把 RHS 的 `∑ wA` 展开成 `∑ wA ∑ t`，再算出内层是常数倍
  have hRHS : (∑ q : (↥A → α) × (↥(A : Set V)ᶜ → α),
          if (∀ u ∈ sub A S hSA, q.1 u = x u.1) then p (extEnd A ω₀ q.1) else 0)
      = (Fintype.card α : ℝ) ^ (Fintype.card V - A.card) *
        ∑ wA : (↥A → α),
          if (∀ u ∈ sub A S hSA, wA u = x u.1) then p (extEnd A ω₀ wA) else 0 := by
    rw [Fintype.sum_prod_type]
    rw [mul_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun wA _ => ?_
    -- 内层：`∑ t, (if cond wA then p (extEnd A ω₀ wA) else 0)` 与 `t` 无关
    by_cases hc : ∀ u ∈ sub A S hSA, wA u = x u.1
    · simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fun, nsmul_eq_mul, Nat.cast_pow, card_tail]
      ring
    · simp only [hc, if_false, Finset.sum_const_zero, zero_mul]
  -- 步骤 1：把 LHS 用 `arrowEquivA` 换元到乘积类型上
  have hLHS : (∑ w : V → α, if ∀ u ∈ S, w u = x u then p w else 0)
      = ∑ q : (↥A → α) × (↥(A : Set V)ᶜ → α),
          if (∀ u ∈ sub A S hSA, q.1 u = x u.1) then p (extEnd A ω₀ q.1) else 0 := by
    rw [← Equiv.sum_comp (arrowEquivA A)
          (fun q : (↥A → α) × (↥(A : Set V)ᶜ → α) =>
            if (∀ u ∈ sub A S hSA, q.1 u = x u.1) then p (extEnd A ω₀ q.1) else 0)]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hfst : ∀ u : ↥A, (arrowEquivA A w).1 u = w u.1 := fun u => arrowEquivA_fst A w u
    have hcond : (∀ u ∈ S, w u = x u) ↔
        (∀ u ∈ sub A S hSA, (arrowEquivA A w).1 u = x u.1) := by
      constructor
      · intro h u hu
        rw [hfst u]
        exact h u.1 (mem_sub_iff A S hSA u |>.mp hu)
      · intro h u hu
        have hv := h ⟨u, hSA hu⟩ (mem_sub_iff A S hSA ⟨u, hSA hu⟩ |>.mpr hu)
        rw [hfst] at hv
        exact hv
    rw [if_congr hcond rfl rfl]
    by_cases hP : ∀ u ∈ sub A S hSA, (arrowEquivA A w).1 u = x u.1
    · rw [if_pos hP, if_pos hP]
      exact p_eq_of_agree_on_A hp ω₀ (fun u => hfst u)
    · rw [if_neg hP, if_neg hP]
  rw [hLHS, hRHS]

end Fate.GraphToProbView7
