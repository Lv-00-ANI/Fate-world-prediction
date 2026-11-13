import FateWorld.Legacy.CondIndepGeneralNZ

/-! ===========================================================================
  §1  `arrowEquivA`  (V → α) ≃ (↥A → α) × (↥(A : Set V)ᶜ → α)
  §2  `arrowEquivA_fst`
  §3  `card_tail`

  注意：补集类型必须写成 `↥(A : Set V)ᶜ`（而不是 `↥Aᶜ`），否则类型对不上。
  零 sorry / admit / axiom。
  =========================================================================== -/

open Finset Fate

set_option linter.unusedSectionVars false

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

namespace Fate.GraphToProbView7

/-- 把定义域拆成 `A` 与其补集：`(V → α) ≃ (↥A → α) × (↥(A : Set V)ᶜ → α)`。 -/
noncomputable def arrowEquivA (A : Finset V) :
    (V → α) ≃ (↥A → α) × (↥(A : Set V)ᶜ → α) :=
  (Equiv.arrowCongr (Equiv.Set.sumCompl (A : Set V)).symm (Equiv.refl α)).trans
    (Equiv.sumArrowEquivProdArrow ↥A ↥(A : Set V)ᶜ α)

/-- 第一分量就是 `w` 在 `A` 上的限制。 -/
theorem arrowEquivA_fst (A : Finset V) (w : V → α) (u : ↥A) :
    (arrowEquivA A w).1 u = w u.1 := rfl

/-- 补集基数：`|↥(A : Set V)ᶜ| = |V| - |A|`。 -/
theorem card_tail (A : Finset V) :
    Fintype.card ↥(A : Set V)ᶜ = Fintype.card V - A.card := by
  have h := Fintype.card_subtype_compl (fun x : V => x ∈ A)
  rw [Fintype.card_coe] at h
  exact h

end Fate.GraphToProbView7
