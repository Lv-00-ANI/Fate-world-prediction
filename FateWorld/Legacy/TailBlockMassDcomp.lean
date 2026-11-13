import FateWorld.Legacy.TailOutExtract
import FateWorld.Legacy.MassADecompFinal

/-! ===========================================================================
  §0  主定理 D 的核心：四个 `mass` 的完整分解

  ## 背景

  主定理 D（有尾块情形）需要把 `mass S p` 分解成「尾块因子 × A 内的 mass」。

  ## 结果

  ```lean
  theorem mass_dcomp_tail (hSA : S ⊆ A) (hZS : Z ⊆ S)
      (hfac : p w = ∏ v, ψ v w) (hread : ReadSet ψ R)
      (hOut : ∀ v ∉ A, R v ⊆ Z)
      (hPA : ∏ v ∈ A, ψ v 只读 A) (x) :
      mass S p x
        = (∏ v ∈ outSet A, ψ v x)
          * (|α|^(|V|-|A|) * ∑ wA, if (wA|_S = x|_S) then ∏ v ∈ A, ψ v (extEnd A x wA) else 0)
  ```

  **⟹ 两个 rw 即可**：先用 `mass_extract_out_of_factorizes` 提出尾块因子，
  再用 `mass_eq_card_mul_massA` 把 A 内部分化成「|α| 幂 × A 上的求和」。

  ## 诚实边界

  * 本文件只给**单个** `mass` 的分解，不给 `CondIndep` 本体。
  * 对四个 S（A、Z、X∪Z、Y∪Z）分别调用即可，但 `CondIndep` 的组装需要
    「A 上的四个求和配平」，那部分未做。
  =========================================================================== -/

namespace Fate.GraphToProbView7

open Finset Fate Fate.View19

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-- ⭐⭐⭐ **单个 `mass` 的完整分解**（主定理 D 的核心）。

`S ⊆ A`、`Z ⊆ S`、尾块因子只读 `Z`、且 `A` 内乘积只读 `A` 时：
`mass S p` = 尾块因子之积 × `|α|^(|V|-|A|)` × （A 上的求和）。 -/
theorem mass_dcomp_tail {A S Z : Finset V} (hSA : S ⊆ A) (hZS : Z ⊆ S)
    {ψ : V → (V → α) → ℝ} {R : V → Finset V} {p : (V → α) → ℝ}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : Fate.View19.ReadSet ψ R)
    (hOut : ∀ v, v ∉ A → R v ⊆ Z)
    (hPA : ∀ w w', (∀ u ∈ A, w u = w' u) → (∏ v ∈ A, ψ v w) = (∏ v ∈ A, ψ v w'))
    (x : V → α) :
    Fate.DAGFactorization.mass S p x
      = (∏ v ∈ outSet A, ψ v x) *
        (((Fintype.card α : ℝ) ^ (Fintype.card V - A.card))
          * ∑ wA : (↥A → α),
              if (∀ u ∈ sub A S hSA, wA u = x u.1)
                then ∏ v ∈ A, ψ v (extEnd A x wA) else 0) := by
  rw [mass_extract_out_of_factorizes ψ hfac hread hSA hZS hOut x]
  rw [mass_eq_card_mul_massA hSA hPA x]

end Fate.GraphToProbView7
