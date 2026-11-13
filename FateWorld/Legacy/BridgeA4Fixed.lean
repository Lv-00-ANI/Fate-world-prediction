import FateWorld.Legacy.ThreeNodeFactorizes
import FateWorld.Legacy._root.CausSeparation
import FateWorld.Legacy.FactorMarkov

/-! ===========================================================================
  §0  `factorizes_colliderP` 的**正确版本**

  ## 原定理（Fate/BridgeA4.lean，为假）

  ```lean
  theorem factorizes_colliderP {G : DAG (Fin 3)} (v₀ : Fin 3) :
      Factorizes (colliderP (α := Bool)) G
  ```

  **对任意图 `G` 声称成立**。但 `colliderP x = [x 0 = x 2]`，
  `Factorizes` 要求 `LocalTo`，即 `colliderP` 只读 `pa(v)`。
  若 `pa(1) ⊉ {0, 2}`，则 `colliderP` 读的坐标超出 `pa(1)`，`LocalTo` 不成立。

  ## 本文件的正确版本

  `factorizes_colliderP_corrected`：**需要 `{0, 2} ⊆ G.parents 1`**。

  证明用 `Fate.ThreeNodeFactorizes.colliderPhi`（现成的分解：
  `colliderPhi v x = if v = 1 then [x 0 = x 2] else 1`），
  再用 `Finset.prod_eq_single 1` 收口。

  ## 诚实边界

  `ThreeNodeFactorizes.lean` 里已有 `colliderDAG` 版本（`colliderDAG` 的 `pa(1) = {0,2}`，
  条件自动满足）。本文件把它推广到**满足该条件的任意图**。
  =========================================================================== -/

namespace Fate.BridgeA4Fixed

open Finset
open Causalean.Graph

-- ⭐ 修正版：Factorizes colliderP G 成立当 pa_G(1) ⊇ {0,2}
theorem factorizes_colliderP_corrected (G : Causalean.Graph.DAG (Fin 3))
    (hpa : ({0, 2} : Finset (Fin 3)) ⊆ G.parents 1) :
    Fate.FactorMarkov.Factorizes
      (Fate.ThreeNodeFactorizes.colliderP (α := Bool)) G := by
  refine ⟨Fate.ThreeNodeFactorizes.colliderPhi (α := Bool), ?_, ?_⟩
  · intro v x y hxy
    unfold Fate.ThreeNodeFactorizes.colliderPhi
    by_cases hv : v = 1
    · subst hv
      simp only
      have h0 : x 0 = y 0 := hxy 0 (Or.inr (hpa (Finset.mem_insert_self _ _)))
      have h2 : x 2 = y 2 := hxy 2 (Or.inr (hpa (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
      rw [h0, h2]
    · simp only [hv, if_false]
  · intro x
    rw [Finset.prod_eq_single 1]
    · simp [Fate.ThreeNodeFactorizes.colliderPhi, Fate.ThreeNodeFactorizes.colliderP]
    · intro b _ hb
      simp [Fate.ThreeNodeFactorizes.colliderPhi, hb]
    · intro h; exact absurd (Finset.mem_univ _) h

end Fate.BridgeA4Fixed
