import FateWorld.Legacy.TailBlockAssemble
import FateWorld.Legacy.FactorizesToHyper

/-! ===========================================================================
  §0  桥的整合：两种情形与 `hfacA` 的来源

  ## 桥的两个主定理

  * **无尾块**（`X∪Y∪Z = univ`）：
    `condIndep_of_factorizes_dSep_general`（`Fate/BridgeDSepGeneral.lean`）
    从 `Factorizes p G` + `G.dSep X Y Z` 直接得 `CondIndep`。**完整、无条件。**

  * **有尾块**（`X∪Y∪Z ⊊ univ`）：
    `condIndep_tail_HA`（`Fate/TailBlockAssemble.lean`）
    从 `hfacA : p w = ∏ v ∈ A, ψ v w` + `hA : ∀ v, R v ⊆ A` + `Split` 得 `CondIndep`。

  ## ⚠ `hfacA` 的来源（本文件的核心结论）

  `Factorizes p G` 给的是 `p w = ∏ v : V, f v w`（**全空间乘积**）。
  而 `hfacA` 需要 `p w = ∏ v ∈ A, ψ v w`（**只 A 内的乘积**）。

  **`Factorizes` 只在 `A = univ` 时推出 `hfacA`**（`facA_of_univ`），
  因为 `LocalTo` 只约束每个因子读哪里，**不说 A 外的因子恒为 1**。

  ⟹ 有尾块情形需要一个**独立的前提**：尾块因子在边缘化后不出现。
     这与 `GraphToProbView7.lean:216` 的诚实登记一致：
     「Tail ⊊ V 的一般情形需要尾块因子沿 A 边界重新分组」。
  =========================================================================== -/

namespace Fate.GraphToProbView7

open Finset Fate Fate.View19

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-- ⭐ **无尾块时 `hfacA` 就是 `Factorizes` 的展开**。 -/
theorem facA_of_univ {p : (V → α) → ℝ} {ψ : V → (V → α) → ℝ}
    (hfac : ∀ w, p w = ∏ v, ψ v w) :
    ∀ w, p w = ∏ v ∈ (Finset.univ : Finset V), ψ v w := by
  intro w
  rw [hfac w]

end Fate.GraphToProbView7
