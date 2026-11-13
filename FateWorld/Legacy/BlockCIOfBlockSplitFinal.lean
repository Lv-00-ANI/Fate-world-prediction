import FateWorld.Legacy.CondIndepGeneralNZ
import FateWorld.Legacy.AncestralInheritanceRouteB

/-! ===========================================================================
  §0  `blockCI_of_block_split` —— `BlockCI_Gap` 的 `C = ∅` 情形

  ## 背景

  `Fate/BridgeStrategy5FiberBijection.lean` §4 声称把 `BlockCI_Gap` 落成定理
  （`blockCI_of_block_split` → `blockCI_of_factorizesC`），但实际没写。

  `BlockCI_Gap p G A B C := ∀ x, p x * mass C p x = mass A p x * mass (B ∪ C) p x`

  ## 本文件的结果（`C = ∅` 情形）

  `blockCI_of_condIndep_zero`：若 `A ∪ B = univ` 且 `CondIndep p A B ∅`，
  则 `BlockCI_Gap p G A B ∅`。

  **关键**：`mass (A∪B) = mass univ = p x`（`DAGFactorization.mass_univ`），
  于是 `CondIndep` 的 `mass (A∪B) · mass ∅ = mass A · mass B`
  正好化为 `p x · mass ∅ = mass A · mass B`，即 `BlockCI_Gap ... ∅`。

  `blockCI_of_block_split`：从因子分解（`hfac` + `hread` + `hsplit`）出发，
  用 `condIndep_general` 得 `CondIndep`，再转成 `BlockCI_Gap ... ∅`。

  ## 诚实边界

  只做了 `C = ∅` 的情形。一般的 `C` 需要额外处理 `mass (B ∪ C)` 与 `mass C` 的关系，
  未做。（相关构件见 `Fate/BlockCIOfBlockSplit.lean` 与 `Fate/MassFactorOfReads.lean`。）
  =========================================================================== -/

namespace Fate.C5f

open Finset Fate Fate.View19 Fate.DAGFactorization Fate.AncestralInheritanceRouteB

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

theorem blockCI_of_condIndep_zero {p : (V → α) → ℝ} {G : Causalean.Graph.DAG V}
    {A B : Finset V} (hAB : A ∪ B = Finset.univ)
    (hci : Fate.FactorMarkov.CondIndep p A B ∅) :
    BlockCI_Gap p G A B ∅ := by
  intro x
  have hz := hci x
  simp only [Finset.union_empty, hAB] at hz
  rw [Fate.DAGFactorization.mass_univ] at hz
  simpa using hz

-- ⭐ 完整版：从因子分解 + Split 直接得 BlockCI_Gap（C = ∅ 情形）
theorem blockCI_of_block_split {ψ : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    {R : V → Finset V} {A B : Finset V}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : Fate.View19.ReadSet ψ R)
    (hsplit : Fate.View19.Split R A B ∅)
    (hAB : A ∪ B = Finset.univ) (hdisj : Disjoint A B)
    (G : Causalean.Graph.DAG V) :
    BlockCI_Gap p G A B ∅ := by
  apply blockCI_of_condIndep_zero hAB
  -- 用 condIndep_general：需要 Split、两两不交、A∪B∪∅ = univ
  have hXZ : Disjoint A ∅ := Finset.disjoint_left.mpr (fun x _ hx0 => absurd hx0 (Finset.notMem_empty x))
  have hYZ : Disjoint B ∅ := Finset.disjoint_left.mpr (fun x _ hx0 => absurd hx0 (Finset.notMem_empty x))
  have hcover : A ∪ B ∪ ∅ = Finset.univ := by
    rw [Finset.union_empty, hAB]
  exact Fate.GraphToProbView7.condIndep_general ψ p hfac hread hsplit hdisj hXZ hYZ hcover

end Fate.C5f
