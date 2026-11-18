import FateWorld.FateV2.Modeling.CondIndepGeneralNZ
import FateWorld.FateV2.Predict.AncestralInheritanceRouteB
/-!
  # Predict · BlockCIOfBlockSplitFinal

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BlockCIOfBlockSplitFinal.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：CondIndepGeneralNZ, AncestralInheritanceRouteB
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

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

namespace FateV2.Predict.C5f

open FateV2.Modeling

open Finset FateV2.Error FateV2.Predict.View19 Fate.DAGFactorization FateV2.Predict.AncestralInheritanceRouteB

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

theorem blockCI_of_condIndep_zero {p : (V → α) → ℝ} {G : FateV2.Modeling.Graph.DAG V}
    {A B : Finset V} (hAB : A ∪ B = Finset.univ)
    (hci : FateV2.Predict.FactorMarkov.CondIndep p A B ∅) :
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
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hsplit : FateV2.Predict.View19.Split R A B ∅)
    (hAB : A ∪ B = Finset.univ) (hdisj : Disjoint A B)
    (G : FateV2.Modeling.Graph.DAG V) :
    BlockCI_Gap p G A B ∅ := by
  apply blockCI_of_condIndep_zero hAB
  -- 用 condIndep_general：需要 Split、两两不交、A∪B∪∅ = univ
  have hXZ : Disjoint A ∅ := Finset.disjoint_left.mpr (fun x _ hx0 => absurd hx0 (Finset.notMem_empty x))
  have hYZ : Disjoint B ∅ := Finset.disjoint_left.mpr (fun x _ hx0 => absurd hx0 (Finset.notMem_empty x))
  have hcover : A ∪ B ∪ ∅ = Finset.univ := by
    rw [Finset.union_empty, hAB]
  exact FateV2.Predict.GraphToProbView7.condIndep_general ψ p hfac hread hsplit hdisj hXZ hYZ hcover

end FateV2.Predict.C5f
