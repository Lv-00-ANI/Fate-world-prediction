import FateWorld.Legacy.SplitFromDAG
import FateWorld.Legacy.FactorizesToHyper

/-! ===========================================================================
  §0  `dSep` **不能**推出主定理 D 所需的 `hTail`

  ## 背景

  主定理 D（`Fate/TailBlockBridge.lean` 的 `condIndep_tail_block`）需要：
  ```
  hTail : ∀ v, v ∉ X ∪ Y ∪ Z → readSetOf G v ⊆ Z
  ```
  即「A 之外的顶点的所有父节点都在 Z 中」。

  ## 本文件的结论（机检）

  **`G.dSep X Y Z` 不能推出上述 `hTail`。**

  反例：`V = Fin 4`，边 `2 → 0`、`2 → 1`（2 是 0 与 1 的共同原因），3 孤立。
  取 `X = {0}`、`Y = {1}`、`Z = {2}`，则
  * `dSep {0} {1} {2}` **成立**（路径 `0 ← 2 → 1` 被 2 阻断）
  * 但 `v = 3 ∉ A = {0,1,2}`，而 `readSetOf G 3 = {3} ⊄ {2}`，
    故 `hTail` **不成立**。

  ## 意义

  ⟹ 主定理 D 虽然数学上已证，但它的 `hTail` 前提无法从 `dSep` 得到，
     需要额外的图结构假设（如「A 外顶点只依赖 Z」）。

  ⚠ 这与 GraphToProbView7.lean:216 的诚实登记一致：文档自认只做到
     「Tail 的因子整体只读 A 的某个子集」的特例。本文件说明那个特例
     在 dSep 语境下也未必可得。
  =========================================================================== -/

namespace Fate.GraphToProbView7
open Finset Fate Fate.View19
universe u

set_option warn.classDefReducibility false

-- 反例图：V = Fin 4，边 2 → 0, 2 → 1（2 是 0 与 1 的共同原因），3 孤立
def ceEdge : Fin 4 → Fin 4 → Prop :=
  fun u v => (u = 2 ∧ v = 0) ∨ (u = 2 ∧ v = 1)

def ceEdgeDec : DecidableRel ceEdge := by
  intro u v; unfold ceEdge; infer_instance

def ceRank (x : Fin 4) : ℕ := if x = 0 ∨ x = 1 then 1 else 0

theorem ceEdge_rank_lt {u v : Fin 4} (h : ceEdge u v) : ceRank u < ceRank v := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · unfold ceRank; decide
  · unfold ceRank; decide

def ceDAG : Causalean.Graph.DAG (Fin 4) where
  edge := ceEdge
  decEdge := ceEdgeDec
  acyclic := by
    intro v h
    have hmono : ∀ {a b : Fin 4},
        Relation.TransGen ceEdge a b → ceRank a < ceRank b := by
      intro a b hab
      induction hab with
      | single h => exact ceEdge_rank_lt h
      | tail _ hbc ih => exact lt_trans ih (ceEdge_rank_lt hbc)
    exact absurd (hmono h) (lt_irrefl _)

-- 检验 dSep {0} {1} {2}
theorem ceDAG_dSep : ceDAG.dSep {0} {1} {2} := by decide

-- 检验 hTail 失败：v = 3 ∉ A = {0,1,2}
theorem ceDAG_hTail_false :
    ¬ (∀ v : Fin 4, v ∉ ({0,1,2} : Finset (Fin 4)) →
        Fate.FactorizesToHyper.readSetOf ceDAG v ⊆ ({2} : Finset (Fin 4))) := by
  intro h
  have h3 : (3 : Fin 4) ∉ ({0,1,2} : Finset (Fin 4)) := by decide
  have hsub := h 3 h3
  have hmem : (3 : Fin 4) ∈ Fate.FactorizesToHyper.readSetOf ceDAG 3 := by
    unfold Fate.FactorizesToHyper.readSetOf
    simp
  have := hsub hmem
  exact absurd this (by decide)

end Fate.GraphToProbView7
