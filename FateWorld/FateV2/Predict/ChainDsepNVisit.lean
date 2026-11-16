import FateWorld.FateV2.Modeling.CausBayesBall
import FateWorld.FateV2.Modeling.CausSeparation
import Mathlib.Tactic

namespace FateV2.Predict.Stage2.ChainDsepN

open FateV2.Modeling

open Finset
open FateV2.Modeling.Graph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-!
  # Predict · ChainDsepNVisit

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ChainDsepNVisit.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausBayesBall, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-- ⭐⭐⭐ **BFS 的 visited 单调性**：

`G.bbReachAux Z frontier visited fuel ⊇ visited`（对任意 `fuel`、`frontier`）。 -/
theorem visited_subset_bbReachAux (G : FateV2.Modeling.Graph.DAG V) (Z : Finset V)
    (frontier visited : Finset (FateV2.Modeling.Graph.DAG.BBState V)) (fuel : ℕ) :
    visited ⊆ G.bbReachAux Z frontier visited fuel := by
  induction fuel generalizing frontier visited with
  | zero =>
    intro s hs
    simp only [FateV2.Modeling.Graph.DAG.bbReachAux]
    exact hs
  | succ n ih =>
    intro s hs
    simp only [FateV2.Modeling.Graph.DAG.bbReachAux]
    split
    · exact hs
    · next hne =>
      have hmem : s ∈ (visited ∪ (frontier.biUnion (G.bbStep Z) \ visited)) :=
        Finset.mem_union_left _ hs
      exact ih _ _ hmem

-- 公理审计
#print axioms visited_subset_bbReachAux

end FateV2.Predict.Stage2.ChainDsepN
