import FateWorld.Legacy._root.CausBayesBall
import FateWorld.Legacy._root.CausSeparation
import Mathlib.Tactic

namespace Fate.Stage2.ChainDsepN

open Finset
open Causalean.Graph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- ⭐⭐⭐ **BFS 的 visited 单调性**：

`G.bbReachAux Z frontier visited fuel ⊇ visited`（对任意 `fuel`、`frontier`）。 -/
theorem visited_subset_bbReachAux (G : Causalean.Graph.DAG V) (Z : Finset V)
    (frontier visited : Finset (Causalean.Graph.DAG.BBState V)) (fuel : ℕ) :
    visited ⊆ G.bbReachAux Z frontier visited fuel := by
  induction fuel generalizing frontier visited with
  | zero =>
    intro s hs
    simp only [Causalean.Graph.DAG.bbReachAux]
    exact hs
  | succ n ih =>
    intro s hs
    simp only [Causalean.Graph.DAG.bbReachAux]
    split
    · exact hs
    · next hne =>
      have hmem : s ∈ (visited ∪ (frontier.biUnion (G.bbStep Z) \ visited)) :=
        Finset.mem_union_left _ hs
      exact ih _ _ hmem

-- 公理审计
#print axioms visited_subset_bbReachAux

end Fate.Stage2.ChainDsepN
