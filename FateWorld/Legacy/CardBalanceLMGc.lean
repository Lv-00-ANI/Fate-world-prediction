import FateWorld.Legacy.MassOfReadsCover
import FateWorld.Legacy.BalanceComponents
import FateWorld.Legacy.BridgeA1
import FateWorld.Legacy.NonDescendantsMem

/-! ===========================================================================
  §0  ⭐ `LMGc` 的指数配平：`|{v} ∪ pa v| + |nd v| = |pa v| + |{v} ∪ nd v|`

  ## 背景

  `Fate/MassOfReadsCover.lean` 给出 `mass S p x = |α|^(|V| - |S|) * p x`
  （当所有因子只读 `S` 时）。

  把它应用到 `LMGc` 的四个 `mass`：

  | 项 | 集合 | `|α|` 指数 |
  |---|---|---|
  | `mass (insert v (pa v))` | `{v} ∪ pa v` | `|V| - |{v}∪pa v|` |
  | `mass (nd v ∪ pa v)` = `mass (nd v)` | `nd v` | `|V| - |nd v|` |
  | `mass (pa v)` | `pa v` | `|V| - |pa v|` |
  | `mass (insert v (nd v ∪ pa v))` = `mass ({v} ∪ nd v)` | `{v} ∪ nd v` | `|V| - |{v}∪nd v|` |

  `LMGc` 要求左右相等 ⟹ 需
    `|{v} ∪ pa v| + |nd v| = |pa v| + |{v} ∪ nd v|`

  ## 本文件

  `card_balance_lmgc`：上述配平。

  ## 证明

  * `v ∉ pa v`（`not_mem_pa_self`）⟹ `|{v} ∪ pa v| = 1 + |pa v|`
  * `v ∉ nd v`（`mem_nd_iff`）⟹ `|{v} ∪ nd v| = 1 + |nd v|`
  * `ring` 收口
  =========================================================================== -/

namespace Fate.Bal2
open Finset Fate Fate.DAGFactorization
open Causalean.Graph
universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

-- 需要：|{v} ∪ pa v| + |nd v| = |pa v| + |{v} ∪ nd v|
theorem card_balance_lmgc (G : Causalean.Graph.DAG V) (v : V) :
    ({(v)} ∪ pa G v).card + (G.nonDescendants v).card
      = (pa G v).card + ({(v)} ∪ G.nonDescendants v).card := by
  have hPS : pa G v ⊆ G.nonDescendants v := Fate.BridgeA1.pa_subset_nonDescendants G v
  have hvS : v ∉ G.nonDescendants v := by
    rw [Fate.NDMem.mem_nd_iff]
    intro h
    exact h.2 rfl
  have hvP : v ∉ pa G v := Fate.DAGFactorization.not_mem_pa_self G v
  -- 左边 = 1 + |pa| + |nd|（因 v ∉ pa，Disjoint {v} (pa)）
  -- 右边 = |pa| + 1 + |nd|（因 v ∉ nd）
  rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr hvP),
      Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr hvS)]
  ring

end Fate.Bal2
