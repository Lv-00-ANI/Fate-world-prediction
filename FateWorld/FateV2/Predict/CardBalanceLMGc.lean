import FateWorld.FateV2.Predict.MassOfReadsCover
import FateWorld.FateV2.Modeling.BalanceComponents
import FateWorld.FateV2.Predict.BridgeA1
import FateWorld.FateV2.Predict.NonDescendantsMem
/-!
  # Predict · CardBalanceLMGc

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CardBalanceLMGc.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MassOfReadsCover, BalanceComponents, BridgeA1, NonDescendantsMem
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

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

namespace FateV2.Predict.Bal2

open FateV2.Modeling
open Finset FateV2.Error Fate.DAGFactorization
open FateV2.Modeling.Graph
universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

-- 需要：|{v} ∪ pa v| + |nd v| = |pa v| + |{v} ∪ nd v|
theorem card_balance_lmgc (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    ({(v)} ∪ pa G v).card + (G.nonDescendants v).card
      = (pa G v).card + ({(v)} ∪ G.nonDescendants v).card := by
  have hPS : pa G v ⊆ G.nonDescendants v := FateV2.Predict.BridgeA1.pa_subset_nonDescendants G v
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

end FateV2.Predict.Bal2
