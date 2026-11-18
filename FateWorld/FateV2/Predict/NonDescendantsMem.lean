import FateWorld.FateV2.Predict.LMGcProjectionNote
import FateWorld.FateV2.Predict.BridgeA1
/-!
  # Predict · NonDescendantsMem

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NonDescendantsMem.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LMGcProjectionNote, BridgeA1
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  ⭐ 用 `nd` 的定义替代 `hcover`：`nd` 的成员刻画

  ## 背景

  `Fate/LMGcProjectionNote.lean` 精确指出：
  `LMGc` 与 `CondIndep` 的形式等价已证（`Fate/LMGcCondIndepEquiv.lean`），
  但 `CondIndepGeneralNZ` 的桥用 `hcover : X ∪ Y ∪ Z = univ` 做**成员推导**
  （`notMemXZ_memY` / `notMemYZ_memX`），而 `LMGc` 取
  `X = {v}`、`Y = nd v`、`Z = pa v` 时 `X ∪ Y ∪ Z ⊊ univ`，故 `hcover` 不可用。

  ## 本文件

  用 `nd` 的**定义**提供成员推导：

  * `mem_nd_iff`：`u ∈ nd v ↔ ¬isAncestor v u ∧ u ≠ v`
  * `not_mem_nd_implies_anc`：`u ∉ nd v` 且 `u ≠ v` ⟹ `isAncestor v u`
  * `not_mem_nd_iff`：`u ∉ nd v ↔ isAncestor v u`（在 `u ≠ v` 下）

  ⟹ 这三条可以在 `LMGc` 场景下替代 `hcover` 的成员推导。
  =========================================================================== -/

namespace FateV2.Predict.NDMem

open FateV2.Modeling
open Finset FateV2.Error Fate.DAGFactorization
open FateV2.Modeling.Graph
universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

-- nd v 的成员刻画
theorem mem_nd_iff (G : FateV2.Modeling.Graph.DAG V) {v u : V} :
    u ∈ G.nonDescendants v ↔ ¬ G.isAncestor v u ∧ u ≠ v := by
  simp only [FateV2.Modeling.Graph.DAG.nonDescendants, Finset.mem_filter, Finset.mem_univ, true_and]

-- ⭐ 若 u ∉ nd v 且 u ≠ v，则 isAncestor v u
theorem not_mem_nd_implies_anc (G : FateV2.Modeling.Graph.DAG V) {v u : V}
    (h1 : u ∉ G.nonDescendants v) (h2 : u ≠ v) : G.isAncestor v u := by
  by_contra hc
  exact h1 ((mem_nd_iff G).mpr ⟨hc, h2⟩)

-- ⭐ 等价形式
theorem not_mem_nd_iff (G : FateV2.Modeling.Graph.DAG V) {v u : V} (h2 : u ≠ v) :
    u ∉ G.nonDescendants v ↔ G.isAncestor v u := by
  constructor
  · intro h; exact not_mem_nd_implies_anc G h h2
  · intro hanc hmem; exact ((mem_nd_iff G).mp hmem).1 hanc

end FateV2.Predict.NDMem
