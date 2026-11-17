import FateWorld.FateV2.Predict.AncestralInheritanceRouteB
import FateWorld.FateV2.Predict.BridgeA1
import FateWorld.FateV2.Modeling.CondIndepGeneralNZ
/-!
  # Predict · LMGcCondIndepEquiv

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LMGcCondIndepEquiv.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：AncestralInheritanceRouteB, BridgeA1, CondIndepGeneralNZ
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  ⭐ `LMGc ⟺ ∀ v, CondIndep p {v} (nd v) (pa v)`

  ## 背景

  `AncestralInheritanceRouteB.lean` 定义了
  ```lean
  def LMGc (p) (G) : Prop := ∀ v x,
      mass (insert v (pa G v)) p x * mass (G.nonDescendants v ∪ pa G v) p x
        = mass (pa G v) p x * mass (insert v (G.nonDescendants v ∪ pa G v)) p x
  ```
  而本会话的 `CondIndep`：
  ```lean
  def CondIndep (p) (X Y Z) : Prop := ∀ x,
      mass (X ∪ Y ∪ Z) p x * mass Z p x = mass (X ∪ Z) p x * mass (Y ∪ Z) p x
  ```

  ## 本文件的结果

  ```lean
  theorem lmgc_iff (p) (G) :
      LMGc p G ↔ ∀ v, CondIndep p {v} (nd v) (pa v)
  ```

  ## 证明

  用 `pa(v) ⊆ nd(v)`（`BridgeA1.pa_subset_nonDescendants`）把
  `nd v ∪ pa v` 化为 `nd v`，然后两边就是同一个等式的不同排列。

  ## 意义

  这把 `AncestralInheritanceRouteB` 的 `LMGc` 与本会话的 `CondIndep` **正式连接**：
  任何关于 `CondIndep p {v} (nd v) (pa v)` 的定理（包括本会话的桥）
  都可以翻译成 `LMGc` 的相应部分。

  **注意**：这不意味着 `LMGc` 可以由 `FactorizesC` 推出——
  `Fate/SolutionCLMGcCounterexample.lean` 已机检证明那是假的。
  本条只给出 `LMGc` 与 `CondIndep` 的**形式等价**。
  =========================================================================== -/

namespace FateV2.Predict.LMGCEquiv

open FateV2.Modeling
open Finset FateV2.Error Fate.DAGFactorization Fate.View19
open FateV2.Modeling.Graph
universe u
variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

-- 先证：pa v ⊆ nd v
theorem pa_sub_nd (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    pa G v ⊆ G.nonDescendants v :=
  Fate.BridgeA1.pa_subset_nonDescendants G v

-- ⭐ LMGc ⟺ ∀ v, CondIndep p {v} (nd v) (pa v)
theorem lmgc_iff (p : (V → α) → ℝ) (G : FateV2.Modeling.Graph.DAG V) :
    Fate.AncestralInheritanceRouteB.LMGc p G ↔
      ∀ v : V, Fate.FactorMarkov.CondIndep p {v} (G.nonDescendants v) (pa G v) := by
  constructor
  · intro h v x
    have hpand := pa_sub_nd G v
    -- LMGc: mass (insert v (pa v)) * mass (nd v ∪ pa v) = mass (pa v) * mass (insert v (nd v ∪ pa v))
    have h1 := h v x
    -- CondIndep: mass ({v} ∪ nd v ∪ pa v) * mass (pa v) = mass ({v} ∪ pa v) * mass (nd v ∪ pa v)
    -- 用 nd ∪ pa = nd（因 pa ⊆ nd）
    have h2 : G.nonDescendants v ∪ pa G v = G.nonDescendants v :=
      Finset.union_eq_left.mpr hpand
    rw [h2] at h1 ⊢
    -- h1: mass (insert v (pa v)) * mass (nd v) = mass (pa v) * mass (insert v (nd v))
    -- 目标: mass ({v} ∪ nd v) * mass (pa v) = mass ({v} ∪ pa v) * mass (nd v)
    -- insert v (pa v) = {v} ∪ pa v（因为 v ∉ pa v）
    -- 化简 {v} ∪ nd ∪ pa = {v} ∪ nd（因 pa ⊆ nd）
    have h3 : ({v} ∪ G.nonDescendants v ∪ pa G v : Finset V) = {v} ∪ G.nonDescendants v := by
      rw [Finset.union_assoc, h2]
    rw [h3]
    -- 目标: mass ({v} ∪ nd v) * mass (pa v) = mass ({v} ∪ pa v) * mass (nd v)
    -- h1 : mass (insert v (pa v)) * mass (nd v) = mass (pa v) * mass (insert v (nd v))
    rw [show (insert v (pa G v) : Finset V) = {v} ∪ pa G v from rfl,
        show (insert v (G.nonDescendants v) : Finset V) = {v} ∪ G.nonDescendants v from rfl] at h1
    rw [mul_comm (mass ({v} ∪ G.nonDescendants v) p x) (mass (pa G v) p x)]
    exact h1.symm
  · intro h v x
    have hpand := pa_sub_nd G v
    have h2 : G.nonDescendants v ∪ pa G v = G.nonDescendants v :=
      Finset.union_eq_left.mpr hpand
    have h1 := h v x
    rw [h2] at h1 ⊢
    -- 目标已被前面的 rw [h2] 化简为：
    --   mass (insert v (pa v)) * mass (nd v) = mass (pa v) * mass (insert v (nd v))
    -- h1 也正是这个形式
    -- h1 : mass ({v} ∪ nd ∪ pa) * mass (pa) = mass ({v} ∪ pa) * mass (nd)
    -- 目标 : mass (insert v (pa)) * mass (nd) = mass (pa) * mass (insert v (nd))
    have h3 : ({v} ∪ G.nonDescendants v ∪ pa G v : Finset V) = insert v (G.nonDescendants v) := by
      rw [Finset.union_assoc, h2]
      exact (Finset.insert_eq v (G.nonDescendants v)).symm
    rw [h3] at h1
    rw [show ({v} ∪ pa G v : Finset V) = insert v (pa G v) from rfl] at h1
    rw [mul_comm (mass (insert v (G.nonDescendants v)) p x) (mass (pa G v) p x)] at h1
    exact h1.symm

end FateV2.Predict.LMGCEquiv
