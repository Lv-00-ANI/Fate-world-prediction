import FateWorld.Legacy.AncestralInheritanceRouteB
import FateWorld.Legacy.BridgeA1
import FateWorld.Legacy.MassBoundaryValues

/-! ===========================================================================
  §0  `FactorizesC ⟹ LMGc`（即 `FactorizesC_implies_LMGc_Gap`）的结构分析

  ## 现状

  `Fate/AncestralInheritanceRouteB.lean:309` 把
  `FactorizesC_implies_LMGc_Gap p G := FactorizesC p G → LMGc p G`
  **登记为 `Prop`，从未证出**。

  `Fate/BridgeA4.lean` 与 `Fate/_a4trim.lean` 都声称证出了它
  （`factorizesL_implies_LGMc`），**但两个文件都编译失败**。

  ## 本会话的化简（关键）

  由 `BridgeA1.pa_subset_nonDescendants`：`pa(v) ⊆ nd(v)`。

  ⟹ `LMGc` 中的四个集合简化为：

  | 原集合 | 化简后 |
  |---|---|
  | `nd(v) ∪ pa(v)` | **`nd(v)`** |
  | `{v} ∪ nd(v) ∪ pa(v)` | **`{v} ∪ nd(v)`** |

  ⟹ `LMGc p G` 等价于
    `mass ({v} ∪ pa v) p x * mass (nd v) p x
       = mass (pa v) p x * mass ({v} ∪ nd v) p x`

  ## 与塔性质的关系

  上式正是**塔性质的形状**。

  而 `Fate/TowerExactLaw.lean` 的 `mass_self_fails` 说明：
  `mass S (mass S p) x ≠ mass S p x` 当 `multS S x ≠ 1`。

  **⟹ 所以 `FactorizesC ⟹ LMGc` 的成立必须依赖「因子化 + 读集封闭」的具体结构，
     而不能靠一般的塔性质。**

  ## 诚实边界

  本文件**只做结构化简**，不含 `FactorizesC ⟹ LMGc` 的证明。
  该 Gap 仍是开放问题——它是 `AncestralInheritanceRouteB` 的核心未证目标。
  =========================================================================== -/
