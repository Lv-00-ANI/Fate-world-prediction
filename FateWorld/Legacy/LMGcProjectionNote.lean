import FateWorld.Legacy.LMGcCoverObstacle
import FateWorld.Legacy.BalanceComponents

/-! ===========================================================================
  §0  `LMGc` 的投影可行性分析：`|α|` 指数**自动抵消**，但 `hcover` 的成员推导失效

  ## 一、`|α|` 指数抵消（好消息）

  当 `p` 在相应集合上可分解时，四个 `mass` 的 `|α|` 指数为：

  | 项 | 指数 |
  |---|---|
  | `mass (X∪Y∪Z)` | `|V| - |X∪Y∪Z|` |
  | `mass Z` | `|V| - |Z|` |
  | `mass (X∪Z)` | `|V| - |X∪Z|` |
  | `mass (Y∪Z)` | `|V| - |Y∪Z|` |

  左边指数和：`2|V| - |XYZ| - |Z|`
  右边指数和：`2|V| - |XZ| - |YZ|`
  差：`|XZ| + |YZ| - |XYZ| - |Z| = 0`（`Disjoint` 下展开）

  **⟹ 这正是 `Fate/BalanceComponents.card_balance`（本会话 R26 已证）。**
  **⟹ ⟹ `|α|` 因子不构成障碍。**

  ## 二、`hcover` 的成员推导失效（坏消息）

  `Fate/CondIndepGeneralNZ.lean` 中 `hcover` 被用于：

  | 引理 | 行 | 用途 |
  |---|---|---|
  | `notMemXZ_memY` | 100 | `v ∉ X` 且 `v ∉ Z` ⟹ **`v ∈ Y`**（由 `hcover`）|
  | `notMemYZ_memX` | 110 | 同理 |
  | 关键引理 | 214, 242 | 同上 |

  **⟹ 这些推导依赖「`X ∪ Y ∪ Z = univ`」。**

  `LMGc` 取 `X = {v}`、`Y = nd v`、`Z = pa v`，此时 `X ∪ Y ∪ Z ⊊ univ`
  （漏掉 `descendants(v) \\ pa(v)`）。

  **⟹ 上述成员推导全部失效。**

  ## 三、结论

  * **指数层面没问题**（`card_balance` 已覆盖）
  * **成员推导层面有问题**（`hcover` 不可去）

  **⟹ `LMGc` 需要一个用「`nd v` 的定义」替代「`hcover`」的成员推导：
       若 `u ∉ {v} ∪ pa v` 且 `u ∉ nd v`，则由 `nd` 的定义直接推出
       `isAncestor v u ∨ u = v`，而不是靠覆盖。**

  ## 诚实边界

  本文件只做分析，不含新定理。
  =========================================================================== -/
