import FateWorld.FateV2.Predict.LMGcFinalVerdict
import FateWorld.FateV2.Predict.MassOfReadsCover
/-!
  # Predict · NoCoverCondIndepPlan

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NoCoverCondIndepPlan.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LMGcFinalVerdict, MassOfReadsCover
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  ⚠ 无 `cover` 的 `CondIndep`：结构性结论

  ## 目标

  若成立，则
  ```lean
  (hfac : Factorizes p G) (hdsep : G.dSep X Y Z) :
      CondIndep p X Y Z          -- 无 hcover
  ```
  可推出 `LMGc`（由 `lmgc_iff`，取 `X = {v}`、`Y = nd v`、`Z = pa v`）。

  ## 分析

  设 `U := X ∪ Y ∪ Z`。`CondIndep` 的四个集合
  `U`、`Z`、`X∪Z`、`Y∪Z` **都是 `U` 的子集**。

  若 `p` 只读 `U`（即所有因子只读 `U`），则

  $$mass_S\,p\,x = |\alpha|^{|V|-|U|} \cdot \sum_{v_{U\setminus S}} p(\text{合并}(x|_S, v))$$

  **⟹ 四个 `mass` 都带**同一个** `|α|^(|V|-|U|)` 因子。**

  **⟹ `CondIndep` 的等式可以约掉它，化为「对 `U\S` 求和」的等式，
     即**子系统 `U` 上的 `CondIndep`**。**

  ## 结论

  * **无 `cover` 版本是有意义的**（不是伪问题）
  * 但它需要：(a) 「`mass S p = |α|^k · 子系统求和`」的桥引理；
    (b) 在子系统上**重做** `CondIndepGeneralNZ` 的整个证明

  **⟹ 这不是「补一行」，而是**证明的结构性重构**。**

  ## 本会话已有的相关工具

  | 工具 | 模块 | 可用于 |
  |---|---|---|
  | `mass_eq_of_reads_cover` | `MassOfReadsCover` | `S = U` 的情形 |
  | `mass_self_insert` | `MassInsertCorrected` | 单个 `mass` 的纤维化 |
  | `mass_insert_sum` / `'` | `DAGFactorization` | 升降维 |
  | `multS_eq_card_pow` | `MultSUnify` | 纤维大小 |
  | `lmgc_iff` | `LMGcCondIndepEquiv` | `LMGc` ↔ `CondIndep` |

  ## 诚实边界

  本文件只做结构性结论。无 `cover` 的 `CondIndep` **未证**。
  =========================================================================== -/
