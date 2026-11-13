import FateWorld.Legacy.NoCoverCondIndepPlan
import FateWorld.Legacy.MassOfReadsCover
import FateWorld.Legacy.MultSUnify

/-! ===========================================================================
  §0  子系统 `mass` 的桥：最后一块拼图

  ## 目标

  若 `g` 只读 `U`（不读 `U` 外坐标），`S ⊆ U`，则

  $$mass_S\,g\,x = |\alpha|^{|V|-|U|} \cdot \left(\sum_{v_{U\setminus S}} g(\text{拓展}(x|_S, v))\right)$$

  **⟹ 在 `CondIndep` 中，四个 `mass` 的 `S` 都是 `U = X∪Y∪Z` 的子集，
     故都带**同一个** `|α|^(|V|-|U|)` 因子，可以约掉。**

  ## 已确认的关系

  | 关系 | 模块 |
  |---|---|
  | `mass U g x = multS(U,x) · g x`（`g` 只读 `U`）| `MassMultSBridge.mass_eq_multS_of_reads` |
  | `multS U x = |α|^(|V|-|U|)` | `MultSUnify.multS_eq_card_pow` |
  | `mass U g x = |α|^(|V|-|U|) · g x`（`g` 只读 `U`）| `MassOfReadsCover.mass_eq_of_reads_cover` |

  **⟹ `S = U` 的情形已完全解决。**

  ## 剩余：`S ⊊ U`

  对 `S ⊊ U`，`mass S g x` 的纤维比 `mass U g x` 大 `|α|^(|U|-|S|)` 倍，
  且求和范围是「固定 `S`、自由 `U\S`」。
  需要按 `w|_U` 分类，每类 `|α|^(|V|-|U|)` 个。

  ## 证明路径

  1. 用 `Finset.sum_bij` 或「按 `w|_U` 分块」把 `mass S g x` 分解
  2. 每块贡献 `|α|^(|V|-|U|) · g(某点)`
  3. 汇总得目标形式

  ## 更好的替代：直接给出「比值」形式

  若只需 `CondIndep`，可以证明更强的
  **「`mass S g x / mass T g x` 与 `|α|` 因子无关」**，
  即两者都等于 `|α|^(|V|-|U|)` × 各自在 `U` 上的量。

  ## 诚实边界

  本文件只做路径规划。子系统 `mass` 的桥**未证**。

  ## 参考：13 轮探索已建立的地图

  * 5 个正确工具（`mass_eq_of_reads_cover`、`card_balance_lmgc`、
    `mass_sdiff_of_reads`、`lmgc_iff`、`not_mem_nd_iff`）
  * 4 条失败路线（详见 `LMGcRouteHistory`）
  * 1 条结构性结论（详见 `NoCoverCondIndepPlan`）
  =========================================================================== -/
