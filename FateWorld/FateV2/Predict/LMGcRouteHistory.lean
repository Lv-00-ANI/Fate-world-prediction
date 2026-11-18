import FateWorld.FateV2.Predict.LMGcCoverGap
/-!
  # Predict · LMGcRouteHistory

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LMGcRouteHistory.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LMGcCoverGap
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  ⚠ `LMGc` 的**路线失败史**（诚实登记）

  ## 时间线

  | 轮次 | 尝试 | 结果 |
  |---|---|---|
  | R177–178 | `FactorizesC ⟹ LMGc` | **机检反例：假** |
  | R179 | `LMGc ⟺ CondIndep {v} (nd v) (pa v)` | **✅ 成立** |
  | R180 | 用 `CondIndepGeneralNZ` 的桥 | ❌ `hcover` 不满足 |
  | R181 | 定位障碍：指数 OK / 成员推导不 OK | 分析 |
  | R182 | 交付 `nd` 成员刻画 | ✅ 但**不适用**（R183） |
  | R183 | 改为「直接计算」 | 分析 |
  | R184 | `mass_eq_of_reads_cover` | **✅ 成立** |
  | R185 | `card_balance_lmgc` | **✅ 成立** |
  | R186 | 定位第二个障碍：`nd v` 的 cover 不满足 | 分析 |
  | R187 | 尝试用 `mass_sdiff_of_reads` 处理后两项 | ❌ **需 `g` 只读 `T\{s}`，而 `p` 读 `v`** |

  ## 核心困难

  `LMGc` 的两个 `mass`（`mass (pa v)`、`mass (nd v)`）都含 `ψ v`，
  而 `ψ v` 读 `{v} ∪ pa v`，**不**只读 `pa v` 或 `nd v`。

  **⟹ 它们无法各自化为 `|α|^k · p x`。**

  正确的做法应当是：**保留 `nd v` 上的求和**，
  证明左右两边的求和结构相同（只是 `ψ v` 的位置不同）。

  ## 已有工具（全部正确，可复用）

  | 工具 | 模块 |
  |---|---|
  | `mass_eq_of_reads_cover` | `MassOfReadsCover` |
  | `card_balance_lmgc` | `CardBalanceLMGc` |
  | `mass_sdiff_of_reads` | `MassSdiffConst` |
  | `lmgc_iff` | `LMGcCondIndepEquiv` |
  | `not_mem_nd_iff` 等 | `NonDescendantsMem` |

  ## 诚实边界

  `LMGc`（在 `Factorizes` + `dSep` 下）仍**未证**。
  本文件只登记路线失败史，避免重复劳动。
  =========================================================================== -/
