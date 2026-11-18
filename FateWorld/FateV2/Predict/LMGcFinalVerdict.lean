import FateWorld.FateV2.Predict.LMGcRouteHistory
import FateWorld.FateV2.Predict.SolutionCLMGcCounterexample
/-!
  # Predict · LMGcFinalVerdict

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LMGcFinalVerdict.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LMGcRouteHistory, SolutionCLMGcCounterexample
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  ⚠ `LMGc` 的**最终判决**：`FactorizesC ⟹ LMGc` 已被机检证伪

  ## 关键澄清

  `Fate/AncestralInheritanceRouteB.lean:309` 的声明是

  ```lean

namespace FateV2.Predict.LMGcFinalVerdict

  def FactorizesC_implies_LMGc_Gap (p) (G) : Prop := FactorizesC p G → LMGc p G
  ```

  **注意：声明里没有 `dSep` 假设。**

  ## 已机检的反例

  `Fate/SolutionCLMGcCounterexample.lean`：
  `G = colliderDAG`、`p = colliderP`、`α = Bool`、`x ≡ false`

  | 量 | 值 |
  |---|---|
  | `mass {0} p x` | 2 |
  | `mass {2} p x` | 2 |
  | `mass ∅ p x` | 4 |
  | `mass {0,2} p x` | 2 |

  `v = 0` 处（`pa(0) = ∅`、`nd(0) = {2}`）：`2·2 = 4·2`，即 `4 = 8`，**假**。

  而 `colliderP` **满足** `FactorizesC colliderDAG`。

  **⟹ `FactorizesC_implies_LMGc_Gap` 是假命题。**

  ## 本轮进一步的分析（为什么「一般」不成立）

  `LMGc` 的两个 `mass`（`mass (pa v)`、`mass (nd v)`）都含 `ψ v`，
  而 `ψ v` 读 `{v} ∪ pa v` ⟹ 在 `mass (nd v)`/`mass (pa v)` 的纤维上
  `ψ v` **随 `w_v` 变化**。

  用 `mass_insert_sum'` 展开：
  `mass (nd v) p x = Σ_a mass ({v}∪nd v) p (unpin v x a)`
  其中被加项**依赖 `a`**。

  而 `LMGc` 左边的 `mass ({v}∪pa v)` 是**单点**（不带 `Σ`）。
  ⟹ 两边结构不对称，无法配对。

  **⟹ `LMGc` 在一般 `Factorizes` 下不成立**（与机检反例一致）。

  ## 唯一可能的拯救：加 `dSep`

  `Fate/BridgeDSepGeneral.condIndep_of_factorizes_dSep_general` 证明
  `Factorizes + dSep + cover ⟹ CondIndep`。

  由 `lmgc_iff`，`CondIndep {v} (nd v) (pa v)` 就是 `LMGc` 在 `v` 处的断言。

  **⟹ 若对每个 `v` 都有 `G.dSep {v} (nd v) (pa v)` 且 cover 成立，
     则 `LMGc` 成立。**

  但 cover 条件 `{v} ∪ nd v ∪ pa v = univ` 等价于 `descendants(v) ⊆ pa v`
  （`Fate/LMGcCoverObstacle.lean`），一般**不成立**。

  **⟹ 需要 `CondIndep` 的无 cover 版本。**

  ## 诚实边界

  本文件汇总 `LMGc` 的最终诊断，不含新定理。
  =========================================================================== -/

end FateV2.Predict.LMGcFinalVerdict
