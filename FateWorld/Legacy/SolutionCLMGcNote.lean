import FateWorld.Legacy.RouteBGapNote
import FateWorld.Legacy.ThreeNodeFactorizes
import FateWorld.Legacy.MassBoundaryValues

/-! ===========================================================================
  §0  ⚠ `FactorizesC ⟹ LMGc` 的**疑似反例**（`colliderDAG` + `colliderP`）

  ## 化简后的 `LMGc` 在 `v = 0` 处的断言

  `pa(0) = ∅`、`nd(0) = {2}` ⟹ `LMGc` 断言：

  $$mass_{\{0\}}\,p\,x\cdot mass_{\{2\}}\,p\,x
      = mass_{\emptyset}\,p\,x\cdot mass_{\{0,2\}}\,p\,x$$

  ## 取 `x ≡ false`、`p = colliderP`（`p w = [w_0 = w_2]`）

  | 量 | 计算 | 值 |
  |---|---|---|
  | `mass {0} p x` | `#{w \| w_0 = false ∧ w_0 = w_2}`（`w_1` 自由）| **2** |
  | `mass {2} p x` | `#{w \| w_2 = false ∧ w_0 = w_2}`（`w_1` 自由）| **2** |
  | `mass ∅ p x` | `∑_w p w = #{w \| w_0 = w_2}` | **4** |
  | `mass {0,2} p x` | `#{w \| w_0 = false ∧ w_2 = false ∧ w_0 = w_2}`（`w_1` 自由）| **2** |

  代入：`2 · 2 = 4 · 2`，即 `4 = 8`，**假**。

  ## 但 `colliderP` 满足 `FactorizesC colliderDAG`

  `ThreeNodeFactorizes.colliderP_factorizes` 已证 `Factorizes colliderP colliderDAG`，
  且 `FactorizesC` 与 `Factorizes` 在「读集封闭」下一致
  （`colliderPhi` 只读 `{v} ∪ pa v`）。

  ## ⟹ 结论

  **`FactorizesC ⟹ LMGc` 疑似为假。**

  这与 `AncestralInheritanceRouteB.lean:309` 把
  `FactorizesC_implies_LMGc_Gap` 只登记为 `Prop`（从不证）是一致的。

  ## 诚实边界

  本文件**只给出数值推导**，尚未机检化（`mass {0} = 2` 已机检，
  其余三个值待补）。完整反例需要四个值都机检。
  =========================================================================== -/
