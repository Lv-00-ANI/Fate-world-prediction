import FateWorld.FateV2.Predict.NonDescendantsMem
import FateWorld.FateV2.Predict.LMGcCondIndepEquiv
/-!
  # Predict · LMGcDirectRoute

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LMGcDirectRoute.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NonDescendantsMem, LMGcCondIndepEquiv
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `LMGc` 的**直接计算路线**（绕开 `zEquiv`）

  ## 一、`zEquiv` 路线为何不通（R181 诊断的修正）

  `Fate/CondIndepGeneralNZ.zEquiv` 需要
    `{w // w ∉ Z} ≃ ({w // w ∉ X∪Z} → α) × ({w // w ∉ Y∪Z} → α)`。

  其 `right_inv` 用 `notMemXZ_memY`：`w ∉ X∪Z ⟹ w ∈ Y`。

  在 `LMGc` 场景（`X = {v}`、`Y = nd v`、`Z = pa v`）中：
  `w ∉ {v} ∪ pa v` 且 `w ∉ nd v`
  ⟹ 由 `not_mem_nd_iff`：`isAncestor v w`
  ⟹ 但我们需要 `w ∈ nd v`，**与 `isAncestor v w` 矛盾**。

  **⟹ `notMemXZ_memY` 在 `LMGc` 场景中不可替换——`hcover` 路线不通。**

  原因：`hcover` 保证「不属于 `X∪Z` 的必属于 `Y`」；
  而 `LMGc` 的 `X∪Y∪Z` 故意漏掉 `descendants(v) \\ pa(v)`，
  那些顶点既不在 `Z`、也不在 `X`、也不在 `Y`，故 `hcover` 的断言无法成立。

  ## 二、正确的路线：直接计算

  `LMGc` 的四个集合都形如 `{v} ∪ S` 或 `S`，其中 `S ∈ {pa v, nd v}`。
  且 `pa v ⊆ nd v`（`BridgeA1.pa_subset_nonDescendants`）。

  **⟹ 可以用 `mass` 的「因子分解 + 读集」直接算四个 `mass`，
     再用 `Finset.card` 的配平（`card_balance`）收口，
     完全绕开 `zEquiv` 的双射。**

  ## 诚实边界

  本文件只做路线修正记录，不含 `LMGc` 的证明。
  `LMGc`（在 `Factorizes` + `dSep` 下）仍是开放目标。
  =========================================================================== -/
