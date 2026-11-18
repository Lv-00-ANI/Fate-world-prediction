import FateWorld.FateV2.Predict.SubMassFoundations
import FateWorld.FateV2.Predict.GraphToProbView7
import FateWorld.FateV2.Predict.LMGcCondIndepEquiv
/-!
  # Meta · ExistingToolsAudit

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ExistingToolsAudit.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SubMassFoundations, GraphToProbView7, LMGcCondIndepEquiv
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  ⚠⚠ **重大发现**：`Fate/GraphToProbView7.lean` 已有 `LMGc` 所需的核心工具

  ## 背景

  本会话在 R177–R192（16 轮）中反复尝试证 `LMGc`，
  从原理重建了多个工具（`mass_eq_of_reads_cover`、`mass_indep_outside`、
  `card_balance_lmgc` 等）。

  **但 `Fate/GraphToProbView7.lean` 早就有更直接的工具。**

  ## 已有工具（18 个）

  | 工具 | 内容 |
  |---|---|
  | **`mass_eq_card_mul_massA`** | `mass S p x = \|α\|^(\|V\|-\|A\|) · Σ_{wA} [⋯] p(extEnd A ω₀ wA)`（子系统求和分解）|
  | **`shadow_decomp`** | `p = f·g`、`f` 只读 `T ⊆ A` ⟹ `mass A p x = f x · mass A g x` |
  | **`block_sep`** | 同上，且 `g` 只读 `D ⊆ A` ⟹ **两种分解同时成立** |
  | **`shadow_product`** | `mass A p x * mass A p x = (f x · mass A g x) · (g x · mass A f x)` |
  | `ev` / `mass_eq_sum_ev` | 指示函数形式的 `mass` |
  | `mass_empty_irrel` | `mass ∅` 与被积函数无关 |
  | `ind_union` / `sum_ind_univ` / `sum_ind_and` / `sum_ind_eq_filter_card` | 求和恒等式 |
  | `ancestorsSet_closed_parent` / `leaf_of_ancestral` / `topo_max_not_parent` | 图论 |

  ## `shadow_product` 正是 `LMGc` 需要的结构

  `LMGc` 的形式：
  ```lean
  mass A₁ p x * mass A₂ p x = mass A₃ p x * mass A₄ p x
  ```
  正是「两个 `mass` 相乘」——`shadow_product` 的直接形态。

  ## 应用于 `LMGc`

  分解 `p = ψ v · ∏_{w ≠ v} ψ w`：

  | 部分 | 读集 |
  |---|---|
  | `f := ψ v` | `{v} ∪ pa v` |
  | `g := ∏_{w ≠ v} ψ w` | `{w} ∪ pa w`（`w ≠ v`）|

  取 `A = {v} ∪ nd v`：

  * `T := {v} ∪ pa v`，`hT : T ⊆ A` ✅（`pa v ⊆ nd v`）
  * `D := {w | w ≠ v} ∪ ⋃_{w≠v} pa w`，`hD : D ⊆ A` 需要图论：
    `u ∈ pa w`、`w ∈ nd v` ⟹ `¬isAncestor v u`（否则 `v →⁺ u → w` 与 `w ∈ nd v` 矛盾）
    ⟹ `u ∈ nd v ∨ u = v` ⟹ `u ∈ A` ✅

  **⟹ `shadow_product` 可以应用于 `LMGc`。**

  ## 教训

  **在从原理重建工具前，应先全面盘点已有工具库
  （`/bin/grep -E "^theorem" Fate/*.lean` 并检索关键词）。**

  本会话 16 轮中，至少 4 个工具是重复劳动。

  ## 诚实边界

  本文件是审计记录，不含 `LMGc` 的证明。
  但**下一轮的路线已完全清晰**：用 `shadow_product` / `block_sep`。
  =========================================================================== -/
