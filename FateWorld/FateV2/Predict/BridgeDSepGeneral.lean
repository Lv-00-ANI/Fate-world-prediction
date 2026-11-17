/-
# 桥的一般 `Z` 整合版：`Factorizes` + `dSep` + 覆盖 ⟹ `CondIndep p X Y Z`

把两段**已入库**的结果串起来：

* `Fate.SplitFromDAG.split_of_dSep`
  : `G.dSep X Y Z → X ∪ Y ∪ Z = univ → Split (readSetOf G) X Y Z`
* `Fate.BridgeIntegrated.condIndep_of_factorizes_general`
  : `Factorizes p G → Split (readSetOf G) X Y Z →` 三对不交 `→` 覆盖 `→ CondIndep p X Y Z`

`dSep` 的前三个合取项**恰好**就是所需的 `Disjoint X Y` / `Disjoint X Z` /
`Disjoint Y Z`，且两处 `hcover` 的类型一致（都是 `X ∪ Y ∪ Z = Finset.univ`），
因此无需任何类型转换。

**本文件不修改任何既有模块；不写 `Fate/` 目录；不改 `Fate.lean`。**
-/

import FateWorld.FateV2.Predict.SplitFromDAG
import FateWorld.FateV2.Predict.BridgeIntegrated
namespace FateV2.Predict

open FateV2.Modeling
namespace BridgeDSepGeneral

open Finset FateV2.Modeling.Graph

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

section Chain

variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

/-- ⭐⭐⭐⭐⭐ **完整桥（一般 `Z`）**：DAG 因子分解 + `dSep` + 覆盖 ⟹ 条件独立。

$$p \text{ 因子分解于 } G \;\wedge\; X \perp_d Y \mid Z \;\wedge\; X\cup Y\cup Z = V
\;\Longrightarrow\; X \perp\!\!\!\perp_p Y \mid Z.$$

三对不交由 `hdsep` 的前三个合取项直接给出（`dSep` 的定义即为
`Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧ Disjoint (bbReachableVertices Z X) Y`），
覆盖条件在两处签名中类型一致，因此证明是纯粹的串联。 -/
theorem condIndep_of_factorizes_dSep_general
    (p : Fate.FactorMarkov.Joint V α) (G : FateV2.Modeling.Graph.DAG V)
    (hfac : Fate.FactorMarkov.Factorizes p G) {X Y Z : Finset V}
    (hdsep : G.dSep X Y Z) (hcover : X ∪ Y ∪ Z = Finset.univ) :
    Fate.FactorMarkov.CondIndep p X Y Z := by
  have hdisj : Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧
      Disjoint (G.bbReachableVertices Z X) Y := hdsep
  obtain ⟨hXY, hXZ, hYZ, _⟩ := hdisj
  exact BridgeIntegrated.condIndep_of_factorizes_general p G hfac
    (SplitFromDAG.split_of_dSep G X Y Z hdsep hcover) hXY hXZ hYZ hcover

end Chain

/-!
  # Predict · BridgeDSepGeneral

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeDSepGeneral.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SplitFromDAG, BridgeIntegrated
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §2  一致性检查：一般版在 `Z = ∅` 处回落到已入库的 `condIndep_of_factorizes_dSep`

  `Fate.SplitFromDAG.condIndep_of_factorizes_dSep` 已存入库且零 `sorry`，
  这里不再重复证明 `Z = ∅` 版本，只登记其签名以供交叉核对：
  * `condIndep_of_factorizes_dSep (hdsep : G.dSep X Y ∅) (hcover : X ∪ Y = univ)
      : CondIndep p X Y ∅`
  它与上面的 `condIndep_of_factorizes_dSep_general` 在 `Z = ∅` 时陈述一致
  （`X ∪ Y ∪ ∅ = univ` 与 `X ∪ Y = univ` 等价），故 emptyZ 版本**跳过**。
  =========================================================================== -/

end BridgeDSepGeneral

end FateV2.Predict