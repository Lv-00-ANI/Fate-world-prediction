import FateWorld.FateV2.Predict.BridgeGeneralize
import FateWorld.FateV2.Predict.BridgeThreeNode
import FateWorld.FateV2.Predict.ChainDSepCondMul
/-!
  # Predict · BridgeGeneralizeWiring

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeGeneralizeWiring.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BridgeGeneralize, BridgeThreeNode, ChainDSepCondMul
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/BridgeGeneralizeWiring` —— **任务 B：把 `BridgeGeneralize` 接进主链（消孤岛）**

  ## 0 为什么需要这个文件

  `grep -c "^import Fate.BridgeGeneralize$" Fate.lean` 早返回 `1`（说明它
  **在链上**），但 `grep -rl "import Fate.BridgeGeneralize" Fate/*.lean` 返回空
  （说明它**没有任何消费者**）—— 即它是一个「编译进来但没人用」的**孤岛**。

  本文件是该岛的第一个（也是唯一一个）消费者：把 `BridgeGeneralize` 的四条
  主结果以**不写签名**的转发形式（`def X := @Y`）重新对外出口，
  形成一条从 `BridgeGeneralize` 到本模块的**实际依赖边**，从而把孤岛接进主链。

  ## 1 内容一览（全部为转发，零新证明义务）

  | # | 名称 | 来源 | 含义 |
  |---|---|---|---|
  | **W1** | `dSep_forces_split_general` | `BridgeGeneralize.dSep_forces_split` | ⭐⭐⭐ 任意 `V`：`dSep + 覆盖 ⟹ Split` |
  | **W2** | `twoBlock_of_dSep_general` | `BridgeGeneralize.dSep_factorizes_separable_general` | ⭐⭐⭐ 主定理（一般 DAG）：`dSep + 覆盖 + Factorizes ⟹ 两块可分离` |
  | **W3** | `condIndep_of_dSep_general` | `BridgeGeneralize.condIndep_of_factorizes_dSep_generalZ` | ⭐⭐⭐ 全链（一般 `Z`）：`⟹ CondIndep` |
  | **W4** | `cover_condition_necessary` | `SplitFromDAG.dSep_not_implies_split_fin3` | ⭐⭐ 覆盖条件**不可去**的机检反例 |
  | **W5** | `chain_dsep_consumed` | `ChainDSepCondMul.dsep_blocks_chain_walk` | ⭐⭐⭐ 链上 `dSep` **真消费**：阻断 `0→1→2` |
  | **W6** | `chain_dsep_selects_Z` | `ChainDSepCondMul.dsep_depends_on_Z` | ⭐⭐⭐ `dSep` 在 `Z` 上非恒定（`{1}` 真 / `∅` 假） |

  **零 `sorry` / `admit` / `axiom`。不修改任何既有模块。**

  ⚠ **任务草稿与本文件的偏差（诚实登记）**：任务说明里写的
  `cover_condition_necessary := @SplitFromDAG.dSep_not_implies_split` **无法通过**
  —— `#check` 探针报
  `error(lean.unknownIdentifier): Unknown identifier 'Fate.SplitFromDAG.dSep_not_implies_split'`。
  在 `Fate/SplitFromDAG.lean` 中仅有 `dSep_not_implies_split_fin3`（两种 `grep`
  模式均确认：`dSep_not_implies_split` 只出现在 `Fate_agent_staging/SplitFromDAG.lean`
  与本仓的**文档字符串**里，正式定理名带 `_fin3` 后缀）。
  故 W4 转发的是实际存在的 `dSep_not_implies_split_fin3`。

  ## 2 前件检查（防同义反复）

  四条转发**逐字沿用**原定理签名，前件为 `G.dSep X Y Z`、`X∪Y∪Z = univ`、
  `Factorizes p G`、`¬ ∀ ...` 等**独立于结论**的图论 / 因子分解假设；
  结论 `Split` / 两块可分离 / `CondIndep` / `¬∀...` 均**不是**前件的重述。
  特别地 W4 的结论 `¬ ∀ G X Y Z, dSep → Split` 是全称命题的否定，
  其前件（无）不含该结论 —— 非空洞。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace BridgeGeneralizeWiring

universe u

/-! ### W1 —— 任意 `V` 的 `dSep ⟹ Split`（接入层） -/

/-- ⭐⭐⭐ **W1（`dSep ⟹ Split`，任意 `V`）**：`G.dSep X Y Z` 加覆盖
`X ∪ Y ∪ Z = univ` 推出读集不横跨 `X` 与 `Y`。

即 `BridgeGeneralize.dSep_forces_split` 的转发。 -/
theorem dSep_forces_split_general {V : Type*} [DecidableEq V] [Fintype V]
    (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V)
    (hdsep : G.dSep X Y Z) (hcover : X ∪ Y ∪ Z = Finset.univ) :
    Fate.View19.Split (Fate.FactorizesToHyper.readSetOf G) X Y Z :=
  @BridgeGeneralize.dSep_forces_split V _ _ G X Y Z hdsep hcover

/-! ### W2 —— 一般 DAG 主定理 -/

/-- ⭐⭐⭐ **W2（主定理，一般 DAG）**：`dSep` + 覆盖 + `Factorizes`
⟹ `p` 可写成只读 `X∪Z` 的 `f` 与只读 `Y∪Z` 的 `g` 之积。

即 `BridgeGeneralize.dSep_factorizes_separable_general` 的转发。 -/
theorem twoBlock_of_dSep_general {V : Type u} [DecidableEq V] [Fintype V]
    {α : Type u} [Fintype α] [DecidableEq α]
    (p : (V → α) → ℝ) (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V)
    (hdsep : G.dSep X Y Z) (hcover : X ∪ Y ∪ Z = Finset.univ)
    (hfac : Fate.FactorMarkov.Factorizes p G) :
    ∃ f g : (V → α) → ℝ,
      (∀ w, p w = f w * g w) ∧ BridgeGeneralize.FrozenOn (X ∪ Z) f ∧
        BridgeGeneralize.FrozenOn (Y ∪ Z) g :=
  @BridgeGeneralize.dSep_factorizes_separable_general V _ _ α _ _ p G X Y Z
    hdsep hcover hfac

/-! ### W3 —— 一般 `Z` 的全链终点 -/

/-- ⭐⭐⭐ **W3（全链，一般 `Z`）**：`Factorizes` + `dSep X Y Z` + 覆盖
⟹ `CondIndep p X Y Z`。

即 `BridgeGeneralize.condIndep_of_factorizes_dSep_generalZ` 的转发。 -/
theorem condIndep_of_dSep_general {V : Type u} [DecidableEq V] [Fintype V]
    {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    (p : Fate.FactorMarkov.Joint V α) (G : FateV2.Modeling.Graph.DAG V)
    (hfac : Fate.FactorMarkov.Factorizes p G) {X Y Z : Finset V}
    (hdsep : G.dSep X Y Z) (hcover : X ∪ Y ∪ Z = Finset.univ) :
    Fate.FactorMarkov.CondIndep p X Y Z :=
  @BridgeGeneralize.condIndep_of_factorizes_dSep_generalZ V _ _ α _ _ _ p G
    hfac X Y Z hdsep hcover

/-! ### W4 —— 覆盖条件不可去的反例 -/

/-- ⭐⭐ **W4（覆盖条件不可去）**：`dSep` **不**一般蕴含 `Split`
（`Fin 3` 撞子反例）。

即 `SplitFromDAG.dSep_not_implies_split_fin3` 的转发，说明 W1/W2/W3 中
的覆盖前件 `X ∪ Y ∪ Z = univ` 无法删除。 -/
theorem cover_condition_necessary :
    ¬ (∀ (G : FateV2.Modeling.Graph.DAG (Fin 3)) (X Y Z : Finset (Fin 3)),
        G.dSep X Y Z → Fate.View19.Split (Fate.FactorizesToHyper.readSetOf G) X Y Z) :=
  @SplitFromDAG.dSep_not_implies_split_fin3

/-! ### W5 / W6 —— 接通 `ChainDSepCondMul`（P0-A2：消「已入库零消费」孤岛）

`Fate/ChainDSepCondMul.lean` 早在 `Fate.lean` 里（`import Fate.ChainDSepCondMul`），
但全库除**文档字符串**外无人引用其任何定理名 —— 审计 F2 判定它为
**「已入库但零消费的孤岛」**。

下面两条定理是该模块的**第一批名字级消费者**（G46）：
定理体里**出现** `Fate.ChainDSepCondMul.dsep_blocks_chain_walk` 与
`Fate.ChainDSepCondMul.dsep_depends_on_Z`，删掉 `import` 会**编译失败**。

**⚠ 前件检查（防同义反复 / D6）**：
* W5 的前件是 `ChainDSepCondMul.G3.dSep {0} {2} {1}` —— 一个**图论**命题；
  结论是全 `Fin 3` 三个具体顶点上的 `IsActiveWalk` **否定**。
  前件**不**包含结论（`dSep` 的某个合取项蕴含结论，但需经
  `dsep_forces_no_active_walk` 推导，不是重述）。
* W6 的前件为**无**（`chain_dsep_selects_Z` 是 `dSep` 的真值**对比**：
  `Z = {1}` 上为真、`Z = ∅` 上为假）。结论是全称式**非恒定**断言，
  其内容正是「`dSep` 携带真实图论信息」，不可能被前件重述。 -/

/-- ⭐⭐⭐ **W5：链上 `dSep` 的真消费 —— 阻断 `0 → 1 → 2`**

在链 `0 → 1 → 2` 上，`dSep {0} {2} {1}` 成立（`ChainDSepCondMul.chain_dsep_true`），
因此 `[0, 1, 2]` **不是** 在条件集 `{1}` 下的 active walk。

即 `ChainDSepCondMul.dsep_blocks_chain_walk` 的转发。

**G46**：证明项中含 `Fate.ChainDSepCondMul.dsep_blocks_chain_walk`。 -/
theorem chain_dsep_consumed :
    ¬ Fate.ChainDSepCondMul.G3.IsActiveWalk ({1} : Finset (Fin 3)) [0, 1, 2] := by
  -- 真消费链：先取 `dSep {0} {2} {1}`，再用它推出阻断结论。
  exact Fate.ChainDSepCondMul.dsep_blocks_chain_walk
    Fate.ChainDSepCondMul.chain_dsep_true

/-- ⭐⭐⭐ **W6：`dSep` 的取值随条件集 `Z` 变化（非恒定谓词）**

同一条 `dSep {0} {2} ·` 在两个条件集上取**不同真值**：
`Z = {1}` 时为真，`Z = ∅` 时为假（空集下 `[0,1,2]` 是 active walk）。

即 `ChainDSepCondMul.dsep_depends_on_Z` 的转发。

**G46**：证明项中含 `Fate.ChainDSepCondMul.dsep_depends_on_Z`。 -/
theorem chain_dsep_selects_Z :
    Fate.ChainDSepCondMul.G3.dSep {0} {2} {1} ∧
      ¬ Fate.ChainDSepCondMul.G3.dSep {0} {2} (∅ : Finset (Fin 3)) :=
  Fate.ChainDSepCondMul.dsep_depends_on_Z

end BridgeGeneralizeWiring
end FateV2.Predict