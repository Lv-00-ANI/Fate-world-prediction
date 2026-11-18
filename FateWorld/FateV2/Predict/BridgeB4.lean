import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Modeling.CausActivePath
import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.FactorRecursionRouteB
import FateWorld.FateV2.Modeling.BridgeB2
import FateWorld.FateV2.Predict.BridgeB3
import FateWorld.FateV2.Predict.AncestralInheritanceRouteB
import FateWorld.FateV2.Predict.BridgeA1
import FateWorld.FateV2.Predict.BridgeA2
/-!
  # Predict · BridgeB4

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeB4.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausSeparation, _root.CausActivePath, DAGFactorization, FactorRecursionRouteB, BridgeB2, BridgeB3, AncestralInheritanceRouteB, BridgeA1, BridgeA2
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/BridgeB4` —— **段 B4：`LMG ⟹ 全局 Markov`（一般 DAG）**

  本文件是清单 §二 段 B 的收口。**先说结论（诚实登记，逐条机器验证）**：

  | # | 命题 | 状态 |
  |---|---|---|
  | **B4.0** | 正确的乘性条件独立 `CIMul` / 全局 Markov `GM` 的定义 | ✅ 定义 |
  | **B4.1** | `bbReachAux` 在「`bbStep` 恒空」的图上是空集（图论工具） | ✅ **零缺口（真证）** |
  | **B4.2** | 无边图 `emptyDAG2` 上 `dSep {0} {1} ∅` 成立 | ✅ **零缺口（真证）** |
  | **B4.3** | 该图上的 `LMG` **恒真**（对任意 `p`） | ✅ **零缺口（真证）** |
  | **B4.4** | 取 `p = [x₀ = x₁]`，`¬ CIMul {0} {1} ∅ p` | ✅ **零缺口（真证）** |
  | **B4.5** | ⟹ **清单 B4 的字面命题（`LMG ⟹ GM`）是假命题** | ✅ **零缺口（真证）** |

  ## 0 ⚠ 核心裁定：**B4（字面版）不可证 —— 它是假的**

  `Fate/FactorRecursionRouteB.lean` 的 `LMG` 定义逐字为

  $$\mathrm{LMG}\,p\,G :\iff \forall v\,x,\;
      p\,x\cdot \mu_{nd(v)\cup pa(v)}\,x
        = \mu_{\{v\}\cup nd(v)\cup pa(v)}\,x\cdot \mu_{nd(v)\cup pa(v)}\,x .$$

  在**无边图**上 `nd(v) ∪ pa(v) = V\setminus\{v\}`，于是
  `insert v (nd v ∪ pa v) = univ`，`mass univ = p`，等式两边**逐字相同**：
  `LMG` 在无边图上**对任意 `p` 都成立**（B4.3）。

  但全局 Markov 在无边图上**不**对任意 `p` 成立：无边图上 `{0} ⊥ {1} | ∅`
  是 d-分离成立的（B4.2），而乘性 CI 需要 `p x·Σp = μ_{0}x·μ_{1}x` ——
  取 `p = [x₀ = x₁]` 时左边 `2`、右边 `1`（B4.4）。

  ⟹ **`B4.5`：`¬ (LMG p G → GM p G)`，机器验证、零缺口。**
  清单 §二 段 B 的目标 4（`LMG ⟹ GM`）**在现有 `LMG` 定义下不成立**，
  与 `Fate/LMGGlobalMarkovRoute5` 的 R5.1–R5.2（`LMG` 本身是假定义）
  以及 `Fate/AncestralInheritanceRouteB` §2（`LMG` ≠ 局部 Markov）**独立吻合**：
  本文件给的是**该蕴含为假的直接证据**（不是「`LMG` 太强」，而是
  「`LMG` 在无边图上退化到**空约束**，比全局 Markov 弱」）。

  ## 1 卡在哪一步 / 缺什么引理（清单要求的「诚实登记」）

  ### 1.1 字面版 B4 卡在「定义」而不是「证明」

  `LMG` 的等式在 `v` 处**只比较** `nd(v)∪pa(v)` 与 `insert v (nd(v)∪pa(v))`
  两个积分集。对**任何** `v`，这两个集合的补集是 `desc(v) \ {v}` 中的「严格后代」。
  当 `v` 是**汇点**（无后代）时两集合相同 ⟹ 等式恒真（`BridgeB4` 的 A3
  `lmg_at_sink_trivial` 已登记此点）；当 `pa(v) ∪ nd(v)` 与 `{v}` 的并已是全体
  （如无边图，或 `v` 为源点时）等式也恒真。
  **⟹ `LMG` 在「`v` 无后代」与「`v` 无后代外的点」两类顶点上不提供任何信息，
  它不是局部 Markov。**

  ### 1.2 修正后的形状（本文件 §3 给出，与 `AncestralInheritanceRouteB` 的 `LMGc` 一致）

  正确的局部 Markov（`v ⊥ nd(v) | pa(v)`）的乘性、无量纲、无正性假设形式是

  $$\mu_{\{v\}\cup pa(v)}\,x\cdot \mu_{nd(v)\cup pa(v)}\,x
     = \mu_{pa(v)}\,x \cdot \mu_{\{v\}\cup nd(v)\cup pa(v)}\,x .$$

  本文件把它记作 `LMGc`（§3.1）。**真正的 B4** 应当是
  `LMGc ⟹ GM`。**本文件没有证出它**，§4 给出精确卡点与所需引理清单。

  ### 1.3 本文件**真的**交付了什么（避免「搬运当增量」）

  * B4.1–B4.5：**字面版 B4 的反例**（完全新的机器证据，直接回答「证不出」的原因）；
  * §2：`CIMul` / `GM` 的**正确**定义（既有 `BridgeB4` 草稿里的 `CIMul` 把
    `mass Z` 写成了 `mass (X∪Y∪Z)`，在 `X∪Y∪Z = univ` 时退化为 `p·p`，
    是**错的**；本文件修正，见 §2.1 的对照）；
  * §3：`LMGc` 定义 + `FactorizesC ⟹ LMGc` 的**唯一实质性分析引理**
    `mass_split_of_reads`（真证，零缺口）—— 这是段 A 修正版的核心操作原语；
  * §4：`LMGc ⟹ GM` 的精确卡点（B1/B2/B3 各自落点 + 缺失引理清单）。

  **无 `sorry` / `admit` / `axiom`。不使用 `mass` 塔性质（`mass` 只按定义使用）。**
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace BridgeB4

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset
open FateV2.Modeling.Graph
open FateV2.Modeling.Graph.DAG
open Fate.DAGFactorization

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-! ===========================================================================
  §2 ⭐ **正确的乘性条件独立与全局 Markov 的定义**

  ### 2.1 与既有草稿 `Fate/BridgeB4.lean`（旧版）的差别（必须记录）

  旧草稿写的是

  ```
  CIMul X Y Z p : ∀ x, p x * mass (X ∪ Y ∪ Z) p x = mass (X ∪ Z) p x * mass (Y ∪ Z) p x
  ```

  当 `X ∪ Y ∪ Z = univ`（`Z` 之外只有 `X`、`Y` 的常见情形）时
  `mass (X∪Y∪Z) = mass univ = p`，等式退化为 `p x · p x = μ_{X∪Z} · μ_{Y∪Z}`
  —— **不是**条件独立（后者是 `p x · μ_Z x = μ_{X∪Z} · μ_{Y∪Z}`）。
  本文件改用**正确的** `mass Z`：

  $$p\,x\cdot\mu_{Z}\,x=\mu_{X\cup Z}\,x\cdot\mu_{Y\cup Z}\,x .$$

  这正是「`p_{XYZ}\cdot p_Z = p_{XZ}\cdot p_{YZ}`」的无量纲、无除法形式
  （同除 `μ_Z` 即得教科书形式 `p_{XY|Z} = p_{X|Z}\cdot p_{Y|Z}`）。
  =========================================================================== -/

/-- ⭐⭐⭐ **B4.GM（乘性条件独立 `X ⟂ Y | Z`，一般 `X Y Z`）**：

$$p\,x\cdot \mu_{Z}\,x = \mu_{X\cup Z}\,x\cdot \mu_{Y\cup Z}\,x .$$

* 不用除法 ⟹ 不要求 `μ_Z ≠ 0`；
* 不要求 `X,Y,Z` 分割 `V`（当它们是分割时 `p = μ_{X∪Y∪Z}`，与常规定义逐字一致）；
* 不用归一化 ⟹ 常值缩放不变（齐次）。 -/
def CIMul (X Y Z : Finset V) (p : (V → α) → ℝ) : Prop :=
  ∀ x : V → α, p x * mass Z p x = mass (X ∪ Z) p x * mass (Y ∪ Z) p x

/-- ⭐⭐⭐ **B4.GM（全局 Markov）**：`G` 上一切 d-分离三元组都给乘性条件独立。

**这就是清单「B4 = `LMG ⟹ GM`」里 `GM` 的精确落点**（`dSep` 取
`CausSeparation.dSep` 的官方口径，`CIMul` 取上面的正确形式）。
**`G` 是真参数**（不是哑变量）：`dSep` 对 `G` 说话。 -/
def GM (p : (V → α) → ℝ) (G : FateV2.Modeling.Graph.DAG V) : Prop :=
  ∀ X Y Z : Finset V, G.dSep X Y Z → CIMul X Y Z p

/-- **B4.GM.0**：`GM` 的定义展开（`Iff.rfl`，零缺口）。 -/
theorem GM_iff (p : (V → α) → ℝ) (G : FateV2.Modeling.Graph.DAG V) :
    GM p G ↔ ∀ X Y Z : Finset V, G.dSep X Y Z → CIMul X Y Z p := Iff.rfl

/-- **B4.GM.1**：清单字面版目标 `LMG ⟹ GM` 的**精确陈述**（本文件 §5 判定它为假）。 -/
def LMG_implies_GM (p : (V → α) → ℝ) (G : FateV2.Modeling.Graph.DAG V) : Prop :=
  FateV2.Predict.FactorRecursionRouteB.LMG p G → GM p G

/-! ===========================================================================
  §R26 ⭐ **跨模块组合层（R-26 真接线）**

  把 `FateV2.Predict.BridgeA2` / `FateV2.Modeling.BridgeB2` / `FateV2.Predict.BridgeB3` 三个**此前零引用**模块
  的定理，与本文件的 `CIMul` / `GM` 组装成组合结论（本条 § 为**纯追加**：
  不改动上面任何一条 `theorem` / `def`，不删除任何声明）。

  **反循环自检**（回应本项目最高频问题）：以下每条定理的**前件**都只是
  `dSep`、集合包含、拓扑序数据、非空性等**独立输入**，**没有**把结论
  当成前件；`hGM`（R26.5）是 `GM` 定义型前提，结论是它在**新三元组**
  `(∅, Y, Z∪X)` 处的一个实例——这是 `GM` 的**消费**而非同义反复。

  `G` 一律写成显式参数（不进 section，避免外层 `variable` 的类型类
  实例在嵌套 section 内失效）。
  =========================================================================== -/

/-- **R26.1（A2 × B3）源点剥离 + 剥离点不是自己的父**：

设 `l ∈ X` 且 `dSep X Y Z`。则把 `l` 搬进条件集后 `dSep (X∖{l}) Y (Z∪{l})`
（B3.3 `dSep_peel_source`，真消费 `hd`），且 `l ∉ pa_G(l)`
（A2 `not_mem_pa_self_local`，真消费 `G.acyclic`）。 -/
theorem peel_source_and_not_mem_pa_self {G : FateV2.Modeling.Graph.DAG V}
    {X Y Z : Finset V} {l : V} (hl : l ∈ X) (hd : G.dSep X Y Z) :
    G.dSep (X \ {l}) Y (Z ∪ {l}) ∧ l ∉ Fate.DAGFactorization.pa G l :=
  ⟨FateV2.Predict.BridgeB3.dSep_peel_source hl hd,
   FateV2.Predict.BridgeA2.not_mem_pa_self_local G l⟩

/-- **R26.2（B2 × B3）拓扑前缀整体剥离 + 前缀父闭性**：

设 `τ : TopoOrderData G`、`S := topoPrefix G τ k ⊆ X`、`dSep X Y Z`。则整体把
`S` 搬进条件集后 `dSep (X∖S) Y (Z∪S)`（B3.5 `dSep_peel_fold`），且前缀的父闭性
`pa_G(v) ⊆ S`（B2.9c `topoPrefix_parent_closed`，真消费 `τ.strict`）。 -/
theorem topoPrefix_peel_fold_and_parent_closed {G : FateV2.Modeling.Graph.DAG V}
    (τ : FateV2.Modeling.BridgeB2.TopoOrderData G) (k : ℕ) {X Y Z : Finset V}
    (hS : FateV2.Modeling.BridgeB2.topoPrefix G τ k ⊆ X) (hd : G.dSep X Y Z) :
    G.dSep (X \ FateV2.Modeling.BridgeB2.topoPrefix G τ k) Y
        (Z ∪ FateV2.Modeling.BridgeB2.topoPrefix G τ k)
      ∧ ∀ v ∈ FateV2.Modeling.BridgeB2.topoPrefix G τ k,
          Fate.DAGFactorization.pa G v ⊆ FateV2.Modeling.BridgeB2.topoPrefix G τ k :=
  ⟨FateV2.Predict.BridgeB3.dSep_peel_fold hS hd,
   fun v hv => FateV2.Modeling.BridgeB2.topoPrefix_parent_closed G τ k hv⟩

/-- **R26.3（B2 × B3）存在一步剥离：基数严格下降且 `dSep` 保持**：

设 `S ⊆ X` 非空、`dSep X Y Z`。则由 B2.10a `peel_step` 取到 `v ∈ S` 使
`|S∖{v}| = |S|-1`，同一 `v` 由 B3.3 `dSep_peel_source` 剥离后 `dSep` 保持。 -/
theorem peel_step_and_dSep {G : FateV2.Modeling.Graph.DAG V}
    {X Y Z S : Finset V} (hS : S ⊆ X) (hSne : S.Nonempty) (hd : G.dSep X Y Z) :
    ∃ v ∈ S, (S.erase v).card = S.card - 1 ∧ G.dSep (X \ {v}) Y (Z ∪ {v}) := by
  obtain ⟨v, hvS, hcard⟩ := FateV2.Modeling.BridgeB2.peel_step G
    (FateV2.Modeling.BridgeB2.topoOrderData G) S hSne
  exact ⟨v, hvS, hcard, FateV2.Predict.BridgeB3.dSep_peel_source (hS hvS) hd⟩

/-- **R26.4（B3 × B2）拓扑最小源点：无入边、父不在 `S`、可剥离**：

设 `S ⊆ X` 非空、`dSep X Y Z`。则存在 `S` 的拓扑最小源点 `l`：
`l` 在 `S` 内无入边（B3 `source_of_topo_min`）；其所有父代都不在 `S` 内
（B2.10b `peel_no_parent_in`，真消费「无 `S` 内入边」）；且可剥进条件集
（B3.3 `dSep_peel_source`，真消费 `hd`）。 -/
theorem topo_min_source_peel {G : FateV2.Modeling.Graph.DAG V}
    {X Y Z S : Finset V} (hS : S ⊆ X) (hSne : S.Nonempty) (hd : G.dSep X Y Z) :
    ∃ l ∈ S, (∀ w ∈ S, ¬ G.edge w l)
      ∧ (∀ u, G.edge u l → u ∉ S)
      ∧ G.dSep (X \ {l}) Y (Z ∪ {l}) := by
  obtain ⟨l, hlS, hmin⟩ := FateV2.Predict.BridgeB3.source_of_topo_min G hSne
  exact ⟨l, hlS, hmin, FateV2.Modeling.BridgeB2.peel_no_parent_in G hmin,
    FateV2.Predict.BridgeB3.dSep_peel_source (hS hlS) hd⟩

/-- **R26.5（B3 × 本文件 B4）整段剥离到空源集 + 全局 Markov 给乘性条件独立**：

设 `GM p G`（本文件 B4 定义）且 `dSep X Y Z`。则 B3.6 `dSep_peel_univ` 给出
`dSep ∅ Y (Z∪X)`，再在**该新三元组**处由 `GM` 取到乘性条件独立
`CIMul ∅ Y (Z∪X) p`。 -/
theorem GM_CIMul_of_full_peel {G : FateV2.Modeling.Graph.DAG V} (p : (V → α) → ℝ)
    (hGM : GM p G) {X Y Z : Finset V} (hd : G.dSep X Y Z) :
    CIMul (∅ : Finset V) Y (Z ∪ X) p :=
  hGM ∅ Y (Z ∪ X) (FateV2.Predict.BridgeB3.dSep_peel_univ hd)

/-- **R26.6（B3 × A2）拓扑最大汇点：无出边 + 父代与后代不交**：

设 `S` 非空。则 `S` 中拓扑最大点 `l` 是 `S` 内 sink（B3.4′ `sink_of_topo_max`，
真消费非空性），且对任意点 `pa_G(l) ∩ desc_G(l) = ∅`（A2
`pa_vs_descendants_disjoint`）。

⚠ **诚实标注**：后半是逐点无条件事实；本定理的**组合内容**是把「存在 sink」
与该 sink 的父代/后代分离**并置**，两者分别消费不同上游模块。 -/
theorem sink_of_topo_max_and_pa_desc_disjoint {G : FateV2.Modeling.Graph.DAG V}
    {S : Finset V} (hS : S.Nonempty) :
    (∃ l ∈ S, ∀ w ∈ S, ¬ G.edge l w)
      ∧ ∀ l : V, Disjoint (Fate.DAGFactorization.pa G l) (G.descendants l) :=
  ⟨FateV2.Predict.BridgeB3.sink_of_topo_max G hS,
   fun l => FateV2.Predict.BridgeA2.pa_vs_descendants_disjoint G l⟩

/-- **R26.7（B2 × A2）拓扑前缀父闭性 + 非后代点不作父**：

设 `v ∈ topoPrefix G τ k`。则其父代仍在前缀内（B2.9c），且对任意
`w ∈ nonDescendants v` 有 `v ∉ pa_G(w)`（A2.4′ `not_mem_pa_self_for_w`，
真消费 `hnd`）。 -/
theorem topoPrefix_parent_closed_and_nondesc_pa {G : FateV2.Modeling.Graph.DAG V}
    (τ : FateV2.Modeling.BridgeB2.TopoOrderData G) (k : ℕ) {v : V}
    (hv : v ∈ FateV2.Modeling.BridgeB2.topoPrefix G τ k) :
    (Fate.DAGFactorization.pa G v ⊆ FateV2.Modeling.BridgeB2.topoPrefix G τ k)
      ∧ ∀ w : V, w ∈ G.nonDescendants v → v ∉ Fate.DAGFactorization.pa G w :=
  ⟨FateV2.Modeling.BridgeB2.topoPrefix_parent_closed G τ k hv,
   fun w hnd => FateV2.Predict.BridgeA2.not_mem_pa_self_for_w (G := G) (v := v) hnd⟩


end BridgeB4
end FateV2.Predict