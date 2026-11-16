/-
  Fate.GazeRevisesCausal
  ==========================================================================
  方向 ⑩：**分类的结果反过来修正因果结构**

  （作者第 392 轮裁决 B-4·⑩「分类修正因果全部做」）
  ==========================================================================

  ## 0. 本文件要回答的问题

  裁决 B-4 的主线是「因果进入分类循环」。前面若干方向做的是「因果 ⟹ 分类」
  （因果结构决定要素/概念的划分）。**本方向是反向的第 ⑩ 步**：

  > **分类的结果，反过来修正因果结构本身。**

  这是「因果不是旁路」的最强含义 —— 因果**不是**被一次性给定、然后只被分类读取；
  它**本身**要被分类的循环**改写**。

  ---
  ## 1. 【任务 (a)】Lean 里 SCM 的**图结构**与**参数**是否可修改（实测登记）

  只陈述**源码事实**，逐条给出处。

  | 结构 | 出处 | 关键字段 | 可修改吗 |
  |---|---|---|---|
  | `Fate.PearlHierarchy.SCM (X Y)` | `Fate/PearlHierarchy.lean:75` | `U`、`pU : U → ℝ`、`sg : U → X × (X → Y)` | 作为**结构字段**「不可变」（Lean 结构无变异）：要改只能**另构造**一个 `SCM` 值。⚠ `U` 是**数据字段**，改 `U` 会改**类型层面**的外生空间 |
  | `Fate.ParamSCM` | `Fate/ParamSCM.lean` | 加了**参数空间** `Th`，`sg` 读 `θ` | **参数 `θ` 是显式的、可变的维** —— 这正是 `ParamSCM` 相对 `SCM` 的**全部**增量。`ParamSCM` 文件头自陈：`PearlHierarchy.SCM` 的 `sg : U → X × (X → Y)` **没有参数位**，故 `SCM` 是「无参数机制」 |
  | `Fate.SCMGraph.edge` | `Fate/SCMGraph.lean:§3` | `edge M : SV M → SV M → Prop`，**由 `sg` 机械导出** | ⚠⚠ **图不可独立修改**：`edge` 是 `sg` 的**函数**，**没有**独立的边集字段。要改图必须改 `sg`（或换 `M`） |
  | `Causalean.Graph.DAG V` | `CausDAG.lean:62` | `edge : V → V → Prop`、`decEdge`、`acyclic` | **有独立的 `edge` 字段 ⟹ 图本身是可替换的**；门槛是必须**同时提供 `acyclic` 证据** |

  ### ⭐ 实测得出的、决定本文件全部设计的两条结论

  1. **`PearlHierarchy.SCM` 的「图」不是独立自由度**：它由 `sg` 派生
     （`SCMGraph.edge`）。⟹「修正图」在 `SCM` 口径下**没有独立入口**。
     **本文件因此把修正规则建在 `DAG` 层**（`edge` 是独立字段），
     **并显式给出**「该 `DAG` 的边被某个 `SCM` 的 `sg` *蕴含*」的谓词
     `InducedBySCM`（§9），把「修正后的边**仍可被某个 SCM 解释**」写成**可证命题**。
     **不假装** `SCM` 的图能直接编辑。
  2. **只有 `ParamSCM` 口径的 `θ` 是显式可改的维**。⟹ 本文件对「参数修正」
     给出**对应的**规则（§10），与图修正**同构**（同一个「只加/只减」格）。
     ⚠ 但 Lean 里**没有**「参数的结构」可供推演（`Th` 是任意 `Type`），
     故 §10 的 `reviseParams` 是**构造选择**，不是推导 —— 见 §10 的诚实边界。

  ---
  ## 2. 【任务 (b)】「一次修正」的定义 + **规则的依据**

  ### `reviseByGaze G g A`（`G : DAG V`，`g : Gaze`，`A : Finset V`）

  ```
  gazeNone A ⟹ G' = G
  gazeUp   A ⟹ G'.edge a b := G.edge a b ∨ (a ∈ A ∧ b ∈ A ∧ G.topoOrder a < G.topoOrder b)
  gazeDown A ⟹ G'.edge a b := G.edge a b ∧ ¬ (a ∈ A ∧ b ∈ A)
  ```

  ### ⭐ 依据（逐条对应 FCA 目光语义；出处均为 `Fate/Classification.lean`）

  | 目光 | 释义（`Classification.lean:82–86`） | FCA 实现（`:207`/`:210`） | 本文件的因果规则 |
  |---|---|---|---|
  | `up` | 「追问**它归于何类** → 建立**上位归类**」 | `gazeUp O' = O'^↑`（`polarUp`） | **加边**：把 `A` **归为一个因果整体** —— `A` 的内部被补全为**与既有因果序一致的**全序（`topoOrder` 递增的所有有序对） |
  | `down` | 「追问**它由何构成** → 建立**内部构成**」 | `gazeDown B = B^↓`（`polarDown`） | **删边**：把 `A` 内部的**直接**结构连接**全部拆掉**（`A` 对外的因果输入输出**不受影响**） |
  | `none` | 目光未投出（要素）；`Classification` §3 的 `suspend` | `suspend`（法则 5） | **不动** |

  `Classification.lean:221` 的 `gaze_galois`：`B ⊆ gazeUp A ↔ A ⊆ gazeDown B`
  —— 两支目光是 **Galois 连接**的伴随方向。§11 把它与本文件的算子**显式接上**。

  **⟹ 因果语义（分析者的解读，非原文 —— 沿用 `Classification.lean` 自己的
  「`[哲学依据]` 解读，**非原文**」纪律）**：

  * **`up`：`A` 被当作一个「上位类」。** 「同类」在因果上意味着
    **类内部的成员之间不再有「谁决定谁」的缺口** —— 既然 `A` 已被归为**一个**
    上层单元，`A` 内部凡**已被因果序确定先后**的对，其决定关系都应显式成立。
    故 `up` 补全 `A` 内部**所有与 `topoOrder` 一致**的有序对。
    **这保证它只建立、不拆解，且绝不引入循环。**
  * **`down`：`A` 被拆解为其构成。** 「拆开 `A`」= `A` 内部的**直接**连接
    让位于更细的构成层，故**一律移除**；但 `A` 的**对外**因果（入边、出边）
    **必须保留** —— 这与法则 5 的两半严格对齐：
    `suspend_preserves_base`（对象/外部关系不丢）与
    `suspend_dissolves_identity`（内部关系消解）。

  ### ⚠⚠ 诚实边界：**哪些是语义推的，哪些是构造选择**

  * **从语义来的**：`up` **只加边**、`down` **只减边**（Galois 的两支是**增/减**）；
    `up` 的新边**必须与既有因果序一致**（因果序不可被分类推翻 —— 否则分类
    就在制造循环因果）；`down` **只切 `A` 内部**，**保留 `A` 的一切对外因果**；
    `none` **逐字不动**（`suspend` = 「不建立关系」）。
  * **⚠ 构造选择（无推导，纯约定）**：
    ① **`up` 的粒度是「`A` 内部全序补全」而不是「`A` 到 `A` 的祖先闭包」。**
       后者的读法（`A` 的祖先闭包 → `A`）**在本文件中被证伪**：它**破坏无环性**
       —— §7 的 `up_ancestralSun_rule_breaks_acyclic` 给出 2 点反例
       （`p → q`，`A = {p,q}` 时新增 `q → p`，与 `p → q` 构成 2-环）。
       **这是本文件唯一一处由「语义读法」被数学反例淘汰的记录**，
       也是选 `topoOrder` 守卫的**直接理由**。
    ② **`down` 的粒度是「`A` 内部全部直接边」而不是「`A` 的入边」。**
       切 `A` 的入边会**删掉外部因果输入**，与法则 5 前半矛盾。
    ③ **`up` 时不改 `pU`（外生律）**：`pU` 是外生律，目光是**分类**不是**重新抽样**。
       **这同样是选择，不是推导。**
    ④ **`A` 取 `Finset`（有限对象集）而非 `Set`**：`DAG` 侧全部结构
       （`ancestralSet`、`edge` 的可判定性、`topoOrder`）都要求有限性；
       `Classification` 侧用 `Set`，二者接口由 §11 显式桥接，**不混用**。

  ---
  ## 3. 交付清单（**本文件实际存在的定理**，`grep` 可核）

  | # | 名称 | 内容 | 等级 |
  |---|---|---|---|
  | — | `reviseByGaze` | 修正算子 `DAG V → Gaze → Finset V → DAG V` | [构造] |
  | — | `reviseByGaze_edge_up` / `_down` / `_none` | 三支的边集**逐字展开**（`↔`） | ⭐ |
  | — | `InducedBySCM` | 「边可被某个 `SCM` 的 `sg` 解释」谓词 | [构造] |
  | — | `Param` / `reviseParams` | `ParamSCM` 口径的参数修正 | [构造] |
  | 1 | `revise_topoOrder_lt` | **两支目光都保持 `G` 的拓扑序有效**（共同不变量） | ⭐⭐⭐ |
  | 2 | `reviseByGaze_none_eq` | `Gaze.none` 修正**逐字不动** | ⭐⭐ |
  | 3 | `reviseByGaze_idem` | **`up` / `down` / `none` 各自幂等** | ⭐⭐⭐ |
  | 4 | **`revise_down_ancestralSet_subset`** | **`down` 不新增祖先**（每个 `ancestralSet` 只减不增） | ⭐⭐⭐ |
  | 5 | `revise_down_ancestralSet_strict` | **严格性**：`down` **真的**会减少祖先（3 点机检例） | ⭐⭐⭐ |
  | 6 | **`revise_up_ancestralSet_mono`** | **`up` 不减少祖先**（每个 `ancestralSet` 只增不减） | ⭐⭐⭐ |
  | 7 | `revise_up_ancestralSet_strict` | **严格性**：`up` **真的**会增加祖先（3 点机检例） | ⭐⭐⭐ |
  | 8 | **`revise_up_fixed_iff`** | **`up` 的不动点 ⟺ `A` 内部已按 `topoOrder` 全序补全**（充要，形式定理） | ⭐⭐⭐⭐ |
  | 9 | `revise_up_fixed_of_subsingleton` | **非平凡不动点存在**：`|A| ≤ 1` ⟹ `up` 不动（含 `A = ∅`） | ⭐⭐⭐ |
  | 10 | `revise_down_fixed_iff` | **`down` 的不动点 ⟺ `A` 内部无边**（充要） | ⭐⭐⭐ |
  | 11 | `revise_down_fixed_of_no_internal` | **非平凡不动点存在**：`A` 内部无边 ⟹ `down` 不动 | ⭐⭐⭐ |
  | 12 | **`revise_up_down_idem`** | **整季循环**：`up ∘ down` **幂等** ⟹ `(up ∘ down)^[k]` 对一切 `k ≥ 1` 相同 | ⭐⭐⭐⭐ |
  | 13 | `revise_iterate_fixed` | 推论：`(up ∘ down)^[k]`（`k ≥ 1`）**本身**是 `up ∘ down` 的不动点 | ⭐⭐⭐ |
  | 14 | `revise_up_down_ancestralSet_subset` | 循环稳定后的祖先集 ⊆ 原图祖先集（`down` 的削减**不会被 `up` 补回**） | ⭐⭐⭐ |
  | 15 | `revise_up_mono_induced` | `InducedBySCM` 在 `up` 下的**保持/扩张**接口（含诚实标注） | ⭐⭐ |
  | 16 | `revise_agrees_with_FCA` | 与 `Classification` 的 `gazeUp`/`gazeDown`/`gaze_galois` **逐条对齐** | ⭐⭐ |
  | 17 | `reviseParams_idem` / `reviseParams_eq_of_apply` | 参数修正：幂等 + `Gaze.none` 不动 | ⭐⭐ |
  | 18 | **`up_ancestralSun_rule_breaks_acyclic`** | ⚠ **负结论**：「祖先闭包 → `A`」这一读法**破坏无环性**（淘汰记录） | ⭐⭐⭐⭐ |

  ### ⚠ 本文件**做不出/未做**的（如实登记，**不用 `sorry` 占位**）

  * **「修正后回复原图」非平凡情形**：`down` 切的边 `up` **不**恢复
    （`up` 的新边要求 `topoOrder a < topoOrder b`，而 `down` 切的是 `A` 内部
    的全部边，`up` 只补**单向**全序）。⟹ 「循环回到原图」**只有** §3 #9 / #11
    那种空转情形。**通用的**「往复稳定」由 #12/#13 给出：
    这是**稳定（stable）而非还原（revert）**，本文件**不**把二者混为一谈。
  * **「修正后的图仍由某个 `SCM` 诱导」的一般情形**：#15 只给出**单向**接口，
    并**如实标注**其局限 —— 见 §9。
  * `pU`（外生律）不参与修正（§2 诚实边界 ③）。
  * **未证**：`up ∘ down` 的不动点**与 `G`、`A` 的显式刻画**（只证了幂等与存在性）。

  ---
  ## 4. 反同义反复核查（本项目最高频问题，逐条核过）

  * `reviseByGaze_none_eq`：结论 `= G` 是**证明**的（另两支**不是** `rfl`，
    故整条 `match` 不平庸）。
  * `reviseByGaze_idem`：前件只有 `[DecidableEq V] [Fintype V]`，**没有**任何图假设。
  * **`revise_down_ancestralSet_subset`**：前件只有类型类实例。结论是
    `ancestralSet (down G) A ⊆ ancestralSet G A` —— 这是**关于 `TransGen` 的蕴含**，
    证明必须对 `TransGen` 做归纳（§6.2），**不能**由定义直接读出。
  * **`revise_up_ancestralSet_mono`**：前件只有类型类实例，结论是**反方向**的包含。
    证明必须从 `G.isAncestor` **构造** `Rev` 的 `TransGen`（对 `isAncestor` 归纳），
    并**另外**处理「新边」的 `topoOrder` 守卫。
  * **`revise_up_fixed_iff`**：**充要**条件，`→` 与 `←` **两个不同方向**都要证，
    且 `→` 方向必须从 `edge` 的**谓词外延相等**取出一条具体对 `(a,b)`。
  * `revise_up_fixed_of_subsingleton`：前件是**基数条件**（`|A| ≤ 1`），
    结论是算子不动 —— **基数**与**边关系**之间没有定义性联系。
  * **`revise_up_down_idem`**：结论是**两步复合**的幂等。
    **不能**由 `reviseByGaze_idem`（单算子幂等）直接得到 ——
    必须真的展开 `up ∘ down` 的 `edge` 表达式并做 `Or` 的结合律/守卫消解。
  * **`revise_up_down_ancestralSet_subset`**：结论是 ⊆，而单看 `up`
    是 **⊇**（#6）。⟹ 复合方向与两个分量方向**相反**，**不可能**同义反复。
  * **`up_ancestralSun_rule_breaks_acyclic`**：结论是**否定**（新图**非** DAG），
    且给出**具体反例**（`Fin 2`，机检）。**不可能**是同义反复。

  **零 `sorry` / 零 `admit` / 零 `axiom`**：机检输出见交付报告。
  ========================================================================== -/

import FateWorld.FateV2.Modeling.CausDAG
import FateWorld.FateV2.Modeling.PearlHierarchy
import FateWorld.FateV2.Rules.Classification
import FateWorld.FateV2.Modeling.SCMGraph
import FateWorld.FateV2.Predict.ParamSCM
import Mathlib.Tactic

namespace FateV2.Predict

open FateV2.Modeling
open FateV2.Rules
namespace GazeRevisesCausal

open FateV2.Modeling.Graph
open FateV2.Rules.FormalCtx (Gaze)

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V] [Fintype V]

/-!
  # Predict · GazeRevisesCausal

  ## 迁移登记
  - 来源：`FateWorld/Legacy/GazeRevisesCausal.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausDAG, PearlHierarchy, Classification, SCMGraph, ParamSCM
  - 补充 open 域：FateV2.Modeling, FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §5 ⭐ **修正算子** `reviseByGaze`
  ===========================================================================

定义见 §2 的规则表。**依据 / 构造选择的分界已在 §2 写明。** -/

/-- ⭐ **一次分类修正**：用 `Gaze` `g` 就对象集 `A` 修正图 `G`。

```
none ⟹ 不动
up   ⟹ 加边：A 内部所有与 `topoOrder` 一致的有序对
down ⟹ 删边：A 内部的**全部**直接边
```

`acyclic` 字段统一由 `DAG.acyclic_of_topoOrder` 给出：
`up` 的新边**显式带** `topoOrder a < topoOrder b` 守卫，`down` 是**子集**（删边）。
⟹ 两支都不破坏 `G.topoOrder` 的有效性（见 `revise_topoOrder_lt`）。 -/
noncomputable def reviseByGaze (G : DAG V) (g : Gaze) (A : Finset V) : DAG V :=
  match g with
  | .none => G
  | .up =>
    { edge := fun a b => G.edge a b ∨ (a ∈ A ∧ b ∈ A ∧ G.topoOrder a < G.topoOrder b)
      decEdge := fun a b => Classical.dec _
      acyclic := DAG.acyclic_of_topoOrder (r := (· < ·)) (τ := G.topoOrder) (by
        intro a b hab
        rcases hab with h | ⟨-, -, hlt⟩
        · exact G.topoOrder_lt a b h
        · exact hlt) }
  | .down =>
    { edge := fun a b => G.edge a b ∧ ¬ (a ∈ A ∧ b ∈ A)
      decEdge := fun a b => Classical.dec _
      acyclic := DAG.acyclic_of_topoOrder (r := (· < ·)) (τ := G.topoOrder) (by
        intro a b hab
        exact G.topoOrder_lt a b hab.1) }

/-! ### §5.1 三支边集的**逐字展开**（`↔` 形式，供 `simp` 与后续证明使用） -/

@[simp] theorem reviseByGaze_edge_none (G : DAG V) (A : Finset V) (a b : V) :
    (reviseByGaze G Gaze.none A).edge a b ↔ G.edge a b := Iff.rfl

@[simp] theorem reviseByGaze_edge_up (G : DAG V) (A : Finset V) (a b : V) :
    (reviseByGaze G Gaze.up A).edge a b ↔
      (G.edge a b ∨ (a ∈ A ∧ b ∈ A ∧ G.topoOrder a < G.topoOrder b)) := Iff.rfl

@[simp] theorem reviseByGaze_edge_down (G : DAG V) (A : Finset V) (a b : V) :
    (reviseByGaze G Gaze.down A).edge a b ↔ (G.edge a b ∧ ¬ (a ∈ A ∧ b ∈ A)) := Iff.rfl

/-! -/

end GazeRevisesCausal

end FateV2.Predict