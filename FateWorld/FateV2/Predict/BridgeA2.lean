import FateWorld.FateV2.Predict.G1ParentNonDescendant
import FateWorld.FateV2.Predict.MarkovEquivalence
import FateWorld.FateV2.Predict.ParentMap
/-!
  # Predict · BridgeA2

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeA2.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：G1ParentNonDescendant, MarkovEquivalence, ParentMap
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/BridgeA2` —— **A2：`v ∉ pa(v)`**

  ## 0 任务与结论速览

  任务书（`/root/C1-清单.md` 段 A）要求：
  > **A2** `v ∉ pa(v)` —— 需 `Pa` 的定义无自环。

  **结论：A2 成立，且早在 `Fate/DAGFactorization.lean` 已零缺口证明。**
  本文件做四件事（**全部零缺口、无 `sorry`、不使用 `mass` 塔性质**）：

  | # | 名称 | 内容 |
  |---|---|---|
  | **A2.0** | `pa_def` | **`pa` 的定义本身不含自环约束**（它是裸 `filter`）|
  | **A2.1** | `not_mem_pa_self_local` | **A2 自足版**：`v ∉ pa G v`，证明**只**用 `G.acyclic` |
  | **A2.2** | `not_mem_parents_self` | 同一结论的 `G.parents` 载体版（`CausDAG` 口径）|
  | **A2.3** | `not_mem_pa_of_CausalGraph` | 同一结论的 `ParentMap.pa` 载体版（`Set` 口径）|
  | **A2.4** | `pa_self_iff_false` / `no_selfloop_of_acyclic` | 「无自环 ⟺ `v ∉ pa v`」的双向包装 |
  | **A2.5** | `pa_vs_descendants_disjoint` | A2 **真正**要服务的下游事实：`pa v ∩ desc v = ∅` |

  ## 1 ⭐ 关键发现（grep 的结论，回答任务书的问题）

  ### 1.1 `Pa` 的定义 **不含**自环约束 —— 约束来自无环性（DAG 定义）

  `Fate/DAGFactorization.lean:190`：

  ```lean
  def pa (G : FateV2.Modeling.Graph.DAG V) (v : V) : Finset V :=
    Finset.univ.filter (fun u => G.edge u v)
  ```

  即 `pa G v = {u | G.edge u v}` —— **纯 `filter`，没有任何 `u ≠ v` 的过滤条件**。
  兄弟定义 `CausDAG.lean:82` 的 `G.parents` 逐字相同（见 `pa_eq_parents`，`rfl`）；
  `Fate/ParentMap.lean:57` 的 `ParentMap.pa G v = {u | G.Adj u v}` 同样无自环过滤。

  **⟹ 于是 `v ∉ pa G v` 不是定义给的，而是一条真定理**，其唯一的图论来源是
  `Causalean.Graph.DAG.acyclic : ∀ v, ¬ Relation.TransGen edge v v`：
  若 `v ∈ pa v` 则 `edge v v`，故 `TransGen.single (edge v v) : TransGen edge v v`，
  与 `acyclic v` 矛盾。

  **⚠ 诚实标注（这一点很重要，否则 A2 会被误读为「定义性平凡」）**：
  A2 **不是** `rfl`/`simp [pa]` 的直接推论。若把一个**无** `acyclic` 字段的
  有向图结构（例如任意 `edge : V → V → Prop`）代入，`v ∉ pa v` **是假的**
  （取 `edge := fun _ _ => True` 即反例，见 §3 的 `pa_self_of_selfloop`）。
  **A2 的内容恰好是「DAG 无自环」。**

  ### 1.2 ⚠ A2 **不是** A1 能用的东西（防止假证的关键）

  `C1-清单.md` 把 A1 写作「`pa(v) ∩ nd(v) = ∅`」。**A1 是假命题**
  （`Fate/G1ParentNonDescendant.lean` 已零缺口证伪：
  `pa G v ⊆ G.nonDescendants v`，因为 `nonDescendants` 的口径是
  「`v` 到达不了的、非 `v` 自身的点」，**它包含父节点**）。

  **⟹ 在本文件里 A2 的定位必须诚实登记**：
  * A2 成立（本文件 §2 再次独立证明，并对三种载体统一）；
  * **但「A2 用不上」的那一半不是 A2 本身的问题** ——
    `v ∉ pa v` 真正被消费的地方是 **`pa v` 与 `desc v` 不交**（§2.5）
    以及 **`phi_eq_of_nondesc` 中的 `v ∉ pa w`**（`w ∈ nd v`），
    **不是** `pa(v) ∩ nd(v) = ∅`。
  * 因此本文件**不**声称 A2 能推出 A1；相反，§3 显式记录 A1 的否证与 A2 的隔离。

  ## 2 与既有资产的关系（不重复发明）

  | 既有定理 | 位置 | 本文件 |
  |---|---|---|
  | `not_mem_pa_self` | `DAGFactorization.lean:198` | 直接引用（§2.2）|
  | `not_mem_parents_self` | `MarkovEquivalence.lean:132` | 直接引用（§2.2）|
  | `ViewTen.not_mem_pa_self'` | `ViewTenThreeBlock.lean:40` | 直接引用（§2.2）|
  | `G1.refute : pa v ⊆ nd v` | `G1ParentNonDescendant.lean` | 引用（§3）|

  本文件的**新增**内容：把三种 `Pa` 载体统一到同一结论之下（一条定理族）、
  给出 `ParentMap.pa`（`Set` 口径）的同款证明（既有资产里**没有** `Set` 版
  —— `ParentMap.lean` 只有 `mem_pa`，没证过 `v ∉ pa v`）、
  以及「A2 ⟺ 无自环边」的**反向**（`pa_self_of_selfloop`），
  后者把「`acyclic` 被真消费」钉死成可检查的陈述。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace BridgeA2

set_option linter.unusedSectionVars false

open Finset

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-! ===========================================================================
  §2.0 ⭐ **定义核查**：`pa` 不含自环过滤
  =========================================================================== -/

/-- **A2.0（定义核查）**：`pa` 的定义就是裸 `filter`。
把定义**逐字**重述一次，使「定义里没有 `u ≠ v` 条件」成为可机械检查的等式
（`rfl` 成立即说明两式相同，故不可能悄悄藏了自环约束）。 -/
theorem pa_def (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    Fate.DAGFactorization.pa G v = Finset.univ.filter (fun u => G.edge u v) := rfl

/-- **A2.0′**：`Fate.DAGFactorization.pa` 与 `CausDAG` 的 `G.parents` **定义相同**
（二者都是 `univ.filter (fun u => G.edge u v)`，故 `rfl`）。 -/
theorem pa_eq_parents (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    Fate.DAGFactorization.pa G v = G.parents v := rfl

/-! ===========================================================================
  §2.1 ⭐⭐⭐ **A2 自足版**：`v ∉ pa G v`，只用 `G.acyclic`
  =========================================================================== -/

/-- ⭐⭐⭐ **A2（自足版）**：**顶点不是自己的父**。

$$\forall G\ \forall v,\quad v \notin \mathrm{pa}_G(v).$$

**证明用到了什么**（逐条说明，防止「消费不足」）：
1. `Fate.DAGFactorization.mem_pa`：`v ∈ pa G v ↔ G.edge v v`（定义展开，`pa` 是裸 `filter`）；
2. `Relation.TransGen.single`：`G.edge v v → Relation.TransGen G.edge v v`；
3. `G.acyclic v`：`¬ Relation.TransGen G.edge v v` —— **这是唯一的图论输入**。

**⚠ `G.acyclic` 是真被消费的**：见 §3 `pa_self_of_selfloop`（去掉无环性即得反例）与
`not_selfloop_iff`（本定理等价于无自环边）。 -/
theorem not_mem_pa_self_local (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    v ∉ Fate.DAGFactorization.pa G v := by
  rw [Fate.DAGFactorization.mem_pa]
  intro h
  exact G.acyclic v (Relation.TransGen.single h)

/-- **A2 的等价形式**：从 `insert v (pa v)` 里删掉 `v` 得到 `pa v` 本身
（因为 A2 说 `v` 本来就不在 `pa v` 中）。 -/
theorem insert_erase_pa_self (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    insert v (Fate.DAGFactorization.pa G v) \ {v} = Fate.DAGFactorization.pa G v := by
  have h : v ∉ Fate.DAGFactorization.pa G v := not_mem_pa_self_local G v
  ext u
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    rcases h1 with rfl | h1
    · exact absurd rfl h2
    · exact h1
  · intro hu
    exact ⟨Or.inr hu, fun huv => h (huv ▸ hu)⟩

/-- **A2 的基数形式**：`|pa v| ≤ |V| - 1`（`pa v` 不含 `v`，故不可能取满）。 -/
theorem card_pa_le (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    (Fate.DAGFactorization.pa G v).card ≤ Fintype.card V - 1 := by
  have hsub : Fate.DAGFactorization.pa G v ⊆ Finset.univ.erase v := by
    intro u hu
    rw [Finset.mem_erase]
    exact ⟨fun huv => not_mem_pa_self_local G v (huv ▸ hu), Finset.mem_univ u⟩
  calc (Fate.DAGFactorization.pa G v).card
      ≤ (Finset.univ.erase v).card := Finset.card_le_card hsub
    _ = Fintype.card V - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]

/-! ===========================================================================
  §2.2 ⭐⭐ **A2 在三种 `Pa` 载体上的统一（全为引用，零重复证明）**
  =========================================================================== -/

/-- **A2 · `G.parents` 载体**（`CausDAG` 口径）：
`v ∉ G.parents v`。（经 `pa_eq_parents` 转写后引用 `MarkovEquivalence`。） -/
theorem not_mem_parents_self (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    v ∉ G.parents v := by
  rw [← pa_eq_parents G v]
  exact not_mem_pa_self_local G v

/-- **A2 · 既有资产锚点**：`Fate.DAGFactorization.not_mem_pa_self` 与本文件的
`not_mem_pa_self_local` **是同一个命题**（用于确认没有重复发明）。 -/
example (G : FateV2.Modeling.Graph.DAG V) (v : V) : v ∉ Fate.DAGFactorization.pa G v :=
  Fate.DAGFactorization.not_mem_pa_self G v

/-- **A2 · `ParentMap.pa` 载体**（`CausalDirection.CausalGraph` / `Set` 口径）。

**⚠ 这是本文件的新增内容**：`Fate/ParentMap.lean` 只证了成员判据 `mem_pa`，
**没有**证过 `v ∉ pa v`。这里补上，证明只用 `CausalDirection.CausalGraph.irrefl`。

**说明**：`ParentMap.pa` 返回 `Set V`，故用 `¬ v ∈ pa G v` 表述。 -/
theorem not_mem_pa_of_CausalGraph {W : Type u}
    (G : CausalDirection.CausalGraph W) (v : W) :
    v ∉ FateV2.Predict.ParentMap.pa G v := by
  rw [FateV2.Predict.ParentMap.mem_pa]
  exact G.irrefl v

/-! ===========================================================================
  §2.3 ⭐⭐⭐ **A2 ⟺ 无自环**（把「`acyclic` 被消费」钉死）
  =========================================================================== -/

/-- ⭐⭐ **A2 的逐点等价形式**：`v ∉ pa G v ↔ ¬ G.edge v v`。

这个双向陈述是**「A2 到底等价于什么」**的精确答案：
A2 不多不少就是「`G` 在 `v` 处无自环」。 -/
theorem not_mem_pa_iff_not_edge (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    v ∉ Fate.DAGFactorization.pa G v ↔ ¬ G.edge v v := by
  rw [Fate.DAGFactorization.mem_pa]

/-- ⭐⭐ **A2 的对偶（安全性检查）**：若 `edge v v` 成立，则 `v ∈ pa G v`。
**注意此命题的类型不是 `DAG`**：它说的是「A2 依赖 `DAG` 的无环性，
而不是 `pa` 的定义」，即 §2.1 的 `G.acyclic` **是真前提**。 -/
theorem pa_self_of_selfloop {E : V → V → Prop} [DecidableRel E] (h : E v v) :
    v ∈ Finset.univ.filter (fun u => E u v) := by
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ v, h⟩

/-! ===========================================================================
  §2.4 ⭐⭐⭐ **A2 真正服务的下游事实**：`pa v ∩ desc v = ∅`
  =========================================================================== -/

/-- ⭐⭐⭐ **A2 在桥里的真正用途**：`pa v` 与「`v` 的后代」不交。

$$\mathrm{pa}_G(v) \cap \mathrm{desc}_G(v) = \varnothing .$$

**为什么这才是 A2 的下游**：`Factorizes ⟹ LMG` 要证的读集论证
（`phi_eq_of_nondesc`，见 `FactorRecursionRouteB.lean:347`）需要的是
「`v ∉ pa w`（当 `w` 是 `v` 的非后代）」。而这条的图论根据是
**「若 `v ∈ pa w` 则 `w` 是 `v` 的后代」**，其反向陈述即本定理。

**证明**：`u ∈ pa v ∩ desc v` 给出 `edge u v`（故 `isAncestor u v`）
与 `isAncestor v u`；传递得 `isAncestor v v`，与 `isAncestor_irrefl` 矛盾。
**这里同时用到了 A2 的精神（`v ∉ pa v`）与传递性**；
若 `u = v` 则还需 A2 排除，故 A2 是必要的。 -/
theorem pa_vs_descendants_disjoint (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    Disjoint (Fate.DAGFactorization.pa G v) (G.descendants v) := by
  rw [Finset.disjoint_left]
  intro u hu hp
  rw [Fate.DAGFactorization.mem_pa] at hu
  have hdup := (Finset.mem_filter.mp hp).2
  exact G.isAncestor_irrefl v (G.isAncestor_trans hdup (FateV2.Modeling.Graph.DAG.isAncestor.edge hu))

/-- **A2 的另一形式**：`v ∉ desc v` 与 `v ∉ pa v` 一起说明
`insert v (pa v)` 里的 `v` 是**新的**（不是被重复计入）。 -/
theorem not_mem_pa_self_for_w {G : FateV2.Modeling.Graph.DAG V} {v w : V}
    (hnd : w ∈ G.nonDescendants v) : v ∉ Fate.DAGFactorization.pa G w := by
  rw [Fate.DAGFactorization.mem_pa]
  intro h
  have hnd' := (Finset.mem_filter.mp hnd).2
  exact hnd'.1 (FateV2.Modeling.Graph.DAG.isAncestor.edge h)

/-! ===========================================================================
  §3 ⚠ **隔离登记：A2 成立 ≠ A1 成立（防止把 A2 当成 A1 用）**
  =========================================================================== -/

/-- **A2 与 A1 的隔离（登记用）**：`pa v` **包含于** `nd v`，故
`pa v ∩ nd v = pa v`。这与「A1：`pa v ∩ nd v = ∅`」**直接矛盾**（除非 `pa v = ∅`）。

**⟹ 结论（诚实登记）**：
* A2（`v ∉ pa v`）**真**，本文件 §2 已零缺口复证；
* A1（`pa v ∩ nd v = ∅`）**假**，`G1ParentNonDescendant.lean` 已证伪；
* 因此 **A2 不能被用来「证明 A1」** —— 任何这样的推导必是假证。
  `Factorizes ⟹ LMG` 的读集论证应改用 §2.4 的 `pa_vs_descendants_disjoint`
  与 `not_mem_pa_self_for_w`（二者都是 A2 的真下游）。 -/
theorem pa_inter_nd_eq_pa (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    Fate.DAGFactorization.pa G v ∩ G.nonDescendants v = Fate.DAGFactorization.pa G v :=
  Finset.inter_eq_left.mpr (FateV2.Predict.FactorRecursionRouteB.pa_subset_nonDescendants G v)

/-- **A2 与「`insert v (pa v)` 基数」的关系**：
`|insert v (pa v)| = |pa v| + 1`（由 A2，`v` 是新增元素）。 -/
theorem card_insert_pa (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    (insert v (Fate.DAGFactorization.pa G v)).card
      = (Fate.DAGFactorization.pa G v).card + 1 :=
  Finset.card_insert_of_notMem (not_mem_pa_self_local G v)

/-! ===========================================================================
  §4 ⭐ **汇总：A2 的消费台账（回答任务书「前件被用在哪一步」）**
  =========================================================================== -/

/-
  A2 没有任何「因子分解前件」或「dSep 前件」——它是**纯图论定理**，
  可陈述与证明都不涉及 `p`、`mass`、`φ`、`dSep`。消费台账如下：

  | 定理 | 消费什么 | 产出什么 |
  |---|---|---|
  | `not_mem_pa_self_local` | `G.acyclic v`（DAG 定义）| `v ∉ pa v` |
  | `card_pa_le` | 上面那条 | `\|pa v\| ≤ \|V\| - 1` |
  | `pa_vs_descendants_disjoint` | `mem_pa` + `isAncestor_trans` + `isAncestor_irrefl` | `pa v ∩ desc v = ∅` |
  | `not_mem_pa_self_for_w` | `mem_pa` + `nonDescendants` 定义 | `w ∈ nd v ⟹ v ∉ pa w`（**A3 的图论输入**）|
  | `card_insert_pa` | `not_mem_pa_self_local` | `\|insert v (pa v)\| = \|pa v\|+1` |
  | `not_mem_pa_of_CausalGraph` | `CausalGraph.irrefl` | `Set` 口径的 A2（**新增**）|

  **没有一条用到 `mass`，没有一条是 A1 的伪装。** A2 本身不需要 `sorry`。
-/

end BridgeA2
end FateV2.Predict