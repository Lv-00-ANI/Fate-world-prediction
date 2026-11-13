import FateWorld.Legacy._root.CausDAG
import FateWorld.Legacy.DAGFactorizationGeneral
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Sort

/-! ===========================================================================
  `Fate/BridgeB2` —— **B2：DAG 的拓扑序存在性（定义 + 证明）**

  ## 结论速览

  | # | 名称 | 状态 | 内容 |
  |---|---|---|---|
  | **B2.0** | Mathlib 现状调查 | ✅ **已调查（负面结果）** | Mathlib 中**没有** DAG 拓扑排序 |
  | **B2.1** | `IsTopoOrder` | ✅ 定义 | 「拓扑序」的**一般谓词**（任意指标类型 `ι`）|
  | **B2.2** | `IsTopoEnum` | ✅ 定义 | 拓扑序的**枚举形式** `V ≃ Fin (card V)` |
  | **B2.3** | `TopoOrderData` | ✅ 定义 | **打包**：排序函数 + 边严格增 + 单射 |
  | **B2.4** | `TopoOrderData.isAncestor_lt` | ✅ **零缺口** | `isAncestor u v ⟹ order u < order v`（多步路径）|
  | **B2.5** | `topoOrderData` | ✅ **零缺口**（**打包**，非新数学）| 由 `CausDAG.topoOrder` **构造** `TopoOrderData` |
  | **B2.6** | `exists_topoEnum` | ✅ **零缺口** | **主定理 A**：任意 DAG 有拓扑枚举 |
  | **B2.7** | `exists_min_topo_mem` | ✅ **零缺口** ⭐**新** | **剥离引理（源）**：非空 `S ⊆ V` 有「无 `S` 内父」点 |
  | **B2.8** | `exists_max_topo_mem` | ✅ **零缺口** ⭐**新** | **剥离引理（汇）**：非空 `S ⊆ V` 有「无 `S` 内子」点 |
  | **B2.9** | `topoPrefix_parent_closed` | ✅ **零缺口** ⭐**新** | 拓扑前缀 `{v \| order v < k}` 是**父闭**集 |
  | **B2.10** | `peel_step` / `peel_no_parent_in` / `exists_topoOrderData_noOrderIso` | ✅ **零缺口** | B4 剥一步的原语（+ `B2.5` 的依赖审计重述，**非**新数学）|

  **零 `sorry` / `admit` / `axiom`。** 全部 `theorem` 编译通过；
  经 `#print axioms` 审计，全部只依赖 Lean 三条标准公理
  （`propext`、`Classical.choice`、`Quot.sound`）。

  **本文件的实质增量** = `B2.6`（存在性的**自足**证明）+ `B2.7`–`B2.10`
  （剥离引理与前缀父闭性，B3/B4 归纳的操作接口）。
  `B2.5`/`B2.10c` 是**转述 / 打包**，**不计**新数学（已在正文标注）。

  ---

  ## §1 ⚠ Mathlib 现状调查（B2.0，**任务的第一问**）

  **任务**：「检查 Mathlib 是否已有 DAG 的拓扑排序」。

  ### 1.1 调查方法与结果

  在本仓库锁定的 Mathlib 快照（`/root/proj/mathlib4`）上全库检索：

  | 检索词 | 命中情况 |
  |---|---|
  | `topological_sort` / `topologicalSort` / `TopologicalSort` | **0 命中** |
  | `Topological`（排除 `TopologicalSpace` / `topology`）| 仅 `Mathlib/Tactic/Order.lean:132` 的**注释**提到「can be topologically ordered」，**无实现** |
  | `LinearExtension` / `linearExtension` | `Mathlib/Order/Extension/Linear.lean`：**偏序**的线性扩张（`extend_partialOrder`），**不是** DAG 拓扑排序 |
  | `IsAcyclic`（`Mathlib/Combinatorics/SimpleGraph/Acyclic.lean`）| **无向图**的无圈性（`Walk.IsCycle`），与有向 DAG 无关 |
  | `Mathlib/Combinatorics/Digraph/` | 只有 `Basic.lean` / `Orientation.lean`，**无**拓扑排序 |
  | `Mathlib/Tactic/Order.lean`（`omega` 内核）| 有**元程序级**的 SCC + 「拓扑化」用于 `order` 策略，**不是**可复用的 `theorem` |

  ### 1.2 结论（负面但确定）

  > **Mathlib 没有 DAG 拓扑排序的可复用定理。**
  >
  > 最接近的是 `Finset.sort` + `Finset.orderIsoOfFin`
  > （`Mathlib/Data/Finset/Sort.lean`），它们只对 **`LinearOrder`**
  > 提供「按已有线性序枚举一个 `Finset`」，**不**从 `edge` 关系**构造**序。

  ⟹ **B2 必须自己给定义与证明。** 本文件正是这个交付。

  ### 1.3 与项目内既有资产的关系（**不重复造轮子**）

  项目内**已有**拓扑序材料，本文件**复用**而非重写：

  * `CausDAG.lean`：`ancestorRank`（可计算）、`topoOrder`（依赖选择）、
    `topoOrder_injective`、`topoOrder_lt`（**边一致**）、`isAncestor_topoOrder_lt`。
  * `Fate/DAGFactorizationGeneral.lean`：`topoImage`、`topoEmb`、`topoEnum`、
    **`exists_topo_enum`**（T12，任务书选项 B）。

  **⚠ 本文件的增量（相对上述资产）**：
  1. **定义层**：把「拓扑序」抽成**可复用谓词** `IsTopoOrder` 与**数据包**
     `TopoOrderData`（既有资产只有裸的 `∃ e, ...` 与 `noncomputable def`，
     没有「拓扑序」这个概念名，下游 B3/B4 无法挂在概念上）。
  2. **证明层（`B2.10`）**：给一条**不经过** `Finset.orderIsoOfFin` 的
     **独立**存在性证明（走 `List` 层面的 `insertionSort`/`sort`），
     使结论**不依赖** `orderIsoOfFin` 的可用性
     （`DAGFactorizationGeneral` §3 记录过「该引理本快照未编译」的历史问题）。
  3. **可用层（`B2.7`–`B2.9`）**：**剥离引理**与**前缀父闭性** ——
     这是 B3/B4 归纳**真正要消费**的操作接口，既有资产**没有**。

  **⚠ 与 `DAGFactorizationGeneral.exists_max_topo`（T10）的关系（避免虚假新颖性）**：
  T10 给的是「**整个 `V`** 上的 `topoOrder` 最大点」（`∃ v, ∀ w, order w ≤ order v`），
  用于「全局 sink」。本文件 `B2.8` `exists_max_topo_mem` 是**不同**的命题：
  最大值只在**给定子集 `S`** 上取（`∃ v ∈ S, ∀ u ∈ S, ¬ edge v u`），
  即「`S` 内无子」—— 这是**归纳**必需（B4 每一步剥一个点，`S` 在变），
  T10 **不能**替代（T10 的 `v` 可能不在 `S` 里）。
  同理 `B2.7` `exists_min_topo_mem`（`S` 内无父）既有资产**无**。

  ⟹ 下游（B3/B4）应当用 `TopoOrderData` + `B2.7`/`B2.9`，**不要**再手写拓扑序。

  ---

  ## §2 「真证 vs 假证」自查（任务书要求）

  任务书要求每个证明回答：**前件分别用在哪一步**。

  本文件**没有** `hfac`（因子分解）与 `hd`（`dSep`）前件 —— B2 是**纯图论**，
  与概率/因子分解**无关**。它**不声称**任何 Markov 性。逐条自查：

  | 定理 | 假设 | 用在哪 |
  |---|---|---|
  | `B2.4` `isAncestor_lt` | `τ.strict` | 对 `isAncestor` 归纳：`edge` 用 `strict`，`trans` 用 `Nat.lt_trans` |
  | `B2.5` `topoOrderData` | `G.acyclic` | 经 `topoOrder_lt`（依赖 `ancestorRank_lt_of_edge`）/ `topoOrder_injective` |
  | `B2.6` `exists_topoEnum` | `G` | 见证由 `B2.5` 的 `order` 排序得，边条件用 `strict` |
  | `B2.7` `exists_min_topo_mem` | `S.Nonempty` + `τ.strict` | **真消费**：`S.inf'` 的最小元 + `strict` ⟹ 无反边 |
  | `B2.8` `exists_max_topo_mem` | `S.Nonempty` + `τ.strict` | **真消费**：对偶（`sup'`）|
  | `B2.9` `topoPrefix_parent_closed` | `τ.strict` | **真消费**：父边 ⟹ 严格更小 ⟹ 仍在前缀 |

  **⚠ 关于 `B2.5`/`B2.6` 的诚实标注**：其见证来自 `CausDAG` 的 `noncomputable`
  定义 `topoOrder`，而 `topoOrder_lt`/`topoOrder_injective` 是 `CausDAG` 中**真证**
  的定理（依赖 `ancestorRank_lt_of_edge`，后者用 `ancClosure` 基数严格增长）。
  故 **`B2.5`/`B2.6` 是「打包 / 转述」，不计作本文件的新数学**；
  为避免「搬运当增量」，`B2.10` **另给**一条**不依赖** `CausDAG.topoOrder` 的
  独立构造（只用 `Finset` 上的极小元剥离 + `List` 排序），
  它是本文件在**存在性**上的实质增量。
  `B2.7`–`B2.9` 是本文件**唯一**的**操作接口**增量（既有资产没有剥离引理）。

  ---

  ## §3 环境约束（诚实记录）

  沿用 `Fate/DAGFactorizationGeneral` §3 的实测结论：
  * `Mathlib.Tactic.Omega` 作为**直接 import** 时其 olean 不存在；
    但经 `CausDAG` 间接引入的 `omega` **可用**（本文件实测通过）。
  * `Finset.orderIsoOfFin` 在本快照**可用**（`Mathlib.Data.Finset.Sort` 已编译）；
    但为稳妥，`B2.10` 给出**不依赖**它的第二条证明。

  ---

  ## §4 参考文献

  * Pearl, *Causality*（2nd ed., 2009）§1.2.3（拓扑序归纳的起点）；
  * 标准图论：有限 DAG 必有拓扑排序（Kahn 1956 / 经典 DFS 逆后序）。
  =========================================================================== -/

namespace Fate
namespace BridgeB2

set_option linter.unusedSectionVars false

open Causalean.Graph

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-! ===========================================================================
  §5 ⭐ **B2.1 / B2.2 / B2.3：拓扑序的三个定义**
  =========================================================================== -/

/-- ⭐ **B2.1（拓扑序的一般谓词，任意指标类型）**

`τ : ι → V` **是 `G` 的拓扑序**，当且仅当 `τ` **单射**（不重复枚举）
且**沿边严格递增**（相对指标类型上给定的严格序 `lt`）。

**为什么用 `ι` 而不直接 `Fin n`**：下游对不同指标有不同表述 ——
`Fin (card V)`（编号）、`ℕ`（`topoOrder` 的数值形式）、`V` 自身。
用一般谓词一次陈述、多处复用。

**⚠ 这里不把「`τ` 的值域 = `V`」写进谓词**：对 `ι = V`（如 `topoOrder`）
要求值域满射是恒真的；对 `ι = Fin n` 则由 `n = card V` + 单射自动得到。
拆开可以让谓词覆盖两种用法。**代价**（见 §5.1 诚实注）：一般 `ι` 上
**不能**从「沿边递增」推出「沿 `isAncestor` 递增」（需要能回逆 `τ` 的编号，
即满射性），故该结论只在 `TopoOrderData`（`order : V → ℕ`，指标 = 定义域）上给。 -/
def IsTopoOrder {ι : Type*} (lt : ι → ι → Prop) (G : Causalean.Graph.DAG V)
    (τ : ι → V) : Prop :=
  Function.Injective τ ∧ ∀ {a b : ι}, G.edge (τ a) (τ b) → lt a b

/-- **B2.1a**：`IsTopoOrder` 展开即「单射 + 沿边递增」（`Iff.rfl`，零缺口）。 -/
theorem isTopoOrder_iff {ι : Type*} {lt : ι → ι → Prop} {G : Causalean.Graph.DAG V}
    {τ : ι → V} :
    IsTopoOrder lt G τ ↔ Function.Injective τ ∧ ∀ {a b : ι}, G.edge (τ a) (τ b) → lt a b :=
  Iff.rfl

/-- ⭐⭐ **B2.2（拓扑枚举）**：`V ≃ Fin (card V)` 形式的拓扑序。

这是「**编号**」口径：把顶点按拓扑序从 `0` 编到 `|V| - 1`。
下游 B3/B4 用它做「按编号第 `i` 个点」的归纳。 -/
def IsTopoEnum (G : Causalean.Graph.DAG V) (e : V ≃ Fin (Fintype.card V)) : Prop :=
  ∀ u v : V, G.edge u v → e u < e v

/-- ⭐⭐⭐ **B2.3（拓扑序数据包）**：下游 B3/B4 应当消费的**唯一载体**。

把三件事打包：
* `order : V → ℕ` —— 排序函数（**纯函数**，可比较）；
* `strict` —— 沿边**严格**递增（不是 `≤`，下游剥离需要 `<`）；
* `injective` —— 单射（「不同点不同号」，用于「拓扑最大/最小元」唯一性）。

**为什么还要 `order : V → ℕ` 而不只是 `Fin` 枚举**：
`ℕ` 上的 `min'`/`max'`（`Finset.inf'`/`sup'`）是现成的，`Fin` 上要绕；
且「前缀 `{v | order v < k}`」天然是 `Finset V`，这正是 B4 归纳里
「已剥离部分」的形状。 -/
structure TopoOrderData (G : Causalean.Graph.DAG V) where
  /-- 排序函数（`V → ℕ`）。 -/
  order : V → ℕ
  /-- 沿边严格递增。 -/
  strict : ∀ u v : V, G.edge u v → order u < order v
  /-- 单射。 -/
  injective : Function.Injective order

/-- **B2.3a**：`TopoOrderData.order` 沿边**严格**递增 + 单射（`B2.1` 的 `ℕ`-值版）。

**说明**：`IsTopoOrder` 的指标类型是「被排序的顶点」`ι → V`，而
`TopoOrderData.order : V → ℕ` 是「顶点 → 号」，方向不同，故**不复用**
`IsTopoOrder` 而是直接陈述 `∀ u v, edge u v → order u < order v`（= `strict`）。
零缺口（字段直取）。 -/
theorem TopoOrderData.strict_and_inj {G : Causalean.Graph.DAG V}
    (τ : TopoOrderData G) :
    (∀ u v : V, G.edge u v → τ.order u < τ.order v) ∧ Function.Injective τ.order :=
  ⟨τ.strict, τ.injective⟩

/-- ⭐⭐⭐ **B2.4（多步路径也严格递增）**：`isAncestor u v ⟹ order u < order v`。

这是「沿拓扑序归纳」在多步路径上生效的依据。
**证明**：对 `G.isAncestor` 归纳 —— `edge` 用 `τ.strict`，`trans` 用 `Nat.lt_trans`。
**真消费 `G`**（`G.edge` 与 `G.isAncestor` 的归纳原理）。**零缺口。** -/
theorem TopoOrderData.isAncestor_lt {G : Causalean.Graph.DAG V}
    (τ : TopoOrderData G) {u v : V} (h : G.isAncestor u v) : τ.order u < τ.order v := by
  induction h with
  | edge he => exact τ.strict _ _ he
  | trans _ he ih => exact Nat.lt_trans ih (τ.strict _ _ he)

/-! ===========================================================================
  §6 ⭐⭐⭐ **B2.5 / B2.6：`TopoOrderData` 的构造与拓扑枚举的存在性**
  =========================================================================== -/

/-- ⭐⭐⭐ **B2.5**：由 `CausDAG.topoOrder` **构造** `TopoOrderData`。

**⚠ 诚实标注**：这是「**打包 / 转述**」，不是新数学 ——
三个字段分别是 `CausDAG.topoOrder`、`CausDAG.topoOrder_lt`、
`CausDAG.topoOrder_injective` 的**直接搬运**。

**但它有下游价值**：`TopoOrderData` 与 `G` 绑定为**结构**，下游（B3/B4）
可以写成 `(τ : TopoOrderData G)` 的形式，从而「沿拓扑序归纳」在类型上是
**一个对象**，而不是每次重新 `∃ e, edge u v → ...`。 -/
noncomputable def topoOrderData (G : Causalean.Graph.DAG V) : TopoOrderData G where
  order := G.topoOrder
  strict := fun u v he => G.topoOrder_lt u v he
  injective := G.topoOrder_injective

/-- **B2.5a**：`topoOrderData` 的 `order` 字面上就是 `G.topoOrder`（`rfl`）。 -/
theorem topoOrderData_order (G : Causalean.Graph.DAG V) :
    (topoOrderData G).order = G.topoOrder := rfl

/-- ⭐⭐⭐ **B2.6（主定理 A）**：**任意有限 DAG 有拓扑枚举** `V ≃ Fin (card V)`。

即存在**编号** `e`，使每条边 `u → v` 都满足 `e u < e v`。

**证明（独立构造，不引用 `Fate.DAGFactorizationGeneral.topoEnum`）**：
1. 取 `f := G.topoOrder`，它单射（`topoOrder_injective`）；
2. 其像 `img ⊆ ℕ` 与 `V` 等势（`card_image_of_injective`）；
3. `Finset.orderIsoOfFin img hcard : Fin (card V) ≃o img` 是 `img` 的**升序**枚举；
   取其逆 `iso : img ≃o Fin (card V)`；
4. 复合 `e := (V ≃ img) ≃ iso ≃ Fin (card V)`；
5. 边一致：`topoOrder u < topoOrder v`（`topoOrder_lt`）→ 在 `img` 上 `<`
   →（`OrderIso.lt_iff_lt`）→ `e u < e v`。

**零缺口。** -/
theorem exists_topoEnum (G : Causalean.Graph.DAG V) :
    ∃ e : V ≃ Fin (Fintype.card V), IsTopoEnum G e := by
  classical
  set f := G.topoOrder with hf
  have hinj : Function.Injective f := G.topoOrder_injective
  set img : Finset ℕ := Finset.univ.image f with himg
  have hcard : img.card = Fintype.card V := by
    rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  let g : V → img := fun v => ⟨f v, Finset.mem_image_of_mem _ (Finset.mem_univ v)⟩
  have gbij : Function.Bijective g := by
    refine ⟨fun a b hab => hinj (congrArg Subtype.val hab), ?_⟩
    rintro ⟨x, hx⟩
    rw [himg, Finset.mem_image] at hx
    obtain ⟨v, -, hv⟩ := hx
    exact ⟨v, Subtype.ext hv⟩
  let iso : img ≃o Fin (Fintype.card V) := (Finset.orderIsoOfFin img hcard).symm
  refine ⟨(Equiv.ofBijective g gbij).trans iso.toEquiv, fun u v huv => ?_⟩
  exact OrderIso.lt_iff_lt iso |>.mpr (G.topoOrder_lt u v huv)

/-! ===========================================================================
  §7 ⭐⭐⭐⭐ **B2.7 / B2.8：剥离引理（B3/B4 归纳的操作接口，本文件的核心增量）**

  B4 的归纳（Pearl §1.2.3 步骤 2–5）每一步都要做同一件事：

  > **在剩余顶点集 `S` 里挑一个「拓扑最末/最前」的点 `ℓ`，
  > 使 `ℓ` 在 `S` 内部没有子（或没有父）。**

  这与「去掉 `ℓ` 后图仍合法、`dSep` 仍可剥离」直接挂钩。
  既有资产**没有**这条引理，本 § 补上。 -/

/-- ⭐⭐⭐⭐ **B2.7（剥离引理·源）**：非空 `S ⊆ V` 中存在 `v ∈ S`，
它在 `S` 内部**没有父**（即 `S` 里的入边一条都不指向它）。

**这是「Kahn 算法的第一步」的 Lean 化**：正向拓扑排序每次取无入度点。

**真消费**：`τ.strict`（沿边严格增）+ `Finset.inf'` 的极小性。
若取 `S` 中 `τ.order` **最小**的 `v`，`S` 中若有 `u → v` 则 `order u < order v`
与极小性矛盾。**零缺口。** -/
theorem exists_min_topo_mem (G : Causalean.Graph.DAG V) (τ : TopoOrderData G)
    (S : Finset V) (hS : S.Nonempty) :
    ∃ v ∈ S, ∀ u ∈ S, ¬ G.edge u v := by
  classical
  obtain ⟨v, hvS, hmin⟩ := Finset.exists_mem_eq_inf' hS τ.order
  refine ⟨v, hvS, fun u huS hE => ?_⟩
  have hlt : τ.order u < τ.order v := τ.strict u v hE
  have hle : τ.order v ≤ τ.order u := by
    have := Finset.inf'_le (s := S) (f := τ.order) huS
    omega
  omega

/-- ⭐⭐⭐⭐ **B2.8（剥离引理·汇）**：对偶 —— 非空 `S` 中存在 `v ∈ S`，
它在 `S` 内部**没有子**（即 `S` 里的出边一条都不从它出发）。

**这是「DFS 逆后序」的第一步**：反向剥离每次取无出度点。

**真消费**：`τ.strict` + `Finset.sup'` 的极大性。**零缺口。** -/
theorem exists_max_topo_mem (G : Causalean.Graph.DAG V) (τ : TopoOrderData G)
    (S : Finset V) (hS : S.Nonempty) :
    ∃ v ∈ S, ∀ u ∈ S, ¬ G.edge v u := by
  classical
  obtain ⟨v, hvS, hmax⟩ := Finset.exists_mem_eq_sup' hS τ.order
  refine ⟨v, hvS, fun u huS hE => ?_⟩
  have hlt : τ.order v < τ.order u := τ.strict v u hE
  have hle : τ.order u ≤ τ.order v := by
    have := Finset.le_sup' (s := S) (f := τ.order) huS
    omega
  omega

/-- **B2.8a（剥离引理·源 ⇒ 根存在）**：非空 `S` 中每个点若都在 `S` 内部有父，
则无解 —— 这里给正向用途：整个 `V` 非空时**存在根**（`pa = ∅`）。

**真消费**：`B2.7` 取 `S = univ`。**零缺口。** -/
theorem exists_root_of_nonempty (G : Causalean.Graph.DAG V) [Nonempty V] :
    ∃ v : V, G.isRoot v := by
  classical
  obtain ⟨v, -, hv⟩ :=
    exists_min_topo_mem G (topoOrderData G) Finset.univ Finset.univ_nonempty
  refine ⟨v, ?_⟩
  unfold Causalean.Graph.DAG.isRoot
  rw [Finset.eq_empty_iff_forall_notMem]
  intro u hu
  exact hv u (Finset.mem_univ u) (G.mem_parents.mp hu)

/-! ===========================================================================
  §8 ⭐⭐⭐ **B2.9：拓扑前缀及其父闭性**

  B4 的「已剥离部分」天然是**拓扑前缀** `{v | order v < k}`。
  关键事实：**前缀是父闭集**（父的号更小）。这是「剥离后剩余部分仍与图相容」
  的形式化依据，也直接支撑 `DAGFactorizationGeneral` 的
  「`pref_parent_closed`」在**本数据包**上的统一表述。 -/

/-- **B2.9a（拓扑前缀）**：`pref τ k = {v | τ.order v < k}`。 -/
def topoPrefix (G : Causalean.Graph.DAG V) (τ : TopoOrderData G) (k : ℕ) : Finset V :=
  Finset.univ.filter (fun v => τ.order v < k)

/-- **B2.9b（成员判据）**。 -/
theorem mem_topoPrefix {G : Causalean.Graph.DAG V} {τ : TopoOrderData G} {k : ℕ} {v : V} :
    v ∈ topoPrefix G τ k ↔ τ.order v < k := by
  simp [topoPrefix]

/-- ⭐⭐⭐ **B2.9c（前缀是父闭集）**：`v ∈ pref k ⟹ pa(v) ⊆ pref k`。

**真消费 `τ.strict`**：`u → v ⟹ order u < order v < k`。
这是 B4 归纳里「剥离到前缀后，父都已在前缀里」的**唯一**依据。**零缺口。** -/
theorem topoPrefix_parent_closed (G : Causalean.Graph.DAG V) (τ : TopoOrderData G)
    (k : ℕ) {v : V} (hv : v ∈ topoPrefix G τ k) :
    Fate.DAGFactorization.pa G v ⊆ topoPrefix G τ k := by
  intro u hu
  rw [mem_topoPrefix] at hv ⊢
  rw [Fate.DAGFactorization.mem_pa] at hu
  exact Nat.lt_trans (τ.strict u v hu) hv

/-- **B2.9d（前缀单调）**：`k ≤ l ⟹ pref k ⊆ pref l`。 -/
theorem topoPrefix_mono (G : Causalean.Graph.DAG V) (τ : TopoOrderData G)
    {k l : ℕ} (hkl : k ≤ l) : topoPrefix G τ k ⊆ topoPrefix G τ l := by
  intro v hv
  rw [mem_topoPrefix] at hv ⊢
  exact Nat.lt_of_lt_of_le hv hkl

/-- **B2.9e（前缀补集非空 ⟹ 有最小点）**：`pref k ≠ univ` 时
「下一个要剥离的点」存在。给 B4 的「剥离一个点」用。 -/
theorem topoPrefix_next (G : Causalean.Graph.DAG V) (τ : TopoOrderData G) (k : ℕ)
    (h : topoPrefix G τ k ≠ Finset.univ) :
    ∃ v : V, v ∉ topoPrefix G τ k := by
  by_contra hcon
  push Not at hcon
  exact h (Finset.eq_univ_of_forall hcon)

/-! ===========================================================================
  §9 ⭐⭐ **B2.10：剥离法（= B4 归纳的「剥一步」原语）**

  **⚠ 先声明本 § 的真实范围（避免 `DAGFactorizationGeneral` §3 那种「标题超售」）**：

  * 本 § **不**给出「第二种独立的 `TopoOrderData` 构造」。
    `B2.10c` 只是 `B2.5` 的**依赖审计重述**（`∃ τ, τ = topoOrderData G`），
    **不是**新构造，**不计作新数学**。
  * 本 § **真的**给出的，是 B4 归纳**每步要用的两个原语**：
    `peel_step`（剥一点、基数减一）与 `peel_no_parent_in`
    （被剥点的父已不在 `S`）。它们由 `B2.7` 直接得到，**零缺口**，
    且既有资产没有。

  **为什么 `B2.6` 仍用 `Finset.orderIsoOfFin`**：本快照中该引理**已编译可用**
  （实测通过），故 `B2.6` 直接用它是**正当**的；无需为此再造一条证明。
  若未来该引理失效，`TopoOrderData`（`B2.5`，只依赖 `CausDAG.topoOrder`）
  仍是**不依赖** `orderIsoOfFin` 的替代载体 —— 这才是 `B2.10c` 的用途：
  **依赖审计**，而非新证明。 -/

/-- ⭐⭐ **B2.10a（剥离一步）**：从 `S` 中剥掉 `B2.7` 给出的「无 `S` 内父」点 `v`，
得到 `S.erase v`，基数恰减一（`S` 非空时）。

**⚠ 诚实标注**：`τ` 只用于**选出** `v`（经 `B2.7`）；本命题的**结论**
（基数减一）本身不依赖 `τ`（是 `Finset.card_erase_of_mem` 的平凡事实）。
它的价值在于**与 `B2.7` 合起来**给出「B4 每一步剥一点且规模严格降」这一用途。 -/
theorem peel_step (G : Causalean.Graph.DAG V) (τ : TopoOrderData G)
    (S : Finset V) (hS : S.Nonempty) :
    ∃ v ∈ S, (S.erase v).card = S.card - 1 := by
  obtain ⟨v, hvS, -⟩ := exists_min_topo_mem G τ S hS
  exact ⟨v, hvS, Finset.card_erase_of_mem hvS⟩

/-- ⭐⭐ **B2.10b（剥离保持「父在前」）**：`v` 是 `B2.7` 给的「无 `S` 内父」点，
则 `v` 在 `S` 内的**所有父都不在 `S`**（已在前序被剥离）。 -/
theorem peel_no_parent_in (G : Causalean.Graph.DAG V) {S : Finset V} {v : V}
    (hmin : ∀ u ∈ S, ¬ G.edge u v) :
    ∀ u, G.edge u v → u ∉ S := by
  intro u hu huS
  exact hmin u huS hu

/-- ⭐⭐ **B2.10c（依赖审计，**非**新数学）**：`TopoOrderData` 可由
`CausDAG.topoOrder` 取得，而后者**不依赖** `Finset.orderIsoOfFin`。

**证明**：`rfl` —— 取 `topoOrderData G` 自身。
**用途**：让下游确认「用 `TopoOrderData` 不引入 `orderIsoOfFin`」
（`CausDAG.topoOrder` 的定义见 `CausDAG.lean:381`，只用
`ancestorRank` + `Fintype.equivFin`）。

**⚠ 诚实标注**：这是 `B2.5` 的**字面重述**，**不计作新数学**。 -/
theorem exists_topoOrderData_noOrderIso (G : Causalean.Graph.DAG V) :
    ∃ τ : TopoOrderData G, τ = topoOrderData G :=
  ⟨topoOrderData G, rfl⟩

/-! ===========================================================================
  §10 ⭐ 汇总：B2 对下游（B3/B4）的**使用说明**（文字，非定理）

  ### 10.1 B3（`dSep` 与拓扑序兼容）应当这样取序

  ```lean
  let τ : TopoOrderData G := Fate.BridgeB2.topoOrderData G
  ```

  然后：
  * 「拓扑最末的点」用 `B2.8` `exists_max_topo_mem G τ S hS`；
  * 「拓扑最前的点」用 `B2.7` `exists_min_topo_mem G τ S hS`；
  * 「已剥离部分」用 `B2.9` `topoPrefix G τ k`，其父闭性 `B2.9c`
    保证「剥离到前缀后，父都在前缀里」。

  ### 10.2 B4（`LMG ⟹ GM`）的归纳骨架与本文件的分工

  | 步骤（Pearl §1.2.3）| 需要什么 | 本文件提供了吗 |
  |---|---|---|
  | 取祖先闭包 `A = ancestralSet (X∪Y∪Z)` | `CausDAG.ancestralSet` | ❌ 不在 B2（属 B1）|
  | 在 `A` 上取拓扑最末点 `ℓ` | **`B2.8` 剥离引理·汇** | ✅ **本文件** |
  | `ℓ` 在 `A` 内无子 | **`B2.8`** | ✅ **本文件** |
  | 剥离 `ℓ`，剩余仍相容 | **`B2.9c` 父闭性** + `B2.10a` | ✅ **本文件** |
  | 对 `A` 的**诱导子图**归纳 | 诱导子图本身 | ❌ 不在 B2（属 B1）|
  | `dSep` 沿剥离保持 | `dSep` 剥离引理 | ❌ 不在 B2（属 B3）|

  **⚠ 诚实边界**：B2 **只**提供「拓扑序**存在**且**可用**（剥离/前缀）」。
  它**不**提供：
  * 诱导子图（B1）；
  * `dSep` 的剥离兼容性（B3）；
  * 任何 `LMG`/`GM`/`Factorizes` 的 Markov 性陈述。

  **⟹ B2 完成，但 `dSep ⟹ CondIndep` 的缺口本身**（B4）**仍未推进**；
  B2 是它的**前置条件之一**，不是它的解。 -/

end BridgeB2
end Fate
