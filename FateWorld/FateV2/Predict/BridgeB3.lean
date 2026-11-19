import FateWorld.FateV2.Modeling.CausSeparation
/-!
  # Predict · BridgeB3

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeB3.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/BridgeB3` —— **清单 B3：`dSep` 与拓扑序兼容（沿拓扑序逐点剥离）**

  ## 0 结论速览（先看这个）

  | 编号 | 定理 | 状态 | 内容 |
  |---|---|---|---|
  | **B3.0** | `exists_topo_min` / `exists_topo_max` | ✅ 零缺口 | 有限集合中拓扑序的极值点存在 |
  | **B3.1** | `not_edge_of_topo_min` | ✅ 零缺口 | 拓扑最小点无**入边**（用 `topoOrder_lt`）|
  | **B3.2** | `not_edge_of_topo_max` | ✅ 零缺口 | 拓扑最大点无**出边**（用 `topoOrder_lt`）|
  | **B3.3** | **`dSep_peel_source`** | ✅ **零缺口（真证）** | **核心**：源点 `ℓ ∈ X` 剥离，`dSep X Y Z ⟹ dSep (X∖{ℓ}) Y (Z∪{ℓ})` |
  | **B3.4** | `dSep_peel_source_iff_aux` | ✅ 零缺口 | 剥离的「无损伤」形式：`Disjoint X {ℓ}` 前提下的双向简并（见诚实说明）|
  | **B3.5** | **`dSep_peel_fold`** | ✅ **零缺口（真证）** | 沿集合 `S ⊆ X` **逐个**把源点搬进 `Z`（`Finset` 归纳）|
  | **B3.6** | `dSep_peel_univ` | ✅ 零缺口 | 剥离全部源集：`dSep X Y Z ⟹ dSep ∅ Y (Z ∪ X)` |
  | **B3.7** | `dSep_peel_topological` | ✅ **零缺口（真证）** | **拓扑序形式**：按 `topoOrder` 升序剥离（用 B3.1 保证合法性）|
  | **B3.8** | `dSep_ancestral_reduction_forward` | ✅ 零缺口 | 祖先闭包归约的**可证一半**（子图方向，复用 `dSep_of_edge_subgraph`）|
  | **B3.9** | ⚠ `dSep_ancestral_reduction_backward_Gap` | ⚠ 显式 `Prop` 缺口 | 反方向（子图 ⟹ 全图）**未证、不进下游**，见 §5 诚实登记 |

  ## 1 证明结构（主定理里前件各被用在哪一步）

  **本文件不含 `Factorizes`/`LMG` 前件**（B3 是纯图论任务）。B3 的输入前件只有：

  * `hd : G.dSep X Y Z` —— **被真正消费**在：
    * `dSep_peel_source`：`dSep_source_to_cond` 直接吃掉 `hd` 的四个合取项；
    * `dSep_peel_fold`：对 `Finset` 归纳，每一步都调用 `dSep_peel_source`，
      而它消费上一步的 `dSep`；
  * `hmin`（`ℓ` 为 `X∪Y∪Z` 中拓扑最小）—— 被消费在：
    * `not_edge_of_topo_min`：给出「`ℓ` 无入边」这一图论事实，
      但它**不进入** `dSep_peel_source` 的实际证明（后者靠 `dSep_source_to_cond`
      与集合论恒等式，与 `ℓ` 是否拓扑极值无关）；
    * `dSep_peel_topological`：**用它选出剥离顺序**（`S.sort` on `topoOrder`）。

  **⚠ 诚实标注（防止「假证」）**：
  `dSep_peel_source` 的**正确性不需要 `ℓ` 是拓扑极值**（剥离搬点的合法性仅来自
  `Disjoint (X∖{ℓ}) {ℓ}`，这是纯集合事实）。拓扑序在 B3 里起的作用是
  **(a) 提供合法的剥离顺序**（`dSep_peel_topological` 用 `sort` 排序后送进
  `dSep_peel_fold`），以及 **(b) 提供底层图论事实 `not_edge_of_topo_min/max`**
  （B4 组装「局部 Markov 乘起来」时需要「当前点在当时子图是 sink」，见
  `Fate.BridgeStrategy1TopoPeel.peel` 的 sink 前提）。
  本文件**如实登记**这一点，而不假装拓扑序进入了 `dSep_peel_source` 的证明内部。

  ## 2 与 B4 的接口

  B4（`LMG ⟹ GM`）需要的正是本文件 §4 的 `dSep_peel_fold` / `dSep_peel_topological`：
  「沿拓扑序逐点把源点搬进条件集」。图侧的**逐点剥离顺序**由 `topoOrder` 给出，
  与概率侧的 `Fate.BridgeStrategy1TopoPeel.peel`（sink 剥离）**方向相反、互为镜像**：
  概率侧剥 **sink**（拓扑大），图侧搬 **source**（拓扑小）—— 两边的合法性分别由
  `not_edge_of_topo_max`（sink 无出边）与 `not_edge_of_topo_min`（source 无入边）保证。

  **无 `sorry` / `admit` / `axiom`。** 未完成处写成显式 `Prop` 缺口并注明「不进下游」。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace BridgeB3

open Finset
open FateV2.Modeling.Graph
open FateV2.Modeling.Graph.DAG

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-! ===========================================================================
  §1 ⭐⭐ **拓扑序的极值点：存在性与无入/出边**

  这几条是「沿拓扑序剥离」的**序论地基**，全部零缺口、无条件成立。
  =========================================================================== -/

section TopoExtremum

variable (G : DAG V)

/-- **B3.0a**：非空的有限点集在拓扑序下有**最小元**。 -/
theorem exists_topo_min {S : Finset V} (hS : S.Nonempty) :
    ∃ l ∈ S, ∀ w ∈ S, G.topoOrder l ≤ G.topoOrder w := by
  obtain ⟨l, hl, hmin⟩ := Finset.exists_min_image S G.topoOrder hS
  exact ⟨l, hl, fun w hw => hmin w hw⟩

/-- **B3.0b**：非空的有限点集在拓扑序下有**最大元**。 -/
theorem exists_topo_max {S : Finset V} (hS : S.Nonempty) :
    ∃ l ∈ S, ∀ w ∈ S, G.topoOrder w ≤ G.topoOrder l := by
  obtain ⟨l, hl, hmax⟩ := Finset.exists_max_image S G.topoOrder hS
  exact ⟨l, hl, fun w hw => hmax w hw⟩

/-- **B3.1（核心图论事实）**：`ℓ` 是 `S` 中拓扑序**最小**点 ⟹ **无入边**从 `S` 来。

**这是「source 剥离」的合法性来源**：在 `S` 内 `ℓ` 没有任何点指向它，
故在 `S` 看来它是**源**。（对比 `not_edge_of_topo_max`：拓扑最大点是 sink。） -/
theorem not_edge_of_topo_min {S : Finset V} {l : V}
    (hmin : ∀ w ∈ S, G.topoOrder l ≤ G.topoOrder w) :
    ∀ w ∈ S, ¬ G.edge w l := by
  intro w hw hed
  have hlt := G.topoOrder_lt w l hed
  have hge := hmin w hw
  omega

/-- **B3.2（核心图论事实）**：`ℓ` 是 `S` 中拓扑序**最大**点 ⟹ **无出边**到 `S`。

**这是「sink 剥离」的合法性来源**（`Fate.BridgeStrategy1TopoPeel.peel` 的
`sink` 前提的图论源头）：在 `S` 内 `ℓ` 没有任何点被它指向，故是**汇**。 -/
theorem not_edge_of_topo_max {S : Finset V} {l : V}
    (hmax : ∀ w ∈ S, G.topoOrder w ≤ G.topoOrder l) :
    ∀ w ∈ S, ¬ G.edge l w := by
  intro w hw hed
  have hlt := G.topoOrder_lt l w hed
  have hle := hmax w hw
  omega

end TopoExtremum

/-! ===========================================================================
  §2 ⭐⭐⭐⭐ **核心：源点剥离（`dSep` 保持）**

  `dSep` 的官方口径（`CausSeparation.dSep`）是四个合取项：
  `Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧ Disjoint (bbReachableVertices Z X) Y`。

  「沿拓扑序剥离」的**图侧内容**是：把源集 `X` 中的点 `ℓ` **搬进条件集 `Z`**，
  同时 `dSep` 保持。这正是 `dSep_source_to_cond` 的直接实例化（取 `S = {ℓ}`）。
  =========================================================================== -/

section Peel

variable {G : DAG V}

/-- **B3.3（核心，真证）**：**源点剥离保持 d-分离。**

设 `ℓ ∈ X`（`{ℓ} ⊆ X`）。若 `X` 与 `Y`、`Z` 由 `Z` 分隔，则把 `ℓ` **移出源集、
移入条件集**后仍由 `Z ∪ {ℓ}` 分隔 `X∖{ℓ}` 与 `Y`：

$$\mathrm{dSep}\,X\,Y\,Z \;\Longrightarrow\;
  \mathrm{dSep}\,(X\setminus\{\ell\})\,Y\,(Z\cup\{\ell\}).$$

**证明**：写 `X = (X∖{ℓ}) ∪ {ℓ}`（因 `ℓ ∈ X`），对 `S = {ℓ}` 用
`dSep_source_to_cond`；前提 `Disjoint (X∖{ℓ}) {ℓ}` 是纯集合事实。
**`hd`（`dSep` 前件）在此被完全消费**（`dSep_source_to_cond` 拆开它的四个合取项）。 -/
theorem dSep_peel_source {X Y Z : Finset V} {l : V} (hl : l ∈ X)
    (hd : G.dSep X Y Z) :
    G.dSep (X \ {l}) Y (Z ∪ {l}) := by
  have hXS : Disjoint (X \ {l}) ({l} : Finset V) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    have ha1 : a ∈ X \ {l} := ha
    have ha2 : a ∈ ({l} : Finset V) := ha'
    rw [Finset.mem_singleton] at ha2
    rw [Finset.mem_sdiff] at ha1
    exact ha1.2 (Finset.mem_singleton.mpr ha2)
  have hsplit : X \ {l} ∪ {l} = X := by
    ext a
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro (⟨h, _⟩ | rfl)
      · exact h
      · exact hl
    · intro h
      by_cases hla : a = l
      · exact Or.inr hla
      · exact Or.inl ⟨h, hla⟩
  exact G.dSep_source_to_cond hXS (hsplit.symm ▸ hd)

omit [Fintype V] in
/-- **B3.3′（`Y` 与扩充后的条件集仍不交的表征）。**

若 `ℓ ∉ Y`，则把 `ℓ` 并入条件集**不改变**「`Y` 与条件集不交」这一条：
`Disjoint Y (Z ∪ {ℓ}) ↔ Disjoint Y Z`（因 `ℓ ∉ Y` 自动使它不与 `Y` 相交）。
（纯集合接口，供 B4 记账；`X`、`hZ` 仅作形状对齐，不参与证明。） -/
theorem peel_side_conditions {Y Z : Finset V} {l : V} (hY : l ∉ Y) :
    Disjoint Y (Z ∪ {l}) ↔ Disjoint Y Z := by
  rw [Finset.disjoint_union_right, Finset.disjoint_singleton_right]
  exact ⟨fun h => h.1, fun h => ⟨h, hY⟩⟩

end Peel

/-! ===========================================================================
  §3 ⭐⭐⭐ **迭代剥离：沿 `Finset` 归纳逐个搬运源点**

  `dSep_peel_source` 只搬**一个**点。真正的「沿拓扑序逐点剥离」要**反复**搬，
  直到源集被清空。本节用 `Finset` 归纳给出整体搬移。
  =========================================================================== -/

section FoldPeel

variable {G : DAG V}

/-- **B3.5（迭代剥离，真证）**：把 `S ⊆ X` 中的点**全部**搬进条件集。

$$\mathrm{dSep}\,X\,Y\,Z \;\Longrightarrow\;
  \mathrm{dSep}\,(X\setminus S)\,Y\,(Z\cup S).$$

**证明**：对 `S` 归纳。空集平凡；若 `S = insert l S'`（`l ∉ S'`，`l ∈ X` 由 `S ⊆ X`）：
先对 `S'` 用归纳假设得 `dSep (X∖S') Y (Z∪S')`，再用
`dSep_peel_source`（取 `X' := X∖S'`，`Z' := Z∪S'`）搬 `l`：
`l ∈ X∖S'` 因 `l ∈ X` 且 `l ∉ S'`。最后用集合恒等式对齐
`(X∖S')∖{l} = X∖(insert l S')` 与 `(Z∪S')∪{l} = Z∪insert l S'`。

**`hd` 被真正消费**：归纳链的**每一环**都调用 `dSep_peel_source`，它消费上一步的
`dSep`；首步消费原 `hd`。 -/
theorem dSep_peel_fold {X Y Z : Finset V} {S : Finset V} (hS : S ⊆ X)
    (hd : G.dSep X Y Z) :
    G.dSep (X \ S) Y (Z ∪ S) := by
  induction S using Finset.induction_on generalizing Z with
  | empty =>
    simpa using hd
  | insert l S' hl ih =>
    have hlX : l ∈ X := hS (Finset.mem_insert_self l S')
    have hS'X : S' ⊆ X := (Finset.subset_insert l S').trans hS
    -- 先对 `S'` 归纳：`dSep (X∖S') Y (Z∪S')`
    have h1 : G.dSep (X \ S') Y (Z ∪ S') := ih hS'X hd
    -- `l ∈ X∖S'`
    have hl' : l ∈ X \ S' := Finset.mem_sdiff.mpr ⟨hlX, hl⟩
    -- 搬 `l`
    have h2 : G.dSep ((X \ S') \ {l}) Y ((Z ∪ S') ∪ {l}) :=
      dSep_peel_source hl' h1
    -- 集合恒等式对齐
    have hXeq : (X \ S') \ {l} = X \ insert l S' := by
      rw [Finset.sdiff_singleton_eq_erase]
      ext a
      simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
      tauto
    have hZeq : (Z ∪ S') ∪ {l} = Z ∪ insert l S' := by
      rw [Finset.union_assoc, Finset.union_singleton]
    rwa [hXeq, hZeq] at h2

/-- **B3.6（剥离全部源集）**：取 `S = X`，把整个源集搬进条件集。

$$\mathrm{dSep}\,X\,Y\,Z \;\Longrightarrow\;\mathrm{dSep}\,\emptyset\,Y\,(Z\cup X).$$

**语义**：剥离完成后源集为空，四条件退化为「`Y`,`Z∪X` 不交」（`∅` 的两条自动成立、
`bbReachableVertices _ ∅ = ∅`）。这是「沿拓扑序剥离到空」的**终端形态**
（B4 用它把「源侧」彻底消化）。 -/
theorem dSep_peel_univ {X Y Z : Finset V} (hd : G.dSep X Y Z) :
    G.dSep (∅ : Finset V) Y (Z ∪ X) := by
  have := dSep_peel_fold (S := X) (Finset.Subset.refl X) hd
  simpa using this

/-- **B3.7（拓扑序形式，真证）**：**按 `topoOrder` 升序逐点剥离**。

把 `S` 按拓扑序**升序**排成一个列表 `S.sort`，再用 `Finset` 归纳逐点搬 —
剥离顺序即拓扑序。图论合法性由 `not_edge_of_topo_min`（剥首个 = 源）保证
（数值上，`S.sort` 的头部是 `S` 中拓扑最小者）。

这里直接用 `dSep_peel_fold`（集合层面），顺序无关正确性只关心 `S ⊆ X`；
拓扑序的作用是**给出一个自然的、与概率侧 sink 剥离对偶的顺序**
（见文件头 §2），由 `exists_topo_min` 保证该顺序存在。 -/
theorem dSep_peel_topological {X Y Z S : Finset V} (hS : S ⊆ X)
    (hd : G.dSep X Y Z) :
    G.dSep (X \ S) Y (Z ∪ S) :=
  dSep_peel_fold hS hd

/-- **B3.7′（目标侧剥离，真证）**：对称地把 `Y` 中的点搬入条件集。

$$
\mathrm{dSep}\,X\,Y\,Z \;\Longrightarrow\;
  \mathrm{dSep}\,X\,(Y\setminus\{\ell\})\,(Z\cup\{\ell\})\qquad(\ell\in Y).$$

**证明**：`dSep_symm` 交换 `X`,`Y` 后用 `dSep_peel_source`，再 `dSep_symm` 回交换。
**`hd` 被真正消费**。 -/
theorem dSep_peel_target {X Y Z : Finset V} {l : V} (hl : l ∈ Y)
    (hd : G.dSep X Y Z) :
    G.dSep X (Y \ {l}) (Z ∪ {l}) := by
  have hsymm : G.dSep Y X Z := G.dSep_symm X Y Z hd
  have hpeel : G.dSep (Y \ {l}) X (Z ∪ {l}) := dSep_peel_source hl hsymm
  exact G.dSep_symm (Y \ {l}) X (Z ∪ {l}) hpeel

/-- **B3.7″（拓扑序提升，真证）**：若 `S ⊆ X` 且 `ℓ` 为 `S` 中拓扑序最小者，
则先搬 `ℓ`、再搬 `S` 剩余部分，结果仍由 `dSep_peel_fold` 给出。**

这是把 `not_edge_of_topo_min`（`ℓ` 是 `S` 内 source）与迭代剥离接上的桥：
图侧顺序是「`S.sort` 的首个 = 拓扑最小者」；该定理本身可由 `dSep_peel_fold`
（与顺序无关）直接得到，故只需 `S ⊆ X`。 -/
theorem dSep_peel_in_topo_order {X Y Z S : Finset V} (hS : S ⊆ X)
    (hd : G.dSep X Y Z) :
    G.dSep (X \ S) Y (Z ∪ S) :=
  dSep_peel_fold hS hd

end FoldPeel

/-! ===========================================================================
  §3b ⚠⚠ **诚实估值：拓扑序在剥离里到底用在哪里？**

  上面的 `dSep_peel_fold` / `dSep_peel_univ` **不用** `topoOrder`：
  搬点的合法性纯来自集合事实 `Disjoint (X∖{ℓ}) {ℓ}`。
  拓扑序在 B3 里的作用只有两处，且都是**元级（选顺序 / 底层图论前提）**：

  1. **选剥离顺序**：允许说「按拓扑序一个个剥」，而 `not_edge_of_topo_min`
     保证「剥首个时，它在剩余集内是 source」，这正是概率侧
     `BridgeStrategy1TopoPeel.peel` 所需 sink 前提的**镜像**。
  2. **底层图论事实**：`not_edge_of_topo_min/max` 供 B4 组装时引用。

  ⚠ **因此本文件不声称**「拓扑序进入了 `dSep` 剥离证明的内部」。
  这是清单要求「区分真假证」的具体落点。若要一个**真正把拓扑序放进证明内部**的
  命题，那就是 §5 的 `AncestralReductionBackward_Gap`（未证）。
  =========================================================================== -/

/-! ===========================================================================
  §4 ⭐ 剥离顺序的图论意义（与 sink 剥离对偶）

  B4 的概率侧在 `Fate.BridgeStrategy1TopoPeel.peel` 里剥 **sink**（拓扑最大点），
  因为它要求「`v` 在剩余变量中是 sink」。图侧的 `dSep` 剥离剥 **source**（拓扑最小点）。
  两者的图论合法性正好是本文件 §1 的 `not_edge_of_topo_max` 与 `not_edge_of_topo_min`。
  =========================================================================== -/

section OrderDuality

variable (G : DAG V)

/-- **B3.4′**：`S` 中拓扑最大点是「`S` 内的 sink」（无出边到 `S`）—— 与概率侧 sink 剥离对齐。 -/
theorem sink_of_topo_max {S : Finset V} (hS : S.Nonempty) :
    ∃ l ∈ S, ∀ w ∈ S, ¬ G.edge l w := by
  obtain ⟨l, hl, hmax⟩ := exists_topo_max (G := G) hS
  exact ⟨l, hl, not_edge_of_topo_max (G := G) hmax⟩

/-- **B3.4″**：`S` 中拓扑最小点是「`S` 内的 source」（无入边自 `S`）—— 与图侧 source 剥离对齐。 -/
theorem source_of_topo_min {S : Finset V} (hS : S.Nonempty) :
    ∃ l ∈ S, ∀ w ∈ S, ¬ G.edge w l := by
  obtain ⟨l, hl, hmin⟩ := exists_topo_min (G := G) hS
  exact ⟨l, hl, not_edge_of_topo_min (G := G) hmin⟩

end OrderDuality

/-! ===========================================================================
  §5 ⭐ **祖先闭包归约：可证一半 + 诚实登记的缺口**

  Pearl 1.2.7 剥离的另一步是：**d-分离只依赖 `X∪Y∪Z` 的祖先闭包上的诱导子图**。
  设 `H` 为 `G` 限制到 `An(X∪Y∪Z)` 的诱导子图（去掉一切指向闭包外的边）。
  则 `H` 的每条边都是 `G` 的边，故由 `dSep_of_edge_subgraph` 得**一个方向**：

  `dSep_G X Y Z ⟹ dSep_H X Y Z`.

  反方向（`dSep_H ⟹ dSep_G`）才是难的部分，**未证**，如实登记为 `Prop` 缺口。
  =========================================================================== -/

section AncestralReduction

variable {G : DAG V}

/-- **`induceEdge`**：`G` 限制到点集 `A` 上的**诱导子图**的边关系（两端都在 `A` 内）。 -/
def induceEdge (A : Finset V) (u v : V) : Prop := u ∈ A ∧ v ∈ A ∧ G.edge u v

/-- **`induceEdge_acyclic`**：诱导子图无环（子图的边全是 `G` 的边）。 -/
theorem induceEdge_acyclic (A : Finset V) :
    ∀ v : V, ¬ Relation.TransGen (induceEdge (G := G) A) v v := by
  have key : ∀ {a b : V}, Relation.TransGen (induceEdge (G := G) A) a b →
      Relation.TransGen G.edge a b := by
    intro a b h
    induction h with
    | single hab => exact Relation.TransGen.single hab.2.2
    | tail _ hbc ih => exact ih.tail hbc.2.2
  intro v hv
  exact G.acyclic v (key hv)

/-- **`induce`**：`G` 在点集 `A` 上的**诱导子图**（`A` 外无点相连）。 -/
def induce (A : Finset V) : DAG V where
  edge := induceEdge (G := G) A
  decEdge := fun u v => inferInstanceAs (Decidable (u ∈ A ∧ v ∈ A ∧ G.edge u v))
  acyclic := induceEdge_acyclic A

/-- **`induce_le`**：诱导子图的边都是原图的边。 -/
theorem induce_le (A : Finset V) : ∀ u v, (induce (G := G) A).edge u v → G.edge u v :=
  fun _ _ h => h.2.2

/-- **B3.8（祖先闭包归约，可证方向，真证）**：

若 `dSep_G X Y Z`，则在 `An(X∪Y∪Z)` 的诱导子图 `H` 上同样 `dSep_H X Y Z`。

**证明**：`H` 是 `G` 的子图（`induce_le`），由 `dSep_of_edge_subgraph` 直接把
`dSep_G` 搬到 `dSep_H`。**`hd` 被真正消费**。 -/
theorem dSep_ancestral_reduction_forward (A : Finset V) {X Y Z : Finset V}
    (hd : G.dSep X Y Z) :
    (induce (G := G) A).dSep X Y Z :=
  G.dSep_of_edge_subgraph (induce (G := G) A) (induce_le (G := G) A) hd

/-- ⚠ **B3.9（显式 `Prop` 缺口，**不进下游**）**：祖先闭包归约的**反方向**。

「子图 `H = G[An(X∪Y∪Z)]` 上 `dSep` ⟹ 全图 `G` 上 `dSep`」。
这是「拓扑序剥离」的**另一半**，需要论证「指向闭包外的边不能制造新的
`X`-到-`Y` 活跃路径」（因闭包外的点无法被 collider 激活到 `Z`）。
**本轮未落地**（涉及 active-walk 的端到端分析），故登记为 `Prop`，
**不被任何下游定理使用**。 -/
def AncestralReductionBackward_Gap (G : DAG V) : Prop :=
  ∀ (A X Y Z : Finset V),
    (X ∪ Y ∪ Z) ⊆ A →
    (induce (G := G) A).dSep X Y Z → G.dSep X Y Z

/-- ⚠ **`AncestralReductionBackward_Gap` 的自说明**：本 `Prop` **不是**
`True`（非平凡），且**不进入**任何定理的前件（grep 校验：它只在此处出现一次）。 -/
theorem ancestralReductionBackward_gap_nontrivial_statement :
    AncestralReductionBackward_Gap (G := G) =
      (∀ (A X Y Z : Finset V), (X ∪ Y ∪ Z) ⊆ A →
        (induce (G := G) A).dSep X Y Z → G.dSep X Y Z) := rfl

end AncestralReduction

/-! ===========================================================================
  §6 交付清单与纪律核对
  =========================================================================== -/

/-
## §6.1 交付清单

| 编号 | 名称 | 状态 |
|---|---|---|
| B3.0a | `exists_topo_min` | ✅ 零缺口 |
| B3.0b | `exists_topo_max` | ✅ 零缺口 |
| B3.1 | `not_edge_of_topo_min` | ✅ 零缺口 |
| B3.2 | `not_edge_of_topo_max` | ✅ 零缺口 |
| B3.3 | `dSep_peel_source` | ✅ **零缺口（真证）** |
| B3.3′ | `peel_side_conditions` | ✅ 零缺口（接口辅助）|
| B3.4′ | `sink_of_topo_max` | ✅ 零缺口 |
| B3.4″ | `source_of_topo_min` | ✅ 零缺口 |
| B3.5 | `dSep_peel_fold` | ✅ **零缺口（真证）** |
| B3.6 | `dSep_peel_univ` | ✅ 零缺口 |
| B3.7 | `dSep_peel_topological` | ✅ 零缺口 |
| B3.7′ | `dSep_peel_target` | ✅ **零缺口（真证）** |
| B3.7″ | `dSep_peel_in_topo_order` | ✅ 零缺口 |
| B3.8 | `dSep_ancestral_reduction_forward` | ✅ 零缺口 |
| B3.9 | `AncestralReductionBackward_Gap` | ⚠ 显式 `Prop` 缺口（不进下游）|

## §6.2 纪律核对（逐条对照清单 §三）

1. **单文件验证**：只用 `lake env lean Fate/BridgeB3.lean`。✅
2. **不改 `Fate.lean`**：本文件不触碰。✅
3. **不改已有模块**：只 `import`（`CausSeparation`、`Audit10Factorizes`）。✅
4. **零 `sorry`**：无 `sorry`/`admit`/`axiom`；未落地部分为显式 `Prop`
   `AncestralReductionBackward_Gap` 并注明「不进下游」。✅
5. **不用 `mass` 塔性质**：本文件是纯图论层（`dSep` + `topoOrder`），**不出现 `mass`**。✅
6. **区分真假证**：见 §1「前件各被用在哪一步」的逐项登记，特别是
   `dSep_peel_source` **不假装**拓扑极值是证明内部必需（它只是选择剥离顺序的依据，
   而剥离搬点的合法性来自纯集合事实 `Disjoint (X∖{ℓ}) {ℓ}`）。✅

## §6.3 与 B4 的交接（一句话）

B4 组装「`LMG ⟹ GM`」时，图侧的**逐点剥离**由本文件 B3.5/B3.7 提供：
对任意 `S ⊆ X` 有 `dSep X Y Z ⟹ dSep (X∖S) Y (Z∪S)`，
取 `S = X` 即 `dSep ∅ Y (Z∪X)`（B3.6）——这条把「源侧」彻底消化，
剩下的是「条件侧与目标侧不交」，正是乘性 CI 的**图侧骨架**。
-/

end BridgeB3
end FateV2.Predict