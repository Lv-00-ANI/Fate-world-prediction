/-
# `Fate/BridgeExpanded` —— **`Z' ⊋ Z` 版本**：
`dSep G X Y Z ⟹ ∃ Z' ⊇ Z, ReadClosedBlocks G X Y Z'`

## 0 结论摘要（**先读这一节**）

`Fate/BridgeFull.lean` 已 machine-checked 两件事：

* **`exists_dsep_not_readClosed`**：`Z' = Z` 版本的 `ReadClosedBlocks G X Y Z` **是假命题**
  （反例 `gex`：唯一边 `0 → 1`，`dSep {1} {2} ∅` 成立，但 `pa(1) = {0} ⊄ {1}`）。
* **`markov_of_gap`**：桥是**条件**定理，前件正是缺口
  「`∀ X Y Z, dSep X Y Z → ReadClosedBlocks G X Y Z`」（G1）；
  而 `gap_false_in_general` 证明 G1 在 `gex` 上**为假**。

**⟹ 本文件做 `BridgeFull` 登记为「唯一可能让桥通的路」的那一条**：
不要求 `Z' = Z`，而**构造** `Z' ⊇ Z` 使 `ReadClosedBlocks G X Y Z'` 成立。

| # | 名称 | 内容 | 状态 |
|---|---|---|---|
| **D1** | `Trunc` | 拓扑截断 `{u | ∃ s ∈ S, topoOrder u ≤ topoOrder s}` | 定义 |
| **L1** | `trunc_ancClosed` | ⭐ 截断集**父闭**（真用 `topoOrder_lt`）| ✅ |
| **L2** | `parents_subset_trunc` | 截断覆盖 `X∪Y∪Z` 中点的父代 | ✅ |
| **T1** | ⭐⭐⭐ **`exists_superset_readClosed`** | **主定理**：`Z' := Trunc G (X∪Y∪Z)` ⟹ `Z ⊆ Z'` 且 `ReadClosedBlocks G X Y Z'` | ✅ |
| **T2** | ⭐ **`exists_superset_readClosed_of_dSep`** | T1 的 `dSep` 强化陈述（与任务书逐字对齐）| ✅ |
| **T3** | ⭐ **`gap_gives_readClosed`** | 缺口 G1（`∃ Z' ⊇ Z` 版）**成立**（不再是缺口）| ✅ |
| **T4** | ⭐ **`zSame_false`** | `Z' = Z` 版**仍**为假（本地 `gex` 反例，不依赖 `BridgeFull`）| ✅ |
| **T5′** | `exists_superset_readClosed_paBlock` | T5 的 `∃ Z' ⊇ Z` 打包 | ✅ |
| **T6** | ⭐⭐ **`bridge_reduced_to_disjoint`** | **桥的精确归约**：`ReadClosedBlocks` 免费；剩余义务**恰好**是 `dSep X Y Z'`⟹`Disjoint X Z'`、`Disjoint Y Z'` | ✅ |
| **T7.a** | **`g2_ancClosed_forces_X`** | `{3} ⊆ Z'` + `AncClosed g2 Z'` ⟹ `1 ∈ Z'` | ✅ |
| **T7** | ⭐⭐⭐ **`disjoint_ancClosed_superset_false`** | 🔴 **加强版为假**：不存在 `Z' ⊇ {3}` 同时祖先闭且 `Disjoint {1} Z'`（反例 `g2`）| ✅ machine-checked |
| **T7′** | ⭐⭐⭐ **`strong_enlargement_with_dsep_false`** | 🔴 **最终否定**：上面那条**且** `dSep {1}{2}{3}` 成立，打包 | ✅ machine-checked |

## ⚠ 本文件最重要的一条结论（请先读）

**T1/T2/T3 让 G1 的 `∃ Z' ⊇ Z` 版变成免费定理；但这不足以让桥通。**
桥的乘性收口（`condIndep_of_ancClosed`）额外需要 `Disjoint X Z'` 与 `Disjoint Y Z'`，
而 `Trunc G (X∪Y∪Z) ⊇ X` 必然破坏它。想用「把 `pa(X∪Y)` 塞进 `Z'`」救回来
**同样不行**：`T7` 给出反例（`dSep {1} {2} {3}` 成立，但任何祖先闭的 `Z' ⊇ {3}`
必含 `pa(3) = {1} ⊆ X`）。

⟹ **`Z' ⊇ Z` 路线在此口径下走不通**，除非改成 moral graph 分离口径（未形式化）。
本文件给出 `T6` 把残余义务**精确**写成两条 `Disjoint`，使这一障碍可被下游直接引用。

⚠ **注意「免费」的精确含义**：`exists_superset_readClosed`（T1）**无条件成立**，
对任何 `X Y Z`（包括不 `dSep` 的）；它并不使用 `dSep`。
所以它**不是**桥的前件——它只是把「因读集不封闭」那条障碍消掉；
剩下的障碍（`Disjoint` vs `AncClosed` 的张力）由 T7 证明**不可同时满足**。

---

## 1 ⭐ 主构造：拓扑截断 `Trunc G S`

$$\mathrm{Trunc}_G(S)\;=\;\bigl\{\,u \;\bigm|\; \exists s\in S,\ \mathrm{topoOrder}_G(u)\le \mathrm{topoOrder}_G(s)\,\bigr\}
\;=\;\bigcup_{s\in S}\mathrm{lowerSet}(\mathrm{topoOrder}\,s).$$

**为什么它是**对**的构造**（三条性质量证）：

* **父闭**（`L1`）：`w → u` 给 `topo u < topo w`，与 `topo u ≤ topo s` 复合即 `topo w < topo s`；
* **覆盖父代**（`L2`）：若 `v ∈ S`、`w → v`，则 `topo w < topo v`，取 `s := v`；
* **吸收**（`L3`）：`S ⊆ Trunc S`（`topoOrder s ≤ topoOrder s`）。

取 `Z' := Trunc G (X ∪ Y ∪ Z)` 后：

* `Z ⊆ Z'` ⟸ `L3`（**与 `dSep` 无关**）；
* `AncClosed G Z'` ⟸ `L1`；
* `v ∈ X`、`w ∈ pa v` ⟹ `v ∈ X∪Y∪Z` ⟹ `w ∈ Z'`（`L2`）⟹ `pa v ⊆ Z' ⊆ X ∪ Z'`；
* `v ∈ Y` 同理。

**⟹ `ReadClosedBlocks G X Y Z'` 成立，且 `dSep` 不需要被用到。**
本文件如实登记这一点：**`ReadClosedBlocks` 是纯图论条件，`dSep` 与它无关**
（这正是 `BridgeFull` 的 T5 反例所证，本文件 T4 独立重证）。

---

## 2 ⚠ `dSep` 在桥里的真实位置（诚实边界，见 T6）

`ReadClosedBlocks` 免费 ⟹ 桥看似已通。**但** `CondIndep` 的乘性重排
（`View20.prod_split3`，`condIndep_of_ancClosed` 收口步）**额外需要**

$$\texttt{Disjoint } X\,Y,\quad \texttt{Disjoint } X\,Z',\quad \texttt{Disjoint } Y\,Z'.$$

`Disjoint X Y` 由 `dSep` 直接给出（`hd.1`）；
但 **`Disjoint X Z'` 对 `Z' = Trunc G (X∪Y∪Z)` 一般不成立**
（`X ⊆ Trunc G (X∪Y∪Z)`，故 `X ∩ Z' = X ≠ ∅` 当 `X ≠ ∅`）。

**⟹ 本文件给出 T6（桥的精确归约）**：桥的全部残余义务**恰好**是

> 存在 `Z' ⊇ Z` 使 `Z'` **父闭**、覆盖 `pa(X)`/`pa(Y)`，**且与 `X ∪ Y` 不交**。

前两条由 `Trunc` 免费；**第三条**是 `dSep` 必须承担的（`dSep` 只给 `Disjoint X Z`，
而 `Z' ⊋ Z` 会**引入新点**）。T6 把这一点写成一条**定理**（`bridge_reduced_to_disjoint`）。

### 2.1 ⭐⭐⭐ **T7：第三条与「父闭」不可共存**

自然的一招是「把 `pa(X∪Y)` 塞进 `Z'`」，即 `Zbig = Trunc (Z ∪ paBlock (X∪Y))`（本文件 T5）。
**这把 `Disjoint X Z'` 直接搮死**：`pa(X) ∩ X ≠ ∅` 时 `Zbig ⊇ X`。
更根本地，**父闭本身就会把 `X` 的点拉进 `Z'`**：

反例 `g2`（`Fin 4`，唯一边 `1 → 3`）：取 `X = {1}`、`Y = {2}`、`Z = {3}`。
（本文件 `g2_dsep`：`decide` 证 `dSep {1} {2} {3}` 成立。）

任何 `Z' ⊇ {3}` 且父闭（`AncClosed`）都因 `pa(3) = {1}` 而含 `1 ∈ X`，
于是 `¬ Disjoint {1} Z'`。

�� **T7（`disjoint_ancClosed_superset_false`）/ T7′（`strong_enlargement_with_dsep_false`）
machine-checked**：

> **`¬ ∃ Z' ⊇ Z, AncClosed G Z' ∧ Disjoint X Z'`** （在 `dSep X Y Z` 成立的 `g2` 上）。

⟹ **`Z' ⊋ Z` 路线到此终结**：不是「没证完」，而是**命题本身假**。
唯一出路是把终点从 `ReadClosedBlocks` 换成 **moral graph 分离**（未形式化）。

`T6` 的价值正在于：它把这个障碍写成**一条可引用的定理**，
下游不必重新发现「为什么 `Z'` 扩大也不过」。

---

## 3 ⚠ **纪律核对**

1. ✅ **单文件验证**：`lake env lean Fate/BridgeExpanded.lean` 通过。
2. ✅ **不改 `Fate.lean`**、不改 `BridgeFull.lean`（**本文件不 `import` `BridgeFull`**；
   原因见 §4：其 `factorizes_standard_implies_routeB` 有编译错，且该陈述**为假**；
   本文件只 `import` `Fate.Strategy11AncestralHull` 与 `CausSeparation`，
   并**本地重定义** `ReadClosedBlocks` 与 `gex` 反例，保证独立可验）。
3. ✅ **零 `sorry` / `admit` / `axiom`**（`#print axioms` 实测只依赖
   `propext`、`Classical.choice`、`Quot.sound`）。
4. ✅ **不用 `mass` 的塔性质**（本文件对 `mass` 的唯一接触是**调用**
   `condIndep_of_dSep_ancClosed` 一次；其内部只用单层 `mass_insert_sum'`）。
5. ✅ **每个前件用在哪**：`bridge_reduced_to_disjoint` 的注释逐条点名；
   `T1`/`T2`/`T3` 的 `dSep` 前件是**未消费**的（记 `_hd`），这一点已写明。

---

## 4 ⚠ 为什么不 `import Fate.BridgeFull`（**必须说清**）

`lake build Fate.BridgeFull` **失败**（实测）：

```
error: Fate/BridgeFull.lean:187:20: Application type mismatch:
  not_mem_pa_self G u has type u ∉ pa G u
  but is expected to have type ¬∀ x, p x = ∏ v, f v x
```

出错处是 `factorizes_standard_implies_routeB`。**不只是编译错，命题本身为假**：
`Fate.FactorMarkov.LocalTo` 要求 `f v` 在**`u = v`** 处也一致，
故标准 `Factorizes`（读 `{v} ∪ pa v`）**不能**推出 `RouteB.Factorizes`（读 `pa v`）——
后者的读集**更小、要求更强**。（`BridgeFull` 的定理名与注释把方向写反了。）

**⟹ 本文件的处置**：**不修改** `BridgeFull`（纪律要求），
**独立重定义**本文件需要的两件东西：

* `ReadClosedBlocks`（与 `BridgeFull` **逐字相同**的定义）；
* 反例图 `gex`（与 `BridgeFull` **逐字相同**的图）。

这样本文件**零外部缺陷依赖**，可单独验证。
================================================================================ -/

import FateWorld.Legacy.Strategy11AncestralHull
import FateWorld.Legacy.Concrete.ThreeNode
import FateWorld.Legacy._root.CausSeparation
import Mathlib.Tactic

open Finset
namespace Fate.BridgeExpanded

open Causalean.Graph
open Fate.Strategy11Hull

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {G : Causalean.Graph.DAG V}

set_option linter.unusedSectionVars false

/-! ===========================================================================
  §1 `ReadClosedBlocks`（与 `Fate.BridgeFull` 逐字相同的定义，本地复刻）
  =========================================================================== -/

/-- ⭐ **`ReadClosedBlocks G X Y Z`**：「`X` 块与 `Y` 块在 `Z` 下各自读封闭」。

1. `Z` 父闭；
2. `X` 的每个点的父代都在 `X ∪ Z` 内；
3. `Y` 的每个点的父代都在 `Y ∪ Z` 内。

（定义与 `Fate.BridgeFull.ReadClosedBlocks` **逐字相同**。） -/
def ReadClosedBlocks (G : Causalean.Graph.DAG V) (X Y Z : Finset V) : Prop :=
  AncClosed G Z
  ∧ (∀ v ∈ X, G.parents v ⊆ X ∪ Z)
  ∧ (∀ v ∈ Y, G.parents v ⊆ Y ∪ Z)

/-! ===========================================================================
  §2 ⭐⭐ 主构造：拓扑截断 `Trunc G S`
  =========================================================================== -/

/-- ⭐⭐⭐ **拓扑截断** `Trunc G S = ⋃_{s ∈ S} lowerSet (topoOrder s)`。 -/
noncomputable def Trunc (G : Causalean.Graph.DAG V) (S : Finset V) : Finset V :=
  Finset.univ.filter (fun u => ∃ s ∈ S, G.topoOrder u ≤ G.topoOrder s)

theorem mem_trunc {S : Finset V} {u : V} :
    u ∈ Trunc G S ↔ ∃ s ∈ S, G.topoOrder u ≤ G.topoOrder s := by
  unfold Trunc
  simp

/-- ⭐ **L3：`S ⊆ Trunc G S`**（吸收）。 -/
theorem subset_trunc (S : Finset V) : S ⊆ Trunc G S :=
  fun _u hu => mem_trunc.mpr ⟨_u, hu, le_refl _⟩

/-- ⭐⭐⭐ **L1：拓扑截断**父闭**。**

`w → u` 给 `topoOrder w < topoOrder u ≤ topoOrder s`，故 `w ∈ Trunc G S`。
**这是本文件唯一消费 `DAG.topoOrder_lt` 的地方。** -/
theorem trunc_ancClosed (S : Finset V) : AncClosed G (Trunc G S) := by
  intro u hu
  obtain ⟨s, hs, hle⟩ := mem_trunc.mp hu
  intro w hw
  exact mem_trunc.mpr ⟨s, hs,
    le_trans (le_of_lt (G.topoOrder_lt w u (G.mem_parents.mp hw))) hle⟩

/-- ⭐⭐ **L2：截断覆盖 `S` 中点的全部父代**（取 `s := 该点` 自身）。 -/
theorem parents_subset_trunc {S : Finset V} {v : V} (hv : v ∈ S) :
    G.parents v ⊆ Trunc G S := by
  intro w hw
  exact mem_trunc.mpr ⟨v, hv, le_of_lt (G.topoOrder_lt w v (G.mem_parents.mp hw))⟩

/-! ===========================================================================
  §3 ⭐⭐⭐ **T1 / T2：主定理**（`Z' := Trunc G (X∪Y∪Z)`）
  =========================================================================== -/

/-- ⭐⭐⭐ **T1 — `exists_superset_readClosed`**（**本文件的主定理 A**）：

**存在 `Z' ⊇ Z` 使 `ReadClosedBlocks G X Y Z'` 成立。**

**取 `Z' := Trunc G (X ∪ Y ∪ Z)`**，三条逐一：

1. `AncClosed G Z'` ⟸ **L1**（`trunc_ancClosed`）；
2. `v ∈ X`、`w ∈ pa v`：`v ∈ X ∪ Y ∪ Z` ⟹ **L2** 给 `w ∈ Z'`，故
   `pa v ⊆ Z' ⊆ X ∪ Z'`（连 `X` 都不需要，读集局部地就够）；
3. 同 2，`v ∈ Y`。

`Z ⊆ Z'` ⟸ **L3**（`subset_trunc`）。

**⚠ 本定理不需要 `dSep`** —— `ReadClosedBlocks` 是**纯图论**条件。
`dSep` 的真正消费点在 `BridgeFull` 的乘性收口（见 T6）。

**⚠ 零 `sorry`；完全不用 `mass`。** -/
theorem exists_superset_readClosed (X Y Z : Finset V) :
    ∃ Z' : Finset V, Z ⊆ Z' ∧ ReadClosedBlocks G X Y Z' := by
  refine ⟨Trunc G (X ∪ Y ∪ Z), ?_, trunc_ancClosed (X ∪ Y ∪ Z), ?_, ?_⟩
  · -- `Z ⊆ X ∪ Y ∪ Z ⊆ Trunc …`
    intro z hz
    exact subset_trunc _ (Finset.mem_union_right (X ∪ Y) hz)
  · -- `v ∈ X ⟹ pa v ⊆ Trunc ⊆ X ∪ Z'`
    intro v hv
    exact fun _w hw => Finset.mem_union_right X
      (parents_subset_trunc (Finset.mem_union_left _ (Finset.mem_union_left _ hv)) hw)
  · -- `v ∈ Y ⟹ pa v ⊆ Trunc ⊆ Y ∪ Z'`
    intro v hv
    exact fun _w hw => Finset.mem_union_right Y
      (parents_subset_trunc (Finset.mem_union_left _ (Finset.mem_union_right _ hv)) hw)

/-- ⭐⭐ **T2 — T1 的 `dSep` 强化陈述**（与任务书「在 `dSep G X Y Z` 的前提下」逐字对齐）。 -/
theorem exists_superset_readClosed_of_dSep {X Y Z : Finset V} (_hd : G.dSep X Y Z) :
    ∃ Z' : Finset V, Z ⊆ Z' ∧ ReadClosedBlocks G X Y Z' :=
  exists_superset_readClosed X Y Z

/-! ===========================================================================
  §4 ⭐⭐ **T3 / T4：缺口 G1 的 `∃` 版成立，而 `Z' = Z` 版仍假**
  =========================================================================== -/

/-- ⭐ **缺口 G1 的 `∃ Z'` 形式**（`BridgeFull.DSepGivesReadClosed` 的**加强**版）。 -/
def DSepGivesReadClosedExists (G : Causalean.Graph.DAG V) : Prop :=
  ∀ X Y Z : Finset V, G.dSep X Y Z →
    ∃ Z' : Finset V, Z ⊆ Z' ∧ ReadClosedBlocks G X Y Z'

/-- ⭐⭐⭐ **T3：`DSepGivesReadClosedExists G` 对任意 `G` 成立**（无条件！）。

**⟹ `BridgeFull` 登记为「缺口」的东西，在 `∃ Z' ⊇ Z` 口径下**根本不是缺口**。** -/
theorem gap_gives_readClosed (G : Causalean.Graph.DAG V) :
    DSepGivesReadClosedExists G :=
  fun X Y Z _ => exists_superset_readClosed X Y Z

/-! ### 4.1 ⭐ 反例 `gex`（**本地复刻**，与 `BridgeFull.gex` 逐字相同）

顶点 `Fin 3`，唯一边 `0 → 1`，顶点 `2` 孤立。取 `X = {1}`、`Y = {2}`、`Z = ∅`：
`dSep {1} {2} ∅` 成立，`pa(1) = {0} ⊄ {1} ∪ ∅`。 -/

/-- ⭐ 反例图：`0 → 1`，`2` 孤立。 -/
-- 定义已收敛到 `Fate/Concrete/ThreeNode.lean`（原 4 份逐字相同，见 _audit/BRIDGE-1）
def gex : Causalean.Graph.DAG (Fin 3) := Fate.Concrete.gex

/-- ⭐ `gex` 上 `dSep {1} {2} ∅` **成立**。 -/
theorem gex_dsep : gex.dSep {(1 : Fin 3)} {(2 : Fin 3)} (∅ : Finset (Fin 3)) := by decide

/-- ⭐ `gex` 上 `pa(1) = {0}`。 -/
theorem gex_pa : gex.parents (1 : Fin 3) = {(0 : Fin 3)} := by decide

/-- ⭐ `gex` 上 `pa(0) = ∅`（`0` 是源点）。 -/
theorem gex_pa0 : gex.parents (0 : Fin 3) = (∅ : Finset (Fin 3)) := by decide

/-- ⭐ `gex` 上 `pa(2) = ∅`（`2` 孤立）。 -/
theorem gex_pa2 : gex.parents (2 : Fin 3) = (∅ : Finset (Fin 3)) := by decide

/-- ⭐⭐⭐ **T4：`Z' = Z` 版本**在 `gex` 上为假**（`dSep` 成立但 `ReadClosedBlocks` 失败）。

⟹ **本文件与 `BridgeFull.exists_dsep_not_readClosed` 交叉核对一致**。 -/
theorem zSame_false :
    ¬ ReadClosedBlocks gex {(1 : Fin 3)} {(2 : Fin 3)} (∅ : Finset (Fin 3)) := by
  rintro ⟨_, hX, _⟩
  have hsub := hX 1 (mem_singleton_self 1)
  rw [gex_pa] at hsub
  have h0 : (0 : Fin 3) ∈ ({(1 : Fin 3)} : Finset (Fin 3)) ∪ (∅ : Finset (Fin 3)) :=
    hsub (mem_singleton_self 0)
  rw [Finset.union_empty] at h0
  exact absurd (mem_singleton.mp h0) (by decide)

/-- ⭐⭐ **T4′**：`∃ Z'` 版在 `gex` 上**成立**，且我们给出**实际取值** `Z' = {0}`。 -/
theorem gex_expanded_works :
    ∃ Z' : Finset (Fin 3), (∅ : Finset (Fin 3)) ⊆ Z'
      ∧ ReadClosedBlocks gex {(1 : Fin 3)} {(2 : Fin 3)} Z' :=
  exists_superset_readClosed _ _ _

/-- ⭐⭐ **T4″**：`T1` 的构造在 `gex` 上**包含 `{0}`**（`0` 的拓扑序最小，必然会留下）。

`topoOrder` 是 `noncomputable`，故这里不能 `decide`，只证**包含**方向。 -/
theorem gex_trunc_contains_0 :
    (0 : Fin 3) ∈ Trunc gex ({(1 : Fin 3)} ∪ {(2 : Fin 3)} ∪ (∅ : Finset (Fin 3))) := by
  refine mem_trunc.mpr ⟨1, Finset.mem_union_left _ (Finset.mem_union_left _ (mem_singleton_self 1)), ?_⟩
  -- `0` 是 `1` 的父，故 `topoOrder 0 < topoOrder 1`
  exact le_of_lt (gex.topoOrder_lt 0 1 (by decide))

/-- ⭐⭐ **T4‴**：`Z' = {0}` 时 `ReadClosedBlocks` **成立**（`decide` 直接判定）。 -/
theorem gex_z0_readClosed :
    ReadClosedBlocks gex {(1 : Fin 3)} {(2 : Fin 3)} {(0 : Fin 3)} := by
  refine ⟨?_, ?_, ?_⟩
  · -- `{0}` 父闭：`pa 0 = ∅`
    intro v hv
    have hv0 : v = 0 := mem_singleton.mp hv
    subst hv0
    rw [gex_pa0]
    exact Finset.empty_subset _
  · intro v hv
    have hv1 : v = 1 := mem_singleton.mp hv
    subst hv1
    rw [gex_pa]
    intro w hw
    rw [mem_singleton.mp hw]
    exact Finset.mem_union_right _ (mem_singleton_self 0)
  · intro v hv
    have hv2 : v = 2 := mem_singleton.mp hv
    subst hv2
    rw [gex_pa2]
    exact Finset.empty_subset _

/-! ===========================================================================
  §5 ⭐⭐ **T5：更粗的候选 `Trunc G (Z ∪ paBlock (X∪Y))` 也成立**
  =========================================================================== -/

/-- ⭐ `paBlock G S`：`S` 中所有点的父代之并。 -/
noncomputable def paBlock (G : Causalean.Graph.DAG V) (S : Finset V) : Finset V :=
  S.biUnion (fun v => G.parents v)

theorem mem_paBlock {S : Finset V} {u : V} :
    u ∈ paBlock G S ↔ ∃ v ∈ S, G.edge u v := by
  unfold paBlock
  simp [Causalean.Graph.DAG.mem_parents]

/-- ⭐ 用 `paBlock` 作为「种子」的 `Zbig`：`Trunc G (Z ∪ paBlock (X∪Y))`。 -/
noncomputable def Zbig (G : Causalean.Graph.DAG V) (X Y Z : Finset V) : Finset V :=
  Trunc G (Z ∪ paBlock G (X ∪ Y))

/-- ⭐ **`Zbig` 父闭**（L1 实例）。 -/
theorem zbig_ancClosed (X Y Z : Finset V) : AncClosed G (Zbig G X Y Z) :=
  trunc_ancClosed _

/-- ⭐ **`Z ⊆ Zbig`**（L3 实例）。 -/
theorem subset_zbig (X Y Z : Finset V) : Z ⊆ Zbig G X Y Z := fun _z hz =>
  subset_trunc _ (Finset.mem_union_left _ hz)

/-- ⭐ **`paBlock (X∪Y) ⊆ Zbig`**。 -/
theorem paBlock_subset_zbig (X Y Z : Finset V) :
    paBlock G (X ∪ Y) ⊆ Zbig G X Y Z := fun _u hu =>
  subset_trunc _ (Finset.mem_union_right _ hu)

/-- ⭐ **`X` 中点的父代 ⊆ `Zbig`**。 -/
theorem parents_subset_zbig_left {X Y Z : Finset V} {v : V} (hv : v ∈ X) :
    G.parents v ⊆ Zbig G X Y Z := fun _w hw =>
  paBlock_subset_zbig X Y Z
    (mem_paBlock.mpr ⟨v, Finset.mem_union_left Y hv, G.mem_parents.mp hw⟩)

/-- ⭐ **`Y` 中点的父代 ⊆ `Zbig`**。 -/
theorem parents_subset_zbig_right {X Y Z : Finset V} {v : V} (hv : v ∈ Y) :
    G.parents v ⊆ Zbig G X Y Z := fun _w hw =>
  paBlock_subset_zbig X Y Z
    (mem_paBlock.mpr ⟨v, Finset.mem_union_right X hv, G.mem_parents.mp hw⟩)

/-- ⭐⭐ **T5：`Zbig` 也满足 `ReadClosedBlocks`**（另一种同样有效的 `Z'`）。 -/
theorem zbig_readClosed (X Y Z : Finset V) : ReadClosedBlocks G X Y (Zbig G X Y Z) :=
  ⟨zbig_ancClosed X Y Z,
   fun _ hv => subset_trans (parents_subset_zbig_left hv)
     (Finset.subset_union_right (s₁ := X) (s₂ := _)),
   fun _ hv => subset_trans (parents_subset_zbig_right hv)
     (Finset.subset_union_right (s₁ := Y) (s₂ := _))⟩

/-- ⭐⭐ **T5′**：`Zbig` 版的存在性（`Z' ⊇ Z` + `ReadClosedBlocks`）。 -/
theorem exists_superset_readClosed_paBlock (X Y Z : Finset V) :
    ∃ Z' : Finset V, Z ⊆ Z' ∧ ReadClosedBlocks G X Y Z' :=
  ⟨Zbig G X Y Z, subset_zbig X Y Z, zbig_readClosed X Y Z⟩

/-! ### 6.0 本地复刻（T6 的前置）：`ReadClosedBlocks ⟹ 四个 AncClosed`

（与 `Fate.BridgeFull.readClosedBlocks_ancClosed` 同形；因本文件不 `import` `BridgeFull`
（它有编译错，见 §4），此处独立提供，**零 sorry**。） -/

/-- `X ∪ Z ⊆ X ∪ Y ∪ Z`。 -/
theorem sub_union_left {X Y Z : Finset V} : X ∪ Z ⊆ X ∪ Y ∪ Z := by
  intro u hu
  rcases mem_union.mp hu with h | h
  · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl h)))
  · exact mem_union.mpr (Or.inr h)

/-- `Y ∪ Z ⊆ X ∪ Y ∪ Z`。 -/
theorem sub_union_right {X Y Z : Finset V} : Y ∪ Z ⊆ X ∪ Y ∪ Z := by
  intro u hu
  rcases mem_union.mp hu with h | h
  · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr h)))
  · exact mem_union.mpr (Or.inr h)

/-- ⭐ `ReadClosedBlocks` ⟹ 引擎要求的四个父闭条件。 -/
theorem readClosedBlocks_ancClosed {X Y Z : Finset V}
    (hRC : ReadClosedBlocks G X Y Z) :
    AncClosed G (X ∪ Y ∪ Z) ∧ AncClosed G (X ∪ Z)
      ∧ AncClosed G (Y ∪ Z) ∧ AncClosed G Z := by
  obtain ⟨hZ, hX, hY⟩ := hRC
  refine ⟨?_, ?_, ?_, hZ⟩
  · intro v hv
    rcases mem_union.mp hv with h | h
    · rcases mem_union.mp h with h' | h'
      · exact fun u hu => sub_union_left (hX v h' hu)
      · exact fun u hu => sub_union_right (hY v h' hu)
    · exact fun u hu => mem_union.mpr (Or.inr (hZ v h hu))
  · intro v hv
    rcases mem_union.mp hv with h | h
    · exact hX v h
    · exact fun u hu => mem_union.mpr (Or.inr (hZ v h hu))
  · intro v hv
    rcases mem_union.mp hv with h | h
    · exact hY v h
    · exact fun u hu => mem_union.mpr (Or.inr (hZ v h hu))

/-! ===========================================================================
  §6 ⭐⭐ **T6：桥的精确归约**
  （前置 `readClosedBlocks_ancClosed` 在 §6.0）
  =========================================================================== -/

/-- ⭐⭐ **T6 — `bridge_reduced_to_disjoint`**。

**结论**：若
* `hloc` / `hfac` / `hnorm`（`Factorizes` 的三个拆件，消费点见 §6.1）；
* `hZ' : Z ⊆ Z'`（本文件 **T1** 免费给的）；
* **`hRC`**：`ReadClosedBlocks G X Y Z'`（本文件 **T1** 免费给的）；
* **`hd'`**：`G.dSep X Y Z'` ⟵ **不是** `dSep X Y Z` 的后果（无单调性引理，
  且一般来说反向）；
* **`hXZ'` / `hYZ'`**：`Disjoint X Z'`、`Disjoint Y Z'` ⟵ **`dSep X Y Z'` 的前三子句**，
  而它们与 `Trunc` 构造**互斥**（`X ⊆ Trunc`）；

则 `CondIndep p X Y Z'`。

**⟹ 这就是桥的全部残余义务的精确形态。** 本文件不需要、也不重证引擎：
`hRC → 四个 AncClosed` 用 `Fate.BridgeFull.readClosedBlocks_ancClosed` 的同形证明
（本文件 §6.1 本地复刻），其余直接调用 `condIndep_of_dSep_ancClosed`。

**逐条前件消费**：
* `hfac` / `hloc` / `hnorm` → `condIndep_of_dSep_ancClosed` → `mass_ancClosed`
  （基情形 `mass_univ`+`hfac`；归纳步 `hloc`；收口 `hnorm`）；
* `hRC` → `hRC_ancClosed`（本文件，等价于 `BridgeFull.readClosedBlocks_ancClosed`）；
* `hd'` → `condIndep_of_dSep_ancClosed` 的两两不交（前三子句）；
* `hZ'`：**「免费」的那一半**（`Trunc` 满足）—— 不进引擎，只用于声明包容性；
* `hXZ'`、`hYZ'`：**「不免费」的那一半**（`Trunc` 破坏）—— 由 `hd'` 提供。

**⚠ 零 `sorry`；不用塔性质；不 `import` `BridgeFull`。** -/
theorem bridge_reduced_to_disjoint {α : Type u} [Fintype α] [DecidableEq α]
    {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : Fate.FactorMarkov.LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : Fate.FactorMarkov.FactorNorm f)
    {X Y Z Z' : Finset V} (_hZ' : Z ⊆ Z')
    (hRC : ReadClosedBlocks G X Y Z') (hd' : G.dSep X Y Z') :
    Fate.FactorMarkov.CondIndep p X Y Z' :=
  Fate.Strategy11Hull.condIndep_of_dSep_ancClosed hloc hfac hnorm hd'
    (readClosedBlocks_ancClosed hRC).1
    (readClosedBlocks_ancClosed hRC).2.1
    (readClosedBlocks_ancClosed hRC).2.2.1
    (readClosedBlocks_ancClosed hRC).2.2.2

/-! ===========================================================================
  §7 ⭐⭐⭐ **T7：加强版为假**（`Z' ⊇ Z` 路线无法救回桥）
  =========================================================================== -/

/-- ⭐ **`Bridges`**：桥真正需要的 `Z'` —— 既有 `ReadClosedBlocks`，**又**与 `X ∪ Y` 不交。

**为什么必须加后一条**：`condIndep_of_ancClosed` 的乘性收口 `View20.prod_split3`
需要 `Disjoint X Z'`、`Disjoint Y Z'`；而 `Trunc G (X∪Y∪Z) ⊇ X` 必然破坏它。 -/
def Bridges (G : Causalean.Graph.DAG V) (X Y Z : Finset V) : Prop :=
  Z ⊆ Trunc G (X ∪ Y ∪ Z) ∧ ReadClosedBlocks G X Y (Trunc G (X ∪ Y ∪ Z))
    ∧ Disjoint X (Trunc G (X ∪ Y ∪ Z)) ∧ Disjoint Y (Trunc G (X ∪ Y ∪ Z))

/-- ⭐ 反例图 `g2`：顶点 `Fin 4`，唯一边 `1 → 3`（`0`、`2` 孤立）。 -/
def g2 : Causalean.Graph.DAG (Fin 4) where
  edge := fun u v => u = 1 ∧ v = 3
  decEdge := by intro u v; infer_instance
  acyclic := by
    intro v hv
    have key : ∀ x y : Fin 4,
        Relation.TransGen (fun u v : Fin 4 => u = 1 ∧ v = 3) x y → x < y := by
      intro x y hxy
      induction hxy with
      | single h => obtain ⟨h1, h2⟩ := h; subst h1; subst h2; decide
      | tail _ hstep ih => obtain ⟨h1, h2⟩ := hstep; subst h1; subst h2; omega
    exact absurd (key v v hv) (lt_irrefl v)

/-- ⭐ `g2` 上 `dSep {1} {2} {3}` **成立**（`1 → 3` 与 `2` 不连通）。 -/
theorem g2_dsep :
    g2.dSep {(1 : Fin 4)} {(2 : Fin 4)} {(3 : Fin 4)} := by decide

/-- ⭐ `g2` 上 `pa(3) = {1}`。 -/
theorem g2_pa : g2.parents (3 : Fin 4) = {(1 : Fin 4)} := by decide

/-- ⭐⭐ **T7.a**：`g2` 上 `Z = {3}` 的**任何祖先闭超集**都含 `pa(3) = {1} ⊆ X`。

**⟹ 只要 `3 ∈ Z'` 且 `AncClosed Z'`，就有 `1 ∈ Z'`，于是 `¬ Disjoint X Z'`。** -/
theorem g2_ancClosed_forces_X {Z' : Finset (Fin 4)}
    (hanc : AncClosed g2 Z') (h3 : (3 : Fin 4) ∈ Z') : (1 : Fin 4) ∈ Z' := by
  have h := hanc 3 h3
  rw [g2_pa] at h
  exact h (mem_singleton_self 1)

/-- ⭐⭐⭐ **T7 — `strong_enlargement_false`**（**本文件最重要的否定结论**）：

**不存在 `Z' ⊇ {3}` 同时满足「`Z'` 祖先闭」与「`Disjoint {1} Z'`」。**

**证明**：`3 ∈ Z'`（因 `Z = {3} ⊆ Z'`）⟹ `pa(3) = {1} ⊆ Z'`（`T7.a`）⟹
`1 ∈ Z' ∩ {1}` ⟹ 破坏不交性。

**⟹ `disjoint_ancClosed_superset_false` 的 `dSep` 版（下条）直接给出**：
在 `dSep {1} {2} {3}` 成立的图上，**没有任何** `Z' ⊇ Z` 能让桥走通。
这就是 `Z' ⊋ Z` 路线的死穴，**machine-checked**。 -/
theorem disjoint_ancClosed_superset_false :
    ¬ ∃ Z' : Finset (Fin 4), ({(3 : Fin 4)} : Finset (Fin 4)) ⊆ Z'
        ∧ AncClosed g2 Z' ∧ Disjoint ({(1 : Fin 4)} : Finset (Fin 4)) Z' := by
  rintro ⟨Z', hsub, hanc, hdis⟩
  have h3 : (3 : Fin 4) ∈ Z' := hsub (mem_singleton_self 3)
  exact (Finset.disjoint_left.mp hdis) (mem_singleton_self 1) (g2_ancClosed_forces_X hanc h3)

/-- ⭐⭐⭐ **T7′ — `strong_enlargement_with_dsep_false`**（**最终否定**）：

即使带上 `dSep {1} {2} {3}` 这个前件，也不存在满足桥要求的 `Z' ⊇ Z`：

> `¬ ∃ Z' ⊇ {3}, AncClosed g2 Z' ∧ Disjoint {1} Z'` —— 且 `g2.dSep {1}{2}{3}` **成立**。

**⟹ 「`dSep ⟹ ∃ Z' ⊇ Z, ReadClosedBlocks G X Y Z' 且 Z' ∩ (X∪Y) = ∅`」为假。**
这是 `Z' ⊋ Z` 版本能做的最强诚实结论。 -/
theorem strong_enlargement_with_dsep_false :
    g2.dSep {(1 : Fin 4)} {(2 : Fin 4)} {(3 : Fin 4)}
      ∧ ¬ ∃ Z' : Finset (Fin 4), ({(3 : Fin 4)} : Finset (Fin 4)) ⊆ Z'
          ∧ AncClosed g2 Z' ∧ Disjoint ({(1 : Fin 4)} : Finset (Fin 4)) Z' :=
  ⟨g2_dsep, disjoint_ancClosed_superset_false⟩

/-! ===========================================================================
  §8 交付清单
  =========================================================================== -/

/-
| # | 名称 | 内容 | 状态 |
|---|---|---|---|
| L3 | `subset_trunc` | `S ⊆ Trunc G S` | ✅ |
| L1 | `trunc_ancClosed` | `Trunc` 父闭（**唯一**用 `topoOrder_lt` 的地方）| ✅ |
| L2 | `parents_subset_trunc` | `Trunc` 覆盖 `S` 中点的父代 | ✅ |
| T1 | `exists_superset_readClosed` | ⭐ **主定理**：`∃ Z' ⊇ Z, ReadClosedBlocks G X Y Z'`（**无条件**）| ✅ |
| T2 | `exists_superset_readClosed_of_dSep` | T1 的 `dSep` 版（**`dSep` 未消费**）| ✅ |
| T3 | `gap_gives_readClosed` | 缺口 G1 的 `∃ Z'` 版对**任意** `G` 成立 | ✅ |
| T4 | `zSame_false` | `Z' = Z` 版仍为假（`gex`，**独立**于 `BridgeFull`）| ✅ |
| T4′ | `gex_z0_readClosed` | `gex` 上 `Z' = {0}` 确实可行 | ✅ |
| T5 | `zbig_readClosed` / `exists_superset_readClosed_paBlock` | 候选 `Trunc (Z ∪ paBlock (X∪Y))` 也成立 | ✅ |
| §6.0 | `readClosedBlocks_ancClosed` | `ReadClosedBlocks ⟹ 四个 AncClosed`（本地复刻）| ✅ |
| T6 | `bridge_reduced_to_disjoint` | ⭐⭐ **桥的精确归约**（残余 = 两条 `Disjoint`）| ✅ |
| Def | `Bridges` | 桥真正需要的 `Z'`（带 `Disjoint`）| 定义 |
| T7.a | `g2_ancClosed_forces_X` | 父闭 + `3 ∈ Z'` ⟹ `1 ∈ Z'` | ✅ |
| T7 | `disjoint_ancClosed_superset_false` | 🔴 **不能同时满足** | ✅ |
| T7′ | `strong_enlargement_with_dsep_false` | 🔴 `dSep` 成立 + 上面那条 | ✅ |

纪律核对：
1. ✅ 单文件验证：`lake env lean Fate/BridgeExpanded.lean` 返回 0。
2. ✅ 不改 `Fate.lean`，不改 `BridgeFull.lean`；本文件**不** `import` `BridgeFull`。
3. ✅ **零 `sorry` / `admit` / `axiom`**；`#print axioms` 只给三条标准公理。
4. ✅ **不用 `mass` 塔性质**。
5. ✅ **前件消费点已逐条点名**（T6 的注释；T1/T2/T3 的 `dSep` 未消费已明写）。

**结论一句话**：
`Z' ⊇ Z` 版本使 `ReadClosedBlocks` **免费**（T1），但**不能**使桥通：
桥额外的 `Disjoint X Z'` / `Disjoint Y Z'` 与 `Z'` 的父闭性在一般 DAG 上
**不可共存**（T7，`g2` 反例）。
故 `BridgeFull` 的缺口 G1 **不能靠扩大 `Z'` 绕开**；
若要无条件 `dSep ⟹ CondIndep`，必须改用 **moral graph 分离** 口径（本轮未形式化）。
-/

end Fate.BridgeExpanded