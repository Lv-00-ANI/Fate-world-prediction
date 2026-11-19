/-
# 视角 11（第三种口径）：图 ⟹ 概率 —— **拓扑前缀块拆分 + 纤维钉死**

> **⚠ 标题与内容已按 2026-06 P0 修复对齐**：原标题写「分离器做前父代」，
> 但「分离器存在」（旧 G1）与「`pa ℓ ⊆ X ∪ Z`」（旧 G3）**经机器证伪**，
> 已删除；本文件实际交付的是**前缀块拆分主定理**（M1/M2），
> 其证明只消费前缀父闭性 + `LocalTo` + `hfac` + `FactorNorm`，**不消费 `SplitterAt`**。

## 0 硬约束（从已证伪的路线继承）

| 事实 | 出处 | 对本题的约束 |
|---|---|---|
| `mass S (mass T p) x ≠ mass (S∪T) p x` | `DAGFactorizationGeneral` T24 `tower_property_false` | **禁止**任何 `mass` 嵌套 |
| 连 `S ⊆ T` 方向的塔也假（`mass` 非归一化）| `TowerAudit` A3 | 同上 |
| `CondMulLike`（集合口径）作为桥终点**退化** | `View20` 的 `massCondMulLike_degenerate` | 终点必须**非退化** |
| 既有「dSep ⟹ CondMul」从未真用 `dSep` 第 4 子句 | `GlobalMarkovMinimal` K8 / `MarkovBridgeAncestral` M8 | 桥必须真消费可达性 |

**本文件全程只用不含嵌套的 `mass` 工具**：`mass_insert_sum`（放开一坐标求和）、
`mass_congr`（边缘只依赖被固定坐标）、`mass_mul`（分离律）以及
`FateV2.Predict.NonemptyFree2.Strategy11.peel_lower`（前缀引擎，其内部也只做**单层**求和）。**无塔。**

## 1 视角 11 的数学构造（与库存里两种既有「视角 11」**都不同**）

库存里已存在两条角度不同的路线（`Strategy11TopoPrefix`／`Strategy11FiberPinned`，
后者走「拓扑前缀 + 纤维钉死」，覆盖**前缀形**分离集）。**本文件走第三条**：

> **把「纤维钉死」的重排（旧称「分离器做父代」）落成前缀块拆分**：
> 乘积按 `X`／`Y`／`Z` 三块用 `Finset.prod_union` 拆开，再用前缀父闭性
> 把每块的求值点从 `w` 换成 `x`／`y`。
>
> ⚠ 原设想中的「分离器」`SplitterAt` 只保留为**定义**（G2/G4 两条真引理），
> 其**存在性**与「`pa ℓ ⊆ X ∪ Z`」**为假**（见 §1.2 修复记录与反例）。

### 1.1 为什么要换到源点侧

* 既有的 `sink` 剥离（`FactorMarkov.sink_peel`）要用 `FactorNorm` +
  「sink 无出边 ⟹ 唯一读者」；前缀引擎（`peel_lower`）用**纯序**取代了 sink 假设
  ——这是思路 11 的**既有**贡献，本文件**复用**它（见 §3 的 Block B）。
* 但 `peel_lower` 的**代价**是只覆盖**前缀形**分离集（`X∪Z`、`Y∪Z`、`Z` 都是
  `topoOrder` 前缀）。**任意 `dSep` 三元组不是前缀形**，这是 `VIEW11_TOPO_PREFIX.md`
  §4 诚实登记的边界。

### 1.2 本文件的构造：`sourceSplitter`（源点 + 分离器）

**定义（`SplitterAt`）**：`ℓ` 是 `X` 中拓扑序**最小**的点，
且 `Z ∪ {ℓ}` 在 `G` 中**不让任何点指向 `ℓ`**：

```
SplitterAt G Z X ℓ  :=  (ℓ ∈ X) ∧ (∀ w ∈ X, topoOrder ℓ ≤ topoOrder w) ∧
                        (∀ u ∈ insert ℓ Z, ¬ G.edge u ℓ)
```

**⚠⚠ 2026-06 修复记录（重要，必读）**

本轮 P0 修复时，下面两条**旧声称的图论事实经机器证伪，已删除**（不保留 `sorry`）：

| 旧编号 | 旧陈述 | 状态 |
|---|---|---|
| **G1**（旧 `splitter_exists`） | `Disjoint X Z ⟹ X.Nonempty ⟹ ∃ ℓ, SplitterAt G Z X ℓ` | ❌ **假** |
| **G3**（旧 `splitter_parents`） | `SplitterAt G Z X ℓ ⟹ G.parents ℓ ⊆ X ∪ Z` | ❌ **假** |

**G1 的反例**（2 点链 `0 → 1`，`X = {1}`，`Z = {0}`）：`Disjoint X Z` 与
`X.Nonempty` 均成立，但 `0 ∈ insert 1 {0}` 且 `0 → 1`，故第三子句不成立，
**不存在** `SplitterAt G {0} {1} ·`。原「证明」把 `u ∈ Z` 一支当成 `l ∈ Z`
（笔误），因而无效：`Z ∪ {ℓ}` 中来自 `Z` 的点**仍可指向 `ℓ`**，
`Disjoint X Z` 对此毫无约束。

**G3 的反例**（同一条链，`X = {1}`，`Z = ∅`，`ℓ = 1`）：`G.parents 1 = {0}`，
而 `X ∪ Z = {1}`，故 `{0} ⊄ {1}`。`SplitterAt` 的第三子句只给出
「`pa ℓ` 与 `Z ∪ {ℓ}` 不交」，**不给** 「`pa ℓ ⊆ X ∪ Z`」。

⟹ **本文件不再声称任何形如「`SplitterAt` 存在」或「`pa ℓ ⊆ X ∪ Z`」的引理。**
下文真正保留、且经 Lean 核验的只有：`SplitterAt` 的**定义**、
`splitter_not_mem_Z`（G2）、`splitter_bb_child_mem`（G4），
以及 **§1/§3 的前缀乘积主定理**（P1–P3、M1、M2）。
后三者的证明**完全不消费** `SplitterAt`，故不受上述证伪影响。

### 1.3 主定理（Block A，本文件唯一的「图做功」）

**Block A（前缀块拆分 + 父闭换求值点 ⟹ 纤维钉死，非退化终点）**：

$$\mathrm{mass}(X\cup Y\cup Z)\,p\ w \cdot \mathrm{mass}\,Z\,p\,w
  \;=\; \mathrm{mass}(X\cup Z)\,p\ x \cdot \mathrm{mass}(Y\cup Z)\,p\ y$$

在「`X∪Y∪Z`、`X∪Z`、`Y∪Z`、`Z` 均为前缀」且 `x|_{X∪Z}=w|_{X∪Z}`、
`y|_{Y∪Z}=w|_{Y∪Z}` 时（M1 `splitter_mass_split`）。

> 右端两个 `mass` 吃**不同**的求值点 `x ≠ y`，故不是「三个 `Disjoint` + `ring`」
> 能得到的退化形态：M1 **真消费** `hfac` + `LocalTo` + 前缀父闭性。

**⚠ 已撤回的旧声称**：原头部列出的 **G5 `splitter_not_bbReachable`** 与
**N1 `splitter_dSep_endpoint`**（「Block A′，真消费 `dSep` 第 4 子句」）
**在本文件中从未存在**（无对应 `theorem`），本轮如实撤回该声称。
本文件**不**声称消费了 `dSep` 的第 4 子句。

### 1.4 交付清单

| 编号 | 定理 | 内容 | 状态 |
|---|---|---|---|
| — | `SplitterAt` | 分离器**定义**（仅定义，无存在性声称） | ✅ |
| **G2** | `splitter_not_mem_Z` | `ℓ ∉ Z`（由 `SplitterAt` 与 `Disjoint X Z`） | ✅ |
| **G4** | `splitter_bb_child_mem` | `ℓ → c ⟹ (c, fromParent) ∈ bbInit X` | ✅ |
| **P1** | `isPrefix_parent_closed` | 前缀对取父封闭（复用序） | ✅ |
| **P2** | `mass_prefix` | 前缀上 `mass` = 局部因子之积（**复用引擎**） | ✅ |
| **P3** | `prod_pinned` | 纤维钉死乘积重排（块拆分，纯代数） | ✅ |
| **M1** | **`splitter_mass_split`** | **Block A 主定理（非退化终点）** | ✅ |
| **M2** | `splitter_condIndep` | `x=y=w` 退化回收为 `CondMulLike`（集合口径） | ✅ |
| ~~G1~~ | ~~`splitter_exists`~~ | 旧声称「`Disjoint X Z ⟹ ∃ ℓ, SplitterAt`」 | ❌ **假，已删除** |
| ~~G3~~ | ~~`splitter_parents`~~ | 旧声称「`pa ℓ ⊆ X ∪ Z`」 | ❌ **假，已删除** |
| ~~G5~~ | ~~`splitter_not_bbReachable`~~ | 旧声称，**从未实现**，已撤回 | ❌ 不存在 |
| ~~N1~~ | ~~`splitter_dSep_endpoint`~~ | 旧声称，**从未实现**，已撤回 | ❌ 不存在 |

**⚠ 无 `sorry` / 无 `axiom`。** 未闭合的（任意非前缀 `dSep`；`dSep` 第 4 子句的消费）
**显式登记在此**，不登记为定理。
-/

import FateWorld.FateV2.Predict.Strategy11TopoPrefix
import FateWorld.FateV2.Predict.View20GraphToProb
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false

namespace FateV2.Predict

open FateV2.Modeling
namespace View11Splitter

open Finset
open FateV2.Modeling.Graph
open FateV2.Modeling.Graph.DAG
open FateV2.Predict.DAGFactorization
open FateV2.Predict.FactorMarkov

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {G : FateV2.Modeling.Graph.DAG V}

/-!
  # Predict · View11SplitterChain

  ## 迁移登记
  - 来源：`FateWorld/Legacy/View11SplitterChain.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Strategy11TopoPrefix, View20GraphToProb
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 **拓扑前缀**（复用 `Strategy11` 的 `lowerSet` 链；本文件只重述两条要用的事实）
  ===========================================================================-/

/-- **`isPrefix`**：`S` 是 `topoOrder` 的前缀（某个 `k` 的 `lowerSet`）。 -/
def isPrefix (G : FateV2.Modeling.Graph.DAG V) (S : Finset V) : Prop :=
  ∃ k : ℕ, S = FateV2.Predict.NonemptyFree2.Strategy11.lowerSet G k

/-- **P1 `isPrefix_parent_closed`**：前缀对「取父」封闭。

这是**纯序**事实：`v ∈ lowerSet k` 且 `u → v` ⟹ `topoOrder u < topoOrder v < k`。
**真用 `G.edge` / `topoOrder_lt`**（不是哑变量）。 -/
theorem isPrefix_parent_closed {S : Finset V} (hS : isPrefix G S) :
    ∀ v ∈ S, G.parents v ⊆ S := by
  obtain ⟨k, rfl⟩ := hS
  intro v hv u hu
  rw [FateV2.Predict.NonemptyFree2.Strategy11.mem_lowerSet] at hv ⊢
  exact lt_trans (G.topoOrder_lt u v (G.mem_parents.mp hu)) hv

/-- **P2 `mass_prefix`**：前缀上的 `mass` = 局部因子之积。

**直接复用引擎** `FateV2.Predict.NonemptyFree2.Strategy11.peel_lower`（其证明内部只用**单层**
`mass_insert_sum'`，**无塔**）。本文件不重证、不改动引擎。 -/
theorem mass_prefix {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    [Nonempty V] (hnorm : FactorNorm f)
    {S : Finset V} (hS : isPrefix G S) :
    ∀ x, mass S p x = ∏ v ∈ S, f v x := by
  obtain ⟨k, rfl⟩ := hS
  exact FateV2.Predict.NonemptyFree2.Strategy11.peel_lower hloc hfac hnorm k

/-! ===========================================================================
  §2 **分离器（splitter）：定义 + 两条真引理（G2、G4）**

  ⚠ **本节的 G1（存在性）与 G3（`pa ℓ ⊆ X ∪ Z`）经机器证伪，已删除**，
  见文件头「2026-06 修复记录」中的反例。**§3 的主定理不消费 `SplitterAt`。**
  ===========================================================================-/

/-- **`SplitterAt G Z X ℓ`**：`ℓ` 是 `X` 中拓扑序**最小**的点，且 `Z ∪ {ℓ}`
（即「`Z` 与 `ℓ` 自己」）中**没有点指向 `ℓ`**。

⚠ **这只是定义**。其**存在性**（旧 G1）与「`pa ℓ ⊆ X ∪ Z`」（旧 G3）
**均为假**（见文件头反例），本文件不再声称。 -/
def SplitterAt (G : FateV2.Modeling.Graph.DAG V) (Z X : Finset V) (l : V) : Prop :=
  l ∈ X ∧ (∀ w ∈ X, G.topoOrder l ≤ G.topoOrder w) ∧
    (∀ u : V, u ∈ insert l Z → ¬ G.edge u l)

/-- 拓扑序最小值选择器（显式 `@` 应用以固定隐式参数）。 -/
theorem exists_topo_min (X : Finset V) (hX : X.Nonempty) :
    ∃ l ∈ X, ∀ w ∈ X, G.topoOrder l ≤ G.topoOrder w :=
  Finset.exists_min_image X G.topoOrder hX

/-- **G2 `splitter_not_mem_Z`**：分离器不在 `Z` 中。 -/
theorem splitter_not_mem_Z {Z X : Finset V} {l : V} (hXZ : Disjoint X Z)
    (hl : SplitterAt G Z X l) : l ∉ Z :=
  (Finset.disjoint_left.mp hXZ) hl.1

/-- **G4 `splitter_bb_child_mem`**：`ℓ → c` ⟹ `(c, fromParent) ∈ bbInit X`。

这是 **`ℓ` 的唯一出射通道**：`ℓ ∈ X`，故 `ℓ` 的孩子以徽章 `fromParent` 进入前沿。 -/
theorem splitter_bb_child_mem {X : Finset V} {l c : V}
    (hlX : l ∈ X) (hc : G.edge l c) :
    ((c, BBDir.fromParent) : BBState V) ∈ G.bbInit X := by
  unfold bbInit
  refine Finset.mem_biUnion.mpr ⟨l, hlX, ?_⟩
  apply Finset.mem_union_left
  exact Finset.mem_map.mpr ⟨c, (G.mem_children).mpr hc, rfl⟩

/-! ===========================================================================
  §3 ⭐⭐⭐ Block A：**前缀块拆分 + 父闭 ⟹ 纤维钉死（非退化终点）**

  ⚠ 本节**不消费** `SplitterAt`（旧 G1/G3 已证伪）。真正的图做功是
  **前缀父闭性**（P1）+ `LocalTo`（`hloc`）+ 因子分解（`hfac`）+ `FactorNorm`。
  ===========================================================================-/

/-- **P3 `prod_pinned`**：纤维钉死乘积重排。

设 `X,Y,Z` 两两不交、`X∪Z` 与 `Y∪Z` 都是前缀。若 `w` 在 `X∪Z` 上等于 `x`、
在 `Y∪Z` 上等于 `y`（`x,y,w` **可互不相同**），则

$$\prod_{v\in X\cup Y\cup Z} f\,v\,w
  = \Bigl(\prod_{v\in X} f\,v\,x\Bigr)\Bigl(\prod_{v\in Y} f\,v\,y\Bigr)
    \Bigl(\prod_{v\in Z} f\,v\,w\Bigr).$$

**⚠ 这是「不用塔」的正确替代**：把乘积按**块**拆开（`Finset.prod_union`），
再用 P1（父闭）+ `LocalTo` 把每块的求值点从 `w` 换成 `x`（或 `y`）。
**不做 `mass ∘ mass`**。 -/
theorem prod_pinned {f : V → (V → α) → ℝ} (hloc : LocalTo G f)
    {X Y Z : Finset V} (hpXZ : isPrefix G (X ∪ Z)) (hpYZ : isPrefix G (Y ∪ Z))
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    {w x y : V → α}
    (hwx : ∀ u, u ∈ X ∪ Z → w u = x u) (hwy : ∀ u, u ∈ Y ∪ Z → w u = y u) :
    (∏ v ∈ X ∪ Y ∪ Z, f v w)
      = (∏ v ∈ X, f v x) * (∏ v ∈ Y, f v y) * (∏ v ∈ Z, f v w) := by
  have h1 : Disjoint (X ∪ Y) Z := by
    rw [Finset.disjoint_union_left]; exact ⟨hXZ, hYZ⟩
  rw [Finset.prod_union h1, Finset.prod_union hXY]
  have hX : (∏ v ∈ X, f v w) = ∏ v ∈ X, f v x := by
    refine Finset.prod_congr rfl fun v hv => ?_
    refine hloc v _ _ fun u hu => ?_
    rcases hu with rfl | hu
    · exact hwx u (Finset.mem_union_left _ hv)
    · exact hwx u (isPrefix_parent_closed hpXZ v (Finset.mem_union_left _ hv) hu)
  have hY : (∏ v ∈ Y, f v w) = ∏ v ∈ Y, f v y := by
    refine Finset.prod_congr rfl fun v hv => ?_
    refine hloc v _ _ fun u hu => ?_
    rcases hu with rfl | hu
    · exact hwy u (Finset.mem_union_left _ hv)
    · exact hwy u (isPrefix_parent_closed hpYZ v (Finset.mem_union_left _ hv) hu)
  rw [hX, hY]

/-- **M1 ⭐⭐⭐ `splitter_mass_split`**：**Block A 主定理（非退化终点）**。

在同一组前缀假设下（`X∪Y∪Z`、`X∪Z`、`Y∪Z`、`Z` 均为前缀），对**任意**
`x y w` 满足 `x|_{X∪Z}=w|_{X∪Z}`、`y|_{Y∪Z}=w|_{Y∪Z}`，有

$$\mathrm{mass}(X\cup Y\cup Z)\,p\,w\cdot\mathrm{mass}\,Z\,p\,w
  =\mathrm{mass}(X\cup Z)\,p\,x\cdot\mathrm{mass}(Y\cup Z)\,p\,y .$$

**⭐ 右端两个 `mass` 吃不同的点 `x ≠ y`** ⟹ 它**不能**由「三个 `Disjoint` + `ring`」
得到（`View20` 的退化判据 D20 明确排除），**必须**用 `hfac` + 父闭性
⟹ **真消费图**，是**非退化**终点。

**证明（五步）**：
1. 四次 `mass_prefix`（P2）把四个 `mass` 换成 `∏ f`（**同一个 `p`、同一个 `f`**）；
2. 把 `∏_{X∪Z}` 与 `∏_{Y∪Z}` 按 `Finset.prod_union` 在各自求值点处拆成 `X`,`Z` / `Y`,`Z`；
3. 把 `Z` 上的因子在两个点之间的差异消掉（`Z` 是前缀，父闭，`x|_{X∪Z}=w|_{X∪Z}`）；
4. `prod_pinned`（P3）重排 `∏_{X∪Y∪Z} f w`；
5. `ring` 收口。

**⚠ 全程无 `mass ∘ mass`。** -/
theorem splitter_mass_split {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    [Nonempty V] (hnorm : FactorNorm f)
    {X Y Z : Finset V}
    (hpXYZ : isPrefix G (X ∪ Y ∪ Z))
    (hpXZ : isPrefix G (X ∪ Z)) (hpYZ : isPrefix G (Y ∪ Z)) (hpZ : isPrefix G Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    {x y w : V → α} (hxXZ : ∀ u, u ∈ X ∪ Z → x u = w u)
    (hyYZ : ∀ u, u ∈ Y ∪ Z → y u = w u) :
    mass (X ∪ Y ∪ Z) p w * mass Z p w = mass (X ∪ Z) p x * mass (Y ∪ Z) p y := by
  have hwx : ∀ u, u ∈ X ∪ Z → w u = x u := fun u hu => (hxXZ u hu).symm
  have hwy : ∀ u, u ∈ Y ∪ Z → w u = y u := fun u hu => (hyYZ u hu).symm
  rw [mass_prefix hloc hfac hnorm hpXYZ w, mass_prefix hloc hfac hnorm hpXZ x,
      mass_prefix hloc hfac hnorm hpYZ y, mass_prefix hloc hfac hnorm hpZ w]
  have hx_split : (∏ v ∈ X ∪ Z, f v x) = (∏ v ∈ X, f v x) * (∏ v ∈ Z, f v x) :=
    Finset.prod_union hXZ
  have hy_split : (∏ v ∈ Y ∪ Z, f v y) = (∏ v ∈ Y, f v y) * (∏ v ∈ Z, f v y) :=
    Finset.prod_union hYZ
  have hZxw : (∏ v ∈ Z, f v x) = (∏ v ∈ Z, f v w) := by
    refine Finset.prod_congr rfl fun v hv => ?_
    refine hloc v _ _ fun u hu => ?_
    rcases hu with rfl | hu
    · exact hxXZ u (Finset.mem_union_right _ hv)
    · exact hxXZ u (Finset.mem_union_right _ (isPrefix_parent_closed hpZ v hv hu))
  have hZyw : (∏ v ∈ Z, f v y) = (∏ v ∈ Z, f v w) := by
    refine Finset.prod_congr rfl fun v hv => ?_
    refine hloc v _ _ fun u hu => ?_
    rcases hu with rfl | hu
    · exact hyYZ u (Finset.mem_union_right _ hv)
    · exact hyYZ u (Finset.mem_union_right _ (isPrefix_parent_closed hpZ v hv hu))
  rw [hx_split, hy_split, hZxw, hZyw,
      prod_pinned hloc hpXZ hpYZ hXY hXZ hYZ hwx hwy]
  ring

/-- **M2 `splitter_condIndep`**：`x = y = w` 时 M1 退化为**集合口径**条件独立。

**⚠ 这是退化终点**（`View20` 判据 D20 已判 `CondMulLike` 退化），本文件**只**用它
**回收**引擎价值，**不**把它当桥的终点（桥的终点是 M1 与 N1）。 -/
theorem splitter_condIndep {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    [Nonempty V] (hnorm : FactorNorm f)
    {X Y Z : Finset V}
    (hpXYZ : isPrefix G (X ∪ Y ∪ Z))
    (hpXZ : isPrefix G (X ∪ Z)) (hpYZ : isPrefix G (Y ∪ Z)) (hpZ : isPrefix G Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    MarkovEquivalence.CondMulLike X Y Z p := by
  intro x
  exact splitter_mass_split hloc hfac hnorm hpXYZ hpXZ hpYZ hpZ hXY hXZ hYZ
    (fun _ _ => rfl) (fun _ _ => rfl)

end View11Splitter
end FateV2.Predict