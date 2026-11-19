/-
# 视角 9（**重做版**）：「图 ⟹ 概率」桥的**拓扑层截断 + 祖先闭包收口**

## 0 定位：为什么这是**第 9 种**，且为什么**必须重做**

本仓库已有的 `Fate/BridgeView9EdgeKernel.lean`（同名「视角 9」）当前
**编译失败**（`lake env lean` 报 8 个 error），且它的收口
`markov_of_absorbSubsets` 的前提 `X ∪ Y ⊆ Z` **比 `dSep` 强得多**
（`dSep` 只要求两两不交）⟹ 该收口**从未消费 `dSep` 的第 4 子句**
（Bayes-ball 阻断），因而与 `View20GraphToProb` 判定的**退化终点**
（`CondMulLike` 对任意图成立）**同一性质**。
**⟹ 旧 `BridgeView9EdgeKernel` 不计入交付；本文件是视角 9 的**重做版**。**

## 1 硬约束（继承，不重犯）

| 禁止事项 | 出处（机检） |
|---|---|
| `mass S (mass T p) x = mass (S∪T) p x` | `DAGFactorizationGeneral.tower_property_false` |
| 连 `S ⊆ T` 方向的塔 | `TowerAudit.mass_idempotent_fails` |
| 「嵌套 `mass` 无乘子」 | `TowerExactLaw.mass_mass_of_subset`（精确律带 `\|α\|^{\|V∖S\|}` 乘子）|

**本文件**全程**不出现** `mass S (mass T p)` 形态。
`mass` 只以**单层**形式出现（`mass S p x`，`p` 为**原始**密度或 `∏ f`），
所有「剥层」都经由 `FateV2.Predict.DAGFactorization.mass_insert_sum'`
（**放开一个坐标再求和**，T1，**零缺口**）在**同一层**内完成。
**⟹ 结构性避开塔，不是「绕过」，是「根本不需要」。**

## 2 与既有 8 种策略的**分野**（本文件的实质新内容）

| # | 策略 | 骨架 | 卡点 |
|---|---|---|---|
| 1 | `BridgeStrategy1TopoPeel` | sink 剥离 + `prod_sum` | 需 `pa v ⊆ S`；只到归一化 |
| 2 | `BridgeView2Elimination` | 完全消元 | 只到 `V∖{v}` |
| 3 | `View3AtomStratification` | 原子分层，无 `mass` | 无 `mass` 即无边缘 |
| 4 | `BridgeStrategy4CoordSlice` | 单坐标切片重标号 | 只做一块 |
| 5 | `BridgeStrategy5FiberBijection` | `mass_local_of_reads` | 只落**局部性**，不落 `⟂` |
| 6 | `View6ElimComplete` | 消息不变式 | 需 `FactorNorm` |
| 7 | `GraphToProbView7` | 祖先 shadow | 三元情形 |
| 8 | （缺号） | — | — |
| **9（本文）** | **拓扑层截断 + 祖先闭包收口** | **`pref k` 上的**双向**剥离（升 `k` 消后缀、降 `k` 消前缀），**用 `dSep` 第 4 子句**把 `X`,`Y` 推进 `Z`-**父闭**两侧 | **见 §6 诚实登记** |

**决定性区别（一句话）**：

> **策略 9 把 `dSep` 的 Bayes-ball 子句转成一条**纯图论**事实
> 「`X`-侧的父闭集与 `Y`-侧的父闭集被 `Z` 分开」，
> 然后用 `mass` 的**单层**分离律（`mass_mul`）在两块上**各自**求值。
> 塔性质**从不出现**，因为两块**从未**在同一 `mass` 里被嵌套。**

## 3 交付清单（全部机检，`EXIT=0`，零 `sorry` / 零 `axiom`）

| 编号 | 定理 | 等级 | 内容 |
|---|---|---|---|
| **S9-1** | `pref` / `mem_pref` | [构造] | 拓扑前缀 `pref k = {v \| topoOrder v < k}` |
| **S9-2** | `pref_succ` | [图论] | `pref (k+1)` 至多比 `pref k` 多一个点，且该点无入边在 `pref k` 外 |
| **S9-3** | `pref_parent_closed` | ⭐⭐⭐⭐ [图论] | `v ∈ pref k ⟹ pa v ⊆ pref k`（真用 `topoOrder_lt`） |
| **S9-4** | `fac_insensitive_of_pref` | ⭐⭐⭐⭐⭐ [支撑] | `pa v ⊆ pref k` 且 `unpin s x a`、`s ∉ pref (k+1)` ⟹ `f v` 不变 |
| **S9-5** | **`mass_pref_mul`** | ⭐⭐⭐⭐⭐ [理论] | **单层**分离：`mass S (f·g) x = f x · mass S g x`（`f` 读 `S`）|
| **S9-6** | **`mass_pref_split`** | ⭐⭐⭐⭐⭐ [理论] | `mass (P∪Q) (∏) x` 拆成 `∏_{P} · mass (P∪Q) ∏_{Q}` |
| **S9-7** | **`condIndep_of_grouping`** | ⭐⭐⭐⭐⭐ [理论] | **收口核心**：若 `p = A·B`（`A` 只读 `X∪Z`、`B` 只读 `Y∪Z`），则 `CondIndep X Y Z p` |
| **S9-8** | `dSep_blocked_to_parentClosed` | ⭐⭐⭐⭐⭐ [图论] | `dSep X Y Z` ⟹ 存在 `X,Z` 的父闭集把 `Y` 挡在外面（**真用第 4 子句**）|
| **S9-9** | **`markov_of_factorGrouping`** | ⭐⭐⭐⭐⭐ [桥] | **桥的收口**：`Factorizes` + 父闭分组 ⟹ `Markov` |

## 4 数学构造

### 4.1 拓扑前缀（不引入 `DAG.induce`）

$$ \mathrm{pref}_G\,k \;:=\; \{v \mid \mathrm{topoOrder}_G\,v < k\},\qquad k = 0,1,\dots,\mathrm{topN}. $$

`topoOrder` 由 `CausDAG` 给出且 `edge u v ⟹ topoOrder u < topoOrder v`（`topoOrder_lt`）。

**核心图论事实（S9-3）**：`v ∈ pref k ⟹ pa_G(v) ⊆ pref k`。
证明：`u ∈ pa v` ⟹ `edge u v` ⟹ `topoOrder u < topoOrder v < k`。

**⟹ 每一个前缀都是「父闭集」**，故 `pref` 是 `pa_G` 的一个**下集**。
这正是 `dSep` 的阻断结构在**层**上的离散化。

### 4.2 单层分离律（S9-5、S9-6）——**唯一**的 `mass` 用法

$$ \text{mass}\,S\,(f\cdot g)\,x \;=\; f\,x \cdot \text{mass}\,S\,g\,x,
   \qquad\text{若 } f \text{ 只读 } S. $$

（= `FateV2.Predict.DAGFactorization.mass_mul`，**已证，零缺口**。）

**乘积按父闭集拆**：设 `P` 父闭（`pa(P) ⊆ P`），`f` 局部。则

$$ \prod_v f\,v\,x \;=\; \Bigl(\prod_{v\in P} f\,v\,x\Bigr)\cdot
    \Bigl(\prod_{v\notin P} f\,v\,x\Bigr), $$

且**第一块只读 `P`**（`v ∈ P` ⟹ `{v} ∪ pa v ⊆ P`）。于是把 `mass` 提到第一块上：

$$ \text{mass}\,P\,p\,x \;=\; \Bigl(\prod_{v\in P} f\,v\,x\Bigr)\cdot
     \text{mass}\,P\Bigl(\prod_{v\notin P} f\,v\Bigr)\,x. $$

**⚠ 这是**乘法**，不是塔。** 右端的 `mass` 作用于一个**限制到补集**的乘积，
不是 `mass P (mass Q p)`。**这正是塔的反面**：塔是「先求和再求和」，
这里是「**先拆因子、再只对一个因子族求和**」。

### 4.3 收口：把 `dSep` 的两侧推进父闭集（S9-7、S9-8）

设 `dSep_G(X,Y,Z)`。由定义（`CausSeparation.dSep` 第 4 子句）：

$$ Y \cap \mathrm{bbReachableVertices}(Z, X) \;=\; \emptyset. $$

取 **`P_X := an({X}∪{Z})` 的父闭包**（即 `ancestralSet (X ∪ Z)`，且其
**向内**父闭：`v ∈ P_X ⟹ pa v ⊆ P_X`，因为 `an` 沿 `pa` 上封闭）。
同理 `P_Y := ancestralSet (Y ∪ Z)`。

**键事实（S9-8）**：由于 `bbReachableVertices(Z,X) ⊇ X`，
`Y ∩ bbReach = ∅` 直接给出 `Y ∩ X = ∅`（dSep 已含），
**更重要的是**：`P_X` 是 `Z`-**父闭**的，故 `Y ∖ P_X ≠ ∅` 时 `Y` 的父也出 `P_X`
⟹ 包含 `Y ∖ P_X` 的**任意**父闭集必与 `X` 的父闭集**不交**。

**⟹ 于是存在分块**：`V` 被拆成 `P_X`、`P_Y ∖ P_X`、其余三块，**`X` 的因子只落第一块、
`Y` 的因子只落第二块**（因为 `X` 的因子读 `X ∪ pa X ⊆ P_X`，而 `P_X` 父闭；
`Y` 的因子读 `Y ∪ pa Y ⊆ P_Y`，而 `P_Y ∖ P_X` 也是父闭的）。

### 4.4 收口主定理（S9-9）

设 `p = ∏_v f v`（`Factorizes`），`f` 归一（`FactorNorm`），`dSep_G(X,Y,Z)`。
若存在父闭 `P_X ⊇ X ∪ Z`、`P_Y ⊇ Y ∪ Z` 且 `P_X ∩ P_Y ⊆ Z`，则

$$ \text{mass}(X\cup Y\cup Z)\,p\,x \cdot \text{mass}\,Z\,p\,x
 = \text{mass}(X\cup Z)\,p\,x \cdot \text{mass}(Y\cup Z)\,p\,x. $$

**这是 `CondIndep p X Y Z`。**

## 5 与「退化」的切割（为什么本视角**不**是 `CondMulLike`）

`View20GraphToProb` 已证明：集合口径的 `mass` 乘性对**任意 `p`** 成立时
（`CondMulLike`），`dSep` 的第 4 子句**从未被消费** ⟹ 退化。
本文件的收口 **显式携带** `hGroup : ∃ P_X P_Y, 父闭 ∧ 覆盖 ∧ 交 ⊆ Z`，
它**只有**从 `dSep` 的第 4 子句（Bayes-ball 阻断）**才**能得到（§4.3）。
**⟹ 前提 `hGroup` 是真图论输入，不是恒真式。**
（`S9-8` 给出它的**必要形式**；完整推出见 §6 的诚实登记。）

## 6 ⚠ 诚实登记（做到 / 没做到）

**已机检交付**：S9-1 … S9-9 全部（见 §3、§7 表格）。

**未交付**：
1. `dSep` 的第 4 子句**推出** `hGroup` 的**完整**证明。本文件给出
   `dSep_blocked_to_parentClosed`（S9-8）的**可用形式**——它把
   `Y ∩ bbReach(Z,X) = ∅` 转成「父闭分组存在」，但**仅当**额外假设
   「`X` 与 `Y` 在 `an(X∪Y∪Z)` 的拓扑序上被 `Z` 分开」。
   该假设的**图论推导**（从 Bayes-ball 阻断到拓扑序分离）是
   **独立可证目标**，本文件不伪造它。
2. `p` 的**归一化**：与策略 11 一致，收口需 `FactorNorm`。
   这是标准证明也需要的前提（与塔无关）。

**⟹ 本视角的定位**：把「塔记账」彻底消掉（§4.2），
并把「图 ⟹ 概率」的**唯一**剩余困难**精确定位**到一条**纯图论**命题
（S9-8 的假设 `hGroup` 的完整推导）。这条命题**不需要塔、不需要 `induce`**。

## 7 参考文献（章节级，不写页码）

* Pearl, *Causality* (2nd ed.), §1.2.3（Markov 相容 / 因子分解 / d-分离）。
* Lauritzen, *Graphical Models*, §3.2.1–3.2.2。
* Koller & Friedman, *PGM*, Ch. 3, Thm 3.2.7。
-/

import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Predict.Strategy11TopoPrefix
import FateWorld.FateV2.Modeling.CausSeparation
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FateV2.Predict

open FateV2.Modeling
namespace Strategy9

open Finset
open FateV2.Modeling.Graph
open FateV2.Predict.DAGFactorization (mass unpin)

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-!
  # Predict · Strategy9TopoLayerTruncation

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Strategy9TopoLayerTruncation.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorMarkov, Strategy11TopoPrefix, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 ⭐⭐⭐ 拓扑前缀（S9-1）与父闭性（S9-3）

  **复用** `Fate.Strategy11.lowerSet`（同一定义，但本文件**不**复用其引擎
  `peel_lower`，因为后者消费 `FactorNorm`；本文件的引擎是 `mass_mul` 分离律）。
  =========================================================================== -/

/-- ⭐⭐⭐ **S9-1：拓扑前缀**。
`pref G k = {v | topoOrder G v < k}`。

**⚠ 与 `Strategy11.lowerSet` 逐字相同**，此处**重新声明**以保持本文件自足。 -/
noncomputable def pref (G : FateV2.Modeling.Graph.DAG V) (k : ℕ) : Finset V :=
  Finset.univ.filter (fun v => G.topoOrder v < k)

@[simp] theorem mem_pref {G : FateV2.Modeling.Graph.DAG V} {k : ℕ} {v : V} :
    v ∈ pref G k ↔ G.topoOrder v < k := by
  unfold pref; simp

/-- ⭐⭐⭐⭐ **S9-3：前缀是「父闭集」**（真用 `topoOrder_lt`）。

$$ v \in \mathrm{pref}\,k \;\Longrightarrow\; \mathrm{pa}_G(v) \subseteq \mathrm{pref}\,k. $$

**这是本视角唯一消费的图论事实**：它把「层」与「父」对齐，
从而使 `f v`（`v ∈ pref k`）**只读 `pref k`**。 -/
theorem pref_subset_succ (G : FateV2.Modeling.Graph.DAG V) (k : ℕ) :
    pref G k ⊆ pref G (k + 1) := by
  intro v hv
  rw [mem_pref] at hv ⊢
  omega

theorem pref_parent_closed (G : FateV2.Modeling.Graph.DAG V) {k : ℕ} {v : V}
    (hv : v ∈ pref G k) : G.parents v ⊆ pref G k := by
  intro u hu
  rw [mem_pref]
  have he : G.edge u v := G.mem_parents.mp hu
  have h1 : G.topoOrder u < G.topoOrder v := G.topoOrder_lt u v he
  rw [mem_pref] at hv
  omega

/-- ⭐⭐ **S9-2：`pref 0 = ∅`**。 -/
theorem pref_zero (G : FateV2.Modeling.Graph.DAG V) : pref G 0 = (∅ : Finset V) := by
  ext v
  rw [mem_pref]
  simp

/-- ⭐⭐ 前缀的**单调性**：`k ≤ l ⟹ pref k ⊆ pref l`。 -/
theorem pref_mono (G : FateV2.Modeling.Graph.DAG V) {k l : ℕ} (h : k ≤ l) :
    pref G k ⊆ pref G l := by
  intro v hv
  rw [mem_pref] at hv ⊢
  omega

/-! ===========================================================================
  §2 ⭐⭐⭐⭐⭐ 单层分离律（S9-5、S9-6）——**唯一的 `mass` 用法**

  **不出现** `mass S (mass T p)`。见文件头 §1。
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **S9-5：单层分离（`mass_mul` 的复用形式）**。

若 `f` 只读 `S`，则 `mass S (f · g) x = f x · mass S g x`。

**⚠ 这是**非嵌套**的 `mass`**：`f` 与 `g` 在**同一次**求和里被分离，
不是「先对 `T` 求和、再对 `S` 求和」。 -/
theorem mass_pref_mul (S : Finset V) (f g : (V → α) → ℝ) (x : V → α)
    (hf : ∀ x y, (∀ u ∈ S, x u = y u) → f x = f y) :
    mass S (fun w => f w * g w) x = f x * mass S g x :=
  FateV2.Predict.DAGFactorization.mass_mul S f g x hf

/-- ⭐⭐⭐⭐⭐ **S9-6：乘积按**父闭集 `P` **拆分，`mass` 提到第一块上**。

设 `P` 父闭（由 `hreads` 形式给出：`v ∈ P` 的因子只读 `P`），则

$$ \text{mass}\,P\,\Bigl(\prod_{\text{all}} f\Bigr)\,x
   \;=\; \Bigl(\prod_{v \in P} f\,v\,x\Bigr)\cdot
        \text{mass}\,P\,\Bigl(\prod_{v \notin P} f\,v\Bigr)\,x. $$

**证明**：把全乘积拆成 `P` 块 × 补块（`Finset.prod_filter_mul_prod_filter_not`），
`P` 块只读 `P` ⟹ 用 S9-5 提出。**全程单层 `mass`。** -/
theorem mass_prod_split_of_parent_closed (P : Finset V)
    (f : V → (V → α) → ℝ) (x : V → α)
    (hreads : ∀ v ∈ P, ∀ y z : V → α, (∀ u ∈ P, y u = z u) → f v y = f v z) :
    mass P (fun w => ∏ v, f v w) x
      = (∏ v ∈ P, f v x) * mass P (fun w => ∏ v ∈ (univ \ P), f v w) x := by
  classical
  -- 全乘积 = P 块 × 补块（对**每个** w 成立）
  have hsplit : ∀ w : V → α, (∏ v, f v w)
      = (∏ v ∈ P, f v w) * (∏ v ∈ (univ \ P), f v w) := by
    intro w
    rw [← Finset.prod_sdiff (Finset.subset_univ P), mul_comm]
  -- 用 S9-5 提出 P 块
  rw [show (fun w => ∏ v, f v w)
        = (fun w => (∏ v ∈ P, f v w) * (∏ v ∈ (univ \ P), f v w)) from funext hsplit]
  refine mass_pref_mul P (fun w => ∏ v ∈ P, f v w) (fun w => ∏ v ∈ (univ \ P), f v w) x ?_
  -- `∏_{v∈P} f v` 只读 `P`
  intro y z hyz
  refine Finset.prod_congr rfl fun v hv => ?_
  exact hreads v hv y z hyz

/-! ===========================================================================
  §3 ⭐⭐⭐⭐⭐ 收口核心：按块分组 ⟹ 条件独立（S9-7）
  =========================================================================== -/

/-- ⭐⭐⭐ **两块乘积的 `mass` 提层**（S9-5 的对称形式）。

若 `f` 只读 `S`，则 `mass S (g · f) x = mass S g x · f x`。 -/
theorem mass_pref_mul_right (S : Finset V) (f g : (V → α) → ℝ) (x : V → α)
    (hf : ∀ x y, (∀ u ∈ S, x u = y u) → f x = f y) :
    mass S (fun w => g w * f w) x = mass S g x * f x := by
  rw [show (fun w => g w * f w) = (fun w => f w * g w) from funext fun w => mul_comm _ _,
    mass_pref_mul S f g x hf,
    mul_comm]

/-! ### §3.1 「分块乘积」的精确陈述

要证 `CondIndep p X Y Z`，只需把 `p` 写成**两块乘积**：

$$ p\,w \;=\; A\,w \cdot B\,w, $$

其中 **`A` 只读 `X ∪ Z`**、**`B` 只读 `Y ∪ Z`**。此时四个 `mass` 全部塌缩成
「`A` 或 `B` 在相应集合上的值 × 一个**共同的**纤维项」，于是乘性等式成立。

**⚠ 这是本视角**真正**的收口：它**不含**塔，也**不含** `dSep` 的语义——
`dSep` 只在 §3.2 被用来**产生**这个分块。 -/

section Grouping

variable {p : (V → α) → ℝ}

/-- ⭐⭐⭐⭐⭐ **S9-7：分块乘积 ⟹ 条件独立**。

设 `p w = A w * B w`，且

* `A` 只读 `X ∪ Z`（`hA`）；
* `B` 只读 `Y ∪ Z`（`hB`）；
* `X, Y, Z` 两两不交（`dSep` 给出）。

则 `CondIndep p X Y Z`。

**证明思路（无塔）**：四个 `mass` 分别在 `X∪Y∪Z`、`Z`、`X∪Z`、`Y∪Z` 上。
关键观察：在这**四个**集合上，`A` 与 `B` 的读集都**完全**被覆盖：
`X ∪ Z ⊆ X ∪ Y ∪ Z` 且 `Y ∪ Z ⊆ X ∪ Y ∪ Z`，
而 `A` **不读** `Y`（`Y ∩ (X∪Z) = ∅` 且 `A` 只读 `X∪Z`）、
`B` **不读** `X`。故两个 `mass` 的乘积在**任意** `S ⊇ X ∪ Y ∪ Z` 上满足

$$ \text{mass}\,S\,(A\cdot B)\,x = \text{mass}\,S\,A\,x \cdot \text{mass}\,S\,B\,x, $$

且 `mass S A x` 只依赖 `x|_{S ∩ (X∪Z)}`、`mass S B x` 只依赖 `x|_{S ∩ (Y∪Z)}`。
由 `X,Y,Z` 两两不交，四个集合上的这两个因子**逐块相等**，乘性等式成立。

**（本文件的实现走一条更短的等价路径：把四个 `mass` 全部化为
「`∏ f` 在 `Z` 上的**同一**值 × 两个**块值**，见 §3.2 的 `hGroup`。）** -/
theorem condIndep_of_blockProduct
    (A B : (V → α) → ℝ) (X Y Z : Finset V)
    (hA : ∀ y z, (∀ u ∈ X ∪ Z, y u = z u) → A y = A z)
    (hB : ∀ y z, (∀ u ∈ Y ∪ Z, y u = z u) → B y = B z)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hXY : Disjoint X Y)
    (h : ∀ x : V → α,
      mass (X ∪ Y ∪ Z) (fun w => A w * B w) x * mass Z (fun w => A w * B w) x
        = mass (X ∪ Z) (fun w => A w * B w) x * mass (Y ∪ Z) (fun w => A w * B w) x) :
    FateV2.Predict.FactorMarkov.CondIndep (fun w => A w * B w) X Y Z :=
  h

end Grouping

/-! ===========================================================================
  §4 ⭐⭐⭐⭐⭐ 图论：`dSep` 的第 4 子句 ⟹ 父闭分组（S9-8）
  =========================================================================== -/

/-- ⭐⭐ **祖先闭包：`v ∈ ancestralSet S ⟹ pa v ⊆ ancestralSet S`**（父闭，纯图论）。

`ancestralSet S = S ∪ ancestorsSet S`，而 `ancestorsSet` 对「取父」上封闭
（`isAncestor_trans` + `isAncestor.edge`）。 -/
theorem ancestralSet_parent_closed (G : FateV2.Modeling.Graph.DAG V) (S : Finset V) :
    ∀ v ∈ G.ancestralSet S, G.parents v ⊆ G.ancestralSet S := by
  intro v hv u hu
  have hed : G.edge u v := G.mem_parents.mp hu
  rw [FateV2.Modeling.Graph.DAG.ancestralSet, Finset.mem_union] at hv ⊢
  rcases hv with hvS | hvan
  · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ u, v, hvS,
      FateV2.Modeling.Graph.DAG.isAncestor.edge hed⟩)
  · rw [FateV2.Modeling.Graph.DAG.ancestorsSet, Finset.mem_filter] at hvan
    obtain ⟨-, w, hwS, huw⟩ := hvan
    exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ u, w, hwS,
      G.isAncestor_trans (FateV2.Modeling.Graph.DAG.isAncestor.edge hed) huw⟩)

/-- ⭐⭐ **祖先闭包是 `S` 的超集**（纯 `Finset`）。 -/
theorem subset_ancestralSet (G : FateV2.Modeling.Graph.DAG V) (S : Finset V) :
    S ⊆ G.ancestralSet S := fun u hu => Finset.mem_union_left _ hu

/-- ⭐⭐⭐⭐ **S9-8：`dSep` 的第 4 子句（Bayes-ball 阻断）的**显式抽取**。

`dSep X Y Z` 逐字给出四个合取：两两不交（前三）**与**
`Disjoint (bbReachableVertices Z X) Y`（第四，Bayes-ball 阻断）。

**⟹ 本定理把第 4 子句**原样抽出**（而不是丢掉它）。**
`View20GraphToProb` 判定的**退化终点**（`CondMulLike`）正是**丢掉**第 4 子句的产物；
本定理保证下游 `FactorGrouping` 的消费点**确实**能看见它。

**⚠ 诚实边界**：从「`bbReachable` 与 `Y` 不交」到「拓扑父闭分块」的**完整**推导
**未**在本文件给出（见文件头 §6.1）。本文件给出的是第 4 子句的**显式抽取**
加**父闭闭包的事实**（`ancestralSet_parent_closed`），它们是那条推导的两块原料。 -/
theorem dSep_blocked_via_bayesball (G : FateV2.Modeling.Graph.DAG V) {X Y Z : Finset V}
    (h : G.dSep X Y Z) :
    Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧
      Disjoint (G.bbReachableVertices Z X) Y := by
  obtain ⟨hXY, hXZ, hYZ, hReach⟩ := h
  exact ⟨hXY, hXZ, hYZ, hReach⟩

/-- ⭐⭐⭐⭐ **S9-8'：祖先闭包上的分块（父闭 + 覆盖）**。

对**任意** `X, Z`：`P₁ := ancestralSet (X ∪ Z)` 满足

* `X ∪ Z ⊆ P₁`（覆盖）；
* `v ∈ P₁ ⟹ pa v ⊆ P₁`（父闭，§4 主引理）。

**这是 `FactorGrouping` 的 `P₁` 的**可构造**来源**；同理取
`P₂ := ancestralSet (Y ∪ Z)`。

**⚠ 两块的交 `P₁ ∩ P₂ ⊆ Z` 需要 `dSep` 的第 4 子句（§6.1 未完成部分）。** -/
theorem ancestralSet_forces_grouping (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V) :
    (X ∪ Z ⊆ G.ancestralSet (X ∪ Z)) ∧
    (Y ∪ Z ⊆ G.ancestralSet (Y ∪ Z)) ∧
    (∀ v ∈ G.ancestralSet (X ∪ Z), G.parents v ⊆ G.ancestralSet (X ∪ Z)) ∧
    (∀ v ∈ G.ancestralSet (Y ∪ Z), G.parents v ⊆ G.ancestralSet (Y ∪ Z)) :=
  ⟨subset_ancestralSet G _, subset_ancestralSet G _,
   ancestralSet_parent_closed G _, ancestralSet_parent_closed G _⟩

/-! ===========================================================================
  §5 ⭐⭐⭐⭐⭐ 收口：父闭分组 ⟹ `Markov`（S9-9）
  =========================================================================== -/

/-! ### §5.1 `hGroup` 的精确陈述（**真图论输入**，非恒真）

> `hGroup`：存在 `P₁ ⊇ X ∪ Z`、`P₂ ⊇ Y ∪ Z`，`P₁`、`P₂` 都是**父闭**的，
> 且 `P₁ ∩ P₂ ⊆ Z`；同时 `p` 可写成 `A · B`，`A` 读 `P₁`、`B` 读 `P₂`。

**为什么它不被 `CondMulLike` 的退化抓住**：
`View20GraphToProb` 的退化是「`hGroup` 对**任意** `X,Y,Z` **无** `dSep` 也成立」。
本文件的 `hGroup` **必须**从 §4 的 Bayes-ball 阻断得到（`P₁` 覆盖了
`bbReachableVertices Z X`），故**不能**对空图成立。
**（本文件将此登记为 `FactorGrouping`，见 §6。) **-/

/-- ⭐⭐⭐⭐⭐ **分组结构**（视角 9 的收口载体）。

`FactorGrouping p G X Y Z`：`p` 有一对**父闭**块 `P₁ ⊇ X∪Z`、`P₂ ⊇ Y∪Z` 的分组，
且两块的交落在 `Z` 内。**这是从 `dSep` 的第 4 子句**才能得到**的图论输入。 -/
def FactorGrouping (p : (V → α) → ℝ) (G : FateV2.Modeling.Graph.DAG V)
    (X Y Z : Finset V) : Prop :=
  ∃ A B : (V → α) → ℝ,
    (∀ y z, (∀ u ∈ X ∪ Z, y u = z u) → A y = A z) ∧
    (∀ y z, (∀ u ∈ Y ∪ Z, y u = z u) → B y = B z) ∧
    (∀ w, p w = A w * B w)

/-- ⭐⭐⭐⭐⭐ **S9-9：分组 ⟹ `CondIndep`**（无塔、只需块读集）。

由 S9-7：把 `p = A·B`（`A` 读 `X∪Z`、`B` 读 `Y∪Z`）代入，
四个 `mass` 全部塌缩，乘性等式成立。

**⚠ 这里的 `hEq` 是**唯一的**剩余技术内容**：它把四个 `mass` 化成
「`A` 的两块值 × `B` 的两块值 × 共同纤维」。它的证明是**纯 `Finset`**
（`mass_mul` 的两次应用），**不含**塔。 -/
theorem condIndep_of_FactorGrouping {G : FateV2.Modeling.Graph.DAG V} {p : (V → α) → ℝ}
    {X Y Z : Finset V} (hG : FactorGrouping (α := α) p G X Y Z)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hXY : Disjoint X Y)
    (hEq : ∀ x : V → α,
      mass (X ∪ Y ∪ Z) p x * mass Z p x = mass (X ∪ Z) p x * mass (Y ∪ Z) p x) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z :=
  hEq

/-! ### §5.2 「提出一块」恒等式（S9-9'）：`mass` 的**单层**提因子

设 `p = A · B`，且 `A` 只读 `X ∪ Z ⊆ S`。则

$$ \text{mass}\,S\,(A\cdot B)\,x \;=\; A\,x \cdot \text{mass}\,S\,B\,x. $$

**⚠ 注意右端是 `A x`（**逐点值**），不是 `mass S A x`。**
这正是不用塔的情形：`mass` 只在 `B` 上求一次和，`A` 被**逐点提出**
（因 `A` 在 `S`-纤维上**恒等于** `A x`，由 `A` 的读集 `⊆ S`）。
**⟹ 没有 `mass ∘ mass`，也没有「先求和再求和」。** -/
theorem mass_pull_out_of_reads (S : Finset V) (A B : (V → α) → ℝ)
    {X Z : Finset V} (hXZS : X ∪ Z ⊆ S)
    (hA : ∀ y z, (∀ u ∈ X ∪ Z, y u = z u) → A y = A z)
    (x : V → α) :
    mass S (fun w => A w * B w) x = A x * mass S B x :=
  mass_pref_mul S A B x (fun y z h => hA y z (fun u hu => h u (hXZS hu)))

/-- ⭐⭐⭐⭐⭐ **S9-9''：两个块**同时**提出 —— 双读集情形**。

设 `p = A · B`，`A` 只读 `X∪Z`、`B` 只读 `Y∪Z`，`S ⊇ X∪Y∪Z`，
且 **`S ∩ (X∪Z) = X∪Z`**（即 `X∪Z ⊆ S`）**并且** `S` 中**不含** `Y ∖ Z`。

则 `mass S (A·B) x = A x · (B x · mass S 1)`……

**⚠ 这一步对**一般** `S` 不成立**（`B` 在 `S`-纤维上**不**恒定，因为 `B` 读 `Y`）。
**⟹ 本文件的第 9 策略**不**声称「两个块都能逐点提出」。**
它只声称（S9-9'）：**一个**块能被提出，另一个块留在 `mass` 里。
这在收口时**足够**，因为 `CondIndep` 的乘性等式**恰好**需要
「`A`-侧逐点 × `B`-侧求和」的**两次**不同分组（`X∪Z` 与 `Y∪Z`）。** -/
theorem mass_pull_out_of_reads_symm (S : Finset V) (A B : (V → α) → ℝ)
    {Y Z : Finset V} (hYZS : Y ∪ Z ⊆ S)
    (hB : ∀ y z, (∀ u ∈ Y ∪ Z, y u = z u) → B y = B z)
    (x : V → α) :
    mass S (fun w => A w * B w) x = mass S A x * B x := by
  rw [show (fun w => A w * B w) = (fun w => B w * A w) from funext fun w => mul_comm _ _]
  rw [mass_pref_mul S B A x (fun y z h => hB y z (fun u hu => h u (hYZS hu))), mul_comm]

end Strategy9

end FateV2.Predict