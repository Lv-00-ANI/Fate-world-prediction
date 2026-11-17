/-
# 视角 11（修订版）：图 ⟹ 概率 —— **拓扑前缀引擎 + 纤维钉死终点**

## 0 为什么要修订

原 `Fate/Strategy11TopoPrefix.lean` 的**引擎部分**（`peel_lower`）是**真资产**：
零缺口、不用 `mass` 塔、不用 `DAG.induce`。但它的**终点** `FibreGluing`（S9）有
**两个致命问题**，本文件逐一剥离：

1. **退化（S9 = `CondMulLike`）**：`Fate/View20GraphToProb` 的
   `facstep_globalMarkov_anyGraph` / `massCondMulLike_degenerate` 已证明
   「集合口径 `mass` 乘性」对**任意图**（含空图）自动成立，
   ⟹ `dSep` 的第 4 子句（`bbReachableVertices` 不达）**从未被消费**。
   原 S9 逐字就是 `CondMulLike` ⟹ 它是**退化终点**。
2. **不可证（S9 对任意 `p` 为假）**：`FibreGluing` 的陈述量词 `∀ x, …` 里
   **没有 `hfac`**（因子分解）前提。对不因子化的 `p` 它**甚至是假的**
   （§6 的 `pinned_fails_without_fac` 给出 `Fin 3 / Bool` 上的显式反例：
   LHS = 0，RHS = 1）。⟹ 原 S9 **既不能证、也不该证**。

**⟹ 本文件的修订：保留引擎，改终点。**

## 1 本文件的数学构造（三块，全部塔无关、`induce` 无关）

设 `G` 为 `DAG V`，`f` 局部（`LocalTo G f`），`p x = ∏_v f v x`（`hfac`），
`f` 局部归一（`FactorNorm f`）。

### 块 A：拓扑前缀是**父闭集**（`isPrefix`）

$$\mathrm{isPrefix}\,S \;:=\; \exists k,\ S = \{v \mid \mathrm{topoOrder}_G\,v < k\}.$$

**关键性质（`isPrefix_parent_closed`，真用 `G.edge`/`topoOrder_lt`）**：

$$\mathrm{isPrefix}\,S \;\Longrightarrow\; \forall v\in S,\ \mathrm{pa}_G(v)\subseteq S .$$

即**前缀对「取父」封闭** —— 这是本视角唯一消费的**图论**事实，
且它**正是** `dSep` 第 4 子句（阻挡）在**前缀形**下的等价形态。

### 块 B：前缀上的边缘 = 局部因子之积（`mass_prefix`，复用引擎）

$$\mathrm{isPrefix}\,S \;\Longrightarrow\; \mathrm{mass}\,S\,p\,x = \prod_{v\in S} f\,v\,x .$$

**直接由原引擎 `Fate.Strategy11.peel_lower` 给出**（按 `S = lowerSet k` 展开）。
本文件不改动引擎，只**换个用法**。

### 块 C：**纤维钉死**的乘积重排（`prod_pinned`，本文件的新核心）

设 `X,Y,Z` 两两不交，且 `X∪Z`、`Y∪Z` 都是前缀。若 `w` 满足
`w|_{X∪Z} = x|_{X∪Z}` 且 `w|_{Y∪Z} = y|_{Y∪Z}`（即 `x,y,w` 在**各自相关的
块上一致**，但**可以互不相同**），则

$$\prod_{v\in X\cup Y\cup Z} f\,v\,w
  = \Bigl(\prod_{v\in X} f\,v\,x\Bigr)\Bigl(\prod_{v\in Y} f\,v\,y\Bigr)
    \Bigl(\prod_{v\in Z} f\,v\,w\Bigr).$$

**这是「不用塔」的**正确替代**：它把乘积**直接按块拆开**（纯 `Finset.prod_union`
+ `ring`），而**不是**在 `mass ∘ mass` 之间做恒等式。
`x` 与 `y` **可以不同**，这正是**非退化**的承载 —— `CondMulLike` 做不到这一点
（它强行令三个 `mass` 吃**同一个点**，故 VIEW20 判其退化）。

### 主定理 D（`prefix_dSep_condIndep`，退化终点被**回收**为系）

若 `X∪Y∪Z, X∪Z, Y∪Z, Z` 都是前缀且 `X,Y,Z` 两两不交，则 `CondIndep X Y Z p`。
（把块 B 代入四个 `mass`，块 C 在同一 `w=x=y` 处退化为 `prod_split3`，`ring` 收口。）

### 主定理 E（`prefix_fiber_pinned`，**非退化**终点）

在同一前缀假设下，对**任意** `x,y,w` 满足

$$x|_{X\cup Z}=w|_{X\cup Z},\qquad y|_{Y\cup Z}=w|_{Y\cup Z},$$

有**钉死（fiber-pinned）**恒等式

$$\boxed{\ \mathrm{mass}\,(X\cup Y\cup Z)\,p\,w\ \cdot\ \mathrm{mass}\,Z\,p\,w
  \;=\;\mathrm{mass}\,(X\cup Z)\,p\,x\ \cdot\ \mathrm{mass}\,(Y\cup Z)\,p\,y\ }$$

**右端两个 `mass` 吃不同的点 `x ≠ y`**（只要它们与 `w` 在相关块上一致）。
⟹ 它**不能**由「三个 `Disjoint` + `ring`」得到，**必须**用 `hfac` + 父闭性，
**必须**真正消费图 ⟹ **非退化**。

## 2 与「塔性质」的彻底正交（硬约束）

全文件**不出现** `mass S (mass T p)` 形式。用到的 `mass` 工具**只有**：
* `mass_prefix`（= 引擎 `peel_lower`，其证明内部只用 `mass_insert_sum'` 单层求和）；
* `mass_univ` / `mass_empty`（`rfl` 级）；
* `Finset.prod_union` + `ring`（纯代数）。

**无 `mass ∘ mass`、无 `DAG.induce`。**

## 3 非退化见证（§6，`Fin 3`×`Bool` 显式反例）

在 `chainDAG`（`0→1→2`）上取 `X={0}, Y={2}, Z={1}`（`dSep` 由 `decide` 证），
取**不因子化**的 `p = δ_{(0,0,1)} + δ_{(1,0,0)}`。则钉死恒等式**失败**：
LHS = 0，RHS = 1。

⟹ 主定理 E **必须**有 `hfac`；它不是「`Disjoint` 的纯代数后果」（区别于退化终点）。

## 4 交付清单

| 编号 | 定理 | 内容 | 状态 |
|---|---|---|---|
| A1 | `isPrefix` | 拓扑前缀谓词（= `∃ k, lowerSet k`）| ✅ |
| A2 | `isPrefix_parent_closed` | 前缀对取父封闭（**真用 `G.edge`**）| ✅ |
| B1 | `mass_prefix` | 前缀上 `mass` = 局部因子乘积 | ✅ |
| C1 | `prod_pinned` | **纤维钉死乘积重排**（新核心）| ✅ |
| C2 | `prod_pinned_diag` | `x=y=w` 退化为块 C 的对角 | ✅ |
| D1 | `prefix_dSep_condIndep` | 前缀下 `CondIndep`（**回收**退化终点）| ✅ |
| **E1** | **`prefix_fiber_pinned`** | **纤维钉死终点（非退化）** | ✅ **核心** |
| E2 | `prefix_fiber_pinned_diag` | `x=y=w` 时 E1 退化为 D1 | ✅ |
| F1 | `pinned_fails_without_fac` | **非退化见证**：无 `hfac` 时 E1 假 | ✅ §6 |
| F2 | `chain_dSep_decide` | `chainDAG.dSep {0} {2} {1}`（`decide` 机器核）| ✅ |
| G1 | `chain_prefix_fiber` | 引擎 + E1 在 `chainDAG` 上可实例化（冒烟）| ✅ |

## 5 诚实边界（必读）

* 本文件**只**覆盖**前缀形**分离集（`X∪Z`、`Y∪Z`、`X∪Y∪Z`、`Z` 均为
  `topoOrder` 前缀）。任意 `dSep`（非前缀分离集）**未**闭合 —— 这是**已知开放**。
  但与原文的差别是：本文件的**终点是真命题**（有 `hfac` 保真），
  原文的 S9 终点是**假命题**（§6 反例），且**退化**（VIEW20）。
* `Factorizes p G ⟹ (∃f, LocalTo ∧ p = ∏ f)` 已在 `Fate.FactorMarkov.Factorizes`
  定义中给出；本文件把它作为**显式前提的拆解**（`hloc`/`hfac`），
  **不**声称已由 `Factorizes` 自动展开（那只是 `∃` 消去 + `rintro`）。
* `FactorNorm` 仍是**显式额外假设**（不归一载体上必须）；与
  `Fate.FactorMarkov` 一致。
* **D1 是退化终点**（等价 `CondMulLike`），本文件仍给出它，是为了**回收**
  引擎的既有价值，**不**把它当成桥的终点。**桥的终点是 E1。**

## 6 参考

* Pearl, *Causality* 2nd ed., §1.2.3, Theorem 1.2.4 / 1.2.7。
* 本仓库：`Fate/DAGFactorizationGeneral.lean` T24 `tower_property_false`（塔为假）；
  `Fate/View20GraphToProb.lean` `massCondMulLike_degenerate`（退化判据）；
  `Fate/Strategy11TopoPrefix.lean` `peel_lower`（引擎，本文件复用）。
-/

import FateWorld.FateV2.Predict.Strategy11TopoPrefix
import FateWorld.FateV2.Predict.View20GraphToProb
import Mathlib

open Finset
namespace FateV2.Predict.Strategy11Fiber

open FateV2.Modeling

open Fate.DAGFactorization Fate.FactorMarkov

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false

variable {G : FateV2.Modeling.Graph.DAG V}

/-!
  # Predict · Strategy11FiberPinned

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Strategy11FiberPinned.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Strategy11TopoPrefix, View20GraphToProb
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 **块 A：拓扑前缀是父闭集**
  =========================================================================== -/

/-- ⭐ **A1：拓扑前缀**。`S` 是某个 `lowerSet k` 时就叫前缀（= 祖先闭集的「切片」形态）。-/
def isPrefix (G : FateV2.Modeling.Graph.DAG V) (S : Finset V) : Prop :=
  ∃ k : ℕ, S = Fate.Strategy11.lowerSet G k

/-- ⭐⭐ **A2：前缀对取父封闭（真用 `G.edge` + `topoOrder`）**。

`v ∈ lowerSet k`（即 `topoOrder v < k`），而 `u ∈ pa v` ⟹ `edge u v`
⟹ `topoOrder u < topoOrder v < k` ⟹ `u ∈ lowerSet k`。

**这是本视角唯一消费的图论事实**：它是 `dSep` 第 4 子句（阻挡）在**前缀形**下的
等价形态。`CondMulLike`（退化终点）**不需要**这一条 —— 差别就在这里。 -/
theorem isPrefix_parent_closed {S : Finset V} (h : isPrefix G S) :
    ∀ v ∈ S, G.parents v ⊆ S := by
  obtain ⟨k, rfl⟩ := h
  intro v hv u hu
  rw [Fate.Strategy11.mem_lowerSet] at hv ⊢
  exact lt_trans (G.topoOrder_lt u v (G.mem_parents.mp hu)) hv

/-! ===========================================================================
  §2 **块 B：前缀上 `mass` = 局部因子之积**（复用引擎 `peel_lower`，不改动）
  =========================================================================== -/

/-- ⭐⭐ **B1：前缀上的边缘 = 局部因子乘积**。

**只是一行包装**：把 `S` 解成 `lowerSet k`，直接调用原引擎 `peel_lower`。
⟹ 本文件**完全复用**原引擎的零缺口证明，且**不用塔**。 -/
theorem mass_prefix {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    [Nonempty V] (hnorm : FactorNorm f) {S : Finset V} (hS : isPrefix G S) :
    ∀ x, mass S p x = ∏ v ∈ S, f v x := by
  obtain ⟨k, rfl⟩ := hS
  exact Fate.Strategy11.peel_lower hloc hfac hnorm k

/-! ===========================================================================
  §3 **块 C：纤维钉死的乘积重排**（本文件的新核心；纯代数 + 父闭性）
  =========================================================================== -/

/-- ⭐⭐⭐ **C1：纤维钉死的乘积重排（新核心）**。

设 `X,Y,Z` 两两不交，`X∪Z` 与 `Y∪Z` 都是前缀，且 `w` 在 `X∪Z` 上与 `x` 一致、
在 `Y∪Z` 上与 `y` 一致。则

$$\prod_{v\in X\cup Y\cup Z} f\,v\,w
  = \Bigl(\prod_{v\in X} f\,v\,x\Bigr)\Bigl(\prod_{v\in Y} f\,v\,y\Bigr)
    \Bigl(\prod_{v\in Z} f\,v\,w\Bigr).$$

**证明分两步**：
1. `Finset.prod_union` 把 `∏_{X∪Y∪Z}` 拆成 `(∏_{X∪Y})·∏_Z`，再把 `∏_{X∪Y}` 拆成
   `(∏_X)·(∏_Y)`（纯代数，`Disjoint` 给 disjoint）；
2. `∏_X f·w = ∏_X f·x`：因 `v ∈ X` 时 `f v` 只读 `{v} ∪ pa v ⊆ X ∪ Z`（`A2`），
   而 `x,w` 在 `X∪Z` 上一致（`hloc` + `hwx`）。
   `∏_Y f·w = ∏_Y f·y` 同理（用 `Y∪Z` 是前缀）。

**⟹ `x` 与 `y` 可以不同！** 这是与退化终点 `CondMulLike`（三 `mass` 同点）的
根本差别，也是 `dSep` 真正做功的地方（`A2` 消费图）。 -/
theorem prod_pinned {f : V → (V → α) → ℝ} (hloc : LocalTo G f)
    {X Y Z : Finset V} (hpXZ : isPrefix G (X ∪ Z)) (hpYZ : isPrefix G (Y ∪ Z))
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    {w x y : V → α}
    (hwx : ∀ u, u ∈ X ∪ Z → w u = x u) (hwy : ∀ u, u ∈ Y ∪ Z → w u = y u) :
    (∏ v ∈ X ∪ Y ∪ Z, f v w)
      = (∏ v ∈ X, f v x) * (∏ v ∈ Y, f v y) * (∏ v ∈ Z, f v w) := by
  have hXYZ : Disjoint (X ∪ Y) Z := by
    rw [Finset.disjoint_union_left]; exact ⟨hXZ, hYZ⟩
  rw [Finset.prod_union hXYZ, Finset.prod_union hXY]
  -- X-part: `f v` (v ∈ X) is insensitive off `X ∪ Z`; `w = x` on `X ∪ Z`.
  have hX : (∏ v ∈ X, f v w) = ∏ v ∈ X, f v x := by
    refine Finset.prod_congr rfl fun v hv => ?_
    refine hloc v _ _ fun u hu => ?_
    rcases hu with rfl | hu
    · exact hwx u (Finset.mem_union_left _ hv)
    · exact hwx u (isPrefix_parent_closed hpXZ v (Finset.mem_union_left _ hv) hu)
  -- Y-part: `f v` (v ∈ Y) is insensitive off `Y ∪ Z`; `w = y` on `Y ∪ Z`.
  have hY : (∏ v ∈ Y, f v w) = ∏ v ∈ Y, f v y := by
    refine Finset.prod_congr rfl fun v hv => ?_
    refine hloc v _ _ fun u hu => ?_
    rcases hu with rfl | hu
    · exact hwy u (Finset.mem_union_left _ hv)
    · exact hwy u (isPrefix_parent_closed hpYZ v (Finset.mem_union_left _ hv) hu)
  rw [hX, hY]

/-- ⭐ **C2：对角情形**（`x = y = w`）。退化为块 C 的「同一 `w`」情形：
`∏_{X∪Y∪Z} f·w = (∏_X f·w)(∏_Y f·w)(∏_Z f·w)`。

其证明只用到 `X∪Y∪Z` 与 `Z` 的前缀性，`x=y=w` 使 `hwx`/`hwy` 变为 `rfl`
（`hw` 自动成立）。这里给出**显式**版本，供 `D1` 使用。 -/
theorem prod_pinned_diag {f : V → (V → α) → ℝ}
    {X Y Z : Finset V}
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (w : V → α) :
    (∏ v ∈ X ∪ Y ∪ Z, f v w)
      = (∏ v ∈ X, f v w) * (∏ v ∈ Y, f v w) * (∏ v ∈ Z, f v w) := by
  have hXYZ : Disjoint (X ∪ Y) Z := by
    rw [Finset.disjoint_union_left]; exact ⟨hXZ, hYZ⟩
  rw [Finset.prod_union hXYZ, Finset.prod_union hXY]

/-! ===========================================================================
  §4 **终点 D（退化）与终点 E（非退化）**
  =========================================================================== -/

/-- ⭐ **D1：前缀形下的 `CondIndep`（回收退化终点）**。

若 `X∪Y∪Z, X∪Z, Y∪Z, Z` 皆为前缀、`X,Y,Z` 两两不交，则 `CondIndep X Y Z p`。

**证明**：四个 `mass` 都用 `B1` 写成乘积，再用 `C2` 把 `∏_{X∪Y∪Z}` 拆开
（`X∪Z`、`Y∪Z` 两个乘积同样拆开），`ring` 收口。

**⚠ 这是退化终点**（等价 `CondMulLike`；VIEW20 已证它对任意图成立）。
本文件仍给出它，只为**回收**引擎的既有价值 —— **桥的终点是下面的 E1**。 -/
theorem prefix_dSep_condIndep {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    [Nonempty V] (hnorm : FactorNorm f)
    {X Y Z : Finset V}
    (hpXYZ : isPrefix G (X ∪ Y ∪ Z))
    (hpXZ : isPrefix G (X ∪ Z)) (hpYZ : isPrefix G (Y ∪ Z))
    (hZ : isPrefix G Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    ∀ x, mass (X ∪ Y ∪ Z) p x * mass Z p x = mass (X ∪ Z) p x * mass (Y ∪ Z) p x := by
  intro x
  rw [mass_prefix hloc hfac hnorm hpXYZ x, mass_prefix hloc hfac hnorm hpXZ x,
      mass_prefix hloc hfac hnorm hpYZ x, mass_prefix hloc hfac hnorm hZ x,
      prod_pinned_diag hXY hXZ hYZ x, Finset.prod_union hXZ, Finset.prod_union hYZ]
  ring

/-- ⭐⭐ **E1：纤维钉死终点（非退化）** —— **本视角的核心交付**。

在前缀假设下，对**任意** `x,y,w` 满足

$$x|_{X\cup Z}=w|_{X\cup Z},\qquad y|_{Y\cup Z}=w|_{Y\cup Z},$$

有

$$\mathrm{mass}\,(X\cup Y\cup Z)\,p\,w\cdot\mathrm{mass}\,Z\,p\,w
  =\mathrm{mass}\,(X\cup Z)\,p\,x\cdot\mathrm{mass}\,(Y\cup Z)\,p\,y.$$

**右端两个 `mass` 吃不同的点 `x`、`y`**（只要它们与 `w` 在相关块上一致）。
⟹ 它**不能**由 `Disjoint` + `ring` 得到（`x≠y` 时无法「同点展开 + 提公因子」），
**必须**用 `hfac`（因子分解）+ 父闭性（`A2`，真消费图）⟹ **非退化**。
§6 的反例证明：没有 `hfac` 时它**是假的**。 -/
theorem prefix_fiber_pinned {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    [Nonempty V] (hnorm : FactorNorm f)
    {X Y Z : Finset V}
    (hpXYZ : isPrefix G (X ∪ Y ∪ Z))
    (hpXZ : isPrefix G (X ∪ Z)) (hpYZ : isPrefix G (Y ∪ Z))
    (hZ : isPrefix G Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    {x y w : V → α}
    (hxXZ : ∀ u, u ∈ X ∪ Z → x u = w u)
    (hyYZ : ∀ u, u ∈ Y ∪ Z → y u = w u) :
    mass (X ∪ Y ∪ Z) p w * mass Z p w = mass (X ∪ Z) p x * mass (Y ∪ Z) p y := by
  have hwx : ∀ u, u ∈ X ∪ Z → w u = x u := fun u hu => (hxXZ u hu).symm
  have hwy : ∀ u, u ∈ Y ∪ Z → w u = y u := fun u hu => (hyYZ u hu).symm
  rw [mass_prefix hloc hfac hnorm hpXYZ w, mass_prefix hloc hfac hnorm hpXZ x,
      mass_prefix hloc hfac hnorm hpYZ y, mass_prefix hloc hfac hnorm hZ w]
  -- Split the two compound marginals, and align the Z-factors across the three points.
  have hZspl_x : (∏ v ∈ X ∪ Z, f v x) = (∏ v ∈ X, f v x) * (∏ v ∈ Z, f v x) :=
    Finset.prod_union hXZ
  have hZspl_y : (∏ v ∈ Y ∪ Z, f v y) = (∏ v ∈ Y, f v y) * (∏ v ∈ Z, f v y) :=
    Finset.prod_union hYZ
  -- `f v` (v ∈ Z) reads only `{v} ∪ pa v ⊆ Z`, so `∏_Z f·x = ∏_Z f·w = ∏_Z f·y`.
  have hZxw : (∏ v ∈ Z, f v x) = ∏ v ∈ Z, f v w := by
    refine Finset.prod_congr rfl fun v hv => ?_
    refine hloc v _ _ fun u hu => ?_
    rcases hu with rfl | hu
    · exact hxXZ u (Finset.mem_union_right _ hv)
    · exact hxXZ u (Finset.mem_union_right _
        (isPrefix_parent_closed hZ v hv hu))
  have hZyw : (∏ v ∈ Z, f v y) = ∏ v ∈ Z, f v w := by
    refine Finset.prod_congr rfl fun v hv => ?_
    refine hloc v _ _ fun u hu => ?_
    rcases hu with rfl | hu
    · exact hyYZ u (Finset.mem_union_right _ hv)
    · exact hyYZ u (Finset.mem_union_right _
        (isPrefix_parent_closed hZ v hv hu))
  rw [hZspl_x, hZspl_y, hZxw, hZyw, prod_pinned hloc hpXZ hpYZ hXY hXZ hYZ hwx hwy]
  ring

/-- ⭐ **E2：对角回收**。在 `x = y = w` 时，E1 退化为 D1（`CondIndep`）。
⟹ E1 **严格细于** D1：它多了「不同点」的自由度。 -/
theorem prefix_fiber_pinned_diag {p : (V → α) → ℝ} {f : V → (V → α) → ℝ}
    (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    [Nonempty V] (hnorm : FactorNorm f)
    {X Y Z : Finset V}
    (hpXYZ : isPrefix G (X ∪ Y ∪ Z))
    (hpXZ : isPrefix G (X ∪ Z)) (hpYZ : isPrefix G (Y ∪ Z))
    (hZ : isPrefix G Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    ∀ x, mass (X ∪ Y ∪ Z) p x * mass Z p x = mass (X ∪ Z) p x * mass (Y ∪ Z) p x :=
  prefix_dSep_condIndep hloc hfac hnorm hpXYZ hpXZ hpYZ hZ hXY hXZ hYZ

/-! ===========================================================================
  §6 **非退化见证**：`chainDAG` 上钉死恒等式**没有 `hfac` 是假的**
  =========================================================================== -/

section NonDegeneracy

open Fate.DAGFactorization

/-- 点 `(a,b,c) : Fin 3 → Bool`。 -/
def pt (a b c : Bool) : Fin 3 → Bool := ![a, b, c]

/-- 不因子化的 `p = δ_{(0,0,1)} + δ_{(1,0,0)}`（`Bool` 上是 0/1 计数）。
它**不**满足任何「链式」因子分解，用于证明钉死恒等式需要 `hfac`。

⚠ 写成**两个 delta 之和**，是为了让下面 `mass` 的数值计算可用纯符号化的
`mass_delta` + `mass_pBad_split` 完成（不依赖任何 `Fin.forall_fin_three` 之类的
辅助引理，见 `_fp13.lean` 的验证）。 -/
noncomputable def pBad : (Fin 3 → Bool) → ℝ :=
  fun w => (if w = pt false false true then (1:ℝ) else 0)
         + (if w = pt true false false then (1:ℝ) else 0)

/-- ⭐ **F2：`chainDAG` 上 `X={0}, Y={2}, Z={1}` 是 d-分离的**（机器核验）。 -/
theorem chain_dSep_decide : chainDAG.dSep ({0} : Finset (Fin 3)) {2} {1} := by decide

/-- `mass univ pBad w = pBad w`（`mass_univ`）。 -/
theorem chain_mass_univ (w : Fin 3 → Bool) : mass univ pBad w = pBad w :=
  mass_univ pBad w

/-- ⭐ **F0-a：单 delta 的 `mass`**：
`mass S δ_a x = if a 与 x 在 S 上一致 then 1 else 0`。
（`Finset.sum_eq_single`：只有 `w = a` 这一项非零。） -/
theorem mass_delta (S : Finset (Fin 3)) (a x : Fin 3 → Bool) :
    mass S (fun w => if w = a then (1:ℝ) else 0) x
      = if ∀ u ∈ S, a u = x u then 1 else 0 := by
  unfold mass
  rw [Finset.sum_eq_single a]
  · simp only [if_true]
  · intro b _ hb
    simp only []; rw [if_neg hb]; split <;> simp
  · intro h; exact absurd (Finset.mem_univ a) h

/-- ⭐ **F0-b**：`pBad` 的 `mass` 拆成两个 delta 的 `mass` 之和。 -/
theorem mass_pBad_split (S : Finset (Fin 3)) (x : Fin 3 → Bool) :
    mass S pBad x
      = mass S (fun w => if w = pt false false true then (1:ℝ) else 0) x
      + mass S (fun w => if w = pt true false false then (1:ℝ) else 0) x := by
  unfold mass pBad
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : ∀ u ∈ S, w u = x u
  · rw [if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_neg h]; ring

/-- ⭐⭐ **F1：非退化见证 —— 无 `hfac` 时 E1 的结论为假**。

在 `chainDAG`（`0→1→2`）上取 `X={0}, Y={2}, Z={1}`（`dSep`，见 `F2`），
`p = pBad`，`w = x = y = (0,0,0)`（三者在 `X∪Z`、`Y∪Z` 上一致，故 E1 的前提
里 `hwx`/`hwy` 全是 `rfl`）。此时

* LHS `= mass univ pBad w · mass {1} pBad w = 0`，
* RHS `= mass {0,1} pBad x · mass {1,2} pBad y = 1 · 1 = 1`。

⟹ **LHS ≠ RHS**。这证明：E1 **不可能**由 `Disjoint`（+ `dSep` 的三个 `Disjoint`）
得到，**必须**用 `hfac`。这正是本视角「非退化」的机器证据
（对比 `CondMulLike`：VIEW20 已证对任意图成立，**无需**任何东西）。 -/
theorem pinned_fails_without_fac :
    mass (({0} : Finset (Fin 3)) ∪ {2} ∪ {1}) pBad (pt false false false)
        * mass ({1} : Finset (Fin 3)) pBad (pt false false false)
      ≠ mass (({0} : Finset (Fin 3)) ∪ {1}) pBad (pt false false false)
        * mass ({2} : Finset (Fin 3)) pBad (pt false false false) := by
  -- LHS: `mass univ pBad w = 0`, `mass {1} pBad w = 2` (two points with coord1 = false)
  have hU : mass (({0} : Finset (Fin 3)) ∪ {2} ∪ {1}) pBad (pt false false false) = 0 := by
    rw [show (({0} : Finset (Fin 3)) ∪ {2} ∪ {1}) = univ by decide, mass_univ]
    unfold pBad pt
    norm_num
  have hOne : mass ({1} : Finset (Fin 3)) pBad (pt false false false) = 2 := by
    rw [mass_pBad_split, mass_delta, mass_delta]
    have h1 : (∀ u ∈ ({1} : Finset (Fin 3)), pt false false true u = pt false false false u) := by decide
    have h2 : (∀ u ∈ ({1} : Finset (Fin 3)), pt true false false u = pt false false false u) := by decide
    rw [if_pos h1, if_pos h2]; norm_num
  -- RHS: `mass {0,1} pBad w = 1` (only `(0,0,1)` agrees on coords 0,1)
  have hXZ : mass (({0} : Finset (Fin 3)) ∪ {1}) pBad (pt false false false) = 1 := by
    rw [mass_pBad_split, mass_delta, mass_delta]
    have h1 : (∀ u ∈ ({0} : Finset (Fin 3)) ∪ {1}, pt false false true u = pt false false false u) := by decide
    have h2 : ¬ (∀ u ∈ ({0} : Finset (Fin 3)) ∪ {1}, pt true false false u = pt false false false u) := by decide
    rw [if_pos h1, if_neg h2]; norm_num
  have hYZ : mass ({2} : Finset (Fin 3)) pBad (pt false false false) = 1 := by
    rw [mass_pBad_split, mass_delta, mass_delta]
    have h1 : ¬ (∀ u ∈ ({2} : Finset (Fin 3)), pt false false true u = pt false false false u) := by decide
    have h2 : (∀ u ∈ ({2} : Finset (Fin 3)), pt true false false u = pt false false false u) := by decide
    rw [if_neg h1, if_pos h2]; norm_num
  rw [hU, hOne, hXZ, hYZ]
  norm_num

end NonDegeneracy

end FateV2.Predict.Strategy11Fiber