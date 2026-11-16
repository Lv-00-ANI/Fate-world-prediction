/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.T33DoGraphConsumer`
阶段：**P5-甲（批 2）—— `Fate.T33DoGraph` 的消费方**

---------------------------------------------------------------------------
本文件做什么（一句话）
---------------------------------------------------------------------------
`Fate.T33DoGraph`（第 230 轮 B2）把 T3.3 的「`do` 的删边 = 模型替换的图侧投影」
落成了一条**元定理**：

* 语义侧 `VecSCM.doMap`（把 `X` 的方程换成常数）；
* 图侧 `doInGraph`（删去一切**指向** `X` 的边，= `GraphOps.delIn` 的邻接关系）；
* 主定理 `t33_graph_eq_doIn`：`graphOf (doMap M X x) = doInGraph (graphOf M) X`。

**该模块只有**单次**干预的等号。** 本文件**不修改**该模块一个字符，只把它的
结论**接到下游**，得到 4 条该模块中**不存在**的定理：

* **C1** 图侧的组合律 `doInGraph_comp`：两次删入边 = 一次联合删入边；
* **C2** 语义侧的组合律 `t33_graph_comp`：**两次干预的图投影** = 联合干预的图投影
  （`t33_graph_eq_doIn` 用两次 + C1）；
* **C3** `t33_acyclic_after_do`：**干预保持无环性**（语义侧，经 `graphOfCG` 打包
  + `doInGraph_acyclic_preserved`）；
* **C4** `t33_no_ancestors_after_do`：**干预后 `X` 中的顶点连祖先都没有**
  ——把模块里的**单条边**结论 `t33_no_parents_after_do` 提升到**传递闭包**层面；
* **C5** `t33_do_graph_fixpoint`：**干预在图层是幂等的**（`doInGraph_fixpoint`）。

---------------------------------------------------------------------------
目标模块的实测声明
（`grep -nE "^(theorem|def|noncomputable def|instance|structure)" Fate/T33DoGraph.lean`）
---------------------------------------------------------------------------
| 类别 | 声明 |
|---|---|
| §1 图侧定义 | `doGraph` `doInGraph` |
| §1.1 幂等 | `doGraph_fixpoint` `doInGraph_fixpoint` `doGraph_subset` `doInGraph_subset` |
| §1.2 无入/出边 | `doInGraph_no_incoming` `doGraph_no_outgoing` `doGraph_transpose` |
| §1.3 组合 | `doGraph_comp` `doGraph_fixpoint'` |
| §2 无环 | `doGraph_acyclic_preserved` `doInGraph_acyclic_preserved` `doGraphCG` |
| §3 语义 | `VecSCM`（structure）`VecSCM.Reads` `VecSCM.doMap` `VecSCM.doMap_const` `VecSCM.doMap_unchanged` `VecSCM.doMap_no_reads` `VecSCM.doMap_reads_iff` |
| §4 主定理 | `graphOf` `graphOf_iff` `t33_graph_eq_doIn` `t33_graph_eq_delIn` `graphOfCG` `t33_graph_eq_doInGraphCG` |
| §4.2 推论 | `t33_no_parents_after_do` |
| §4.3 反例 | `ceM` `ceM_edge` `ce_not_doGraph` `ce_doIn_holds` |
| §5 对接 | `doInGraph_eq_delIn_adj` `doGraph_eq_delOut_adj` `doMap_shared_structure` |

（全部位于 `Fate.R230` 命名空间内，`VecSCM.*` 在其中；本文件 `open Fate.R230`。）

---------------------------------------------------------------------------
⚠⚠ 同义反复自检（纪律 7：逐条核对「前件是否已把结论包进去」）
---------------------------------------------------------------------------
| 定理 | 前件 | 结论 | 是否同义反复 |
|---|---|---|---|
| **C1** `doInGraph_comp` | 无（只有 `G X X'`） | `doInGraph (doInGraph G X) X' = doInGraph G (X ∪ X')` | **否**（模块只有 `doGraph_comp`，**入边版不存在**；需 `funext` + `propext` 真证）|
| **C2** `t33_graph_comp` | `M X x X' x'` | `graphOf (doMap (doMap M X x) X' x') = doInGraph (doInGraph (graphOf M) X) X'` | **否**（模块只有**单次**干预的 `t33_graph_eq_doIn`；组合需两次 + C1）|
| **C3** `t33_acyclic_after_do` | `h : graphOf M` 无环（**语义图**的传递闭包非自反）| `graphOf (doMap M X x)` 无环 | **否**（前提讲 `M`，结论讲 `doMap M X x`；模块的 `doInGraph_acyclic_preserved` 只讲 `G.Adj`，**不涉及 `graphOf`/`doMap`**；需 `graphOfCG` 打包 + 主定理）|
| **C4** `t33_no_ancestors_after_do` | `x₀ ∈ X`、`a` 任意 | `¬ TransGen (graphOf (doMap M X x)) a x₀` | **否**（模块的 `t33_no_parents_after_do` 只有**单条边** `¬ graphOf ... a x₀`；传递闭包需对 `TransGen` 归纳）|
| **C5** `t33_do_graph_fixpoint` | `M X x` | `graphOf (doMap (doMap M X x) X x) = graphOf (doMap M X x)` | **否**（模块只有图侧 `doInGraph_fixpoint`，语义侧需两次主定理 + 该引理）|

**无一条把结论写进前件。**

---------------------------------------------------------------------------
⚠ 已知边界（如实登记）
---------------------------------------------------------------------------
* `VecSCM.doMap` 的 `[DecidablePred (· ∈ X)]` 是**实例参数**，故 C2 / C5 中
  「同一集合的两次使用」在**不同实例**下是**不同项**；本文件的定理对每个实例都成立，
  但**不声称** `doMap M X x` 在实例层面定义无关（后者需要 `propext` 上的重写，**未证**）。
* 本文件**不使用** `T35Rule1*` / do-calculus 三条规则（T3.3 的语义侧 `VecSCM`
  与 `PearlHierarchy.SCM` 不是同一载体，见模块 §5 `doMap_shared_structure` 的登记）。

**本文件不含 `sorry` / `admit` / `axiom`。**
-/

import FateWorld.FateV2.Predict.T33DoGraph
namespace FateV2.Predict

open FateV2.Modeling
namespace T33DoGraphConsumer

open Fate.R230

universe u

variable {E V D : Type*}

/-!
  # Predict · T33DoGraphConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T33DoGraphConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T33DoGraph
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  图侧：**删入边也满足组合律**
    ===========================================================================

模块给了 `doGraph_comp`（**删出边**的组合律），但 `doInGraph` 是 T3.3 的**正确**
投影载体，**它的组合律模块里没有**。下面补上，C2 要用。 -/

/-- ⭐⭐⭐ **C1：删入边的组合律**。

$$\mathrm{doInGraph}(\mathrm{doInGraph}(G,X),X') = \mathrm{doInGraph}(G, X \cup X')$$

**⭐ 证明**：**两边都是 `G a b` 再附加一个「`b` 不属于某个集合」的条件**，
**而 `b ∉ X ∪ X'` 恰是 `b ∉ X ∧ b ∉ X'`** —— **逐点 `propext`。** -/
theorem doInGraph_comp {W : Type*} (G : W → W → Prop) (X X' : Set W) :
    doInGraph (doInGraph G X) X' = doInGraph G (X ∪ X') := by
  funext a b
  refine propext ⟨fun h => ⟨h.1.1, ?_⟩, fun h => ⟨⟨h.1, ?_⟩, ?_⟩⟩
  · intro hmem
    rcases hmem with hmem | hmem
    · exact h.1.2 hmem
    · exact h.2 hmem
  · intro hmem; exact h.2 (Or.inl hmem)
  · intro hmem; exact h.2 (Or.inr hmem)

/-- ⭐⭐ **C1b：删入边的幂等性是组合律的推论**（与模块的 `doInGraph_fixpoint` 一致，
这里由 C1 独立推出，作为 C1 的**自检**）。 -/
theorem doInGraph_fixpoint' {W : Type*} (G : W → W → Prop) (X : Set W) :
    doInGraph (doInGraph G X) X = doInGraph G X := by
  rw [doInGraph_comp, Set.union_self]

/-! ===========================================================================
    §2  语义侧：**两次干预的图投影**
    =========================================================================== -/

/-- ⭐⭐⭐ **C2：两次干预的图投影 = 嵌套的删入边**。

$$\mathrm{graphOf}\bigl((M_{\mathrm{do}(X=x)})_{\mathrm{do}(X'=x')}\bigr)
  = \mathrm{doInGraph}\bigl(\mathrm{doInGraph}(\mathrm{graphOf}(M), X),\, X'\bigr)$$

**⭐ 这是 T3.3 主定理 `t33_graph_eq_doIn` 的**两次应用****：
**先对外层干预用一次，再对内层 `doMap` 用一次。**
**⟹ 「`do` 的图侧投影」对**干预的复合**是**同态**。** -/
theorem t33_graph_comp (M : VecSCM E V D) (X X' : Set V)
    [DecidablePred (· ∈ X)] [DecidablePred (· ∈ X')]
    (x x' : V → D) :
    graphOf (VecSCM.doMap (VecSCM.doMap M X x) X' x')
      = doInGraph (doInGraph (graphOf M) X) X' := by
  rw [t33_graph_eq_doIn (M := VecSCM.doMap M X x) X' x']
  rw [t33_graph_eq_doIn M X x]

/-- ⭐⭐⭐ **C2'：两次干预 = 一次联合干预（图侧投影层面）**。

$$\mathrm{graphOf}\bigl((M_{\mathrm{do}(X=x)})_{\mathrm{do}(X'=x')}\bigr)
  = \mathrm{doInGraph}\bigl(\mathrm{graphOf}(M),\, X \cup X'\bigr)$$

**⭐ 由 C2 + C1 得到**：**嵌套的 `do` 在图上**合并成一个联合干预**** ——
**这就是「`do` 的组合律」在语义侧的精确形式。** -/
theorem t33_graph_comp_union (M : VecSCM E V D) (X X' : Set V)
    [DecidablePred (· ∈ X)] [DecidablePred (· ∈ X')]
    (x x' : V → D) :
    graphOf (VecSCM.doMap (VecSCM.doMap M X x) X' x')
      = doInGraph (graphOf M) (X ∪ X') := by
  rw [t33_graph_comp, doInGraph_comp]

/-- ⭐⭐ **C5：干预在图层是幂等的**。

$$\mathrm{graphOf}\bigl((M_{\mathrm{do}(X=x)})_{\mathrm{do}(X=x)}\bigr)
  = \mathrm{graphOf}(M_{\mathrm{do}(X=x)})$$

**⭐ 由 C2' + `Set.union_self`** —— **即**：**重复同一干预不改变图投影。** -/
theorem t33_do_graph_fixpoint (M : VecSCM E V D) (X : Set V) [DecidablePred (· ∈ X)]
    (x : V → D) :
    graphOf (VecSCM.doMap (VecSCM.doMap M X x) X x) = graphOf (VecSCM.doMap M X x) := by
  rw [t33_graph_comp_union, Set.union_self, ← t33_graph_eq_doIn]

/-! ===========================================================================
    §3  无环性的传递：**干预不创造环**（语义侧）
    ===========================================================================

模块的 `doInGraph_acyclic_preserved` 只讲 `G.Adj`；这里把它与 `graphOf` / `doMap`
接上：**语义图无环 ⟹ 干预后的语义图无环。** -/

/-- ⭐⭐⭐ **C3：干预保持语义图的无环性**。

$$\Bigl(\forall v,\ \neg\,\mathrm{TransGen}(\mathrm{graphOf}(M))\,v\,v\Bigr)
  \implies \Bigl(\forall v,\ \neg\,\mathrm{TransGen}(\mathrm{graphOf}(M_{\mathrm{do}(X=x)}))\,v\,v\Bigr)$$

**⭐ 证明**：**把 `graphOf M` 用 `graphOfCG` 打包成 `CausalGraph`**
（模块 §4.1 给的设施），**再用 `doInGraph_acyclic_preserved`。** -/
theorem t33_acyclic_after_do (M : VecSCM E V D)
    (h : ∀ v : V, ¬ Relation.TransGen (graphOf M) v v)
    (X : Set V) [DecidablePred (· ∈ X)] (x : V → D) :
    ∀ v : V, ¬ Relation.TransGen (graphOf (VecSCM.doMap M X x)) v v := by
  rw [t33_graph_eq_doIn]
  exact doInGraph_acyclic_preserved (graphOfCG M h) X

/-- ⭐⭐ **C3b：干预后的语义图本身是一个 `CausalGraph`**（**可直接喂给
`GraphOps` / do-calculus**）。

**⭐ 由 C3 + `graphOfCG`** —— **即**：**干预把一个无环的语义模型**变成**一个 DAG。** -/
def t33_doGraphCG (M : VecSCM E V D)
    (h : ∀ v : V, ¬ Relation.TransGen (graphOf M) v v)
    (X : Set V) [DecidablePred (· ∈ X)] (x : V → D) :
    CausalDirection.CausalGraph V :=
  graphOfCG (VecSCM.doMap M X x) (t33_acyclic_after_do M h X x)

/-- ⭐⭐ **C3c：C3b 的邻接关系与 `GraphOps.delIn` 一致**（**与既有图设施的对接**）。

**⭐ 由 C2 之前的主定理 + `doInGraph_eq_delIn_adj`**：
**干预后的语义图 = 原图删入边。** -/
theorem t33_doGraphCG_adj (M : VecSCM E V D)
    (h : ∀ v : V, ¬ Relation.TransGen (graphOf M) v v)
    (X : Set V) [DecidablePred (· ∈ X)] (x : V → D) (a b : V) :
    (t33_doGraphCG M h X x).Adj a b ↔
      (GraphOps.delIn (graphOfCG M h) X).Adj a b := by
  show graphOf (VecSCM.doMap M X x) a b ↔ (GraphOps.delIn (graphOfCG M h) X).Adj a b
  rw [t33_graph_eq_doIn]
  exact doInGraph_eq_delIn_adj (graphOfCG M h) X a b

/-! ===========================================================================
    §4  ⭐⭐⭐ **干预后 `X` 连祖先都没有**（传递闭包层面）
    ===========================================================================

模块的 `t33_no_parents_after_do` 只说「**没有边**指向 `X`」。
**下面的 C4 把它提升到**路径**层面**：**`X` 中的顶点在干预后不可达** ——
**这是「`do(X=x)` 切断 `X` 的一切因果输入」的精确表述。** -/

/-- ⭐⭐⭐ **C4：干预后 `X` 中的顶点没有祖先**。

$$\forall x_0 \in X,\ \forall a,\ \neg\,\mathrm{TransGen}\bigl(\mathrm{graphOf}(M_{\mathrm{do}(X=x)})\bigr)\,a\,x_0$$

**⭐ 证明**：**对 `TransGen` 归纳** ——
**最后一条边指向 `x_0 ∈ X`，而干预后 `X` 无入边**（C2 用的主定理 + 模块的
`doInGraph_no_incoming`），**矛盾**。 -/
theorem t33_no_ancestors_after_do (M : VecSCM E V D) (X : Set V) [DecidablePred (· ∈ X)]
    (x : V → D) {x₀ : V} (hx : x₀ ∈ X) (a : V) :
    ¬ Relation.TransGen (graphOf (VecSCM.doMap M X x)) a x₀ := by
  intro h
  induction h with
  | single hab => exact t33_no_parents_after_do M X x hx a hab
  | tail _ hbc _ => exact t33_no_parents_after_do M X x hx _ hbc


/-- ⭐⭐ **C4b：C4 与 C3 的合成 —— 干预后 `X` 是「源点且仍无环」**。

**⭐ 这不是 C4 或 C3 中的任一条**：它同时说
（i）`X` 中顶点**无祖先**，（ii）整个干预图**无环**。 -/
theorem t33_do_X_is_sources_in_dag (M : VecSCM E V D)
    (h : ∀ v : V, ¬ Relation.TransGen (graphOf M) v v)
    (X : Set V) [DecidablePred (· ∈ X)] (x : V → D) :
    (∀ v : V, ¬ Relation.TransGen (graphOf (VecSCM.doMap M X x)) v v) ∧
      (∀ _x₀ ∈ X, ∀ a : V, ¬ Relation.TransGen (graphOf (VecSCM.doMap M X x)) a _x₀) :=
  ⟨t33_acyclic_after_do M h X x, fun _z hz a => t33_no_ancestors_after_do M X x hz a⟩

/-! ===========================================================================
    §5  小结
    ===========================================================================

| 编号 | 定理 | 消费了哪些目标模块结论 | 是否同义反复 |
|---|---|---|---|
| **C1** | `doInGraph_comp` | 仅用 `doInGraph` 的**定义**（组合律模块里没有）| 否 |
| **C1b** | `doInGraph_fixpoint'` | C1 + `Set.union_self`（**自检**：与模块 `doInGraph_fixpoint` 一致）| 否 |
| **C2** | `t33_graph_comp` | `t33_graph_eq_doIn`（两次）| 否 |
| **C2'** | `t33_graph_comp_union` | C2 + C1 | 否 |
| **C5** | `t33_do_graph_fixpoint` | C2' + `t33_graph_eq_doIn` + `Set.union_self` | 否 |
| **C3** | `t33_acyclic_after_do` | `t33_graph_eq_doIn` + `graphOfCG` + `doInGraph_acyclic_preserved` | 否 |
| **C3b** | `t33_doGraphCG`（def）| C3 + `graphOfCG` | 否 |
| **C3c** | `t33_doGraphCG_adj` | `t33_graph_eq_doIn` + `doInGraph_eq_delIn_adj` | 否 |
| **C4** | `t33_no_ancestors_after_do` | `t33_no_parents_after_do`（对 `TransGen` 归纳）| 否 |
| **C4b** | `t33_do_X_is_sources_in_dag` | C3 + C4 | 否 |

**本文件不含 `sorry` / `admit` / `axiom`。** -/

end T33DoGraphConsumer

end FateV2.Predict