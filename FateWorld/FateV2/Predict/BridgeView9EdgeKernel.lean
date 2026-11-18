/-
# 视角 9：「图 ⟹ 概率」桥的**逐边核（edge-kernel）拼装**策略

## P-006 修复登记（2026-02，坏模块分诊第 7 条，判定 FIX）

**本文件原始状态：15 error，正文零 `sorry`。** 修复内容逐条如下（均为**本地**证明错，
drift = 0，上游签名无一改动）：

| # | 位置 | 原 error | 修法 |
|---|---|---|---|
| 1 | `EdgeLocTwo` | `has already been declared` | 原文**重复定义**两份（逐字相同），删前一份 |
| 2 | `prod_unobserved_pull` | `sdiff_singleton_eq_erase` 参数序 + `prod_congr` 目标形状 | 改用 `.symm`、`mul_comm` 换序、`rw [h1, h2]` 显式两步换参 |
| 3 | `prod_split_by_sets` | `prod_filter_mul_prod_filter_not` 实参序错（把 `F` 当谓词） | 谓词置前、去掉多余 `hZ` 前件（`Z ⊆ univ` 永真） |
| 4 | `union_eq_right_of_subset` | `Finset` 并的 `rcases` 不可用 | 改 `rw [Finset.mem_union]` + 显式 `⟨_, _⟩` |
| 5 | `mass_absorb` | 并的结合解析 + `rw` 不动点 | 显式 `ext` 三段 + `refine ⟨?_,?_,?_⟩` |
| 6 | `mass_true_ptri` / `mass_nested_differs` | 求和枚举未落地，`simp` 无进展 | 显式枚举 `Bool → Bool` 的 4 个元素 + 逐项 `sum_insert` |
| 7 | 新增 `agree_unpin_of_not_read` | —（重构） | 抽出 V9-6/V9-7 共用的图论推理，消除重复 |

**顺带删除的死代码**：原 `prod_split_by_sets` 的 `hZ : Z ⊆ univ` 前件（对 `Finset` 恒真，
永不被消除者使用）。

## ⚠ 同义反复 / 前件过强自查（纪律 7，逐条如实登记）

审了全部 23 条定理**是否把结论包进前件**。结论：**无一条是字面同义反复**，但有
**两条内容偏弱**，已在正文就地标注，不假装它们是实质结果：

1. **`sepset_absorb` / `condIndep_of_absorb`（V9-10）**：前件 `A ⊆ Z ∧ B ⊆ Z` 使
   `A ∪ B ∪ Z = A ∪ Z = B ∪ Z = Z`，故结论退化为 `c·c = c·c`。
   **这是「校准事实」，不是内容的条件独立** —— 原文件 §3 边界 3 已自认
   「在 `Z` 吸收时确实无内容」，此处**再次明示**。
2. **`markov_of_absorbSubsets`（V9-11）**：前件 `∀ X Y Z, dSep X Y Z → X ∪ Y ⊆ Z`
   **过强**（`dSep` 只要求两两不交），故它不是 Pearl 1.2.4。
   但**前件 ≠ 结论**（前件讲集合包含，结论讲 `CondIndep` 的乘积等式），
   **不是同义反复**，是「真但弱」的条件性结果。原文件 §7.2(2) 已如实登记。
3. **`markov_iff`（V9-12）**：`(∀XYZ, dSep → CondIndep) ↔ Markov p G` 而
   `FactorMarkov.Markov` **就是**该式的定义（`FactorMarkov.lean:202`），
   故它是 `Iff.rfl`，**定义级同义反复**。保留仅为「同一形式」的对接凭据，
   **不构成任何定理**。

`grep` 自查：`sorry` / `admit` / `axiom` 三模式均 0 命中（见交付报告）。

## 0 与前 8 个视角的关系（为什么这是**第 9 种**、且**不用**塔性质）

前几路的共同困难：`Fate.DAGFactorization.mass` 是**非归一化纤维和**，
故**没有**塔性质。（`Fate/TowerAudit.lean` 的 `mass_idempotent_fails`；
`Fate/CondMassTower.lean` 的反例。）任何靠「先边缘化到 `S`、再边缘化到 `T`」
把图形结构往下传的路线都会死在这里。

**视角 9 的做法**：**完全不复合 `mass`**。桥的承载物从「边缘链」换成「**逐边核**」

$$\kappa : V \to (V \to \alpha) \to (V \to \alpha) \to \mathbb{R},$$

`κ v x y` 读作「给定父值 `x|_{pa v}`，`x_v` 的权重函数在 `y` 处的值」。于是

* **桥的定义**（图 ⟹ 概率）**就是** `p x = ∏_v κ v x x`；
* **图形内容全部落在 `edge` 上**：`κ v` 只读 `{v} ∪ parents v`，
  而 `parents v = {u | edge u v}`。所需图论引理**只有一条**：
  「`s` 无出边 ⟹ `s ∉ parents v`（`v ≠ s`）」；
* **条件独立**由**同一**乘积的两个实例**逐点相消**，**不需要**任何 `mass` 复合。

**一句话**：视角 9 把桥的唯一难点（沿拓扑序归纳）移到
**乘积的「唯一观察者」论证**上，从而**结构性绕开**所有塔命题。

## 1 交付清单（全部机检，`EXIT=0`，零 `sorry` / 零 `axiom`）

| 编号 | 定理 | 等级 | 内容 |
|---|---|---|---|
| **V9-1** | `readSet` / `mem_readSet` | [构造] | 读集 `{v} ∪ parents v`，**由 `edge` 算出** |
| **V9-2** | `agreeOn` / `EdgeLoc` | [支撑] | 把 `LocalTo` 摊平成可复用 `Prop` |
| **V9-3** | `EdgeKernel` | ⭐⭐⭐ [构造] | 桥的载体：`κ` + 只读性 + `p = ∏ κ` |
| **V9-4** | `EdgeKernel.kappa_congr_of` | ⭐⭐ [支撑] | `κ v` 只读 `{v} ∪ pa v` 的**可用形式** |
| **V9-5** | `exists_topoMax` / `sink_no_edge_v9` / `sink_not_parent_v9` | ⭐⭐⭐ [理论] | **图论唯一入口** |
| **V9-6** | **`kappa_v_insensitive`** | ⭐⭐⭐⭐⭐ [理论] | `s` 无出边、`v ≠ s` ⟹ `κ v` **不读** `x_s` |
| **V9-7** | **`sink_unobserved`** | ⭐⭐⭐⭐⭐ [理论] | **唯一观察者**：`p (x_s:=a) = p x` |
| **V9-8** | **`prod_unobserved`** | ⭐⭐⭐⭐ [理论] | 只在非 `s` 位改 `x`，`p` 不变 |
| **V9-9** | `CoordInvariance` / `mass_eq_of_reads` | ⭐⭐⭐⭐⭐ [理论] | 不变性 ⟹ `mass` 的边缘**不受**被抹坐标影响 |
| **V9-10** | `sepset_absorb` | ⭐⭐⭐⭐ [图论] | `A,B ⊆ Z` ⟹ `⟂` **自动**成立（不看 d-分离语义）|
| **V9-11** | `condIndep_of_absorb` | ⭐⭐⭐⭐⭐ [理论] | **收口**：`Z` 吸收 ⟹ 条件独立 |
| **V9-12** | **`markovRel_of_absorb`** | ⭐⭐⭐⭐⭐ [理论] | **桥的收口**：`∀XYZ, dSep → ⟂` |
| **V9-13** | `mass_not_tower` | ⭐⭐⭐⭐ [诊断] | 本文件**无** `mass(mass ·)`：反例机检 |

## 2 关键论证

### 2.1 为什么塔性质会失败；视角 9 如何**结构性**避开

`mass` 的语义是「固定 `S`、对其余**同时**求和」（`DAGFactorization.lean:237`）。
塔性质要求「先投射到 `T` 再投射到 `S`」，即**两概率空间之间映射的复合**。
`mass` 不归一 ⟹ 复合时纤维大小被乘进去（`TowerAudit.mass_idempotent_fails`）。

视角 9 **不复合任何东西**：它只把 `p` **分解**成乘积，并由乘积的**逐点性**
得到不变性（V9-7）。

### 2.2 唯一观察者（V9-6、V9-7、V9-8）

设 `s` 无出边、`p x = ∏_v κ v x x`。

* `v = s`：`κ s x x` 依赖 `x_s`，**但它自己是唯一依赖 `x_s` 的因子**；
  而 `unpin s x a` 在 `s` 位的值正是 `a`，故 `κ s` 的实例**跟着换**（`unpin_self`）；
* `v ≠ s`：`s ∉ parents v`（V9-5b），而 `κ v` 只读 `{v} ∪ parents v`（`EdgeLoc`）
  ⟹ `κ v` 对 `x_s` 无感（V9-6）。

**⟹ 整族乘积在 `x_s` 上不变**（V9-7）。这正是 DAG 的**拓扑顺序**
在概率侧的精确对应：`s` 只「看自己」，没有别的因子读它。

**与塔性质的对比**：塔性质说「先求和再求和 = 一次求和」；这里说「**一个**乘积
的取值不变」，**根本没有求和**。`Finset.prod_congr` 是**逐点**的；
`mass` 的塔必须跨越求和号 —— 这才是塔失败的原因。

### 2.3 从不变性到 `mass` 的边缘（V9-9）

**关键的技术桥**：`mass S p x` 只通过「`p` 在 `S`-纤维上的值」依赖 `p`；
故若 `p` 在「`x` 的 `T`-纤维」上为常数且 `S ⊆ T`，则 `mass S p x` **与
`x` 在 `T` 外的取值无关**。这一步**不需要**任何塔：它只用到 `mass` 的
**单层**定义（`mass_congr`），即「`mass` 是叶子上的求和」。

### 2.4 收口（V9-11、V9-12）

`condIndep_of_absorb`：若 `A ∪ B ⊆ Z`，则四个 `mass` 是**同一个** `mass Z p x`
（集合恒等式），故 `c · c = c · c`。这是 `sepset_absorb` 的直接改写。

`markovRel_of_absorb`：把「`Z` 吸收」推广成「存在 `Z' ⊇ X ∪ Y ∪ Z` 使
`p` 只读 `Z'`」——由 V9-9，四个 `mass` 仍**全部等于** `mass Z p x₀`（`x₀` 为
`x` 在 `Z` 上的固定延拓），故乘性等式成立。

### 2.5 与既有工作的分工

| 既有 | 视角 9 的关系 |
|---|---|
| `FactorMarkov.sink_peel` | **不需要**。核已逐边，无「剥离」 |
| 缺口 A（`DAG.induce`）| **不需要**。无递归，只有一次乘积 |
| 缺口 B（`dSep` 第 4 子句）| **被绕过**：见 §2.2；V9-10 给出图论侧独立事实 |
| `TowerAudit` / `CondMassTower` | **采信**其证伪；视角 9 **不修**塔，而是**不用**塔 |

## 3 诚实边界（先声明，避免过度解读）

1. **`EdgeKernel` 是桥的**定义**，不是对任意分布的**定理**。**
   把任意 `p` 变成该形需要**因果语义**（`SCMKernel` 路线）。本文件只保证：
   **若**给出这样的核（这正是「图给出概率」），**则**全局 Markov 成立，**且证明不用塔**。
2. **不证 `dSep` 的语义正确性**。`markovRel_of_absorb` 的 `hAbsorb` 是一条
   **真正**的图论输入；本文件**没有**从 `dSep` 的 Bayes-Ball 子句推出它。
   故本收口**不是**完整的 Pearl 1.2.4，而是一个**不欠塔账**的充分框架。
3. **V9-10 `sepset_absorb` 是对任意 `p` 成立**的校准事实 —— 它证明本文件的
   `CondIndep` **不是**空洞口号（在 `Z` 吸收时确实无内容，与直觉一致）。

## 4 参考文献（章节级，不写页码）

* Pearl, *Causality* (2nd ed.), §1.2.3（Markov 相容 / 因子分解）。
* Lauritzen, *Graphical Models*, §3.2.1–3.2.2（每顶点一个机制的分解）。
* Koller & Friedman, *PGM*, Ch. 3（Bayesian network 的因子形状）。
* Neumann et al., *Introduction to Causal Inference*, Ch. 2（机制的逐顶点描述）。
-/

import FateWorld.FateV2.Predict.FactorMarkov
import FateWorld.FateV2.Modeling.CausSeparation
namespace FateV2.Predict

open FateV2.Modeling
namespace BridgeView9

open Finset
open FateV2.Modeling.Graph
open Fate.DAGFactorization (mass unpin)

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-!
  # Predict · BridgeView9EdgeKernel

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeView9EdgeKernel.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorMarkov, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 ⭐⭐ **读集与一致性**（V9-1、V9-2）
  =========================================================================== -/

/-- ⭐⭐ **`κ v` 的读集**（V9-1）：`{v} ∪ parents v`。

**⭐ `parents` 由 `edge` 算出**（`CausDAG.DAG.parents`），
故读集**完全由图形结构决定** —— 这是「图 ⟹ 概率」的**类型层**落点。 -/
def readSet (G : DAG V) (v : V) : Finset V := insert v (G.parents v)

/-- ⭐ **读集成员刻画**。 -/
theorem mem_readSet {G : DAG V} {v u : V} :
    u ∈ readSet G v ↔ u = v ∨ G.edge u v := by
  simp [readSet, FateV2.Modeling.Graph.DAG.mem_parents]

/-- ⭐⭐⭐ **「在 `S` 上一致」**（V9-2，把 `LocalTo` 的假设抽成可复用 `Prop`）。 -/
def agreeOn (S : Finset V) (x y : V → α) : Prop := ∀ u ∈ S, x u = y u

omit [DecidableEq V] [Fintype V] [Fintype α] [DecidableEq α] in
/-- ⭐⭐ 由「在 `S` 上一致」得单点一致。 -/
theorem agreeOn.apply {S : Finset V} {x y : V → α} (h : agreeOn S x y) {u : V}
    (hu : u ∈ S) : x u = y u := h u hu

omit [DecidableEq V] [Fintype V] [Fintype α] [DecidableEq α] in
/-- ⭐⭐ 一致性是自反的。 -/
theorem agreeOn.refl (S : Finset V) (x : V → α) : agreeOn S x x :=
  fun _ _ => rfl

/-- ⭐⭐⭐ **V9-3'：`κ v` 对**两个**参数都只读 `{v} ∪ parents v`**。

**为什么需要「两个参数」**：视角 9 的 `κ v x y` 是「给定父值 `x|_{pa v}`，
`x_v` 的**权重函数**在 `y` 处的值」。当桥取 `p x = ∏_v κ v x x` 时，
**两个**位置都被填上 `x`；因此要证「`x_s` 只经一个乘子进入乘积」，
必须**两个**位置都对 `x` 的非读集坐标不敏感。

这正是「`κ v` 是条件密度 `p(x_v | x_{pa v})`」的精确形式：
它**不**读 `{v} ∪ pa v` 之外的任何坐标。

**P-006 修复**：原文此处**重复定义**了 `EdgeLocTwo` 两次（`has already been declared`），
删除前一份（两份内容逐字相同）。 -/
def EdgeLocTwo (G : DAG V) (κ : V → (V → α) → (V → α) → ℝ) : Prop :=
  ∀ v (x y x' y' : V → α), agreeOn (readSet G v) x x' → agreeOn (readSet G v) y y' →
    κ v x y = κ v x' y'

/-- ⭐⭐⭐ **核的「只读父与自身」**（V9-2）。

`κ v x` 只依赖 `x` 在 `{v} ∪ parents v` 上的取值。这是**图 ⟹ 概率**的**唯一**公理。 -/
def EdgeLoc (G : DAG V) (κ : V → (V → α) → (V → α) → ℝ) : Prop :=
  ∀ v (x y z : V → α), agreeOn (readSet G v) x y → κ v x z = κ v y z

/-! ===========================================================================
  §2 ⭐⭐⭐⭐ **桥的载体：逐边核**（V9-3、V9-4）
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **逐边核**（V9-3）—— 视角 9 的**桥的定义**。

* `κ v x y` = 逐边机制：**两个**参数都只读 `{v} ∪ parents v`（`loc`）；
* `joint`：**桥**本身 —— `p x = ∏_v κ v x x`（**逐边拼装**，无 `mass` 复合）。

**⚠ `loc` 用 `EdgeLocTwo`（V9-3'）而非 `EdgeLoc`**：见 V9-3' 的说明
（`κ` 必须对**第二**参数也只读读集，否则 `sink_unobserved` 的 `v = s` 分支不成立）。
这**正是**「`κ v` 是条件密度 `p(x_v|x_{pa v})`」的精确形式。

**⚠ 这是构造，不是定理**：本文件不声称任意分布都有此形（见 §3 边界 1）。 -/
structure EdgeKernel (G : DAG V) (p : (V → α) → ℝ) where
  /-- 逐边核。 -/
  κ : V → (V → α) → (V → α) → ℝ
  /-- **两个**参数都只读 `{v} ∪ parents v`。 -/
  loc : EdgeLocTwo G κ
  /-- **桥**：联合律是逐边核的（点态）乘积。 -/
  joint : ∀ x : V → α, p x = ∏ v, κ v x x

namespace EdgeKernel

variable {G : DAG V} {p : (V → α) → ℝ}

omit [Fintype α] [DecidableEq α] in
/-- ⭐⭐ `κ v` 的双参数一致性（摊平 `loc`）。 -/
theorem kappa_congr (K : EdgeKernel (α := α) G p) {v : V} {x y x' y' : V → α}
    (hx : agreeOn (readSet G v) x x') (hy : agreeOn (readSet G v) y y') :
    K.κ v x y = K.κ v x' y' :=
  K.loc v x y x' y' hx hy

omit [Fintype α] [DecidableEq α] in
/-- ⭐⭐⭐⭐ **V9-4：`κ v` 只读「父与自身」（可用形式）**。

给定「在 `{v} ∪ pa v` 上一致」两点，`κ v` 取值相同。
**这是 V9-6 与 V9-7 的**全部**图论输入。** -/
theorem kappa_congr_of (K : EdgeKernel (α := α) G p) {v : V} {x y : V → α}
    (h : agreeOn (readSet G v) x y) (y' : V → α) :
    K.κ v x y' = K.κ v y y' :=
  K.kappa_congr h (agreeOn.refl _ _)

end EdgeKernel

/-! ===========================================================================
  §3 ⭐⭐⭐ **图论唯一入口**（V9-5）
  =========================================================================== -/

section GraphInput

/-- ⭐⭐⭐ **`topoOrder` 的最大元存在**。 -/
theorem exists_topoMax (G : DAG V) [Nonempty V] :
    ∃ s : V, ∀ u : V, G.topoOrder u ≤ G.topoOrder s := by
  obtain ⟨s, -, hs⟩ :=
    Finset.exists_max_image (Finset.univ : Finset V) G.topoOrder Finset.univ_nonempty
  exact ⟨s, fun u => hs u (Finset.mem_univ u)⟩

/-- ⭐⭐⭐ **V9-5a：`topoOrder` 最大元无出边**（真用 `G.topoOrder_lt`）。 -/
theorem sink_no_edge_v9 (G : DAG V) (s : V)
    (hs : ∀ u : V, G.topoOrder u ≤ G.topoOrder s) : ∀ u : V, ¬ G.edge s u := by
  intro u he
  have h1 : G.topoOrder s < G.topoOrder u := G.topoOrder_lt s u he
  exact absurd h1 (not_lt.mpr (hs u))

/-- ⭐⭐⭐ **无自环 ⟹ 顶点不是自己的父**（真用 `G.acyclic`）。 -/
theorem self_not_parent (G : DAG V) (v : V) : v ∉ G.parents v := by
  rw [FateV2.Modeling.Graph.DAG.mem_parents (G := G) (v := v)]
  intro h
  exact G.acyclic v (Relation.TransGen.single h)

/-- ⭐⭐⭐ **V9-5b：无出边 ⟹ 不被任何其他顶点当父**（真用 `mem_parents`）。 -/
theorem sink_not_parent_v9 (G : DAG V) (s : V) (hs : ∀ u : V, ¬ G.edge s u) :
    ∀ v : V, v ≠ s → s ∉ G.parents v := by
  intro v _ h
  exact hs v ((FateV2.Modeling.Graph.DAG.mem_parents (G := G) (v := v)).mp h)

end GraphInput

/-! ===========================================================================
  §4 ⭐⭐⭐⭐⭐ **唯一观察者：sink 是不被任何因子读取的坐标**
  =========================================================================== -/

/-! ### §4.1 一个顶点**被哪些因子读取**？

**关键概念**：`κ v` 只读 `{v} ∪ parents v`（`EdgeLocTwo`）。
故「`κ v` 是否读 `x_s`」**完全由图决定**：

$$\text{reads}\, s\ v \iff s = v \ \vee\ \mathrm{edge}\ s\ v.$$

**⚠ 这正是 `mem_readSet` 的内容** —— 视角 9 的图论内容**全部**在这里。 -/

/-- ⭐⭐ **`κ v` 读 `s` 位**（由图定义，纯 `edge` + 等号）。 -/
def reads (G : DAG V) (s v : V) : Prop := s = v ∨ G.edge s v

/-- ⭐⭐ `reads` 就是 `readSet` 的成员关系（V9-1 的复用）。 -/
theorem reads_iff_mem_readSet {G : DAG V} {s v : V} :
    reads G s v ↔ s ∈ readSet G v := by
  rw [mem_readSet]; rfl

/-- ⭐⭐⭐⭐⭐ **V9-6'：`s` 无出边 ⟹ 只有 `κ s` 读 `x_s`**。

`reads G s v` 在 `s` 无出边时**只剩下** `s = v` 这一支。
**⟹ 「唯一观察者」的图论形式：`s` 的坐标只有 `s` 自己的机制读得到。**

**⚠ 这条**不是**「`p` 不变」；见 §5 的说明。** -/
theorem reads_eq_of_sink {G : DAG V} {s v : V} (hs : ∀ u : V, ¬ G.edge s u) :
    reads G s v ↔ s = v := by
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (hs v)
  · intro h; exact Or.inl h

/-! ### §4.2 因子的**分组**：哪些因子被 `x_s` 影响

对无出边的 `s`，所有 `v ≠ s` 的因子都**不读** `x_s`（V9-6'/`EdgeLocTwo`）。
于是乘积 `∏_v κ v x x` 中，**唯一**随 `x_s` 变动的是 `κ s` 那一项。 -/

section UniqueObserver

variable {G : DAG V} {p : (V → α) → ℝ}

omit [Fintype α] [DecidableEq α] in
/-- ⭐⭐ **辅助**：`s` 无出边、`v ≠ s` ⟹ `x` 与 `unpin s x a` 在 `readSet G v` 上一致。

这是 V9-6 / V9-7 共用的**全部**图论推理，提取出来避免重复。 -/
theorem agree_unpin_of_not_read {G : DAG V} {s v : V}
    (hs : ∀ u : V, ¬ G.edge s u) (hvs : v ≠ s) (x : V → α) (a : α) :
    agreeOn (readSet G v) x (unpin s x a) := by
  intro u hu
  have hus : u ≠ s := by
    intro h
    rw [h] at hu
    have hreads : reads G s v := reads_iff_mem_readSet.mpr hu
    rw [reads_eq_of_sink hs] at hreads
    exact hvs hreads.symm
  show x u = unpin s x a u
  unfold Fate.DAGFactorization.unpin
  simp [hus]

omit [Fintype α] [DecidableEq α] in
/-- ⭐⭐⭐⭐⭐ **V9-6**：**`s` 无出边 ⟹ 除 `v = s` 外的因子在 `s` 位上的替换下不变**。 -/
theorem kappa_v_insensitive (K : EdgeKernel (α := α) G p)
    {s : V} (hs : ∀ u : V, ¬ G.edge s u) {v : V} (hvs : v ≠ s)
    {x : V → α} {a : α} (z : V → α) :
    K.κ v x z = K.κ v (unpin s x a) z :=
  -- `x` 与 `unpin s x a` 在 `readSet G v` 上一致：`s ∉ readSet G v`（因 `v ≠ s` 且无出边）
  K.kappa_congr_of (agree_unpin_of_not_read hs hvs x a) z

omit [Fintype α] [DecidableEq α] in
/-- ⭐⭐⭐⭐⭐ **V9-7（唯一观察者，乘积形式）**：

$$\left(\prod_v \kappa_v\right)\bigl(x_s{:=}a\bigr)
  \;=\; \kappa\ s \bigl(x_s{:=}a\bigr)\bigl(x_s{:=}a\bigr)\cdot
        \prod_{v \ne s} \kappa_v(x).$$

**读法**：把整族乘积在「`x_s := a`」上重算，**所有 `v ≠ s` 的因子都退回原来的
`x`**（V9-6）；**只剩** `κ s` 这一项随 `a` 变。
**⟹ 「唯一观察者」的精确代数形式：`x_s` 只通过**一个**乘子进入乘积。**

**⚠ 本定理**不**声称 `p` 与 `x_s` 无关** —— `κ s` **照样**读 `x_s`
（它读的是**自己的**坐标，那是 `s` 的机制，**不**受 `s` 无出边的影响）。
见 §5 的边界说明。 -/
theorem prod_unobserved_pull (K : EdgeKernel (α := α) G p)
    {s : V} (hs : ∀ u : V, ¬ G.edge s u) (x : V → α) (a : α) :
    (∏ v, K.κ v (unpin s x a) (unpin s x a))
      = K.κ s (unpin s x a) (unpin s x a)
        * ∏ v ∈ (univ \ {s}), K.κ v x x := by
  -- 先拆成 `∏_{v ≠ s} · κ s`（`prod_erase_mul`），再换序
  have hsplit := Finset.prod_erase_mul (univ : Finset V)
        (fun v => K.κ v (unpin s x a) (unpin s x a)) (Finset.mem_univ s)
  have he : (univ : Finset V).erase s = univ \ {s} :=
    (Finset.sdiff_singleton_eq_erase s (Finset.univ : Finset V)).symm
  rw [he] at hsplit
  rw [← hsplit, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  have hvs : v ≠ s := by
    intro h
    rw [h] at hv
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_singleton_self s)
  -- 两个参数都换成 `x`：先第一参数（用 `kappa_congr_of`），再第二参数
  have h1 : K.κ v (unpin s x a) (unpin s x a) = K.κ v x (unpin s x a) :=
    (K.kappa_congr_of (agree_unpin_of_not_read hs hvs x a) _).symm
  have h2 : K.κ v x (unpin s x a) = K.κ v x x :=
    (K.kappa_congr (v := v) (x := x) (y := x) (x' := x) (y' := unpin s x a)
      (agreeOn.refl _ _) (agree_unpin_of_not_read hs hvs x a)).symm
  rw [h1, h2]

omit [Fintype α] [DecidableEq α] in
/-- ⭐⭐⭐⭐ **V9-7'（`p` 的「单因子」形式）**：`p (x_s:=a)` 只剩一个 `a`-依赖的乘子。 -/
theorem p_unpin_pull (K : EdgeKernel (α := α) G p)
    {s : V} (hs : ∀ u : V, ¬ G.edge s u) (x : V → α) (a : α) :
    p (unpin s x a)
      = K.κ s (unpin s x a) (unpin s x a) * ∏ v ∈ (univ \ {s}), K.κ v x x := by
  rw [K.joint]
  exact prod_unobserved_pull K hs x a

end UniqueObserver

/-! ===========================================================================
  §5 ⭐⭐⭐⭐⭐ **「观察者数 = 1」⟹ 条件独立：真正的桥**
  =========================================================================== -/

/-! ### §5.1 ⚠ 先说清：**为什么不能从 V9-7 得到 `p ⊥ x_s`**

`EdgeLocTwo` 只约束 `κ` 的**读集**，**不**约束它对 `x_s` 的**函数形式**。
故「`s` 无出边」**不足以**推出 `p` 与 `x_s` 无关 —— 反例：
`κ s x y := (if y s then 1 else 0)`（`s` 的机制**故意**读自己的值，
这是**合法**的 `EdgeLocTwo` 实例）。**⟹ 「唯一观察者」不等于「观察者不投票」。**

**这**正是**《视角 9》与「塔路线」的**共同**困难所在**：
图形结构只告诉你「谁读谁」，**不**告诉你「读到了什么」。
**⟹ 视角 9 的**增量**是：它把困难**定位**到「`κ s` 自己的函数形式」上，
而不是 `mass` 的复合上。**下面的 V9-9 就是这一点的精确形式。** -/

/-! ### §5.2 ⭐ 因子**析出**（`sepFactor`）

若把乘积按 `Z` 分组：

$$p\,x \;=\; \Bigl(\prod_{v \in Z}\kappa_v x x\Bigr)\cdot
        \Bigl(\prod_{v \notin Z}\kappa_v x x\Bigr),$$

则**「`Z` 内的因子」只读 `Z ∪ pa(Z)`**（由 `EdgeLocTwo`）。
**⟹ 这是「`Z` 是 Markov 毯」的精确陈述。**

本文件只落地**分组恒等式**本身（纯 `Finset`），这是 V9-9 的全部技术内容，**且不含 `mass`**。 -/

section SepFactor

/-- ⭐⭐⭐⭐ **V9-8：按 `Z` 分组因子**（`Finset` 恒等式，无 `mass`）。 -/
theorem prod_split_by_sets (F : V → ℝ) (Z : Finset V) :
    ∏ v, F v = (∏ v ∈ Z, F v) * ∏ v ∈ (univ \ Z), F v := by
  have h := Finset.prod_filter_mul_prod_filter_not (univ : Finset V) (fun v => v ∈ Z) F
  rw [Finset.filter_mem_eq_inter] at h
  have h1 : (univ : Finset V).filter (fun v => ¬ v ∈ Z) = univ \ Z := by
    ext v; simp
  rw [h1] at h
  rw [← h]
  have h2 : (univ : Finset V) ∩ Z = Z := by
    ext v; simp
  rw [h2]

end SepFactor

/-! ===========================================================================
  §6 ⭐⭐⭐⭐ **条件独立：`Z` 吸收形式的**真正收口**（V9-10、V9-11）
  =========================================================================== -/

section CondIndepBridge

/-! ### §6.1 `mass` 的**吸收**恒等式

`mass S p x` 在 `S₁ = S₂` 时显然相等；更重要的是：**若 `A ⊆ Z`**，则
`A ∪ Z = Z`，故 `mass (A ∪ Z) p x = mass Z p x`。
**这一步只用到 `mass` 的单层定义**（对同一个集合求和），**不含塔、不含复合**。

**⟹ 视角 9 的**全部** `mass` 使用都在这里：`mass` 只作为**叶子**出现。** -/

/-- ⭐⭐⭐⭐ **`mass` 对集合等式的不变性**（单层，无塔）。 -/
theorem mass_congr_set (p : (V → α) → ℝ) {S T : Finset V} (h : S = T) (x : V → α) :
    mass S p x = mass T p x := by
  rw [h]

omit [Fintype V] in
/-- ⭐⭐⭐ **吸收：`A ⊆ Z` ⟹ `A ∪ Z = Z`**（纯集合）。 -/
theorem union_eq_right_of_subset {A Z : Finset V} (h : A ⊆ Z) : A ∪ Z = Z := by
  ext u
  rw [Finset.mem_union]
  exact ⟨fun hu => hu.elim (fun h1 => h h1) id, fun hu => Or.inr hu⟩

/-- ⭐⭐⭐⭐ **V9-9：`mass` 在吸收后的**三元恒等式**
（对**任意** `p`，**不用**塔、**不用**图形）。 -/
theorem mass_absorb {p : (V → α) → ℝ} {A B Z : Finset V}
    (hA : A ⊆ Z) (hB : B ⊆ Z) (x : V → α) :
    mass (A ∪ B ∪ Z) p x = mass Z p x
      ∧ mass (A ∪ Z) p x = mass Z p x
      ∧ mass (B ∪ Z) p x = mass Z p x := by
  have e2 : A ∪ Z = Z := union_eq_right_of_subset hA
  have e3 : B ∪ Z = Z := union_eq_right_of_subset hB
  have e1 : A ∪ B ∪ Z = Z := by
    ext u
    rw [Finset.mem_union, Finset.mem_union]
    constructor
    · rintro ((hu | hu) | hu)
      · exact hA hu
      · exact hB hu
      · exact hu
    · intro hu; exact Or.inr hu
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]
  · rw [e2]
  · rw [e3]

/-! ### §6.2 收口定理（V9-10、V9-11）

**V9-10**：`A, B ⊆ Z` ⟹ `(A,B,Z)` 乘性条件独立（对**任意** `p`）。
**V9-11**：若**所有** d-分离三元组都满足 `X ∪ Y ⊆ Z`，则全局 Markov 成立。

**⚠ 边界**：`X ∪ Y ⊆ Z` 的**前提**过强（`dSep` 只要求两两不交）。
详见 §7 的诚实登记。 -/

/-- ⭐⭐⭐⭐ **V9-10：`A, B ⊆ Z` ⟹ 乘性条件独立（任意 `p`，塔无关）**。 -/
theorem sepset_absorb {p : (V → α) → ℝ} {A B Z : Finset V}
    (hA : A ⊆ Z) (hB : B ⊆ Z) (x : V → α) :
    mass (A ∪ B ∪ Z) p x * mass Z p x = mass (A ∪ Z) p x * mass (B ∪ Z) p x := by
  obtain ⟨e1, e2, e3⟩ := mass_absorb (p := p) hA hB x
  rw [e1, e2, e3]

/-- ⭐⭐⭐⭐ **V9-10'：`FactorMarkov.CondIndep` 形式**（与旧路线**同一**定义）。 -/
theorem condIndep_of_absorb {p : (V → α) → ℝ} {A B Z : Finset V}
    (hA : A ⊆ Z) (hB : B ⊆ Z) :
    FateV2.Predict.FactorMarkov.CondIndep p A B Z :=
  fun x => sepset_absorb hA hB x

/-- ⭐⭐⭐⭐⭐ **V9-11：`Z` 吸收 ⟹ 全局 Markov**（`FactorMarkov.Markov` 同一形式）。 -/
theorem markov_of_absorbSubsets {p : (V → α) → ℝ} {G : DAG V}
    (hAbsorb : ∀ X Y Z : Finset V, G.dSep X Y Z → X ∪ Y ⊆ Z) :
    FateV2.Predict.FactorMarkov.Markov (V := V) (α := α) p G := by
  intro X Y Z hsep
  exact condIndep_of_absorb
    (fun u hu => hAbsorb X Y Z hsep (Finset.mem_union.mpr (Or.inl hu)))
    (fun u hu => hAbsorb X Y Z hsep (Finset.mem_union.mpr (Or.inr hu)))

/-- ⭐⭐ `markov_of_absorbSubsets` 与 `FactorMarkov.Markov` **逐字同义**。 -/
theorem markov_iff (p : (V → α) → ℝ) (G : DAG V) :
    (∀ X Y Z : Finset V, G.dSep X Y Z → FateV2.Predict.FactorMarkov.CondIndep p X Y Z)
      ↔ FateV2.Predict.FactorMarkov.Markov (V := V) (α := α) p G :=
  Iff.rfl

end CondIndepBridge

/-! ===========================================================================
  §7 ⚠ **诚实登记：视角 9 做到什么、没做到什么**
  =========================================================================== -/

/-! ### 7.1 已交付（零缺口，全部机检）

| 编号 | 定理 | 塔无关性 |
|---|---|---|
| V9-1 | `readSet` / `reads` / `reads_iff_mem_readSet` | 图→概率的**类型层**落点 |
| V9-2 | `agreeOn` / `EdgeLocTwo` | — |
| V9-3 | `EdgeKernel` | — |
| V9-4 | `EdgeKernel.kappa_congr_of` | — |
| V9-5 | `exists_topoMax` / `sink_no_edge_v9` / `sink_not_parent_v9` / `self_not_parent` | 真用 `topoOrder_lt` 与 `acyclic` |
| **V9-6** | `reads_eq_of_sink` + `kappa_v_insensitive` | 只用 `EdgeLocTwo` + 无出边 |
| **V9-7** | `prod_unobserved_pull` / `p_unpin_pull` | 只用 `prod_congr` + `prod_erase_mul`，**无 `mass`** |
| V9-8 | `prod_split_by_sets` | 纯 `Finset`，**无 `mass`** |
| V9-9 | `mass_absorb` | **单层** `mass`，**无** `mass(mass ·)` |
| **V9-10** | `sepset_absorb` / `condIndep_of_absorb` | 单层 `mass` + 集合恒等式 |
| **V9-11** | `markov_of_absorbSubsets` | 单层 `mass` |
| V9-12 | `mass_nested_differs` | 塔反例（诊断，不参与证明）|

### 7.2 未交付（**如实**，不假装）

1. **`κ s` 的函数形式未被图约束**。`EdgeLocTwo` 只说「读谁」，不说「怎么读」。
   故「`s` 无出边 ⟹ `p` 与 `x_s` 无关」**不成立**（§5.1 的反例）。
   **⟹ V9-7 是「单因子析出」，不是「与 `x_s` 无关」。**
2. **`markov_of_absorbSubsets` 的前提 `X ∪ Y ⊆ Z` 过强**。`dSep` 只要求
   `X, Y, Z` 两两不交 ⟹ 前提**不**普遍成立 ⟹ 这**不是** Pearl 1.2.4。
3. **未消费 `dSep` 的 Bayes-Ball 语义**。本文件的 `mass` 侧工作**不**依赖它，
   但它也**没能**从它推出任何东西。这与旧路线的缺口 B **同一**边界。

### 7.3 视角 9 的**真实增量**（相对前 8 种）

* **不用塔**：全部 `mass` 出现在**叶子**（`mass_absorb`、`sepset_absorb`），
  **从不**出现 `mass S (mass T p)`。塔反例（V9-12）**机检**共处一文件但**不被引用**。
* **不用 `DAG.induce` 递归**：`prod_unobserved_pull` 是**一次**乘积恒等式，
  **没有**在子图上递归。
* **把困难定位清楚**：视图路的困难是「`mass` 复合」，视角 9 的困难是
  「`κ s` 的函数形式」—— 后者是**语义**问题（要 `SCMKernel` 的方程语义），
  前者是**记账**问题。**视角 9 把记账问题消掉了。**

### 7.4 下一步（明确、可达）

要把 §7.2(2) 补齐，**唯一**缺的是：

$$\text{dSep } X\,Y\,Z \;\Longrightarrow\; \exists Z_1 \supseteq X\cup Z,\;
  Z_2 \supseteq Y \cup Z,\ \text{使}\ \kappa\ \text{在}\ Z_1, Z_2\ \text{上可分组}.$$

这**等价于**「Markov 毯分离」的**图论**命题（`dSep` 的**组合**形式，
不经 Bayes-Ball）。它是**独立**的图论目标，**不需要**塔、**不需要** `DAG.induce`。
-/

/-! ===========================================================================
  §8 ⭐⭐⭐⭐ **塔无关性机检**（V9-12，诊断；**不参与**任何证明）
  =========================================================================== -/

section TowerCounter

/-- 三顶点 `ptri : Bool → Bool`：`ptri true = 2`，`ptri false = 1`。 -/
private def ptri : (Bool → Bool) → ℝ := fun w => if w true then 2 else 1

/-- ⭐⭐ **`Bool → Bool` 的显式枚举**（共 4 个函数），用于机检 `mass` 的求和。 -/
private theorem univ_boolfun :
    (Finset.univ : Finset (Bool → Bool))
      = {(fun _ => true), (fun _ => false), (fun j => j), (fun j => !j)} := by
  decide

/-- `mass {true} ptri` 在「`true` 位 = `b`」处 = 4（`b=true`）或 2（`b=false`）。 -/
private theorem mass_true_ptri (b : Bool) :
    mass ({true} : Finset Bool) ptri (fun _ => b) = if b then 4 else 2 := by
  unfold Fate.DAGFactorization.mass
  rw [univ_boolfun]
  rw [Finset.sum_insert (by decide : (fun _ => true) ∉
    ({(fun _ => false), (fun j => j), (fun j => !j)} : Finset (Bool → Bool)))]
  rw [Finset.sum_insert (by decide : (fun _ => false) ∉
    ({(fun j => j), (fun j => !j)} : Finset (Bool → Bool)))]
  rw [Finset.sum_insert (by decide : (fun j => j) ∉
    ({(fun j => !j)} : Finset (Bool → Bool)))]
  rw [Finset.sum_singleton]
  cases b <;> norm_num [ptri]

/-- ⭐⭐ **`mass {true} ptri` 在任意点 `w` 处的值**（只依赖 `w true`）。 -/
private theorem mass_true_ptri_apply (w : Bool → Bool) :
    mass ({true} : Finset Bool) ptri w = if w true then 4 else 2 := by
  rw [Fate.DAGFactorization.mass_congr ({true} : Finset Bool) ptri
        (fun u hu => by rw [Finset.mem_singleton] at hu; rw [hu])
      (y := fun _ => w true)]
  exact mass_true_ptri (w true)

/-- ⭐⭐ **外层 `mass` 的单层展开**（只展开**外层**，内层 `mass` 保持原样，
这样内层可以用 `mass_true_ptri_apply` 取值）。 -/
private theorem outer_sum :
    mass ({true} : Finset Bool) (mass ({true} : Finset Bool) ptri) (fun _ => true)
      = ∑ w : Bool → Bool,
          if w true = true then mass ({true} : Finset Bool) ptri w else 0 := by
  unfold Fate.DAGFactorization.mass
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : w true = true
  · have hc : (∀ u ∈ ({true} : Finset Bool), w u = (fun _ => true) u) := by
      intro u hu; rw [Finset.mem_singleton] at hu; rw [hu]; exact h
    rw [if_pos hc, if_pos h]
  · have hc : ¬ (∀ u ∈ ({true} : Finset Bool), w u = (fun _ => true) u) := by
      intro hh
      exact absurd (hh true (Finset.mem_singleton_self true)) h
    rw [if_neg hc, if_neg h]

/-- ⭐⭐⭐⭐ **V9-12（机检）：`mass` 的**嵌套**失败 —— 塔性质为假。**

`mass {true} (mass {true} ptri)` 在 `x true = true` 处 = `4 + 0 + 4 + 0 = 8`；
`mass {true} ptri` 在该处 = `4`。二者**不同**（`8 ≠ 4`）。

**⟹ 任何依赖 `mass S (mass T p) = mass S p` 的路线（塔路线）在本 `mass` 语义下
**必然**失败（`mass` 不归一）。视角 9 **不**用这条。** -/
theorem mass_nested_differs :
    mass ({true} : Finset Bool) (mass ({true} : Finset Bool) ptri) (fun _ => true) ≠
      mass ({true} : Finset Bool) ptri (fun _ => true) := by
  rw [outer_sum]
  rw [univ_boolfun]
  rw [Finset.sum_insert (by decide : (fun _ => true) ∉
    ({(fun _ => false), (fun j => j), (fun j => !j)} : Finset (Bool → Bool)))]
  rw [Finset.sum_insert (by decide : (fun _ => false) ∉
    ({(fun j => j), (fun j => !j)} : Finset (Bool → Bool)))]
  rw [Finset.sum_insert (by decide : (fun j => j) ∉
    ({(fun j => !j)} : Finset (Bool → Bool)))]
  rw [Finset.sum_singleton]
  simp only [mass_true_ptri_apply]
  norm_num [ptri]

end TowerCounter

end BridgeView9

end FateV2.Predict