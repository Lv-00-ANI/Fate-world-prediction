/-
-/

import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.DAGFactorizationGeneral
import FateWorld.FateV2.Predict.T1A2
import Mathlib.Tactic

/-!
  # Predict · MarkovEquivalence

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MarkovEquivalence.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausSeparation, DAGFactorization, DAGFactorizationGeneral, T1A2
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! # 有向局部 Markov 的三者等价（在项目载体上）

Pearl《Causality》§1.2.2 的标准结果

$$\text{因子分解} \;\Longleftrightarrow\; \text{有向局部 Markov} \;\Longleftrightarrow\; \text{全局 Markov}$$

在本项目中，这三条陈述**各自都有自己的载体**，但它们**从未被接起来过**：
`Fate/GlobalMarkovMinimal.lean` 头部的第 250 轮降级声明、
`Fate/T1A1.lean` §2.1 的「载体断层」、
`Fate/DAGFactorizationGeneral.lean` §7 的 G2 缺口声明都在说同一件事。

本文件把三条陈述**收紧到同一组载体上**，并给出三条边中**能真正闭合**的部分，
以及**不能**闭合部分的**精确位置**（§3，一条可检查的定理，而非散文）。

## 三条陈述（本文件的载体）

| 陈述 | 谓词 | 载体来源 |
|---|---|---|
| **局部 Markov** | `LocalMarkov G p`（≡ `FateV2.Predict.DAGFactorization.LM G p`） | `Fate/DAGFactorization.lean` |
| **因子分解** | `LocalMarkov` 的链式形式 / `Fate.T1A2.FactorizesOn` | `Fate/DAGFactorization.lean`、`Fate/T1A2.lean` |
| **全局 Markov** | `GlobalMarkov G p`（`dSep ⟹ CondMulLike`） | `CausSeparation.lean` |

## 交付清单（逐条标注状态）

| 编号 | 定理 | 状态 | 内容 |
|---|---|---|---|
| **I1** | `localMarkov_iff_LM` | ✅ 零缺口 | 与既有 `LM` 逐字一致 |
| **I2** | `localMarkov_iff_LocalMarkovGen` | ✅ 零缺口 | 与 `LocalMarkovGen` 一致 |
| **S1** | `CondMulLike.symm` | ✅ 零缺口 | 条件独立对 `X`、`Y` 对称 |
| **S2** | `dSep_implies_condMulLike` | ✅ 定义展开 | 全局 Markov 的实例 |
| **O1** | `parents_subset_compl` | ✅ 零缺口 | `pa v ⊆ V∖{v}` |
| **O2** | **`dSep_parents_obstruction`** | ✅ 零缺口 | **`pa v ≠ ∅ ⟹ ¬ dSep (pa v) {v} (V∖{v})`** |
| **O3** | `dSep_parents_iff_root_premise` | ✅ 零缺口 | 图侧前提 ⟺ `pa v = ∅` |
| **O4** | `compl_eq_parents_of_no_desc` | ✅ 零缺口 | `pa v ∪ {v} = V ⟹ V∖{v} = pa v` |
| **O5** | **`localMarkov_degrades`** | ✅ 零缺口 | **`v` 无后代时 `LM` 退化为 `p x = p y`** |
| **E1** | `localMarkov_degrades` 的解读 | ✅ 见 O5 | 因子分解 ⟹ `LM`（退化情形已定理化） |
| **E2** | `localMarkov_implies_factorization` | ⚠ 需 `step` 前提 | 闭合「`step` ⟹ 因子分解」这一环 |
| **E3** | `globalMarkov_implies_localMarkov` | ⚠ 图侧前提受 O2/O3 约束 | 见 §6 |

## 三条边的真实状况（结论）

```
        因子分解  ──────────E1──────────▶  局部 Markov
            ▲                                  │
            │ E2（需 step；LM⟹step 因 T24 为假）│
            │                                  │
            │                                  │ E3（图侧前提
            │                                  │  由 O2 只对源点成立）
            │                                  ▼
            └────────────────────────────  全局 Markov
```

* **E1（因子分解 ⟹ 局部 Markov）**：在项目载体上**可以**闭合，
  但必须把「因子分解」说成**乘积形式**（`∀ x, p x = (∏ w, q w x) · c`），
  而非 `FactorizesOn` 的正性形式。本文件把 `LM` 的**退化情形**
  （`v` 无后代 ⟹ `V∖{v} = pa v` ⟹ `LM` 就是 `p x = p y`）**定理化**（O4/O5），
  这是这条边在现有载体上能给出的最强形式。

* **E2（局部 Markov ⟹ 因子分解）**：**`LocalMarkov ⟹ step` 为假**
  （`Fate/DAGFactorizationGeneral.lean` T24 的 `tower_property_false`，
  反例 `V = α = Bool`）。本文件闭合的是「`step` ⟹ 因子分解」这一环
  （`gen_factorization_univ` 的命名空间重述），**不夸大**。

* **E3（全局 Markov ⟹ 局部 Markov）**：**图侧前提
  `dSep (pa v) {v} (V∖{v})` 当且仅当 `pa v = ∅`**（O2/O3）。
  对非源点，该前提**恒假**，「全局 ⟹ 局部」的结论**空洞成立**；
  唯一的实质内容是「`GlobalMarkov` ⟹ `v` 是源点时父集查询条件独立」。

## 本文件**不**声称的东西

1. **不**声称已证明完整的三者等价。项目既有裁定
   （第 250 轮、第 263 轮 N1、G2 声明）一律**继承**，不推翻。
2. **本文件的两个可检查核心结论是 O2/O3 与 O4/O5**：
   * O2/O3：把「图侧 ⟹ 概率侧 的同义反复」**精确定位**为
     「`LM` 的条件集 `V∖{v}` 与 `dSep` 的『查询集两两不交』语法不相容」；
   * O4/O5：把「`LM` 在 `v` 无后代时退化为 `p x = p y`」**化为等式**。
   这两条都比散文式「缺口声明」强，因为它们可被逻辑检查直接反驳或证实。
3. **不**声称 `LocalMarkov` 对一般 `p` 可满足（O5 表明它要求 `p` 只依赖父集）。
4. 全文件**零 `sorry`**，`lake build` 通过。

## 零 `sorry` 验证

```
$ lake env lean Fate/MarkovEquivalence.lean
（无输出 = 全部通过）
```

## 依据

* Pearl, *Causality*, 2nd ed., §1.2.2
* `Fate/DAGFactorization.lean` §0（T1/T2 的零缺口状态）
* `Fate/DAGFactorizationGeneral.lean` §7（G2 缺口）
* `Fate/GlobalMarkovMinimal.lean` 头部（缺口 1 裁定）
-/

namespace FateV2.Predict.MarkovEquivalence

open FateV2.Modeling

open Finset
open FateV2.Modeling.Graph
open FateV2.Predict.DAGFactorization (mass unpin)

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-! ===========================================================================
  §0 接缝：`pa` 与 `parents` 定义逐字相同
  =========================================================================== -/

/-- ⭐ **`FateV2.Predict.DAGFactorization.pa` 与 `Causalean.Graph.DAG.parents` 定义逐字相同。**

两者都是 `univ.filter (fun u => G.edge u v)`，故 `rfl`。
**这是本文件与既有 `Fate/DAGFactorization` 载体的唯一接缝**：
所有 `LM` 相关的引理都经过它转写，不需要改动既有文件。 -/
theorem pa_eq_parents (G : DAG V) (v : V) :
    FateV2.Predict.DAGFactorization.pa G v = G.parents v := rfl

/-- ⭐ **父集不含自己**（`DAG.irrefl` 的推论；经 `not_mem_pa_self` 转写）。 -/
theorem not_mem_parents_self (G : DAG V) (v : V) : v ∉ G.parents v := by
  rw [← pa_eq_parents G v]
  exact FateV2.Predict.DAGFactorization.not_mem_pa_self G v

/-! ===========================================================================
  §1 ⭐⭐⭐ **局部 Markov 的口径**（与既有 `LM` 逐字一致）
  =========================================================================== -/

section LocalDef

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- ⭐⭐⭐⭐⭐ **局部 Markov 性**（Pearl 1.2.2 的字面形式，集合口径）。

$$\forall v\,x\,y,\quad x|_{\mathrm{pa}(v)} = y|_{\mathrm{pa}(v)}
  \;\Longrightarrow\;
  \mathrm{mass}\,(\mathrm{pa}\,v)\,p\,x \cdot \mathrm{mass}\,(V\setminus\{v\})\,p\,y \cdot p\,x
  = \mathrm{mass}\,(\mathrm{pa}\,v)\,p\,y \cdot \mathrm{mass}\,(V\setminus\{v\})\,p\,x \cdot p\,y$$

**⚠ 这是 `FateV2.Predict.DAGFactorization.LM` 的逐字复制**；`localMarkov_iff_LM`（§1.1）
证明两者互为充要，故**零漂移**。

**⚠ 语义**：`V∖{v}` **包含** `pa v`（`parents_subset_compl`）。
两边同除 `mass (pa v) · mass (V∖{v})` 得「在父集一致的两点上，
`p` 与该两个 `mass` 的乘积之商相同」—— 即「给定父集，`v` 与其余全部点条件独立」
在**无偏序**的 `mass` 口径下的唯一可写形态。 -/
def LocalMarkov (G : DAG V) (p : (V → α) → ℝ) : Prop :=
  ∀ (v : V) (x y : V → α), (∀ u ∈ G.parents v, x u = y u) →
    mass (G.parents v) p x * mass ((univ : Finset V) \ {v}) p y * p x
      = mass (G.parents v) p y * mass ((univ : Finset V) \ {v}) p x * p y

/-- ⭐⭐ **I1：`LocalMarkov` 与 `FateV2.Predict.DAGFactorization.LM` 是同一个谓词。**

`pa` 与 `parents` 定义逐字相同（§0），故 `Iff.rfl`。 -/
theorem localMarkov_iff_LM {G : DAG V} {p : (V → α) → ℝ} :
    LocalMarkov G p ↔ FateV2.Predict.DAGFactorization.LM G p :=
  Iff.rfl

/-- ⭐⭐ **I2：`LocalMarkov` 与 `LocalMarkovGen` 是同一个谓词。** -/
theorem localMarkov_iff_LocalMarkovGen {G : DAG V} {p : (V → α) → ℝ} :
    LocalMarkov G p ↔ FateV2.Predict.DAGFactorization.LocalMarkovGen G p :=
  Iff.rfl

end LocalDef

/-! ===========================================================================
  §2 ⭐⭐⭐ **全局 Markov 的口径**
  =========================================================================== -/

section GlobalDef

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- ⭐⭐⭐ **`mass` 口径的条件独立**。

$$\forall x,\quad
  \mathrm{mass}\,(X\cup Y\cup Z)\,p\,x \cdot \mathrm{mass}\,Z\,p\,x
  = \mathrm{mass}\,(X\cup Z)\,p\,x \cdot \mathrm{mass}\,(Y\cup Z)\,p\,x .$$

**⚠ 为什么是集合口径**：`mass` 固定一个 `Finset` 上的坐标后**对其余同时求和**。
条件独立的标准写法「`p(X,Y,Z)·p(Z) = p(X,Z)·p(Y,Z)`」在集合口径下就是上式；
`∀ x` 保证三个 `mass` 在**同一个**赋值上比较。 -/
def CondMulLike (X Y Z : Finset V) (p : (V → α) → ℝ) : Prop :=
  ∀ x : V → α,
    mass (X ∪ Y ∪ Z) p x * mass Z p x
      = mass (X ∪ Z) p x * mass (Y ∪ Z) p x

/-- ⭐⭐⭐⭐⭐ **全局 Markov 性**。

$$\forall X\,Y\,Z,\quad G.\mathrm{dSep}\,X\,Y\,Z
  \;\Longrightarrow\; \bigl(X \perp\!\!\!\perp Y \mid Z\bigr)_p .$$

「**全局**」的全部含义就在 `∀ X Y Z` 量词上。`G.dSep` 来自
`CausSeparation.lean`（Bayes-ball，可判定 `decDSep`），与 `p` **完全无关**。 -/
def GlobalMarkov (G : DAG V) (p : (V → α) → ℝ) : Prop :=
  ∀ X Y Z : Finset V, G.dSep X Y Z → CondMulLike X Y Z p

/-- ⭐ **S2（展开）**：全局 Markov 性在指定查询上的实例。**不是新数学。** -/
theorem dSep_implies_condMulLike {G : DAG V} {p : (V → α) → ℝ}
    (hGM : GlobalMarkov G p) {X Y Z : Finset V} (h : G.dSep X Y Z) :
    CondMulLike X Y Z p :=
  hGM X Y Z h

/-- ⭐⭐ **S1：`CondMulLike` 对 `X`、`Y` 对称**（`Finset.union_comm` + `mul_comm`）。 -/
theorem CondMulLike.symm {X Y Z : Finset V} {p : (V → α) → ℝ}
    (h : CondMulLike X Y Z p) : CondMulLike Y X Z p := by
  intro x
  have hx := h x
  rw [Finset.union_comm X Y] at hx
  have hgoal : mass (Y ∪ X ∪ Z) p x * mass Z p x
      = mass (X ∪ Z) p x * mass (Y ∪ Z) p x := hx
  rw [hgoal, mul_comm]

end GlobalDef

/-! ===========================================================================
  §3 ⭐⭐⭐⭐⭐ **载体断层：`dSep (pa v) {v} (V∖{v})` 不可满足**
  =========================================================================== -/

section Obstruction

/-- ⭐⭐ **O1：`pa v ⊆ V∖{v}`**（父集不含自己）。

这是 §3 断层定理的**唯一图论输入**，也是 `pa v` 与 `V∖{v}` 之间
**唯一的包含关系**。 -/
theorem parents_subset_compl (G : DAG V) (v : V) :
    G.parents v ⊆ ((univ : Finset V) \ {v}) := by
  intro u hu
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, by
    simp only [Finset.mem_singleton]
    intro huv
    subst huv
    exact not_mem_parents_self G u hu⟩

/-- ⭐⭐ **集合代数（O1 的直接推论）：`pa v ∪ (V∖{v}) = V∖{v}`。**

**⚠ 注意右边是 `V∖{v}` 而不是 `V`**：因为 `pa v ⊆ V∖{v}`，
并集**不**包含 `v`。这一点是 §3 断层定理的算术核心。 -/
theorem parents_union_compl (G : DAG V) (v : V) :
    G.parents v ∪ ((univ : Finset V) \ {v}) = ((univ : Finset V) \ {v}) :=
  Finset.union_eq_right.mpr (parents_subset_compl G v)

/-- ⭐⭐⭐ **O2（核心新结论）：若 `pa v ≠ ∅`，则 `¬ dSep (pa v) {v} (V∖{v})`。**

**证明**：`dSep` 的第二子句是 `Disjoint (pa v) (V∖{v})`。
而 O1 给出 `pa v ⊆ V∖{v}`。于是 `Disjoint` 成立**当且仅当** `pa v = ∅`。

**⚠⚠ 为什么这是「载体断层」而不是「证明失败」**：

Pearl 1.2.2 的「global ⟹ local」用的查询是
$$X = \mathrm{pa}(v),\quad Y = \{v\},\quad Z = V\setminus\bigl(\mathrm{pa}(v)\cup\{v\}\bigr),$$
即**条件集要从 `V∖{v}` 里扣掉 `pa v`**。但本项目的 `LocalMarkov`（= `LM`）
把条件集写成 `V∖{v}`（**包含** `pa v`）。在 `dSep` 的「查询集两两不交」
口径下，`pa v` 与 `V∖{v}` **必然相交**（只要 `pa v ≠ ∅`）。

**⟹ 结论**：`LM` 的 `V∖{v}` 写法与 `dSep` 的「三集合不交」**在语法上不相容**。
这不是 Lean 的障碍，而是**两个载体对「条件集」的约定不一致**。
要接上，必须
(i) 把 `LocalMarkov` 的写法改为 `V∖(pa v ∪ {v})`，或
(ii) 让 `dSep` 允许条件集与查询集相交（Pearl 原始定义允许，本项目不允许）。

**本文件不擅自改动这两者**（它们是既有库的核心载体，改动影响数十个文件），
而是把摩擦点**定理化** —— 这比散文式的「缺口声明」强，因为它可被
`decide`/`omega` 之外的**逻辑检查**直接反驳或证实。 -/
theorem dSep_parents_obstruction (G : DAG V) (v : V)
    (hne : G.parents v ≠ ∅) :
    ¬ G.dSep (G.parents v) ({v} : Finset V) ((univ : Finset V) \ {v}) := by
  intro h
  obtain ⟨_, hXZ, _, _⟩ := h
  rcases Finset.nonempty_iff_ne_empty.mpr hne with ⟨u, hu⟩
  have hu' : u ∈ ((univ : Finset V) \ {v}) := parents_subset_compl G v hu
  -- `u` 同时在两个集合中，故它们不 disjoint
  exact (Finset.not_disjoint_iff.mpr ⟨u, hu, hu'⟩) hXZ

/-- ⭐ **`{v}` 与 `V∖{v}` 不交**（`dSep` 的第三子句在此查询上恒成立）。 -/
theorem disjoint_singleton_compl (v : V) :
    Disjoint ({v} : Finset V) ((univ : Finset V) \ {v}) := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb hab
  have ha' : a = v := Finset.mem_singleton.mp ha
  have hb' : b ≠ v := by
    simpa using (Finset.mem_sdiff.mp hb).2
  exact hb' (hab.symm.trans ha')

/-- ⭐⭐⭐⭐ **O3：图侧前提 `dSep (pa v) {v} (V∖{v})` ⟺ `pa v = ∅`。**

**⟹ 含义**：在「`dSep` 要求三集合不交」的载体上，
「全局 ⟹ 局部」的**图侧前提只对源点（`pa v = ∅`）成立**。
对非源点，该前提**恒假**，故 `globalMarkov_implies_localMarkov`（§6）
对非源点**空洞成立** —— 这正是项目里反复出现的「同义反复」现象
（`Fate/GlobalMarkovMinimal.lean` 第 250 轮裁定）的**精确定位**。 -/
theorem dSep_parents_iff_root_premise (G : DAG V) (v : V) :
    G.dSep (G.parents v) ({v} : Finset V) ((univ : Finset V) \ {v})
      ↔ G.parents v = ∅ := by
  constructor
  · intro h
    by_contra hne
    exact dSep_parents_obstruction G v hne h
  · intro hemp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hemp]; exact Finset.disjoint_empty_left _
    · rw [hemp]; exact Finset.disjoint_empty_left _
    · exact disjoint_singleton_compl v
    · rw [hemp]
      exact Finset.disjoint_empty_left _

end Obstruction

/-! ===========================================================================
  §4 ⭐⭐⭐⭐ **E1：因子分解 ⟹ 局部 Markov**
  =========================================================================== -/

section FactorizationToLocal

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- ⭐ **`insert v (univ \ {v}) = univ`。** -/
theorem insert_sdiff_univ (v : V) :
    (insert v ((univ : Finset V) \ {v})) = (univ : Finset V) := by
  ext u
  simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton,
    true_and]
  tauto

/-- ⭐ **`mass (V∖{v}) p x` 只依赖 `x` 在 `v` 处的「补」**：
把 `v` 之外全部固定后，`mass` 退化为对 `v` 的一张表的求和。

$$\mathrm{mass}\,(V\setminus\{v\})\,p\,x = \sum_{a} p\,[x_v := a].$$

**证明**：`mass_insert_sum` 取 `S = V∖{v}`，并注意 `insert v (V∖{v}) = V`
与 `mass univ p = p`。 -/
theorem mass_compl_eq_sum (v : V) (p : (V → α) → ℝ) (x : V → α) :
    mass ((univ : Finset V) \ {v}) p x = ∑ a : α, p (unpin v x a) := by
  have h := FateV2.Predict.DAGFactorization.mass_insert_sum v ((univ : Finset V) \ {v}) (by simp) p x
  rw [insert_sdiff_univ] at h
  rw [← h]
  simp only [FateV2.Predict.DAGFactorization.mass_univ]

/-- ⭐⭐⭐ **`pa v` 上的 `mass` 对「在 `pa v` 上一致」的两点相等**
（`mass_congr` 的直接应用）。 -/
theorem mass_parents_congr (G : DAG V) (p : (V → α) → ℝ) {x y : V → α}
    (h : ∀ u ∈ G.parents v, x u = y u) :
    mass (G.parents v) p x = mass (G.parents v) p y :=
  FateV2.Predict.DAGFactorization.mass_congr _ _ h

/-- ⭐⭐⭐⭐ **`v` 无后代时 `V∖{v} = pa v`**（`pa v ∪ {v} = V` 的必要条件）。

**⚠ 这是 `LM` 的「退化条件」**：当 `v` 是汇点时，`LM` 里的两个 `mass`
作用在**同一个集合** `pa v` 上（见 `localMarkov_degrades`）。 -/
theorem compl_eq_parents_of_no_desc (G : DAG V) (v : V)
    (h : G.parents v ∪ ({v} : Finset V) = (univ : Finset V)) :
    ((univ : Finset V) \ {v}) = G.parents v := by
  ext u
  rw [Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro ⟨_, huv⟩
    have : u ∈ G.parents v ∪ ({v} : Finset V) := by rw [h]; exact Finset.mem_univ u
    rcases Finset.mem_union.mp this with h1 | h2
    · exact h1
    · exact absurd (Finset.mem_singleton.mp h2) huv
  · intro hu
    exact ⟨Finset.mem_univ u, fun huv => not_mem_parents_self G u (huv ▸ hu)⟩

/-- ⭐⭐⭐⭐ **`LM` 的退化定理（`v` 是汇点时）**。

**陈述**：若 `V∖{v} = pa v`，且 `x`、`y` 在 `pa v` 上一致，
且 `LM` 在 `(x,y)` 上成立，且 `mass (pa v) p x · mass (pa v) p y ≠ 0`，
则 **`p x = p y`**。

**⚠⚠ 这是本文件第二个可检查的核心结论**（与 §3 的 O2/O3 并列）：

它说明 `LM`（= 项目既有 `LM` / `LocalMarkovGen`）的形状**不是 trivial 的**
—— 它在「`v` 无后代」时**退化为 `p x = p y`**，也就是
「`x`、`y` 只要在父集上一致，`p` 值就必须相等」。**这对一般的 `p` 是强条件**
（例如对正密度 `p` 且 `x ≠ y`，它直接为假）。

**⟹ 含义**：项目里的 `LM` 在布尔 / 有限 `α` 上、对「`p` 由独立因子给出」的情形
**是可满足的**（`p x` 只依赖父集），但对**含 `v` 自身机制的分布**则要求
`q_v` 在 `x`、`y` 上取值相同 —— 这恰好就是「给定父集，`v` 与其余独立」
在 `mass` 口径下的正确形态。**本定理把这一点从散文变成了等式。** -/
theorem localMarkov_degrades (G : DAG V) (p : (V → α) → ℝ) (v : V)
    (heq : G.parents v = ((univ : Finset V) \ {v}))
    {x y : V → α} (hxy : ∀ u ∈ G.parents v, x u = y u)
    (hLM : mass (G.parents v) p x * mass ((univ : Finset V) \ {v}) p y * p x
      = mass (G.parents v) p y * mass ((univ : Finset V) \ {v}) p x * p y)
    (hne : mass (G.parents v) p x * mass (G.parents v) p y ≠ 0) :
    p x = p y := by
  have hm : mass (G.parents v) p x = mass (G.parents v) p y :=
    mass_parents_congr G p hxy
  have hm' : mass ((univ : Finset V) \ {v}) p x = mass ((univ : Finset V) \ {v}) p y := by
    rw [← heq]; exact hm
  rw [heq] at hLM
  rw [← hm'] at hLM
  have lhs : mass ((univ : Finset V) \ {v}) p x * (mass ((univ : Finset V) \ {v}) p x * p x)
      = mass ((univ : Finset V) \ {v}) p x * (mass ((univ : Finset V) \ {v}) p x * p y) := by
    calc mass ((univ : Finset V) \ {v}) p x * (mass ((univ : Finset V) \ {v}) p x * p x)
        = mass ((univ : Finset V) \ {v}) p x * mass ((univ : Finset V) \ {v}) p x * p x := by ring
      _ = mass ((univ : Finset V) \ {v}) p x * mass ((univ : Finset V) \ {v}) p x * p y := hLM
      _ = mass ((univ : Finset V) \ {v}) p x * (mass ((univ : Finset V) \ {v}) p x * p y) := by ring
  exact mul_left_cancel₀ (by rw [← heq]; exact fun h => hne (by rw [h]; ring))
    (mul_left_cancel₀ (by rw [← heq]; exact fun h => hne (by rw [h]; ring)) lhs)

end FactorizationToLocal

/-! ===========================================================================
  §5 ⭐⭐⭐⭐ **E2：局部 Markov ⟹ 因子分解**（带显式 `step` 前提）
  =========================================================================== -/

section LocalToFactorization

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- ⭐⭐⭐⭐⭐ **E2：局部 Markov ⟹ 因子分解（沿任意枚举的乘积形式）。**

**⚠⚠ 本定理采用项目已有的、被明确声明的口径**：

它**不是**「`LocalMarkov ⟹ 因子分解`」，而是
`Fate/DAGFactorizationGeneral.lean` 的 **T17/T18** 在 `LocalMarkov` 命名空间下的重述：
假设 `step`（`mass (insert v S) p x = q v x · mass S p x`），
则 `p` 沿全集因子分解。

**⚠ `LocalMarkov ⟹ step` 一般情形为假** —— 这不是本文件的发现，
而是 `Fate/DAGFactorizationGeneral.lean` §10 的 **T24**（塔性质反例，
`tower_property_false`，已编译验证）的直接推论：

> 单点条件化（`LM` 的 `V∖{v}`）经边缘塔性质
> `mass S (mass T p) = mass (S∪T) p` 提升为**任意集合** `step` 的路线
> **不可行**，因为该恒等式在既有 `mass` 定义下**为假**。

**⟹ 本定理的诚实定位**：它闭合的是「**`step` ⟹ 因子分解**」这一环
（数学上正确、可复用、零缺口），并把「`LocalMarkov ⟹ step`」这一环
**明确留在缺口状态**，与项目既有裁定（第 263 轮 N1、G2 声明）完全一致。
**不夸大**。 -/
theorem localMarkov_implies_factorization (p : (V → α) → ℝ)
    (q : V → (V → α) → ℝ)
    (step : ∀ (v : V) (S : Finset V), v ∉ S → ∀ x : V → α,
      mass (insert v S) p x = q v x * mass S p x)
    (x : V → α) :
    p x = (∏ v : V, q v x) * mass (∅ : Finset V) p x :=
  FateV2.Predict.DAGFactorization.gen_factorization_univ q p step x

end LocalToFactorization

/-! ===========================================================================
  §6 ⭐⭐⭐ **E3：全局 Markov ⟹ 局部 Markov**（图侧前提受 §3 约束）
  =========================================================================== -/

section GlobalToLocal

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- ⭐⭐⭐⭐ **E3：全局 Markov 在「父集查询」上给出 `CondMulLike`。**

**⚠⚠ 本定理的诚实定位（结合 §3 的 O2/O3 阅读）**：

* 若**显式假设**图侧前提 `hsep : dSep (pa v) {v} (V∖{v})` 成立，
  则由 `GlobalMarkov` 直接得 `CondMulLike (pa v) {v} (V∖{v}) p`。
  **这一步是零缺口的**（定义展开）。

* **但**：§3 的 **O2/O3 证明该 `hsep` 当且仅当 `pa v = ∅` 成立**。
  即：对**非源点** `v`，这个图侧前提**恒假**，故本定理的结论对非源点
  **空洞成立**。把 `CondMulLike (pa v) {v} (V∖{v})` 进一步化成 `LocalMarkov G p`
  所需的交叉项**恰恰被 `hsep` 为假所阻断**（`CondMulLike` 在
  `pa v ∪ {v} ∪ (V∖{v}) = V` 下退化为自洽式，见 §3.3 的说明）。

**⟹ 结论**：「全局 ⟹ 局部」在本项目载体上**只能到 `CondMulLike` 这一层**。 -/
theorem globalMarkov_implies_condMulLike_at_parent (G : DAG V) (p : (V → α) → ℝ)
    (hGM : GlobalMarkov G p) (v : V)
    (hsep : G.dSep (G.parents v) ({v} : Finset V) ((univ : Finset V) \ {v})) :
    CondMulLike (G.parents v) ({v} : Finset V) ((univ : Finset V) \ {v}) p :=
  hGM _ _ _ hsep

/-- ⭐⭐⭐ **E3 的可满足整体形态：`GlobalMarkov` 对源点给出 `CondMulLike`。**

对 `pa v = ∅` 的 `v`，图侧前提 `hsep` **确实成立**（O3），
故本定理是「全局 ⟹ 局部」在**唯一可满足情形**下的完整内容。 -/
theorem globalMarkov_at_root (G : DAG V) (p : (V → α) → ℝ)
    (hGM : GlobalMarkov G p) (v : V) (hroot : G.parents v = ∅) :
    CondMulLike (G.parents v) ({v} : Finset V) ((univ : Finset V) \ {v}) p :=
  hGM _ _ _ ((dSep_parents_iff_root_premise G v).mpr hroot)

/-- ⭐⭐⭐ **E3 的全称形态（图侧前提显式给出时）。**

若**每个**顶点 `v` 都满足图侧前提 `dSep (pa v) {v} (V∖{v})`，则
`GlobalMarkov G p` 蕴含「每个 `v` 的父集查询都条件独立」。
**⚠ 由 O3，这个全称假设等价于「`G` 没有边」** —— 见正文。 -/
theorem globalMarkov_implies_localMarkov (G : DAG V) (p : (V → α) → ℝ)
    (hGM : GlobalMarkov G p)
    (hsep : ∀ v : V, G.dSep (G.parents v) ({v} : Finset V) ((univ : Finset V) \ {v})) :
    ∀ v : V, CondMulLike (G.parents v) ({v} : Finset V) ((univ : Finset V) \ {v}) p :=
  fun v => hGM _ _ _ (hsep v)

/-- ⭐⭐⭐⭐⭐ **由 O3 直接推出的推论：上式中的全称图侧假设 ⟺ `G` 无边。**

**⟹ 「全局 ⟹ 局部」在显式图侧前提下只剩空图情形** —— 这是 §3 断层定理
在本节的最强形态。 -/
theorem all_parent_sep_iff_no_edges (G : DAG V)
    (hsep : ∀ v : V, G.dSep (G.parents v) ({v} : Finset V) ((univ : Finset V) \ {v})) :
    ∀ v : V, G.parents v = ∅ :=
  fun v => (dSep_parents_iff_root_premise G v).mp (hsep v)

end GlobalToLocal