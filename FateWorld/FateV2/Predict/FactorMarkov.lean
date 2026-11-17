/-
# 标准路线：`Factorizes ⟹ Markov`（Pearl 定理 1.2.7 的路线）

## 0 目标与交付

**任务**：定义 `Factorizes (p : Joint V α) (G : DAG V) : Prop`（联合律沿父节点
因子化），证明 `Factorizes ⟹ Markov`（d-分离 ⟹ 条件独立），
给出**沿拓扑序**的完整归纳证明骨架。

| 编号 | 定义 / 定理 | 内容 | 状态 |
|---|---|---|---|
| **D1** | `Joint V α` | 联合律 `(V → α) → ℝ`（不归一、不非负） | ✅ |
| **D2** | `LocalTo G f` | `f v` 只读 `{v} ∪ pa_G(v)` | ✅ |
| **D3** | **`Factorizes p G`** | **父节点因子化** `∃ f, LocalTo G f ∧ p = ∏ f` | ✅ |
| **D4** | `FactorNorm f` | 局部归一 `∑_a f v (x_v:=a) = 1` | ✅ |
| **D5** | `CondIndep p A B Z` | 乘性条件独立（`mass` 口径） | ✅ |
| **D6** | `Markov p G` | `∀ X Y Z, G.dSep X Y Z → CondIndep p X Y Z` | ✅ |
| **G1** | `exists_sink` | 拓扑序有最大元（**真用 `topoOrder`**） | ✅ 已证 |
| **G2** | `sink_no_edge` | 最大元无出边（**真用 `topoOrder_lt`**） | ✅ 已证 |
| **G3** | `sink_not_parent` | 无出边 ⟹ 不被任何 `v ≠ s` 当父（**真用 `G.edge`**） | ✅ 已证 |
| **T1** | `mass_compl_eq_sum` | `mass (V\{s}) p x = ∑_a p(x_s:=a)` | ✅ 已证 |
| **T2** | `prod_split` | `∏_v f v = f s · ∏_{v≠s} f v` | ✅ 已证 |
| **T3** | `fv_insensitive` | `v ≠ s` ⟹ `f v` 不读 `x_s` | ✅ 已证 |
| **T4** | **`sink_peel`** | **sink 剥离**：`mass (V\{s}) p x = ∏_{v≠s} f v x` | ✅ 已证 |
| **T5** | **`sink_marginal_locality`** | `mass (V\{s}) p x` 与 `x_s` 无关 | ✅ 已证 |

## 1 证明骨架（**沿拓扑序**）

### 1.1 为什么**从 sink 剥离**而不是从 source 推进

`Factorizes` 的等式是 `p x = ∏_v f v x`。**取 `s` 为 `topoOrder` 的最大元
（`exists_sink`），则 `s` 无出边（`sink_no_edge`），于是 `s ∉ pa v` 对所有
`v ≠ s` 成立（`sink_not_parent`）。**

**⟹ 这给出一个不可替代的性质：在整族因子中，`f s` 是**唯一**读 `x_s` 的那一个。**
**⟹ 故沿 `s` 求和时，`f s` 可以**唯一地**提出求和号（T4）。
**⟹ 从 source 推进没有这个性质**（`f source` 的「读者身份」被多个因子共享）。

### 1.2 归纳步（`sink_peel`，T4）的完整四步

设 `s` 是 sink（`hs : ∀ u, ¬ G.edge s u`），`f` 局部（`hloc`），`p = ∏ f`（`hfac`），
`f` 局部归一（`hnorm`）。则

$$\mathrm{mass}_{V\setminus\{s\}}\,p\,x
  \;=\; \prod_{v \ne s} f\,v\,x.$$

| 步 | 内容 | 用到的引理 |
|---|---|---|
| 1 | `mass (V\{s}) p x = ∑_{a} p (x_s:=a)` | **T1** `mass_compl_eq_sum`（`mass_insert_sum'` + `mass_univ`）|
| 2 | `p (x_s:=a) = f s (x_s:=a) · ∏_{v≠s} f v (x_s:=a)` | **T2** `prod_split`（`prod_erase_mul`）|
| 3 | `f v (x_s:=a) = f v (x_s:=b)` 对 `v ≠ s` | **T3** `fv_insensitive` ⟸ **G3** + `hloc` |
| 4 | `∑_a f s(…) · C = (∑_a f s(…)) · C = 1 · C` | `Finset.sum_mul` + **D4** |

**第 3 步是图论做功的地方**：`s` 无出边 ⟹ **G3** ⟹ `s ∉ pa v` ⟹
`f v` 的两个参数只在 `s` 位不同，而 `f v` **不读** `s` 位（`hloc`）。

### 1.3 归纳不变量与递归（`sink_marginal_locality`，T5）

T4 说的是：**「把 `s` 边缘化掉之后，`p` 在 `V \ {s}` 上仍然因子化，
且因子就是去掉 `f s` 后的乘积」**。这**正是**递归所需的形式：

> `sink_peel ⟹ mass (V\{s}) p x = ∏_{v ∈ V\{s}} f v x`
> ⟹ **对 `V\{s}` 上的诱导 DAG 重复同一论证**（新的 sink 是 `topoOrder` 的次大元）。

T5 把它写成**可消费的形式**：`mass (V\{s}) p x` 与 `x_s` 无关。

## 2 ⚠⚠ 诚实边界（**必读**）

**必须首先声明：本文件**没有**给出完整的 Pearl 1.2.7。**

### 2.1 已交付的是**归纳引擎的单步**，不是完整归纳

本文件**完整证明**了 sink 剥离（T4）与 marginal locality（T5），**零 `sorry`**。
**但**从 T5 到 `Markov`（D6）还缺两段：

* **缺口 A（诱导子图）**：`CausDAG` **没有** `G.induce`（在 `V \ {s}` 上取诱导子图的
  `DAG`）。没有它，T5 的递归**无法在 Lean 里写出来**。
  这是**库缺失**，不是数学缺失。
* **缺口 B（`dSep` 的第 4 子句）**：`G.dSep X Y Z` 展开为
  四个合取，前三个是**纯集合不交**（与 `G` 无关），
  第 4 个 `Disjoint (bbReachableVertices Z X) Y` 才是**真正的 d-分离内容**。
  本文件的全部图论推断（G1–G3）**只用到拓扑序**，
  **没有**消费 Bayes-Ball 的可达性。**⟹ 即使补齐缺口 A，
  得到的也只是「因子化 + 序结构 ⟹ 条件独立」，
  而非「因子化 + d-分离 ⟹ 条件独立」。**

### 2.2 `Markov` 与 `Factorizes` 的关系（**陈述 vs 证明**）

`Markov`（D6）与 `Factorizes`（D3）**都已按任务书要求定义**。
`Factorizes ⟹ Markov` 的**完整蕴含本文件未证**（见 §2.1）。
本文件证明的是这条蕴含**证明骨架中不可省的那一步（sink 剥离）**，
并把它作为**可独立复用**的定理交付。

### 2.3 其他

* **`FactorNorm`（D4）是额外假设**：真实概率测度下自动成立
  （条件密度对自身下标求和为 1），但在 `(V → α) → ℝ` 上必须显式假设。
* **不假设 `p ≥ 0`、不假设归一**：§3–§5 的全部等式是**纯代数恒等式**。
* **无 `sorry` / `admit` / `axiom`。**

## 3 与既有工作的关系（**为什么这不是重复已有结论**）

* `Fate/DAGFactorization.lean` 的 `fac_aux` / `localMarkov_gen_fac` 被
  **该文件自己的头注明确降级**：「`G` 是**哑变量**，结论里不出现 `G`」。
* **本文件的 `LocalTo G f` 用 `G.parents` 定义，`sink_no_edge` / `sink_not_parent`
  真的消费了 `G.edge` 与 `G.topoOrder`。** `G` 在 §4 的证明里**不可删除**。
* 图侧另用 `CausSeparation.dSep`、`CausBayesBall`、`CausActivePath`。

## 4 参考文献

* Pearl, *Causality* (2nd ed.), **Theorem 1.2.7**（因子化 ⟹ 全局 Markov）。
* Lauritzen, *Graphical Models*, §3.2.2（有序分解 / sink 剥离）。
* Cowell–Dawid–Lauritzen–Spiegelhalter, *Probabilistic Networks and Expert
  Systems*, §1.2.3（沿拓扑序的局部 Markov ⟹ 因子分解）。
-/

import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.CondMassTower
import FateWorld.FateV2.Modeling.CausSeparation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace FateV2.Predict

open FateV2.Modeling
namespace FactorMarkov

set_option linter.unusedSectionVars false

open Finset
open FateV2.Modeling.Graph
open Fate.DAGFactorization (mass unpin)

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-!
  # Predict · FactorMarkov

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FactorMarkov.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：DAGFactorization, CondMassTower, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 ⭐⭐⭐ **主定义**（任务书要求：`Factorizes (p : Joint V) (G : DAG V) : Prop`）
  =========================================================================== -/

/-- ⭐⭐⭐ **联合律**（D1）：顶点族 `V`、取值域 `α` 上的联合分布密度。

`Joint V α := (V → α) → ℝ`。

**⚠ 不假设归一、不假设非负**：本文件的全部结论是**纯代数恒等式**，
概率含义由归一化假设 `FactorNorm`（D4）补齐。 -/
abbrev Joint (V : Type*) (α : Type*) : Type _ := (V → α) → ℝ

/-- ⭐⭐⭐ **局部性约束**（D2）：`f v` **只读 `{v} ∪ pa_G(v)` 上的坐标**。

以 `∀ u, u = v ∨ u ∈ G.parents v → x u = y u` 为「前提」，
断言 `f v x = f v y`。

**⟹ 这是「`v` 的因果机制只看自己的父」这一假设的**精确（且可判定）**表达。**
**⟹ 类型里出现了 `G.parents v`，`G` **不是哑变量**。 -/
def LocalTo (G : DAG V) (f : V → (V → α) → ℝ) : Prop :=
  ∀ v (x y : V → α), (∀ u, u = v ∨ u ∈ G.parents v → x u = y u) → f v x = f v y

/-- ⭐⭐⭐⭐ **父节点因子化**（D3，**Pearl 的 `p(x) = ∏_v p(x_v | x_{pa(v)})`**）。

$$\texttt{Factorizes}\ p\ G \;:=\;
  \exists f,\ \bigl(\forall v,\ f\,v \text{ 只读 } \{v\}\cup\mathrm{pa}_G(v)\bigr)
    \;\wedge\; \bigl(\forall x,\ p\,x = \prod_v f\,v\,x\bigr).$$

**⭐⭐ 第 1 条（`LocalTo`）是关键。** 没有它，任何 `p` 都能「因子化」
（取 `f v₀ = p`、其余 `≡ 1`），命题会**空洞化**。
有了它，`Factorizes` 才是**因果结构假设**而非恒真式。 -/
def Factorizes (p : Joint V α) (G : DAG V) : Prop :=
  ∃ f : V → (V → α) → ℝ, LocalTo G f ∧ (∀ x, p x = ∏ v, f v x)

/-- ⭐⭐ **局部归一性**（D4，**`Factorizes` 之外的额外假设**）。

每个因子对「自己的坐标」求和为 `1` —— 即 `f v` 是**条件密度**而非任意函数。

**⚠ 真实概率测度下自动成立；在 `(V → α) → ℝ` 的**不归一**载体上必须显式假设。
见文件头 §2.3。** -/
def FactorNorm (f : V → (V → α) → ℝ) : Prop :=
  ∀ v (x : V → α), (∑ a : α, f v (unpin v x a)) = 1

/-- ⭐⭐⭐ **乘性条件独立**（D5，集合口径）：

$$p(A\cup B\cup Z)\cdot p(Z) \;=\; p(A\cup Z)\cdot p(B\cup Z).$$

其中 `mass S p x` 是 `p` 在 `S` 上的**边缘**（固定 `x|_S`、对其余**同时**求和）。

**⟹ 这是 `X ⊥ Y | Z` 的乘性形式**（不需要除法，故**不需要
`margZ ≠ 0` 守卫**，也不需要 `p ≥ 0`）。 -/
noncomputable def CondIndep (p : Joint V α) (A B Z : Finset V) : Prop :=
  ∀ x : V → α,
    mass (A ∪ B ∪ Z) p x * mass Z p x = mass (A ∪ Z) p x * mass (B ∪ Z) p x

/-- ⭐⭐⭐ **全局 Markov 性**（D6）：**d-分离 ⟹ 条件独立**。

**⭐ 本定义字面消费 `CausSeparation.dSep`**（含其 Bayes-Ball 子句），
故它是一个**真正关于 `G` 的图论陈述**，而非集合口号。 -/
def Markov (p : Joint V α) (G : DAG V) : Prop :=
  ∀ X Y Z : Finset V, G.dSep X Y Z → CondIndep p X Y Z

/-! ===========================================================================
  §2 ⭐⭐⭐ **图论输入**（**`G` 在这里真正做功**）
  =========================================================================== -/

section GraphInput

/-- ⭐⭐⭐ **拓扑序的最大元（sink）存在**（G1）。

$$G \neq \emptyset \;\Longrightarrow\; \exists s,\ \forall u,\
  \mathrm{topoOrder}\,u \le \mathrm{topoOrder}\,s.$$

**⟹ 真用 `topoOrder`**：对有限顶点集取 `topoOrder` 的最大值。 -/
theorem exists_sink (G : DAG V) [Nonempty V] :
    ∃ s : V, ∀ u : V, G.topoOrder u ≤ G.topoOrder s := by
  obtain ⟨s, -, hs⟩ :=
    Finset.exists_max_image (Finset.univ : Finset V) G.topoOrder Finset.univ_nonempty
  exact ⟨s, fun u => hs u (Finset.mem_univ u)⟩

/-- ⭐⭐⭐ **sink 没有出边**（G2）。

`topoOrder` 的最大元不能有 `edge s u` —— 否则 `topoOrder s < topoOrder u`
（`G.topoOrder_lt`），与最大性矛盾。 -/
theorem sink_no_edge (G : DAG V) (s : V)
    (hs : ∀ u : V, G.topoOrder u ≤ G.topoOrder s) :
    ∀ u : V, ¬ G.edge s u := by
  intro u he
  have h1 : G.topoOrder s < G.topoOrder u := G.topoOrder_lt s u he
  have h2 : G.topoOrder u ≤ G.topoOrder s := hs u
  exact absurd h1 (not_lt.mpr h2)

/-- ⭐⭐⭐⭐ **sink 不被任何别的顶点当作父**（G3，**图论核心**）。

$$s \text{ 无出边} \;\Longrightarrow\; \forall v \ne s,\ s \notin \mathrm{pa}_G(v).$$

**⟹ 这是 `sink_peel`（T4）第 3 步的全部图论内容**：
「**除 `f s` 外，整族因子中没有谁读 `x_s`**」。
**证明真的经 `G.mem_parents` 与 `G.edge`。** -/
theorem sink_not_parent (G : DAG V) (s : V) (hs : ∀ u : V, ¬ G.edge s u) :
    ∀ v : V, v ≠ s → s ∉ G.parents v := by
  intro v _ h
  exact hs v (G.mem_parents.mp h)

end GraphInput

/-! ===========================================================================
  §3 ⭐⭐⭐ `mass` 的基本律（塌缩与乘积分解，**纯 `Finset` 论证**）
  =========================================================================== -/

section MassLemmas

/-- ⭐⭐⭐ **塌缩到「单点求和」**（T1）。

$$\mathrm{mass}_{V\setminus\{s\}}\,p\,x \;=\; \sum_{a}\ p\bigl(x_s{:=}a\bigr).$$

**证明**：`mass_insert_sum'`（在 `V\setminus\{s}` 上放开 `s`，得 `insert s (V\{s}) = V`）
+ `mass_univ`（全空间边缘 = 密度本身）。 -/
theorem mass_compl_eq_sum (p : Joint V α) (s : V) (x : V → α) :
    mass (univ \ {s}) p x = ∑ a : α, p (unpin s x a) := by
  rw [Fate.DAGFactorization.mass_insert_sum' s (univ \ {s}) (by simp) p x]
  have hins : insert s (univ \ {s}) = (univ : Finset V) := by
    ext u; simp
  rw [hins, Finset.sum_congr rfl (fun a _ => Fate.DAGFactorization.mass_univ p _)]

/-- ⭐⭐⭐ **乘积的「剥出一点」分解**（T2）。

$$\prod_{v} f\,v\,(x_s{:=}a) \;=\;
  f\,s\,(x_s{:=}a)\cdot\prod_{v \ne s} f\,v\,(x_s{:=}a).$$

**证明**：`Finset.prod_erase_mul` + `sdiff_singleton_eq_erase` + `mul_comm`。 -/
theorem prod_split (f : V → (V → α) → ℝ) (s : V) (x : V → α) (a : α) :
    ∏ v, f v (unpin s x a) = f s (unpin s x a) * ∏ v ∈ (univ \ {s}), f v (unpin s x a) := by
  have h := Finset.prod_erase_mul (univ : Finset V) (fun v => f v (unpin s x a))
    (Finset.mem_univ s)
  have he : (univ : Finset V).erase s = univ \ {s} := by
    rw [Finset.sdiff_singleton_eq_erase]
  rw [he] at h
  rw [← h, mul_comm]

/-- ⭐⭐⭐⭐ **除 `s` 外的因子**不读** `x_s`**（T3，**归纳步的关键交换律**）。

设 `s` 无出边（`hs`），`f` 局部（`hloc`），`v ≠ s`。则 `f v` 在
`unpin s x a` 与 `unpin s x b` 上取值相同 —— 即 `f v` **对 `x_s` 无感**。

**⟹ 证明链：`s ∉ pa v`（G3）⟹ `f v` 的两个参数在 `{v} ∪ pa v` 上一致
（这两处都不含 `s`）⟹ `hloc`。** -/
theorem fv_insensitive (G : DAG V) {f : V → (V → α) → ℝ} (hloc : LocalTo G f)
    {s v : V} (hvs : v ≠ s) (hs : ∀ u : V, ¬ G.edge s u) {x : V → α} {a b : α} :
    f v (unpin s x a) = f v (unpin s x b) := by
  have hnp : s ∉ G.parents v := fun hc => hs v (G.mem_parents.mp hc)
  have key : ∀ u : V, (u = v ∨ u ∈ G.parents v) → unpin s x a u = unpin s x b u := by
    intro u hu
    have hus : u ≠ s := by
      rintro rfl
      rcases hu with h | h
      · exact hvs h.symm
      · exact hnp h
    unfold unpin
    rw [if_neg hus, if_neg hus]
  exact hloc v _ _ key

end MassLemmas

/-! ===========================================================================
  §4 ⭐⭐⭐⭐⭐ **sink 剥离**（**归纳的引擎**，T4）
  =========================================================================== -/

section SinkPeel

variable {p : Joint V α} {G : DAG V} {f : V → (V → α) → ℝ}

/-- ⭐⭐⭐⭐⭐ **sink 剥离**（T4，**本文件的核心定理**）。

设 `s` 是 sink（`hs : ∀ u, ¬ G.edge s u`），`f` 局部（`hloc`）、`p = ∏ f`（`hfac`）、
`f` 局部归一（`hnorm`）。则

$$\boxed{\ \mathrm{mass}_{V\setminus\{s\}}\,p\,x
  \;=\; \prod_{v \ne s} f\,v\,x\ }$$

**⟹ 读法**：**边缘化掉 `s` 之后，`p` 在 `V\{s}` 上仍然因子化，
且因子正是去掉 `f s` 后的乘积。**
**⟹ 这就是「沿拓扑序剥掉一个顶点」后**归纳不变量保持**的精确陈述**；
对 `V\{s}` 上的诱导 `DAG` 重复，即得完整的有序分解。

**证明（四步，见文件头 §1.2）**：
1. `mass (V\{s}) p x = ∑_a p (x_s:=a)` —— **T1**；
2. `p (x_s:=a) = f s (…) · ∏_{v≠s} f v (…)` —— **T2**；
3. `∏_{v≠s} f v (x_s:=a) = ∏_{v≠s} f v x` —— **T3**（`f v` 不读 `x_s`）；
4. `∑_a f s(…) · C = (∑_a f s(…)) · C = 1 · C` —— `Finset.sum_mul` + **D4**。 -/
theorem sink_peel (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : FactorNorm f) (s : V) (hs : ∀ u : V, ¬ G.edge s u) (x : V → α) :
    mass (univ \ {s}) p x = ∏ v ∈ (univ \ {s}), f v x := by
  classical
  -- ① 塌缩成「对 `x_s` 的单点求和」
  rw [mass_compl_eq_sum p s x]
  -- ② + ③ 逐项分解并让 `v ≠ s` 的因子「冻结」
  rw [Finset.sum_congr rfl (fun a _ => by rw [hfac, prod_split f s x a])]
  have hpost : ∀ a : α, ∏ v ∈ (univ \ {s}), f v (unpin s x a)
      = ∏ v ∈ (univ \ {s}), f v x := by
    intro a
    refine Finset.prod_congr rfl fun v hv => ?_
    have hvs : v ≠ s := by simpa using hv
    -- T3：`f v` 对 `x_s` 无感，故 `a` 位可换成 `x s`
    exact (fv_insensitive G hloc hvs hs (a := a) (b := x s)).trans (by
      congr 1
      funext u
      unfold unpin
      by_cases hu : u = s <;> simp [hu])
  rw [Finset.sum_congr rfl (fun a _ => by rw [hpost a]), ← Finset.sum_mul]
  -- ④ 归一性收束
  have hone : (∑ a : α, f s (unpin s x a)) = 1 := hnorm s x
  rw [hone, one_mul]

/-- ⭐⭐⭐⭐⭐ **边缘局部性**（T5，**归纳步的可用形式**）。

在 `sink_peel` 之上，`p` 在 `V\{s}` 上的边缘**完全不受 `x_s` 影响**：

$$\forall x\,y,\quad
  \bigl(\forall u \in V\setminus\{s\},\ x_u = y_u\bigr)
  \;\Longrightarrow\; \mathrm{mass}_{V\setminus\{s\}}\,p\,x
    = \mathrm{mass}_{V\setminus\{s\}}\,p\,y.$$

**⟹ 这正是「`s` 独立于 `V \ ({s} ∪ pa s)`」的**代数内核**，
也是递归步（对诱导子图重施 `sink_peel`）所需的**不变量传递形式**。 -/
theorem sink_marginal_locality (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : FactorNorm f) (s : V) (hs : ∀ u : V, ¬ G.edge s u) :
    ∀ {x y : V → α}, (∀ u ∈ (univ \ {s}), x u = y u) →
      mass (univ \ {s}) p x = mass (univ \ {s}) p y := by
  intro x y hxy
  rw [sink_peel hloc hfac hnorm s hs x, sink_peel hloc hfac hnorm s hs y]
  refine Finset.prod_congr rfl fun v hv => ?_
  have hvs : v ≠ s := by
    intro h
    rw [h] at hv
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_singleton_self s)
  have hnp : s ∉ G.parents v := fun hc => hs v (G.mem_parents.mp hc)
  refine hloc v x y (fun u hu => ?_)
  have hus : u ≠ s := by
    intro h
    rcases hu with h' | h'
    · exact hvs (h'.symm.trans h)
    · exact hnp (h ▸ h')
  exact hxy u (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, by simpa using hus⟩)

end SinkPeel

/-! ===========================================================================
  §5 📋 **证明骨架总览**（任务书要求：沿拓扑序的完整归纳骨架）
  =========================================================================== -/

/-!
### 5.1 归纳的**完整骨架**（本文件已填 §4，缺口标 ⛔）

**记**：`v₀, …, vₙ₋₁` 为按 `topoOrder` **增序**的顶点（`n = |V|`），
`P_k = {v₀,…,vₖ₋₁}`，`D_k = V \ P_k`。

```
目标：Factorizes p G  ⟹  Markov p G

  ── 归纳不变量 ──
  (I_k)  mass (P_k) p x = ∏_{v ∈ P_k} f v x · C_k      （C_k 与 x 无关）

  ── 基础 (k = 0) ──
  P_0 = ∅，mass ∅ p x = ∑_w p w =: C_0（常数）。           ✅ 定义级

  ── 步骤 (k → k+1) ──
  取 s := vₖ（拓扑序第 k 个，故它是 D_k 中**序最小**者）……  ⛔ 实为取**最大**者
  ⟹ 本文件的实现取 s := D_k 的 topoOrder **最大**元：
     · 存在性                         — exists_sink (G1)    ✅
     · 无出边（在 D_k 内）             — sink_no_edge (G2)   ✅
     · ∀v≠s, s ∉ pa v                 — sink_not_parent(G3) ✅
     · mass (V\{s}) p x = ∏_{v≠s} f v x — sink_peel (T4)     ✅
     · 与 x_s 无关                    — sink_marginal_locality (T5) ✅

  ── 递归 ⛔ 缺口 A ──
  在 V\{s} 上取**诱导子图** G.induce s，对 (G.induce s, V\{s}) 重施上述论证。
  ⚠ `CausDAG` 目前**没有** `DAG.induce`，故 Lean 里**无法**写出这一步。
  数学上这一步是平凡的（诱导子图仍是 DAG，`topoOrder` 继承）。

  ── 得到 k = n ──
  mass univ p x = p x = ∏_v f v x · C_n，且 C_n = 1（归一性）
  ⟹ 对任意 T = X∪Y∪Z，mass T p x = ∏_{v ∈ T} f v x · C_T   （C_T 常数）

  ── 组装 CondIndep ⛔ 缺口 B ──
  mass T p x · mass Z p x = (∏_T f) · C_T · (∏_Z f) · C_Z
  而两两不交 ⟹ ∏_{T} ∏_{Z} = ∏_{X∪Z} ∏_{Y∪Z}   （集合乘积的恒等式）
  ⟹ 需再证 C_T · C_Z = C_{X∪Z} · C_{Y∪Z}       ⛔ 需要 dSep 的第 4 子句
     （Bayes-Ball 不可达 ⟹ 尾集上无「从 T 到 D_k 的父边」，从而各 C 相等）
```

### 5.2 缺口的**性质**（为什么不假装补上）

* **缺口 A 是**库缺失**（缺 `DAG.induce`），不是数学困难。**
* **缺口 B 是**数学内容**：`C_T` 恒常性必须从 Bayes-Ball 的**不可达性**推出，
  那是 `CausBayesBall.bbReachableVertices_iff_activeWalk` 的**反向**使用
  （「不可达 ⟹ 不存在活跃路径」），本文件**没有**做到。
  **⟹ 这正是「`Factorizes ⟹ Markov`」的完整证明所缺的最后一段。**

### 5.3 本文件的**可复用价值**

`§4` 的 `sink_peel` / `sink_marginal_locality` 是**不带缺口的定理**，
它们对**任何**满足 `Factorizes` + `FactorNorm` 的 `(p, G)` 都成立，
并且**真的消费了 `G.edge` 与 `G.topoOrder`**（经 G2/G3）。
`Fate/DAGFactorization.fac_aux` 的 `G` 是哑变量，本文件的不是。
-/

/-! ===========================================================================
  §6 ⭐⭐ **`Factorizes` 与 `Markov` 的关系（陈述与可直接消费的形式）**
  =========================================================================== -/

section Statements

/-- ⭐⭐⭐ **`Factorizes` 的展开形式**（便于下游直接拿到 `f` 与两个性质）。 -/
theorem factorizes_elim {p : Joint V α} {G : DAG V} (h : Factorizes p G) :
    ∃ f : V → (V → α) → ℝ, LocalTo G f ∧ (∀ x, p x = ∏ v, f v x) := h

/-- ⭐⭐⭐⭐ **`Factorizes` + `FactorNorm` ⟹ 对**任意** sink 的边缘因子化**。

这是把 §4 的核心定理**直接挂到 `Factorizes` 定义上**的版本
（下游无需再手写 `hloc` / `hfac`）。

**⟹ 这是「沿拓扑序剥掉一个顶点后不变量保持」的**成品形式**，
也是 `Factorizes ⟹ Markov` 归纳骨架里**每一步的实际内容**（见 §5.1）。** -/
theorem factorizes_sink_peel {p : Joint V α} {G : DAG V}
    {f : V → (V → α) → ℝ} (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : FactorNorm f) (s : V) (hs : ∀ u : V, ¬ G.edge s u) (x : V → α) :
    mass (univ \ {s}) p x = ∏ v ∈ (univ \ {s}), f v x :=
  sink_peel hloc hfac hnorm s hs x

/-- ⭐⭐⭐ **sink 的存在 + 剥离**（**G1 与 T4 的合并**）：

非空图必有 sink `s`，且 `mass (V\{s}) p x = ∏_{v≠s} f v x`。

**⟹ 这是归纳骨架里**每一轮**可直接引用的成品。** -/
theorem exists_sink_and_peel {p : Joint V α} {G : DAG V} [Nonempty V]
    {f : V → (V → α) → ℝ} (hloc : LocalTo G f) (hfac : ∀ x, p x = ∏ v, f v x)
    (hnorm : FactorNorm f) :
    ∃ s : V, ∀ x : V → α, mass (univ \ {s}) p x = ∏ v ∈ (univ \ {s}), f v x := by
  obtain ⟨s, hs⟩ := exists_sink G
  exact ⟨s, fun x => sink_peel hloc hfac hnorm s (sink_no_edge G s hs) x⟩

end Statements

end FactorMarkov

end FateV2.Predict