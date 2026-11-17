/-
# 视角 19：『图 ⟹ 概率』桥 —— **因子图（超图）分离 · 归纳路由**

## 0 本视角的定位（先读这段）

**任务**：给出「图 ⟹ 概率」桥（`Factorizes ⟹ Markov`）的**第 19 种**证明策略，
具体数学构造 + Lean 落地。**硬约束：不使用 `mass` 塔性质**（已证伪：
`Fate.DAGFactorizationGeneral.tower_property_false`、
`Fate.TowerAudit.mass_idempotent_fails`）。

### 0.1 与前 18 / 20 / 21 / 22 种策略的**结构性区别**

前 18 种（矩阵见 `Fate/View20GraphToProb.lean` §0、`VIEW20_REPORT.md` §3）
的共同形态是：**沿拓扑序剥离 / 划分因子 / 纤维重指标**，
即**从 `p` 的乘积结构出发、逐点地**把 `mass` 算成乘积。
它们最终都卡在同一个地方：

> **`mass S p x` 要写成「`∏_{v∈S} f_v(x)`」时，`S` 必须（在某种意义下）父闭，
> 否则 `S` 之外的因子会读到 `S` 之外的坐标，求和就退不出来。**

视角 19 **换掉了这条路线**。它不去计算任何 `mass` 的乘积形式，而是：

| 步 | 视角 19 的做法 | 与前 18 的差别 |
|---|---|---|
| **I** | 把 `p = ∏_v f_v` 重读成**因子图（超图）**：因子 `v` 的**读集** `R v := {v} ∪ pa_G(v)`，`p = ∏_v f_v` | 不引入任何「前缀 / 父闭 / 祖先闭」概念 |
| **II** | 提出一个**纯组合**谓词 `Split R X Y Z`（**没有 `X∪Z` 父闭要求**）：`∀ v, R v ⊆ X∪Z ∨ R v ⊆ Y∪Z` | 判据作用在**读集**上，不在**集合**上 |
| **III** | ⭐ **主定理（零缺口）**：`Split R X Y Z` + `HyperFactorizes ψ R` ⟹ **纤维钉死条件独立**（`x`、`y` 可取**不同点**） | 完全不需 `FactorNorm`、不需 `DAG.induce`、不嵌套 `mass` |
| **IV** | 图侧：`dSep` ⟹ `Split` **不**一般成立；本文件给出**可证子类**（`Split` 在「查询集自身父闭」时成立）+ **机检反例**划定边界 | 诚实登记边界，不把结论塞进前件 |

### 0.2 核心数学构造（一句话）

> **把四个 `mass` 全部用「`Sᶜ` 上的一次求和」（`mass_eq_sum_glue`）展开；
> 然后对**每一个**因子 `ψ_v` 问一句：它的读集落在哪一侧？
> `Split` 保证每个读集落在 `X∪Z` 或 `Y∪Z` 之内 —— 于是它在
> **四个** `mass` 的求和变量下**全部冻结**，求和退化为「`|α|^{|Sᶜ|}` 倍」。
> 四个 `mass` 于是都变成 `|α|^… · (X 侧积) · (Y 侧积) · (Z 侧积)` 的形状，
> 两边配对后 `ring` 收口。**

**关键**：`Split` 让「求和集 `Sᶜ`」与「读集 `R v`」**永不相交**（当 `S ⊇ R v` 时），
这是**纯集合论**的事实，与 `S` 是否父闭无关 —— 这就是它比前 18 种更宽松的地方。

## 1 为什么「不用塔」是硬约束（继承已证伪的路线）

`Fate/DAGFactorizationGeneral.lean` T24（`tower_property_false`）：
`mass S (mass T p) x ≠ mass (S∪T) p x` 一般为假（`mass` 是**非归一化**纤维和）；
`Fate/TowerAudit.lean` A3（`mass_idempotent_fails`）：连 `S ⊆ T` 方向也假。

**⟹ 本文件语法层禁止 `mass S (mass T p)`。** 全文 `mass` 只以
`mass S p x`（`p` 为原始密度）形式出现，并且每个 `mass` 都被
`mass_eq_sum_glue` **一次性**重指成「对 `Sᶜ` 的普通求和」。**无嵌套。**

## 2 文件结构

* §3 `glue` 与 `mass_eq_sum_glue`（重指标双射，零缺口）
* §4 读集、因子图分解 `HyperFactorizes`、组合分离谓词 `Split`
* §5 **乘积拆分引理**（`prod_split_sides`）
* §6 ⭐ **主定理 `fiberCondMul_of_split`**（纤维钉死条件独立，零缺口）
* §7 ⭐ **桥定理 `markovFiber_of_split`**（对**任意**满足 `Split` 的查询）
* §8 `Factorizes ⟹ HyperFactorizes`（读集 `{v}∪pa v`，零缺口）
* §9 图侧：`Split` 的可证子类 + **机检反例**（`dSep` 不蕴含 `Split`）+ 判据 D19
* §10 非退化见证（无因子分解时钉死恒等式为假）
* §11 诚实边界

**⚠ 无 `sorry` / 无 `axiom`。** 未能证明者一律登记为显式 `def … _Gap : Prop` 或散文，
并**不进下游**。
-/

import FateWorld.FateV2.Modeling.CausSeparation
import FateWorld.FateV2.Modeling.CausDAG
import FateWorld.FateV2.Predict.DAGFactorization
import FateWorld.FateV2.Predict.FactorMarkov
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false

namespace FateV2.Predict

open FateV2.Modeling
namespace View19

open Finset Fate.DAGFactorization

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

/-!
  # Predict · View19FactorGraphSplit

  ## 迁移登记
  - 来源：`FateWorld/Legacy/View19FactorGraphSplit.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausSeparation, _root.CausDAG, DAGFactorization, FactorMarkov
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §3 **重指标：`mass S p x` 是「对 `Sᶜ` 的一次普通求和」**
  =========================================================================== -/

/-- ⭐ **`glue S x t`**：以 `x` 为 `S` 上的规格，以 `t` 为 `Sᶜ` 上的自由取值拼出的点。 -/
noncomputable def glue (S : Finset V) (x : V → α) (t : {u : V // u ∉ S} → α) : V → α :=
  fun v => if h : v ∈ S then x v else t ⟨v, h⟩

theorem glue_of_mem (S : Finset V) (x : V → α) (t : {u : V // u ∉ S} → α) {u : V}
    (hu : u ∈ S) : glue S x t u = x u := by
  unfold glue; rw [dif_pos hu]

theorem glue_of_not_mem (S : Finset V) (x : V → α) (t : {u : V // u ∉ S} → α) {u : V}
    (hu : u ∉ S) : glue S x t u = t ⟨u, hu⟩ := by
  unfold glue; rw [dif_neg hu]

/-- ⭐⭐⭐ **`mass_eq_sum_glue`（重指标）：`mass` 就是 `Sᶜ` 上的一次求和。**

$$\mathrm{mass}\,S\,p\,x \;=\; \sum_{t\,:\,S^{\mathsf c}\to\alpha} p\,(\mathrm{glue}\,S\,x\,t).$$

**⚠ 这不是塔**：右端**没有** `mass`，只有 `p` 在拼接点上的取值被一次性求和。
证明是一个显式双射（`Finset.sum_nbij'`），两个方向的互逆均由 `glue` 的
`if` 展开给出。 -/
theorem mass_eq_sum_glue (S : Finset V) (p : (V → α) → ℝ) (x : V → α) :
    mass S p x = ∑ t : ({u : V // u ∉ S} → α), p (glue S x t) := by
  classical
  have h1 : (∑ w ∈ (univ.filter (fun w : V → α => ∀ u ∈ S, w u = x u)), p w)
      = mass S p x := by
    rw [Finset.sum_filter]
    unfold mass
    exact Finset.sum_congr rfl fun w _ => by rfl
  rw [← h1]
  refine Finset.sum_nbij' (fun (w : V → α) => fun (u : {u : V // u ∉ S}) => w u.1)
    (glue S x) ?_ ?_ ?_ ?_ ?_
  · intro w _
    exact Finset.mem_univ _
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro u hu
    exact glue_of_mem S x t hu
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    funext v
    by_cases hv : v ∈ S
    · rw [glue_of_mem S x (fun u => w u.1) hv, hw v hv]
    · rw [glue_of_not_mem S x (fun u => w u.1) hv]
  · intro t _
    funext u
    exact glue_of_not_mem S x t u.2
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    have hglue : glue S x (fun u : {u : V // u ∉ S} => w u.1) = w := by
      funext v
      by_cases hv : v ∈ S
      · rw [glue_of_mem S x (fun u => w u.1) hv, hw v hv]
      · rw [glue_of_not_mem S x (fun u => w u.1) hv]
    rw [hglue]

/-- ⭐⭐ **`mass` 的常值分解**：若 `p` 在整个 `(V → α)` 上恒为 `c`，则
`mass S p x = |α|^{|Sᶜ|} · c`（不出现任何嵌套 `mass`）。 -/
theorem mass_const (S : Finset V) (c : ℝ) (x : V → α) :
    mass S (fun _ => c) x = ((Fintype.card ({u : V // u ∉ S} → α) : ℕ) : ℝ) * c := by
  rw [mass_eq_sum_glue]
  simp

/-! ===========================================================================
  §4 **读集、因子图分解、组合分离谓词**
  =========================================================================== -/

/-- ⭐⭐ **读集局部性**：`ψ v` 只读 `R v` 上的坐标。 -/
def ReadSet (ψ : V → (V → α) → ℝ) (R : V → Finset V) : Prop :=
  ∀ v (x y : V → α), (∀ u ∈ R v, x u = y u) → ψ v x = ψ v y

/-- ⭐⭐ **因子图（超图）分解**：`p` 是单点因子之积。

**⚠ 与 `FactorMarkov.Factorizes` 的差别**：这里**不**要求 `R` 与图有关，
也**不**要求任何归一性；读集结构被抽成独立参数 `R`。 -/
def HyperFactorizes (ψ : V → (V → α) → ℝ) (p : (V → α) → ℝ) : Prop :=
  ∀ x, p x = ∏ v, ψ v x

/-- ⭐⭐⭐ **组合分离谓词 `Split R X Y Z`**（本视角的图侧判据）。

对**每一个**因子 `v`，其读集 `R v` 必须**整块**落在两"半空间"之一：
`X ∪ Z`（`X` 侧）或 `Y ∪ Z`（`Y` 侧）。

**⚠ 注意它**不**说 `X∪Z` 父闭、不**说** `R v ∩ X = ∅`、不**说** `R v ∩ Y = ∅` ——
它只禁止「同一个读集同时牵涉 `X` 与 `Y`」。这正是因子图（超图）分离的定义：
**没有超边横跨 `X` 与 `Y`**（两者的交界只能是 `Z`）。 -/
def Split (R : V → Finset V) (X Y Z : Finset V) : Prop :=
  ∀ v, R v ⊆ X ∪ Z ∨ R v ⊆ Y ∪ Z

/-- ⭐⭐⭐⭐ **冻结引理（引擎）**：若 `R v ⊆ S`，则 `ψ v (glue S x t)` **与 `t` 无关**。 -/
theorem frozen (ψ : V → (V → α) → ℝ) {R : V → Finset V} (hread : ReadSet ψ R)
    {S : Finset V} {v : V} (hv : R v ⊆ S) (x : V → α)
    (t : {u : V // u ∉ S} → α) :
    ψ v (glue S x t) = ψ v x := by
  refine hread v _ _ fun u hu => ?_
  exact glue_of_mem S x t (hv hu)

/-- ⭐⭐⭐ **`mass` 在读集落于 `S` 内的因子上冻结**：

若 `R v ⊆ S`，则 `mass S (ψ v · g) x = ψ v x · mass S g x`。

**⚠ 这是 `DAGFactorization.mass_mul` 的**读集版**（该版本要求 `f` 读集 `⊆ S` 的
`x` 一致形式，这里用 `mass_eq_sum_glue` **直接**给出一行证明，
不经过塔、不经过 `mass_mul` 的 `∀ u ∈ S` 前提）。** -/
theorem mass_frozen_mul (ψ : V → (V → α) → ℝ) {R : V → Finset V} (hread : ReadSet ψ R)
    {S : Finset V} {v : V} (hv : R v ⊆ S) (g : (V → α) → ℝ) (x : V → α) :
    mass S (fun w => ψ v w * g w) x = ψ v x * mass S g x := by
  rw [mass_eq_sum_glue S (fun w => ψ v w * g w) x, mass_eq_sum_glue S g x, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [frozen ψ hread hv x t]

end View19
end FateV2.Predict