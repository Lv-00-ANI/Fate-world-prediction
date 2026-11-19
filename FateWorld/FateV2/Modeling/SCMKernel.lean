import FateWorld.FateV2.Modeling.SCMSemantics
import FateWorld.FateV2.Modeling.CausDAG
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
  # Modeling · SCMKernel

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SCMKernel.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SCMSemantics, _root.CausDAG
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §K  ⭐⭐⭐⭐ **SCM 的 Kernel 视角**（每节点一个 kernel，Markov 性可证）

  ## 本模块要解决的问题

  `SCMSemantics`（第 68 轮）用**裸函数** `X × Y → ℝ` 表达 SCM 的联合 / 条件 / 干预律，
  并在 `§68.4` 如实登记了缺口：

  > ⚠ 「有限律 → `Measure`」的嵌入 **未做**；
  > ⚠ 「d-分离 ⟹ 该嵌入下条件独立」 **未做**。

  `FinMeasureBridge`（第 87 轮）做了前者的一半：把**裸律打包**成 `Measure`。
  但**两轮都没有**把 SCM 的**结构**（＝每个节点一个机制）本身写成概率论对象。

  **⟹ 本模块做的是**：把 SCM **直接**写成 Mathlib 的 `ProbabilityTheory.Kernel`
  （`Kernel α β` 就是可测族 `α → Measure β`）。于是

  * **每节点一个 `Kernel`**（该节点的**机制** $P(X_v \mid \mathrm{pa}(v))$）；
  * **SCM** = 这些机制沿拓扑序的**组合**（`⊛`，即 `Kernel.compProd` 的折叠）；
  * **Markov 性** 成为**可证的定理**（`SCMK.markov_fiber`，零缺口），
    因为 `Kernel.compProd` 的**定义就是**「逐节点抽样的序列化」。

  ## 与现有 `Fintype` 载体的接口（本模块的**第一公民**）

  | 现有载体 | 本模块的接口 | 位置 |
  |---|---|---|
  | `PearlHierarchy.SCM X Y`（`sg : U → X × (X → Y)`）| `ofPearl` / `ofPearl_joint_apply` | `§K.5` |
  | `Causalean.Graph.DAG V`（`parents v`）| ⚠ **未做**（见 `§K.8` 的缺口登记）| — |
  | `SCMSemantics.jointLaw`（裸律 `ℝ`）| `ofPearl_joint_apply`（同形式的 `ℝ≥0∞` 值）| `§K.5` / `§K.6` |
  | `Fintype` 上的加权 `δ` 和 | `mkMeasure` / `discreteKernel` | `§K.1`–`§K.2` |

  ## 等级与边界（**先说清楚，免得被当成在吹**）

  | 内容 | 等级 | 状态 |
  |---|---|---|
  | `mkMeasure`（有限加权 `δ` 和）+ 三条求值引理 | [支撑] | ✅ 零缺口 |
  | `discreteKernel`（有限型上的 `Kernel`）| ⭐⭐⭐ [构造] | ✅ 零缺口 |
  | `discreteKernel_apply_singleton` / `_univ` | [支撑] | ✅ 零缺口 |
  | `isMarkovKernel_discreteKernel`（行和为 1 ⟹ Markov 核）| ⭐⭐⭐ [理论] | ✅ 零缺口 |
  | `SCMK`（每节点一 kernel 的 SCM 载体）| ⭐⭐⭐⭐ [构造] | ✅ 零缺口 |
  | `SCMK.joint`（机制组合 = 联合 kernel）| ⭐⭐⭐⭐⭐ [理论] | ✅ **零缺口** |
  | **`SCMK.markov_fiber`**（**Markov 性主定理**）| ⭐⭐⭐⭐⭐ [理论] | ✅ **零缺口** |
  | `SCMK.markov_marginal`（边缘化推论，同上）| ⭐⭐⭐⭐ [理论] | ✅ 零缺口 |
  | `SCMK.locallyMarkov`（局部 Markov 性的 kernel 表述）| ⭐⭐⭐⭐ [理论] | ✅ 零缺口 |
  | `ofPearl` / `ofPearl_joint_apply`（与 `PearlHierarchy.SCM` 接口）| ⭐⭐⭐ [验证] | ✅ 零缺口 |
  | 与 `SCMSemantics.jointLaw` 的**逐字等式** | ⚠ **不做**（类型不同，见 `§K.6`）| — |
  | `DAG` 父集 → 条件域（`dagMechanism`）| ⚠ **未做**（见 `§K.8`）| — |

  **⚠ 边界（如实登记，不夸大）**：

  1. **本模块证的是「结构 Markov 性」**：机制**按拓扑序折叠**后，
     给定父值 $x$，联合律在 $X = x$ 纤维上**等于**该节点的机制
     `kY (·, x)`。这是 `Kernel.compProd` 的**定义级**内容 ⟹ **可证且无缺口**。
     **这不是**「d-分离 ⟹ 条件独立」——
     后者是**图侧**命题，需要的桥梁是 `CondIndepFun` 与 kernel 的对接，
     **本模块只提供 kernel 一侧的完备接口**（见 `§K.7` 的登记）。
  2. **只做二元 + N 元折叠**：`compProd` 是二元运算，N 元靠 `fold`
     （见 `§K.8`），**拓扑序的正确性**取 `DAGFactorizationGen` 的既有结论
     （`Causalean.Graph.DAG` 一侧的 `pa` 已就绪）。
     **本模块不重新证明拓扑序存在性**。
  3. **⚠ 无硬编码**（依作者裁决 Q-1）：所有 `Kernel` 都由权重函数 `w` 产生，
     没有任何具体数值进入定义。
  =========================================================================== -/

namespace FateV2.Modeling
namespace SCMKernel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u v

/-! ===========================================================================
  §K.1  有限加权 `δ` 和 —— 离散测度的最简载体
  =========================================================================== -/

/-- [支撑] **有限加权 Dirac 和**：把权重列 `w : β → ℝ≥0∞` 读成一个 `Measure β`。

$$w \mapsto \sum_{b\in\beta} w_b \cdot \delta_b.$$

**⚠ 为什么不用 `Measure.count`**：SCM 的机制一般**不等权**，
故须显式带权重 `w`。 -/
noncomputable def mkMeasure {β : Type v} [MeasurableSpace β] [Fintype β]
    (w : β → ℝ≥0∞) : Measure β :=
  ∑ b : β, w b • Measure.dirac b

/-- [支撑] **`mkMeasure` 在任意集合上的值**（逐项展开）。 -/
@[simp] lemma mkMeasure_apply {β : Type v} [MeasurableSpace β] [Fintype β]
    (w : β → ℝ≥0∞) (s : Set β) :
    mkMeasure w s = ∑ b : β, w b * (Measure.dirac b) s := by
  simp [mkMeasure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]

/-- ⭐ [支撑] **`mkMeasure` 在单点上的值 = 该点权重**。 -/
lemma mkMeasure_singleton {β : Type v} [MeasurableSpace β] [Fintype β]
    [MeasurableSingletonClass β] (w : β → ℝ≥0∞) (b : β) :
    mkMeasure w {b} = w b := by
  rw [mkMeasure_apply, Finset.sum_eq_single b]
  · simp
  · intro b' _ hb
    simp [Set.mem_singleton_iff, hb]
  · intro h; exact absurd (Finset.mem_univ b) h

/-- ⭐ [支撑] **`mkMeasure` 的全空间值 = 权重和**。 -/
lemma mkMeasure_univ {β : Type v} [MeasurableSpace β] [Fintype β]
    [MeasurableSingletonClass β] (w : β → ℝ≥0∞) :
    mkMeasure w (Set.univ : Set β) = ∑ b, w b := by
  rw [mkMeasure_apply]
  simp only [Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]

/-- ⭐ [支撑] **权重和 = 1 ⟹ `mkMeasure` 是概率测度**。 -/
theorem mkMeasure_isProbabilityMeasure {β : Type v} [MeasurableSpace β] [Fintype β]
    [MeasurableSingletonClass β] (w : β → ℝ≥0∞) (h : ∑ b, w b = 1) :
    IsProbabilityMeasure (mkMeasure w) :=
  ⟨by rw [mkMeasure_univ, h]⟩

/-! ===========================================================================
  §K.2  有限型上的 `Kernel` —— 与现有 `Fintype` 载体的**主接口**
  =========================================================================== -/

/-- ⭐⭐⭐ [构造] **有限型上的离散 `Kernel`**：逐行是加权 `δ` 和的核。

$$\kappa_a = \sum_{b} w(a,b)\cdot\delta_b.$$

**⟹ 这就是「给定 `a` 后 `b` 的转移律」**，即 SCM 中**一个节点的机制**。

**⚠ 为什么能只用 `Kernel.ofFunOfCountable`**：
`Kernel` 的 `measurable'` 要求 `a ↦ κ a s` 可测。在**可数**（含 `Fintype`）、
**可测单点**的 `α` 上，任何 `a ↦ Measure β` 都自动可测
（`measurable_of_countable`）。**⟹ 无需额外的可测性假设，这正是与
`Fintype` 载体对接的关键。** -/
noncomputable def discreteKernel {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α] [Fintype β]
    (w : α → β → ℝ≥0∞) : Kernel α β :=
  Kernel.ofFunOfCountable (fun a => mkMeasure (w a))

/-- [支撑] `discreteKernel` 的定义性展开。 -/
@[simp] lemma discreteKernel_apply {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α] [Fintype β]
    (w : α → β → ℝ≥0∞) (a : α) :
    discreteKernel w a = mkMeasure (w a) := rfl

/-- ⭐ [支撑] **`discreteKernel` 在单点上的值 = 转移权重**。 -/
theorem discreteKernel_apply_singleton {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
    (w : α → β → ℝ≥0∞) (a : α) (b : β) :
    discreteKernel w a {b} = w a b := by
  rw [discreteKernel_apply, mkMeasure_singleton]

/-- ⭐ [支撑] **`discreteKernel` 的全空间值 = 行和**。 -/
theorem discreteKernel_apply_univ {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
    (w : α → β → ℝ≥0∞) (a : α) :
    discreteKernel w a (Set.univ : Set β) = ∑ b, w a b := by
  rw [discreteKernel_apply, mkMeasure_univ]

/-- ⭐⭐⭐ [理论] **行和恒为 1 ⟹ 该离散核是 Markov 核**（概率核）。

**⟹ 这是把「SCM 的每个机制是概率分布」翻译成 Mathlib 的 `IsMarkovKernel`，
从而可以套用 Kernel 库的全部引理（`compProd_preimage_fst` 等）。** -/
theorem isMarkovKernel_discreteKernel {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
    (w : α → β → ℝ≥0∞) (h : ∀ a, ∑ b, w a b = 1) :
    IsMarkovKernel (discreteKernel w) :=
  ⟨fun a => by rw [discreteKernel_apply]; exact mkMeasure_isProbabilityMeasure (w a) (h a)⟩

/-- ⭐⭐ [支撑] **`discreteKernel` 是有限核**（有限型上，总质量 ≤ 行和之 sup）。

**⟹ 这是为了让 `discreteKernel` **无需额外假设**就能用在 `compProd` 里**
（`compProd_apply` 要求两侧 `IsSFiniteKernel`）。** -/
theorem isFiniteKernel_discreteKernel {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
    (w : α → β → ℝ≥0∞) (C : ℝ≥0∞) (hC : C < ∞) (h : ∀ a, ∑ b, w a b ≤ C) :
    IsFiniteKernel (discreteKernel w) :=
  ⟨⟨C, hC, fun a => by rw [discreteKernel_apply_univ]; exact h a⟩⟩

/-- ⭐⭐ [支撑] **`discreteKernel` 是 s-有限核**（`Fintype` 的 `β` 使其自动成立）。

**⚠ 本引理**要求**行和有限上界 `C`；**`ℝ≥0∞` 值行和一般可以取 `∞`**，
故本引理**带显式上界假设**，不假装自动成立。 -/
theorem isSFiniteKernel_discreteKernel {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
    (w : α → β → ℝ≥0∞) (C : ℝ≥0∞) (hC : C < ∞) (h : ∀ a, ∑ b, w a b ≤ C) :
    IsSFiniteKernel (discreteKernel w) :=
  haveI := isFiniteKernel_discreteKernel w C hC h
  inferInstance

/-- ⭐ [支撑] **`discreteKernel` 的总质量 = 行和**（`ℝ≥0∞` 口径）。

**⟹ 这是 `IsMarkovKernel` 判据的**逐点**形式，供不经类型类的场合使用。** -/
theorem discreteKernel_totalMass {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
    (w : α → β → ℝ≥0∞) (a : α) :
    (discreteKernel w a) (Set.univ : Set β) = ∑ b, w a b :=
  discreteKernel_apply_univ w a

/-! ===========================================================================
  §K.3  ⭐⭐⭐⭐⭐ **SCM 的 Kernel 载体**（每节点一个 `Kernel`）
  =========================================================================== -/

/-- ⭐⭐⭐⭐ [构造] **Kernel 口径的两节点 SCM**。

**⚠ 为什么从二元起**：`Kernel.compProd` 是**二元**运算
（`Kernel α β → Kernel (α × β) γ → Kernel α (β × γ)`），
「每节点一个 kernel」的**归纳**须从二元起（N 元见 `§K.8` 的 `fold`）。

| 字段 | 含义 | Mathlib 类型 |
|---|---|---|
| `kX` | $X$ 的**外生机制** | `Kernel Unit X` |
| `kY` | $Y$ 在**父节点 $X$ 给定**下的机制 | `Kernel (Unit × X) Y` |

**⚠ 与 `PearlHierarchy.SCM` 的差别**：后者用**单个 `sg : U → X × (X → Y)`**
把两个机制**揉在一起**；本结构把 `kX` / `kY` **分开承载** ——
**这正是「每节点一个 kernel」的形式化体现**，也是能套用 `compProd`
（从而**免费**得到 Markov 性）的原因。

**⚠ 关于 `Unit`**：`compProd` 要求左核定义域是 `α`、右核含 `α × β`。
SCM 没有外生可观测点，故取 `α = Unit`（**唯一**的点）——
这不是 hack，而是「SCM 的联合律就是一个**概率测度**」的精确表达。 -/
structure SCMK (X Y : Type u) [MeasurableSpace X] [MeasurableSpace Y] where
  /-- $X$ 的外生机制。 -/
  kX : Kernel Unit X
  /-- $Y$ 在父节点 $X$ 给定下的机制。 -/
  kY : Kernel (Unit × X) Y

namespace SCMK

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]

/-- ⭐⭐⭐⭐⭐ [理论] **SCM 的联合 kernel**：两机制沿拓扑序的 `compProd`。

$$\kappa_{\mathrm{joint}} := k_X \otimes_k k_Y
  : \mathrm{Kernel}\ \mathrm{Unit}\ (X\times Y).$$

**⚠ 读法**：`compProd` 的定义就是「**先按 `kX` 抽 $X$，再按 `kY` 抽 $Y$**」
——**这正是「按拓扑序逐节点抽样」**，与 SCM 的语义**逐字一致**。 -/
noncomputable def joint (M : SCMK X Y) : Kernel Unit (X × Y) :=
  M.kX ⊗ₖ M.kY

/-! ===========================================================================
  §K.4  ⭐⭐⭐⭐⭐ **Markov 性主定理**
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ [理论] **Markov 性主定理（`compProd` 纤维公式）**。

**陈述**：对任意 `x : X`、可测 `t ⊆ Y`，

$$\boxed{\ \kappa_{\mathrm{joint}}\ (\cdot)\ \bigl(\{p : X\times Y \mid p_1 = x \wedge p_2 \in t\}\bigr)
  = k_X(\cdot)\{x\}\ \cdot\ k_Y(\cdot, x)(t)\ }$$

**⟹ 精确读法**：

$$
\kappa_{\mathrm{joint}}(\cdot)\bigl[\,X = x,\ Y \in t\,\bigr]
  = \underbrace{k_X(\cdot)\{x\}}_{\text{$X$ 的边缘}} \cdot
    \underbrace{k_Y(\cdot,x)(t)}_{\text{给定 $X=x$ 后 $Y$ 的机制}}.
$$

**这就是 Markov 性**：联合律在纤维 $X = x$ 上**分解**为「$X$ 的边缘」×
「$Y$ 只依赖 $x$ 的机制」。**$Y$ 不越过 $x$ 再读 $X$ 的任何其他信息。**

**证明**：`compProd_apply`（`Kernel` 的组合-积分解）+
「除 $b = x$ 外的纤维为空」—— 这是**定义级**论证，**零缺口**。 -/
theorem markov_fiber (M : SCMK X Y) [MeasurableSingletonClass X]
    [IsSFiniteKernel M.kX] [IsSFiniteKernel M.kY]
    (x : X) (t : Set Y) (ht : MeasurableSet t) :
    M.joint () {p : X × Y | p.1 = x ∧ p.2 ∈ t} = M.kX () {x} * M.kY ((), x) t := by
  classical
  have hmeas : MeasurableSet {p : X × Y | p.1 = x ∧ p.2 ∈ t} :=
    (measurableSet_singleton x).preimage measurable_fst |>.inter (ht.preimage measurable_snd)
  rw [joint, Kernel.compProd_apply hmeas M.kX M.kY ()]
  have hfib : ∀ b : X, M.kY ((), b) (Prod.mk b ⁻¹' {p : X × Y | p.1 = x ∧ p.2 ∈ t}) =
      ({x} : Set X).indicator (fun _ => M.kY ((), x) t) b := by
    intro b
    by_cases hb : b = x
    · subst hb; simp
    · have h0 : (Prod.mk b ⁻¹' {p : X × Y | p.1 = x ∧ p.2 ∈ t}) = (∅ : Set Y) := by
        ext c; simp [hb]
      rw [h0, measure_empty]
      simp [hb]
  rw [lintegral_congr hfib]
  rw [lintegral_indicator_const (measurableSet_singleton x), mul_comm]

/-- ⭐⭐⭐⭐ [理论] **Markov 性的边缘推论**（对 $Y$ 求和消去，得 $X$ 的边缘）。

$$\kappa_{\mathrm{joint}}(\cdot)\bigl[\{p \mid p_1 = x\}\bigr] = k_X(\cdot)\{x\}.$$

**⟹ 与 `markov_fiber` 合读**：两式相除（在 $k_X(\cdot)\{x\} \ne 0$ 时）
得到**条件律** $Y \mid X = x$ **就是** `kY (·, x)` ——
这正是 `SCMSemantics.condY` 的 kernel 版本。**零缺口**（`t = univ` 代入）。 -/
theorem markov_marginal (M : SCMK X Y) [MeasurableSingletonClass X]
    [IsSFiniteKernel M.kX] [IsMarkovKernel M.kY]
    (x : X) :
    M.joint () {p : X × Y | p.1 = x} = M.kX () {x} := by
  have h := markov_fiber M x (Set.univ : Set Y) MeasurableSet.univ
  simp only [Set.mem_univ, and_true] at h
  rw [h, measure_univ, mul_one]

/-- ⭐⭐⭐⭐ [理论] **`markov_fiber` 的「纤维条件律」形式**（最贴近 SCM 语义）。

$$\boxed{\ \kappa_{\mathrm{joint}}(\cdot)\bigl[\{p \mid p_1 = x \wedge p_2 \in t\}\bigr]
  = \kappa_{\mathrm{joint}}(\cdot)\bigl[\{p \mid p_1 = x\}\bigr] \cdot k_Y(\cdot,x)(t)\ }$$

**⟹ 这是 $\Pr(Y\in t\mid X = x) = k_Y(\cdot,x)(t)$ 的**无除法**表述** ——
**不需要 `kX (){x} ≠ 0`**，故对退化情形也成立。**零缺口**。 -/
theorem markov_conditional (M : SCMK X Y) [MeasurableSingletonClass X]
    [IsSFiniteKernel M.kX] [IsMarkovKernel M.kY]
    (x : X) (t : Set Y) (ht : MeasurableSet t) :
    M.joint () {p : X × Y | p.1 = x ∧ p.2 ∈ t}
      = M.joint () {p : X × Y | p.1 = x} * M.kY ((), x) t := by
  rw [markov_fiber M x t ht, markov_marginal M x]

/-- ⭐⭐⭐⭐ [理论] **`markov_conditional` 的「机制独立性」读法**（主定理的规范名）。

`Y` 在给定 $X = x$ 下的律**与 $X$ 的边缘无关**：它**只**由 `kY (·, x)` 决定。

$$\frac{\kappa_{\mathrm{joint}}[X=x, Y\in t]}{\kappa_{\mathrm{joint}}[X=x]}
  = k_Y(\cdot,x)(t).$$

⟹ 与 `markov_conditional` 同一内容，命名以 SCM 语义为准。**零缺口**。 -/
theorem mechanism_of_fiber (M : SCMK X Y) [MeasurableSingletonClass X]
    [IsSFiniteKernel M.kX] [IsMarkovKernel M.kY]
    (x : X) (t : Set Y) (ht : MeasurableSet t) :
    M.joint () {p : X × Y | p.1 = x ∧ p.2 ∈ t}
      = M.joint () {p : X × Y | p.1 = x} * M.kY ((), x) t :=
  markov_conditional M x t ht

/-! ### §K.4b  ⭐⭐⭐⭐ **局部 Markov 性**（Pearl §1.2.3 的 kernel 表述） -/

/-- ⭐⭐⭐⭐ [理论] **局部 Markov 性（kernel 形式）**。

对**任意** $x$，$Y$ 在纤维 $X=x$ 上的律**不依赖** $X$ 的其他分量——
形式上：**存在**一族机制 $g : X \to \mathrm{Measure}\ Y$，使
$\kappa_{\mathrm{joint}}[X=x, Y\in t] = \kappa_{\mathrm{joint}}[X=x]\cdot g(x)(t)$。

**⟹ 本定理**证明**：`SCMK.joint` **满足**这一性质，且 $g$ **可以显式取**
`fun x => kY ((), x)`。**这正是「机制由父节点唯一决定」的 kernel 表述。** -/
theorem locallyMarkov (M : SCMK X Y) [MeasurableSingletonClass X]
    [IsSFiniteKernel M.kX] [IsMarkovKernel M.kY] :
    ∃ g : X → Measure Y, ∀ (x : X) (t : Set Y), MeasurableSet t →
      M.joint () {p : X × Y | p.1 = x ∧ p.2 ∈ t}
        = M.joint () {p : X × Y | p.1 = x} * g x t :=
  ⟨fun x => M.kY ((), x), fun x t ht => markov_conditional M x t ht⟩

end SCMK

/-! ===========================================================================
  §K.5  ⭐⭐⭐ **与 `PearlHierarchy.SCM` 的接口**（现有 `Fintype` 载体）
  =========================================================================== -/

section PearlInterface

variable {X Y : Type u} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSingletonClass X] [MeasurableSingletonClass Y]

/-- ⭐⭐⭐ [构造] **`PearlHierarchy.SCM` → `SCMK`**（**载体转换接口**）。

给定 `M : PearlHierarchy.SCM X Y`（`sg : U → X × (X → Y)`，`pU : U → ℝ`），
构造两个机制：

* `kX`：$X$ 的机制 —— **外生律沿 `u ↦ (sg u).1` 的推前**；
* `kY`：$Y$ 在 $x$ 给定下的机制 —— **外生律沿 `u ↦ (sg u).2 x` 的推前**。

**⚠ `pU` 的 `ℝ` → `ℝ≥0∞`**：`PearlHierarchy` 的律是**裸 `ℝ`**（可为负、可不归一），
故本接口**取正部** `ENNReal.ofReal`。**这不是无损嵌入**：若 `pU` 有负值，
转换后信息丢失 —— **依本项目纪律，这一点必须写明**，
而不是假装「`ℝ` 与 `ℝ≥0∞` 一样」。**`pU ≥ 0` 时无损**（见 `ofPearl_weight`）。 -/
noncomputable def ofPearl (M : PearlHierarchy.SCM X Y) : SCMK X Y where
  kX := discreteKernel (fun _ x => ∑ u, ENNReal.ofReal (M.pU u) * (if (M.sg u).1 = x then 1 else 0))
  kY := discreteKernel (fun p y => ∑ u, ENNReal.ofReal (M.pU u) * (if (M.sg u).2 p.2 = y then 1 else 0))

omit [MeasurableSingletonClass Y] in
/-- ⭐ [支撑] **`ofPearl` 的 `kX` 权重展开**（定义性）。 -/
lemma ofPearl_kX_apply (M : PearlHierarchy.SCM X Y) (x : X) :
    (ofPearl M).kX () {x} =
      ∑ u, ENNReal.ofReal (M.pU u) * (if (M.sg u).1 = x then 1 else 0) := by
  rw [ofPearl, discreteKernel_apply_singleton]

/-- ⭐ [支撑] **`ofPearl` 的 `kY` 权重展开**（定义性）。 -/
lemma ofPearl_kY_apply (M : PearlHierarchy.SCM X Y) (x : X) (y : Y) :
    (ofPearl M).kY ((), x) {y} =
      ∑ u, ENNReal.ofReal (M.pU u) * (if (M.sg u).2 x = y then 1 else 0) := by
  rw [ofPearl, discreteKernel_apply_singleton]

/-- ⭐⭐⭐ [验证] **`ofPearl` 的联合律在纤维盒子上 = `SCMSemantics` 条件的乘积**。

$$\kappa^{\mathrm{ofPearl}}_{\mathrm{joint}}(\cdot)\bigl[X=x, Y=y\bigr]
  = \Bigl(\sum_u \mathrm{ofReal}(p_U u)[\dots]\Bigr)\cdot
    \Bigl(\sum_u \mathrm{ofReal}(p_U u)[\dots]\Bigr)$$

**⟹ 这是 `markov_fiber` 在 `ofPearl` 上的**显式求值** ——
把 kernel 侧的抽象定理**落到现有载体的数值形式**上。
**⚠ 证明只需 `markov_fiber` + 两条展开引理，故零缺口，但价值在于**接口**而非新数学。** -/
theorem ofPearl_joint_apply (M : PearlHierarchy.SCM X Y) (x : X) (y : Y) :
    (ofPearl M).joint () {p : X × Y | p.1 = x ∧ p.2 = y} =
      (∑ u, ENNReal.ofReal (M.pU u) * (if (M.sg u).1 = x then 1 else 0)) *
      (∑ u, ENNReal.ofReal (M.pU u) * (if (M.sg u).2 x = y then 1 else 0)) := by
  have hbd : ∀ (_a : Unit), ∑ b, ∑ u, ENNReal.ofReal (M.pU u) *
      (if (M.sg u).1 = b then 1 else 0) ≤ ∑ u, ENNReal.ofReal (M.pU u) := by
    intro _a
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [Finset.sum_eq_single (M.sg u).1]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb)]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  haveI hfin : IsSFiniteKernel (ofPearl M).kX :=
    isSFiniteKernel_discreteKernel _ (∑ u, ENNReal.ofReal (M.pU u))
      (ENNReal.sum_lt_top.mpr (fun u _ => ENNReal.ofReal_lt_top)) hbd
  have hbd2 : ∀ (_p : Unit × X), ∑ b, ∑ u, ENNReal.ofReal (M.pU u) *
      (if (M.sg u).2 _p.2 = b then 1 else 0) ≤ ∑ u, ENNReal.ofReal (M.pU u) := by
    intro _p
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [Finset.sum_eq_single ((M.sg u).2 _p.2)]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb)]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  haveI hfin2 : IsSFiniteKernel (ofPearl M).kY :=
    isSFiniteKernel_discreteKernel _ (∑ u, ENNReal.ofReal (M.pU u))
      (ENNReal.sum_lt_top.mpr (fun u _ => ENNReal.ofReal_lt_top)) hbd2
  have h := SCMK.markov_fiber (ofPearl M) x {y} (measurableSet_singleton y)
  simp only [Set.mem_singleton_iff] at h
  rw [h, ofPearl_kX_apply, ofPearl_kY_apply]

end PearlInterface

/-! ===========================================================================
  §K.6  ⭐⭐⭐ **与 `SCMSemantics.jointLaw` 的一致性**
  =========================================================================== -/

/-! ### 说明（**为什么这里只有一个接口引理而不是完整等式**）

`SCMSemantics.jointLaw` 是 `ℝ` 值的**裸函数**
（`M.U × X × Y → ℝ`），而本模块的 `joint` 是 `ℝ≥0∞` 值的 **`Measure`**。
两者**不是同一个类型**，故「等式」只能经由 `ENNReal.ofReal` 建立：

$$\kappa^{\mathrm{ofPearl}}_{\mathrm{joint}}(\cdot)[X=x,Y=y]
  = \mathrm{ofReal}\bigl(\text{某 } \mathbb{R} \text{ 值}\bigr).$$

**⚠ 依纪律，这里不伪造「逐字一致」的等式**：

* `jointLaw` 的取值 `pU u * (if ... then 1 else 0)` 本身**不保证非负**；
* `mkMeasure` 的权重是 `ℝ≥0∞`（**必非负**）。

故本节的接口引理**只在 `pU ≥ 0` 的假设下**声称两者一致
（见 `jointLaw_nonneg` 与上节的 `ofPearl_joint_apply`）。
**⟹ 本节不做新东西，只登记「一致性的确切条件」** ——
这比伪造一个逐字等式**诚实**。

**⚠ 无新定理**：`§K.5` 的 `ofPearl_joint_apply` 已经是本节的全部内容，
且其右侧就是 `jointLaw` 形式的 `ℝ≥0∞` 版本。**故 §K.6 不重复陈述。** -/

/-! ===========================================================================
  §K.7  ⚠⚠ **剩余缺口登记**（**第 68 轮以来的精确状态**）
  =========================================================================== -/

/-! ### §K.7 的缺口表（**如实回答 `SCMSemantics:§68.4` 的登记**）

`SCMSemantics`（第 68 轮）登记的缺口共两条。**本模块的处置**：

| 第 68 轮缺口 | 本模块状态 | 依据 |
|---|---|---|
| 「有限律 → `Measure`」的嵌入 | ✅ **已做，且做得更彻底** | `mkMeasure` / `discreteKernel`（`§K.1`–`§K.2`）**直接**给 `Kernel`，不经裸律中转 |
| SCM 的**结构**（每节点一机制）写成概率对象 | ✅ **已做** | `SCMK`（`§K.3`），`joint = kX ⊗ₖ kY` |
| **Markov 性**（结构口径）| ✅ **已证，零缺口** | `SCMK.markov_fiber`（`§K.4`）|
| 局部 Markov 性（kernel 形式）| ✅ **已证，零缺口** | `SCMK.locallyMarkov`（`§K.4b`）|
| **d-分离 ⟹ `CondIndepFun`**（图侧）| ❌ **仍未做** | 需 `CondIndepFun` 与 kernel 对接；本模块只提供 kernel 侧接口 |

**⟹ 精确的剩余缺口**：**只剩图侧那一条**，即

$$
\text{d-分离}(X;Y\mid Z) \implies \bigl(\text{本模块的 } \texttt{joint} \text{ 在 } Z \text{ 给定下使 } X \perp Y\bigr).
$$

**⚠ 本模块**不**声称它已解决，也不**不**声称它未解决** ——
它**只提供**该桥所需的**左端**（一个完整的 `Kernel`，其纤维公式
`SCMK.markov_fiber` 已**可证**）。**右端的 `CondIndepFun` 对接**留给后续轮次。

**⚠ 与 `PearlGlobalMarkov` / `MarkovBridgeTheorem` 的关系**：
那些模块在 **`Finset` × `ℝ`** 口径下证了**代数的**因子分解；
本模块证的是 **`Kernel` 口径的结构 Markov 性**。**两者的对象不同、
不可互相替代**，故本模块**不**声称「补上了它们」。
-/

/-! ===========================================================================
  §K.8  ⭐⭐⭐ **N 元折叠**（每节点一个 kernel 的一般形式）
  =========================================================================== -/

/-! ### §K.8 说明：N 元折叠的口径（**不伪造未证的定义**）

`Kernel.compProd` 是**二元**运算
（`Kernel α β → Kernel (α × β) γ → Kernel α (β × γ)`）。
「每节点一个 kernel」在 $n$ 节点上的一般形式应写为**沿拓扑序的折叠**：

$$\kappa = k_{v_1} \otimes_k \bigl(k_{v_2} \otimes_k (k_{v_3} \otimes_k \cdots)\bigr),$$

其中 $v_1, \dots, v_n$ 是 `Causalean.Graph.DAG` 的**拓扑序**
（`DAGFactorizationGen.topoEnum` 已给出其存在性）。

**⚠ 本轮处置（依纪律，不越过能证的边界）**：

* **本轮只形式化二元情形**（`§K.3`–`§K.4`），
  因为 **二元折叠的 Markov 性已零缺口证明**（`SCMK.markov_fiber`）；
* **N 元折叠的 `SCMK` 载体**需要「把 `α × β` 迭代成嵌套右边」的类型工程
  （`compProd` 的右核定义域是 `α × β`，折叠时域会长成
  `Unit × X₁ × (X₂ × (X₃ × …))` 的嵌套形式）；**本轮不写半成品的 `chain`**，
  因为**一个类型不对的 `def` 比缺席更糟**（它会被后续引用，而编译器不报错）。
* **⚠ 因此 §K.8 是本轮「如实登记的未做项」**，不是「已做但略」。
  与 `SCMSemantics:§68.4` 的纪律一致：**缺口该写明就写明**。

**N 元折叠的**正确**做法（下一轮的起点）**：
定义 `SCMKFamily (n : ℕ) (V : Fin n → Type) (pa : ∀ i, Set (V i))`
（父集索引），再对 `n` 做**结构递归**，
每一步用 `compProd` 并套用本轮的 `markov_fiber`
（`markov_fiber` 的**陈述不依赖节点数**，故每步都直接可用）。 -/

end SCMKernel

end FateV2.Modeling