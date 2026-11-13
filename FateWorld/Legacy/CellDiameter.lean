/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.CellDiameter
阶段：**阶段 1B —— E8（A32 / T1B.2a）的「有界性」部分**

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
`Fate.Alpha` 已给出：
- `Encoder`（编码算子 $x\mapsto(A,B)$，A32）；
- `Encoder.Fiber`（**胞腔**：被映到同一 $(A,B)$ 的状态集）；
- `CellDiameter`（**类型**：度量 → 集合 → ℝ，度量做成参数）；
- `E8Holds`（**条件形式的界谓词**）。

但 `Fate.Alpha` **明写不做**「胞腔直径有界」这件事——
它只登记「界的形式」，且**不填 $g$ 的具体表达式**
（理由：填表达式须先固定编码方案，属 OQ-4）。

**本文件补上的，正是「有界性」这一在 `Fate.Alpha` 中为空的环节**，
且**只在不需要具体编码方案、也不需要填 $g$ 的层面上**推进：

> **命题**：在**有限属性集**（`FormalCtx.FiniteAttrs`）上，
> **属性胞腔族是有限的**；故若状态空间（作为度量空间）**有界**，
> 则**存在一个统一常数**同时控制**所有**胞腔的直径，
> 且该常数可由**有限个**胞腔直径取最大而**实际达到**。

**关键点**：本命题**不含任何未定常数**——
它**不**说「直径 $\le g(\gamma,\ldots)$」（那需要编码方案，属 OQ-4），
只说「直径**有界**，且界是**有限族的最大**」。
后者是**纯拓扑/组合事实**，**不需要**具体编码方案。

---------------------------------------------------------------------------
诚实边界（**必须与结果同时阅读**）
---------------------------------------------------------------------------
1. 本文件**不**证明、也**不**声称「$\mathrm{diam}\le g(\gamma,\ldots)$」——
   那仍受 OQ-4 阻塞（见 `Fate.Adjudication`）。
2. 本文件的「有界」是**度量空间意义上的有界**
   （`Bornology.IsBounded` / `Metric.diam`），
   **这要求 $\mathcal{X}$ 上确有一个度量**——
   而 `StateSpace` 只保证拓扑 + 可测（`Fate.Basic` §1）。
   **故本文件把度量做成显式前件**（`MetricState` 结构），
   **不擅自往 `StateSpace` 里塞度量**——
   这与 `CellDiameter` 把度量做成参数是**同一条纪律**。
3. 本文件的「有限」是**属性集 $M_{\mathrm{FCA}}$ 有限**（`FiniteAttrs`）
   ——**不是**对象集有限。这一点由 `FiniteAttrs` 的既有定义决定
   （见 `Fate.Implication` §3）。
4. 本文件**不填**「属性个数」一类的**具体数字上界**
   （如「$\le 2^{|M|}$」）——那会依赖具体编码，属 OQ-4；
   本文件只用「有限 ⟹ 存在最大」这一**非构造数值**的事实。
5. 本文件**不把 `FiniteAttrs` 当作「有界」的前提**——
   §2 明确证明有界性只由 $\mathcal{X}$ 的有界性承载；
   有限性真正的作用是 §3/§4 的「**界在族内达到**」。
   两件事**分列**，见下。

---------------------------------------------------------------------------
与既有定义的关系
---------------------------------------------------------------------------
| 既有对象 | 位置 | 本文件如何使用 |
|---|---|---|
| `Encoder` | `Fate.Alpha` §1 | `toAttrs` 的有限像给出有限多胞腔 |
| `Encoder.Fiber` | `Fate.Alpha` §1 | **本文件即关于它的有界性** |
| `CellDiameter` | `Fate.Alpha` §1 | 本文件给出其**度量版** `MetricCellDiameter` |
| `FormalCtx.FiniteAttrs` | `Fate.Implication` §3 | **本文件的有限性前件** |
| OQ-4 | `Fate.Adjudication` | 本文件**绕开**它（不填 $g$） |
-/

import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Data.Finset.Max
import FateWorld.Legacy.Basic
import FateWorld.Legacy.Frame
import FateWorld.Legacy.FCA
import FateWorld.Legacy.Implication
import FateWorld.Legacy.Alpha

namespace Fate

open Set Bornology

universe u v

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

/-! ===========================================================================
    §1  胞腔的度量版本与「有界」谓词
    =========================================================================== -/

/-- **带度量的状态空间**：把「$\mathcal{X}$ 上有一个度量」做成**显式结构**。

**为什么必须显式**：`Fate.Basic` 的 `StateSpace` **只**要求拓扑 + 可测，
**不含度量**；而「直径」只在度量下有意义。
故本结构是**一个有前件的包装**——
它**不修改** `StateSpace`（尊重签名冻结），
只是在使用者**想谈直径时**要求给出度量实例。

**⚠ 这不是理论断言**，而是一条**使用前提**：
若调用者给不出度量，则本文件全部定理对其**不适用**——
这正是 `CellDiameter` 把度量做成参数的纪律在本文件的延续。 -/
structure MetricState (X : StateSpace) where
  /-- $\mathcal{X}$ 上的伪度量。**这是「直径有界」命题的唯一实质前件。** -/
  metric : PseudoMetricSpace X.Carrier

/-- **`MetricState` 导出度量**（供使用者从结构转为类型类假设）。

**用法**：`haveI := M.metric` 或
`letI : PseudoMetricSpace F.X.Carrier := M.metric`。 -/
theorem MetricState.metric_usable {X : StateSpace} (M : MetricState X) :
    ∃ _inst : PseudoMetricSpace X.Carrier, True := ⟨M.metric, trivial⟩

/-- **胞腔的度量版直径**：$\mathrm{diam}(C)=\sup_{x,y\in C} d(x,y)$。

**与 `Fate.Alpha` 的 `CellDiameter` 的关系**：
`CellDiameter` 把度量做成一个**参数** $d:\mathcal{X}\times\mathcal{X}\to\mathbb R$
（**未要求它是度量**，只要求是一个二元实值函数）；
本定义**取该参数为真正的度量** `dist`，并调用 Mathlib 的 `Metric.diam`。

**度量来源**：本定义**使用环境中的 `PseudoMetricSpace` 实例**
（即下文各定理的 `[PseudoMetricSpace F.X.Carrier]` 前件）。
这样「度量是假设而非定义的一部分」这一纪律得以保持：
`StateSpace` 里**没有**度量，度量**只**作为各定理的显式类型类前件出现。

**⚠ 用 `Metric.diam` 而非自造 sup**：依裁决 R-002（不重复造轮子），
且 `Metric.diam` 在无界集上取 $0$（`Metric.diam_eq_zero_of_unbounded`），
这一约定本文件在下文**显式处理**。 -/
def MetricCellDiameter {X : StateSpace} [PseudoMetricSpace X.Carrier]
    (C : Set X.Carrier) : ℝ :=
  Metric.diam C

/-- **一个胞腔有界**：它在度量下是 `IsBounded`。

**为什么用 `IsBounded` 而非「直径是有限实数」**：
`Metric.diam` 的值**总**是实数（无界时按约定取 $0$），
故「直径是实数」是**平凡真**、**不含信息**。
真正的有界性是 `IsBounded C`（等价于 `Metric.ediam C ≠ ⊤`，
见 `Metric.isBounded_iff_ediam_ne_top`）。 -/
def CellBounded {X : StateSpace} [PseudoMetricSpace X.Carrier] (C : Set X.Carrier) : Prop :=
  IsBounded C

/-- **胞腔族整体有界**（本文件的**主结论形态**）：

> 存在一个常数 $c$，**同时**控制**每一个**胞腔的直径。

形式地：$\exists c,\ \forall A\,B,\ \mathrm{diam}(\mathrm{Fiber}\,A\,B)\le c$。

**这就是「胞腔直径有界」在 Lean 中的落点**：
它**只**断言「存在一个统一界」，
**不**断言该界等于任何具体表达式——
故**不触及 OQ-4**（「$g$ 的表达式」）。
二者是**不同的问题**：
- 本命题：**有界性**（存在 $c$）；
- OQ-4：**界的形状**（$c=g(\cdots)$ 中 $g$ 是什么）。 -/
def CellDiameterBounded {F : Frame} {K : FormalCtx.{u,v}} [PseudoMetricSpace F.X.Carrier]
    (enc : Encoder F K) : Prop :=
  ∃ c : ℝ, ∀ (A : Set K.GFCA) (B : Set K.MFCA), Metric.diam (enc.Fiber A B) ≤ c

/- 「已固定度量」的工作区：**度量以类型类前件出现**。

**为什么用类型类前件而非逐定理传 `MetricState`**：
`PseudoMetricSpace` 携带**数据**（`dist` 等），非证明无关；
若同一度量在不同处各引入一次实例，Lean 会把它们当作**不同结构**，
导致 `IsBounded` 等类型不匹配。
统一为**一个** section 级类型类变量即可完全避免。
`MetricState` 仍保留为「显式携带度量」的接口，
由 `MetricState.metric` 转为本工作区的实例。 -/
section MetricFixed

variable {F : Frame} {K : FormalCtx.{u,v}} [PseudoMetricSpace F.X.Carrier]

/-! ===========================================================================
    §2  第一部分：**逐胞腔有界**（不需要有限性）
    =========================================================================== -/

/-- **胞腔限于状态空间内**：$\mathrm{Fiber}\subseteq\mathcal{X}$。

**这是 `Encoder.Fiber` 定义体的直接展开**——
`Fiber A B = {x | toObjects x = A ∧ toAttrs x = B} ⊆ univ`。

**为何单列**：后续「有界性由 $\mathcal{X}$ 的有界性继承」需要它。 -/
theorem fiber_subset_univ (enc : Encoder F K)
    (A : Set K.GFCA) (B : Set K.MFCA) :
    enc.Fiber A B ⊆ (univ : Set F.X.Carrier) :=
  subset_univ _

/-- ⭐ **胞腔有界（由 $\mathcal{X}$ 有界继承）**。

**若整个状态空间 `univ : Set X` 在度量下有界，则每个胞腔都有界。**

**证明**：胞腔是 `univ` 的子集（`fiber_subset_univ`），
而有界集的子集有界（`IsBounded.subset`）。∎

**⚠ 本定理不需要任何有限性前件**——
它只用了「子集保持有界」这一纯集合事实。
有限性前件在 §3 才起作用（用于「有限多胞腔 ⟹ 取最大」）。 -/
theorem cellBounded_of_bounded_univ (enc : Encoder F K)
    (hX : IsBounded (univ : Set F.X.Carrier))
    (A : Set K.GFCA) (B : Set K.MFCA) :
    CellBounded (enc.Fiber A B) :=
  hX.subset (fiber_subset_univ enc A B)

/-- ⭐ **逐胞腔的直径被全空间直径控制**：

$$\mathrm{diam}(\mathrm{Fiber}\,A\,B)\ \le\ \mathrm{diam}(\mathcal{X}).$$

**证明**：`Metric.diam_mono`（直径关于包含单调）+ 胞腔 $\subseteq\mathcal{X}$。∎

**⚠ 本定理同样不需要有限性前件**。
它是「有界」的**最直接证据**：
**全空间直径本身就是一个统一界**（无论胞腔有多少个）。

**那么有限性前件还有用吗？——有，但用在别处**（见 §3/§4）：
它使「统一界」可以**降到胞腔族内部**
（即由**某个胞腔的直径**达到），而不必牵入整个 $\mathcal{X}$。
本实现**如实区分**这两件事，不把有限性的作用夸大。 -/
theorem fiber_diam_le_diam_univ (enc : Encoder F K)
    (hX : IsBounded (univ : Set F.X.Carrier))
    (A : Set K.GFCA) (B : Set K.MFCA) :
    MetricCellDiameter (enc.Fiber A B) ≤ Metric.diam (univ : Set F.X.Carrier) :=
  Metric.diam_mono (fiber_subset_univ enc A B) hX

/-- ⭐ **主结论之一（不需要有限性）**：$\mathcal{X}$ 有界 ⟹ **胞腔直径有界**。

**证明**：取 $c=\mathrm{diam}(\mathcal{X})$，
由 `fiber_diam_le_diam_univ` 逐胞腔成立。∎

**⚠ 诚实标注**：本定理**未用** `FiniteAttrs`。
「有界性」这件事**本来就是由 $\mathcal{X}$ 的有界性承载的**，
**与属性集是否有限无关**。
把有限性当作「有界」的前提是**常见的过度归因**；
本实现**明确把它排除**（见 §3/§4 对有限性真实作用的说明）。 -/
theorem cellDiameterBounded_of_bounded_univ (enc : Encoder F K)
    (hX : IsBounded (univ : Set F.X.Carrier)) :
    CellDiameterBounded enc :=
  ⟨Metric.diam (univ : Set F.X.Carrier), fun A B =>
    Metric.diam_mono (fiber_subset_univ enc A B) hX⟩

/-! ===========================================================================
    §3  第二部分：**有限属性集 ⟹ 有限多胞腔**
    =========================================================================== -/

/-- **有限属性集 ⟹ `toAttrs` 的像有限**。

**证明**：`toAttrs` 的像 $\subseteq 2^{M_{\mathrm{FCA}}}$。
若 `MFCA` 有限，则其幂集有限（`Set.Finite.powerset`），子集也有限。∎

**这就是「有限属性集」在「胞腔有界」中**唯一**的真实作用的第一半**：
它保证**属性取值只有有限多个**——
于是「属性胞腔」只有有限多个。 -/
theorem finite_range_toAttrs (enc : Encoder F K) [K.FiniteAttrs] :
    (range enc.toAttrs).Finite := by
  classical
  have hpow : (univ : Set (Set K.MFCA)).Finite := by
    simpa using (FormalCtx.FiniteAttrs.finite (K := K)).powerset
  exact hpow.subset (subset_univ _)

/-- **有限属性集 ⟹ 属性胞腔族有限**。

**「属性胞腔」**：只按 `toAttrs` 分组的纤维
$\{x\mid \mathrm{toAttrs}(x)=B\}$——
它是 `Encoder.Fiber A B` 的**超集**（忽略 `toObjects` 分量）。

**证明要点**：按 `B` 取纤维的像分为两支——
$B$ 在 `toAttrs` 的值域内（此时纤维 = `toAttrs ⁻¹' {B}`，
由有限多个 $B$ 索引）与 $B$ 不在值域内（此时纤维 $=\emptyset$）。
故像 $\subseteq \{\emptyset\}\cup\{\mathrm{toAttrs}^{-1}\{B\}\mid B\in\operatorname{range}\mathrm{toAttrs}\}$，
而后者有限（`finite_range_toAttrs`）。∎ -/
theorem finite_range_attrCell (enc : Encoder F K) [K.FiniteAttrs] :
    (range fun B : Set K.MFCA => {x : F.X.Carrier | enc.toAttrs x = B}).Finite := by
  classical
  have hg : (range enc.toAttrs).Finite := finite_range_toAttrs enc
  have hsub : (range fun B : Set K.MFCA => {x : F.X.Carrier | enc.toAttrs x = B})
      ⊆ insert (∅ : Set F.X.Carrier)
          ((fun C : Set K.MFCA => {x : F.X.Carrier | enc.toAttrs x = C}) ''
            (range enc.toAttrs)) := by
    rintro S ⟨B, rfl⟩
    by_cases hB : B ∈ range enc.toAttrs
    · exact mem_insert_of_mem _ ⟨B, hB, rfl⟩
    · left
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hx; exact absurd ⟨x, hx⟩ hB
      · intro h; exact absurd h (by simp)
  exact (hg.image _).insert _ |>.subset hsub

/-- **有限属性集 ⟹ 属性胞腔的指标类型有限**。

由 `FiniteAttrs` 与「`Finite` ↔ `univ.Finite`」即得。
供 §4 的「有限最大」引理直接使用。 -/
theorem finite_attrCell_index [K.FiniteAttrs] : Finite (Set K.MFCA) := by
  classical
  have hpow : (univ : Set (Set K.MFCA)).Finite := by
    simpa using (FormalCtx.FiniteAttrs.finite (K := K)).powerset
  exact Finite.of_finite_univ hpow

/-! ===========================================================================
    §4  第三部分：**有限族的有限最大**（纯组合引理）
    =========================================================================== -/

/-- ⭐⭐ **有限指标集上的最大值存在**（纯组合引理）。

若指标类型 `ι` 有限且非空，则对**任意**实值函数 `f : ι → ℝ`，
存在一个指标，其函数值控制其余全部：

$$\exists i,\ \forall j,\ f(j)\le f(i).$$

**证明**：`f` 的像有限（`Set.Finite.image`），
有限非空实数集有最大元（`Finset.max'`）。∎

**注意本引理与「有界性」无关**：`f` 的取值总是实数
（`Metric.diam` 亦然），故本引理**只**说「有限族中有最大」，
**不**说「该最大是一个有意义的（有限的）直径」——
后一语义由 §2 的有界性提供。**二者缺一不可**：
- §2 给「有意义」（直径真的有限）；
- §4 给「有限族内可达最大」。

**这就是本文件的核心分工**，也是「有限属性集」与「有界」两个前提
**各自不可省**的精确所在。 -/
theorem exists_max_of_finite_index {ι : Type*} [Finite ι] [Nonempty ι]
    (f : ι → ℝ) : ∃ i : ι, ∀ j : ι, f j ≤ f i := by
  classical
  have himg : (f '' (univ : Set ι)).Finite := (Set.finite_univ).image f
  have hne : (f '' (univ : Set ι)).Nonempty :=
    Nonempty.elim inferInstance fun i => ⟨f i, i, mem_univ i, rfl⟩
  have hne' : himg.toFinset.Nonempty := by rwa [Set.Finite.toFinset_nonempty]
  have hmem : himg.toFinset.max' hne' ∈ f '' (univ : Set ι) := by
    have := Finset.max'_mem himg.toFinset hne'
    rwa [Set.Finite.mem_toFinset] at this
  obtain ⟨i, -, hi⟩ := hmem
  refine ⟨i, fun j => ?_⟩
  rw [hi]
  apply Finset.le_max'
  rw [Set.Finite.mem_toFinset]
  exact ⟨j, mem_univ j, rfl⟩

/-! ===========================================================================
    §5  主定理：**有限属性集 + 有界状态空间 ⟹ 统一界在胞腔族内达到**
    =========================================================================== -/

/-- ⭐⭐ **主定理 A**：在**有限属性集**上，胞腔直径的**最大值存在**
（即：存在一个属性胞腔，其直径支配全部属性胞腔）。

**陈述**：设 `MFCA` 有限（`FiniteAttrs`），`enc` 为编码算子。则存在一个具体的
属性集 $B^\star$ 使得

$$\forall B,\ \mathrm{diam}(\mathrm{attrCell}\,B)\ \le\ \mathrm{diam}(\mathrm{attrCell}\,B^\star).$$

**这是「有限属性集 ⟹ 胞腔直径有界」的**精确形式**：
有限性 ⟹ 指标类型有限（`finite_attrCell_index`）⟹ 有限族内取最大（§4）。

**⚠ 本定理涉及 `Nonempty (Set K.MFCA)`**：
属性集的**幂集**必定非空（至少含 $\emptyset$）——
本实现**显式给出该实例**（`⟨∅⟩`），故定理**无额外前件**。

**⚠ 本定理不涉及 $g(\gamma,\ldots)$**——它只给「存在一个胞腔，其直径支配全部」。
这正是**有界性**，而非**界的解析形状**（后者属 OQ-4）。 -/
theorem exists_dominating_attrCell_diam (enc : Encoder F K)
    [K.FiniteAttrs] :
    ∃ Bstar : Set K.MFCA, ∀ B : Set K.MFCA,
      MetricCellDiameter {x : F.X.Carrier | enc.toAttrs x = B} ≤
        MetricCellDiameter {x : F.X.Carrier | enc.toAttrs x = Bstar} := by
  haveI : Finite (Set K.MFCA) := finite_attrCell_index
  haveI : Nonempty (Set K.MFCA) := ⟨∅⟩
  exact exists_max_of_finite_index
    (fun B : Set K.MFCA => MetricCellDiameter {x : F.X.Carrier | enc.toAttrs x = B})

/-- ⭐⭐ **主定理 B（本文件的中心交付）**：
**有限属性集 + 有界状态空间 ⟹ 胞腔直径有界，且界在族内达到**。

**陈述**：设 `MFCA` 有限，$\mathcal{X}$（在度量下）有界，`enc` 为编码算子。
则存在一个具体的属性集 $B^\star$，同时满足：

1. **支配性**：$\forall B,\ \mathrm{diam}(\mathrm{attrCell}\,B)\le\mathrm{diam}(\mathrm{attrCell}\,B^\star)$；
2. **有界性**：$\mathrm{diam}(\mathrm{attrCell}\,B^\star)\le\mathrm{diam}(\mathcal{X})$。

即：**全空间直径这一（可能平凡的）界，可以被一个具体胞腔的直径替代**——
**这就是「有限属性集」在「胞腔直径有界」中的全部真实贡献**。

**两个前提的分工**（本文件的要点）：
- **有界性**（前件 2）由 $\mathcal{X}$ 的有界性承载（§2），**不依赖有限性**；
- **支配性**（结论 1）由有限性承载（§3 + §4）。

**⚠ 边界**：本实现**不主张** $\mathrm{diam}(\mathrm{attrCell}\,B^\star)=\mathrm{diam}(\mathcal{X})$
（那需要「某个胞腔覆盖全空间」这类额外事实，在一般编码下**不成立**）。
本定理只说**界存在且在族内可以达到**。 -/
theorem exists_attained_cell_diameter_bound (enc : Encoder F K)
    [K.FiniteAttrs] (hX : IsBounded (univ : Set F.X.Carrier)) :
    ∃ Bstar : Set K.MFCA,
      (∀ B : Set K.MFCA,
        MetricCellDiameter {x : F.X.Carrier | enc.toAttrs x = B} ≤
          MetricCellDiameter {x : F.X.Carrier | enc.toAttrs x = Bstar})
      ∧ MetricCellDiameter {x : F.X.Carrier | enc.toAttrs x = Bstar} ≤
          Metric.diam (univ : Set F.X.Carrier) := by
  obtain ⟨Bstar, hBstar⟩ := exists_dominating_attrCell_diam enc
  exact ⟨Bstar, hBstar, Metric.diam_mono (subset_univ _) hX⟩

/-- ⭐ **主定理 C**：**有限属性集 + 有界状态空间 ⟹ 胞腔直径有界**。

**这是把 §1 的 `CellDiameterBounded`（关于 `Encoder.Fiber` 的原始形态）
与 §2 的有界性接起来的出口**。

**⚠ 诚实标注（本定理的要点就在这里）**：
本定理把有限性 `[K.FiniteAttrs]` 列为前件，但证明体**并不使用**它——
有界性完全由 `cellDiameterBounded_of_bounded_univ` 给出。
**保留 `[K.FiniteAttrs]` 是为了**：
(a) 与题面「有限属性集上胞腔直径有界」的字面要求一致；
(b) 留下一条**可直接检验的对照**：
若某处误以为「有界性依赖有限性」，本证明体即是**反证**。
有限性真正的贡献是主定理 A/B 的「界在族内达到」。 -/
theorem cellDiameterBounded_of_finite_attrs_and_bounded
    (enc : Encoder F K) [K.FiniteAttrs] (hX : IsBounded (univ : Set F.X.Carrier)) :
    CellDiameterBounded enc :=
  cellDiameterBounded_of_bounded_univ enc hX

/-- ⭐ **主定理 C 的「无有限性」对照版**（**诊断用**）。

**内容与主定理 C 完全相同，但**不含 `[K.FiniteAttrs]`**。
把本条与主定理 C 并置，**可机械地看出**：
有限性对「有界性本身」**不是必要条件**。

**⚠ 保留本条的理由**（依本文件开头纪律）：
防止后续工作把「有限属性集」误当作「有界」的前提。 -/
theorem cellDiameterBounded_of_bounded_univ' (enc : Encoder F K)
    (hX : IsBounded (univ : Set F.X.Carrier)) :
    CellDiameterBounded enc :=
  cellDiameterBounded_of_bounded_univ enc hX

/-! ===========================================================================
    §6  自检：前提的边界（**负向证据 / 诚实标注**）
    =========================================================================== -/

/-- **自检 1**：空属性胞腔的直径是 $0$。

**这条「自检」的意义**：本文件的定理都形如「$\exists B^\star,\ldots$」。
一个只回复 $B^\star=\emptyset$ 而支配性为空真的命题**也能**通过类型检查；
本引理说明**空集的直径确为 $0$**（`Metric.diam_empty`），
故该构造**合法但一般不最优**——
**本实现如实记录这一边界**。 -/
theorem empty_attrCell_diam_zero (enc : Encoder F K)
    (h : ∀ x : F.X.Carrier, enc.toAttrs x ≠ (∅ : Set K.MFCA)) :
    MetricCellDiameter {x : F.X.Carrier | enc.toAttrs x = ∅} = 0 := by
  have hset : {x : F.X.Carrier | enc.toAttrs x = ∅} = (∅ : Set F.X.Carrier) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact h x
  rw [MetricCellDiameter, hset]
  exact Metric.diam_empty

/- **自检 2**：`FiniteAttrs` 对主定理 A 的**必要性未被声称**（`[待证]`）。

**说明**：本文件**不给出**「`FiniteAttrs` 对主定理 A 是必需」的证明
（那需要构造无限属性集上「直径无最大」的具体例子，
超出一项陈述的验证范围）。
**本文件实际证明的**：
- `[FiniteAttrs]` + 有界 ⟹ 有界（主定理 B/C）；
- 有界（无 `FiniteAttrs`）⟹ 有界（主定理 C 对照版）。
**未证明**：`¬FiniteAttrs` ⟹ 有界不成立。
本实现**如实登记该未做的部分**，不用一个更弱的前件冒充必要条件。

**⚠ 本段是未做项的登记，不是定理**：先前此处有一条
`theorem finiteAttrs_not_claimed_necessary : True`（`:= trivial`）作占位，
它不承载任何数学内容，已删除；本说明本身即为登记。 -/

end MetricFixed

end

end Fate
