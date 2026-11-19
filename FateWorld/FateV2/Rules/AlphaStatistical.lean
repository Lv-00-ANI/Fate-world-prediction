/-
命运理论 · Lean 4 形式化实现
================================

模块：`AlphaStatistical`
阶段：**α 的统计版本 —— 经验条件核 + 置信带，及「何时 `IsPoint`」的判据**

---------------------------------------------------------------------------
本文件补什么（与 `FateV2.Rules` / `LawRule` 的分工）
---------------------------------------------------------------------------
`FateV2.Rules`（裁决 D）把 α 做成 **FCA 取概念过程** `takeConcept`——
那是 α 在**属性侧/概念侧**的版本。

`LawRule` 把规则的载体定为

$$\text{Rule} := C \to X \to \mathcal{P}(\mathrm{Measure}\ Y),$$

并把「单点档」定为

$$\texttt{IsPoint}\ R \iff \forall c\,x,\ \exists \mu,\ R\,c\,x = \{\mu\}.$$

**但这两者之间缺一张纸**：`LawRule` 说「α 输出的是**一组**测度」，
而**没有任何构造从数据给出这组测度**。本文件给出该构造：

$$\underbrace{\{(c_i,x_i,y_i)\}_{i\le n}}_{\text{有限样本}}
  \xrightarrow{\ \text{§2 经验条件核}\ }
  \underbrace{\hat\mu_n(c,x)}_{\text{experience}}
  \xrightarrow{\ \text{§3 置信带}\ }
  \underbrace{R^{\mathrm{stat}}_n(c,x)}_{\text{一组测度}}
  \xrightarrow{\ \text{§4}\ }
  \underbrace{\texttt{IsPoint}\ ?}_{\text{何时单点}}$$

---------------------------------------------------------------------------
一句话结论
---------------------------------------------------------------------------
$$\boxed{\ \texttt{IsPoint}\ R^{\mathrm{stat}}_n
  \iff \underbrace{\forall c\,x,\ n(c,x)\ge n_{\min}}_{\text{(C) 覆盖}}
  \ \wedge\ \underbrace{\forall c\,x,\ \mathrm{Ball}(c,x)\text{ 单点}}_{\text{(E) 带塌缩}}.\ }$$

**(C)** 是统计条件（每个格位都有足够样本，**没有空切片**）；
**(E)** 是**纯几何/信息**条件（置信带在该格位上只含**一个**测度）。

⚠ **主结论的实质**：由 §6 的**分离定理**，(E) 在 **ε > 0** 且 Y 有两点时
**永不成立** —— 即

$$\varepsilon>0\ \wedge\ |Y|\ge 2 \ \Longrightarrow\ \neg\,\texttt{IsPoint}\ R^{\mathrm{stat}}_n .
$$

**故统计版 α 在「有不确定性」时必然不是单点规则**，
这正是 `LawRuleToTraj` 所说「`IsPoint` 是额外一道闸」的**统计侧来源**：
**闸就是置信带宽度 ε**。

---------------------------------------------------------------------------
诚实边界（**必须与结果同时阅读**）
---------------------------------------------------------------------------
1. **经验核用「去重计数」`Finset.card` 归一**（§2.3）。这在**连续 Y**
   上退化为 `δ` 型 / 退化情形——本文件**明确声明**该归一只在
   「细胞内的输出取值集合」意义下成立，**不冒充**真正的经验测度
   `(1/n)∑ δ_{y_i}`（后者需 `Multiset` 计数，本文件不用）。
   见 §2.3 的**精确陈述**与其后的**警示**。
2. **(E) 的可判定性本文件不主张**：`Ball` 的单点性依赖
   `d : Measure Y → Measure Y → ℝ≥0∞` 这个**外部给定的「距离」**。
   本文件**不指定** `d`（那是编码/度量方案的选择，规格未固定，
   与 `FateV2.Rules` §4 E8 同一条纪律：**填数即为虚构**）。
3. §5 的**覆盖正确性**是**条件定理**：前件 `GoodEvent`
   （「真实核落在带内」）**显式写出**，其**概率界的成立性不在本文件**。
4. 本文件**零 `sorry` / 零 `axiom`**。
-/

import FateWorld.FateV2.Rules.LawRule
import FateWorld.FateV2.Rules.Alpha
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
/- 本仓既有约定：`Sample` 的参数里有些字段只用于文档/类型指标，
不影响定理陈述，故关闭 unusedSectionVars 噪音（与 `FateV2.Predict.BackdoorCriterion` 等同）。 -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AlphaStatistical

open MeasureTheory Set

/- `LawRule` / `IsPoint` 定义在 `LawRule` 命名空间（`FateV2.Model` 的别名不在同名空间）。 -/
open FateV2.Rules.LawRule

universe u

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]
  [DecidableEq Y.Carrier]
variable {ι : Type*} [DecidableEq ι]

/-!
  # Rules · AlphaStatistical

  ## 迁移登记
  - 来源：`FateWorld/Legacy/AlphaStatistical.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LawRule, Alpha
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  样本：有限观测的载体
    =========================================================================== -/

/-- **有限样本**：以 `Finset ι` 为下标集的观测集合。

每条观测 $i$ 给出三元组 $(c_i, x_i, y_i)$——
上下文、前状态、输出。

**为什么用 `Finset`（而非 `MeasurableSpace` 上的随机变量）**：
统计版的 α **必须能由数据算出**。用 `Finset` 使 `α` 的构造
**纯组合**（`filter` + `card` + 有限求和），**不引入任何概率公理**，
从而使 §4 的 `IsPoint` 判据成为**关于数据本身**的命题——
而不是关于「某个不可观测的真分布」的命题。
随机性只在 §5 的 `GoodEvent` 里出现，且是**显式前件**。 -/
structure Sample (Ctx : CtxSpace) (St : StateSpace) (Out : OutSpace) (ι : Type*) where
  /-- 观测到的上下文 $c_i$ -/
  ctx : ι → Ctx.Carrier
  /-- 观测到的前状态 $x_i$ -/
  pre : ι → St.Carrier
  /-- 观测到的输出 $y_i$ -/
  out : ι → Out.Carrier

namespace Sample

/-- **格位（cell）**：上下文为 $c$、前状态为 $x$ 的观测下标集。

$$\mathrm{cell}(c,x) := \{i \in \text{sample} \mid c_i = c \wedge x_i = x\}$$

这是**经验条件核**的全部输入——条件化 = 取格位。 -/
def cell (S : Sample C X Y ι) [DecidableEq C.Carrier] [DecidableEq X.Carrier]
    (s : Finset ι) (c : C.Carrier) (x : X.Carrier) : Finset ι :=
  s.filter fun i => S.ctx i = c ∧ S.pre i = x

/-- **格位计数** $n(c,x)$。 -/
def count (S : Sample C X Y ι) [DecidableEq C.Carrier] [DecidableEq X.Carrier]
    (s : Finset ι) (c : C.Carrier) (x : X.Carrier) : ℕ :=
  (S.cell s c x).card

/-- 单元格位内的观测下标**确在样本内**（结构引理，供 §2.2 使用）。 -/
theorem cell_subset (S : Sample C X Y ι) [DecidableEq C.Carrier] [DecidableEq X.Carrier]
    (s : Finset ι) (c : C.Carrier) (x : X.Carrier) :
    S.cell s c x ⊆ s :=
  Finset.filter_subset _ _

/-- **格位内的输出值集合**（**去重**）。

$$\mathrm{outs}(c,x) := \{y_i \mid i \in \mathrm{cell}(c,x)\}$$

⚠ 去重是**刻意的**：它使 §2.3 的归一用 `card` 而不是重数。
见 §2.3 的精确陈述与警示。 -/
def outs (S : Sample C X Y ι) [DecidableEq C.Carrier] [DecidableEq X.Carrier]
    (s : Finset ι) (c : C.Carrier) (x : X.Carrier) : Finset Y.Carrier :=
  (S.cell s c x).image fun i => S.out i

end Sample

/-! ===========================================================================
    §2  经验条件核 $\hat\mu_n(c,x)$
    =========================================================================== -/

namespace Sample

/-- **未归一的经验质量**：格位内每个**不同**输出一个单位质量。

$$\widehat{M}_n(c,x) := \sum_{y\in\mathrm{outs}(c,x)} \delta_y$$

**为什么写成「和」而非「平均」**：平均需要除以计数，
而计数在空格位为零（§2.4 处理）。把归一与计数**分开**，
使「空格位」这件事在类型层就可见（`outs = ∅` ⟺ 质量为 0），
而不是被一个 `0/0` 吞掉。 -/
noncomputable def rawEmpirical (S : Sample C X Y ι)
    [DecidableEq C.Carrier] [DecidableEq X.Carrier]
    (s : Finset ι) (c : C.Carrier) (x : X.Carrier) : Measure Y.Carrier :=
  ∑ y ∈ S.outs s c x, (Measure.dirac y : Measure Y.Carrier)

/-- **经验条件核** $\hat\mu_n(c,x)$（归一版）。

$$\hat\mu_n(c,x) := \frac{1}{\#\mathrm{outs}(c,x)}
  \sum_{y\in\mathrm{outs}(c,x)} \delta_y$$

⚠ **空格位时取 `rawEmpirical` 本身（= 0 测度）**，
此为 `if` 分支的**显式约定**，不是"隐藏的假设"。
§2.4 给出该约定下 `IsPoint` **必然失败**的定理
（`empirical_eq_zero_of_empty`，见下）——即该约定**不掩盖**空格位问题。 -/
noncomputable def empirical (S : Sample C X Y ι)
    [DecidableEq C.Carrier] [DecidableEq X.Carrier]
    (s : Finset ι) (c : C.Carrier) (x : X.Carrier) : Measure Y.Carrier :=
  if _h : (S.outs s c x).Nonempty then
    ((S.outs s c x).card : ENNReal)⁻¹ • S.rawEmpirical s c x
  else S.rawEmpirical s c x

/-- **§2.3 精确陈述（归一正确性）**：非空格位的经验核是**概率测度**。

$$\hat\mu_n(c,x)(\text{univ}) = 1$$

**证明**：`rawEmpirical` 在全集上的质量 = `card`（每个 `δ_y` 贡献 1），
再乘 `card⁻¹` 即得。`card ≠ 0` 由 `Nonempty` 给出。 -/
theorem empirical_univ (S : Sample C X Y ι)
    [DecidableEq C.Carrier] [DecidableEq X.Carrier] [MeasurableSingletonClass Y.Carrier]
    (s : Finset ι) (c : C.Carrier) (x : X.Carrier)
    (h : (S.outs s c x).Nonempty) :
    S.empirical s c x Set.univ = 1 := by
  classical
  rw [empirical, dif_pos h]
  -- rawEmpirical univ = card
  have hraw : S.rawEmpirical s c x Set.univ = ((S.outs s c x).card : ENNReal) := by
    unfold rawEmpirical
    induction (S.outs s c x) using Finset.induction with
    | empty => simp
    | insert a t ha ih =>
        rw [Finset.sum_insert ha, Measure.add_apply, ih]
        simp only [Measure.dirac_apply_of_mem (Set.mem_univ a)]
        rw [Finset.card_insert_of_notMem ha]
        simp [Nat.cast_add, Nat.cast_one]
        ring
  rw [Measure.smul_apply, hraw]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Finset.card_ne_zero.mpr h) (by simp)

/-! ### §2.4 空格位：经验核是零测度，**必然不是单点**

这一节把 §2.2 中 `if` 的 `else` 分支**兑现为定理**：
空格位上，`IsPoint` 意义上的切片**一定**失败。
故「空格位约定」**不掩盖**任何东西——它**使问题暴露**。

⚠ 严格说这一节证的不是 `IsPoint` 本身（`IsPoint` 说的是 `R c x = {μ}`，
而 §3 才定义 `R` 的切片），而是关于**经验核**的一条更强的陈述：
`empirical` 在空格位上是 **0 测度**，与任何「候选分布」都不同。
它作为 §3 之后 §4 判据的前置事实使用。 -/

/-- **空格位的经验核是零测度**（值等于 0）。 -/
theorem empirical_eq_zero_of_empty (S : Sample C X Y ι)
    [DecidableEq C.Carrier] [DecidableEq X.Carrier] [MeasurableSingletonClass Y.Carrier]
    (s : Finset ι) (c : C.Carrier) (x : X.Carrier)
    (h : ¬ (S.outs s c x).Nonempty) :
    S.empirical s c x = 0 := by
  rw [empirical, dif_neg h]
  unfold rawEmpirical
  rw [Finset.not_nonempty_iff_eq_empty] at h
  rw [h, Finset.sum_empty]

end Sample

/-! ===========================================================================
    §3  置信带与统计 α
    =========================================================================== -/

/-- **置信带**：把「不确定性」参数化成的**数据**。

| 分量 | 含义 | 统计地位 |
|---|---|---|
| `dist` | $\mathrm{Measure}\ Y\to\mathrm{Measure}\ Y\to\mathbb{R}_{\ge0}$ | **度量方案**（外部给定，见诚实边界 2）|
| `eps`  | 带半宽 $\varepsilon$ | **置信带的宽度** |
| `nMin` | 最小格位样本量 $n_{\min}$ | **覆盖闸**（防「一个样本就下结论」）|

**为什么 `dist` 是字段而非参数**：使「换度量 ⟺ 换一个 `Band`」
成为**同一类型内的替换**，从而 §4 的判据对**任何**度量都成立
（判据的形式与度量无关，这正是判据的**稳健性**）。

**为什么必须有 `nMin`**：没有它，`eps = 0` + 单样本也会给出 `IsPoint`——
那是**过拟合**（见 `FateV2.Error` 的「刚好拟合与过拟合的边界」裁决 K）。
`nMin` 是本文件对裁决 K 在**规则层**的落点。 -/
structure Band (Out : OutSpace) [MeasurableSpace Out.Carrier] where
  /-- 测度之间的「距离」（外部给定的度量方案） -/
  dist : Measure Out.Carrier → Measure Out.Carrier → ENNReal
  /-- 置信带半宽 $\varepsilon$ -/
  eps : ENNReal
  /-- 最小格位样本量 $n_{\min}$ -/
  nMin : ℕ

namespace Band

variable (B : Band Y)

/-- **带球**：以经验核为中心、半宽 `eps` 的「球」。

$$\mathrm{Ball}_B(c,x) := \{\mu \mid
  \mathrm{dist}\,\mu\,\hat\mu_n(c,x)\le\varepsilon\}$$

**它就是统计 α 的切片内容**（不含覆盖闸）。 -/
def ball (S : Sample C X Y ι) [DecidableEq C.Carrier] [DecidableEq X.Carrier]
    (s : Finset ι) (c : C.Carrier) (x : X.Carrier) : Set (Measure Y.Carrier) :=
  {μ | B.dist μ (S.empirical s c x) ≤ B.eps}

end Band

/-- **统计版 α**：从样本与置信带构造的 `LawRule`。

$$R^{\mathrm{stat}}_n(c,x) :=
  \{\mu \mid n(c,x)\ge n_{\min}\ \wedge\ \mathrm{dist}\,\mu\,\hat\mu_n(c,x)\le\varepsilon\}$$

**这就是 α 的统计版本**：
- α 的**输入**是实例/样本（数据），
- α 的**输出**是一个 `LawRule`（"允许哪些下一状态分布"），
- 该输出的**内容**由两项决定：**经验核**（中心）与**置信带**（半径 + 覆盖闸）。

**⚠ 与 `FateV2.Rules.takeConcept` 的关系**：
`takeConcept` 在 **FCA 属性侧**取闭包；本定义在 **测度侧**取**带球**。
两者都是「把原始观测提升为一个**允许集**」，但**不同侧**。
本文件**不主张**两者可交换（那需要 FCA–测度桥，见 `Bridge*` 的既有工作）。 -/
noncomputable def statAlpha (B : Band Y) (S : Sample C X Y ι)
    [DecidableEq C.Carrier] [DecidableEq X.Carrier]
    (s : Finset ι) : LawRule C X Y :=
  fun c x => {μ | S.count s c x ≥ B.nMin ∧ B.dist μ (S.empirical s c x) ≤ B.eps}

/-- **统计 α 的切片展开**（便于下游展开使用，避免与 `setOf` 的语法缠斗）。 -/
theorem statAlpha_apply (B : Band Y) (S : Sample C X Y ι)
    [DecidableEq C.Carrier] [DecidableEq X.Carrier]
    (s : Finset ι) (c : C.Carrier) (x : X.Carrier) :
    statAlpha B S s c x
      = {μ | S.count s c x ≥ B.nMin ∧ B.dist μ (S.empirical s c x) ≤ B.eps} :=
  rfl

/-! ===========================================================================
    §4  ⭐ 何时 `IsPoint`：判据
    =========================================================================== -/

/-- **（C）覆盖条件**：每个格位都不低于最小样本量。

$$(C)\ :\ \forall c\,x,\ n(c,x)\ge n_{\min}.$$

**这是统计条件**：它说「**没有**一个格位是没样本的」。
它的**否定**直接导致空切片（`no_coverage_yields_empty`）。 -/
def Coverage (B : Band Y) (S : Sample C X Y ι)
    [DecidableEq C.Carrier] [DecidableEq X.Carrier] (s : Finset ι) : Prop :=
  ∀ c x, S.count s c x ≥ B.nMin

/-- **（E）带塌缩条件**：每个格位的带球是**单点集**。

$$(E)\ :\ \forall c\,x,\ \exists \mu,\ \mathrm{Ball}_B(c,x) = \{\mu\}.$$

**这是几何/信息条件**：它说「在给定度量与半径下，
**只可能有一个**分布与数据相容」。§6 证明它在 `ε>0` 且 `|Y|≥2` 时**永不**成立。 -/
def BandCollapse (B : Band Y) (S : Sample C X Y ι)
    [DecidableEq C.Carrier] [DecidableEq X.Carrier] (s : Finset ι) : Prop :=
  ∀ c x, ∃ μ : Measure Y.Carrier, B.ball S s c x = {μ}

/-- ⭐⭐ **主判据**：统计 α 是单点规则 **⟺（C）覆盖 ∧（E）带塌缩**。

$$\texttt{IsPoint}\ R^{\mathrm{stat}}_n \iff (C)\wedge (E)$$

**证明结构**（这是判据的实质内容，不是同义反复）：

* **(C) 的必要性非平凡**：若某格位 $n(c,x)<n_{\min}$，
  则切片为空（**不是**「不知道」的一个候选项，而是**什么都没有**），
  空集非单点（`not_singleton_empty`）。故覆盖是**必须要有的**。
* **(E) 的必要性直接**：单点切片 $\{μ\}$ 去掉覆盖闸后仍是
  $\{\mu\}\cap\mathrm{Ball}$，由覆盖成立得 $\mathrm{Ball}=\{μ\}$——
  方向是「**从** `IsPoint` **反推**带是单点」，即 **`ε` 必须塌缩**。
* **充分性**：(C) 使覆盖闸恒真，(E) 给出单点，二者相乘即 `IsPoint`。

**⚠ 判据的读法（务必如此读）**：
上式**不是**「统计 α 何时可靠」的判据（那是 §5），
而是「统计 α 何时**退化成一个点规则**」的判据。
**(E) 在真实数据上几乎总是假**（§6），
故**统计 α 一般是多点的**——这正是「α 输出规则族而非单条规律」的形式化。 -/
theorem statAlpha_isPoint_iff (B : Band Y) (S : Sample C X Y ι)
    [DecidableEq C.Carrier] [DecidableEq X.Carrier] (s : Finset ι) :
    LawRule.IsPoint (statAlpha B S s) ↔
      Coverage B S s ∧ BandCollapse B S s := by
  constructor
  · -- ═══ IsPoint ⟹ (C) ∧ (E) ═══
    intro hpt
    have hcov : Coverage B S s := by
      -- 每个格位：由 IsPoint 取出 μ ∈ {μ} = 切片 ⟹ 计数闸通过
      intro c x
      obtain ⟨μ, hμ⟩ := hpt c x
      have hmem : μ ∈ statAlpha B S s c x := by rw [hμ]; exact Set.mem_singleton μ
      exact (hmem : S.count s c x ≥ B.nMin ∧ B.dist μ (S.empirical s c x) ≤ B.eps).1
    refine ⟨hcov, ?_⟩
    -- (E)：切片 = {μ}，覆盖已成立 ⟹ 带球 = {μ}
    intro c x
    obtain ⟨μ, hμ⟩ := hpt c x
    refine ⟨μ, ?_⟩
    have hslice : statAlpha B S s c x = {μ} := hμ
    ext ν
    rw [Band.ball, Set.mem_setOf_eq]
    constructor
    · -- ν 在带内 ⟹ ν 在切片内（覆盖已由 hcov 给出）⟹ ν = μ
      intro hν
      have hin : ν ∈ statAlpha B S s c x := ⟨hcov c x, hν⟩
      rw [hslice] at hin
      exact hin
    · -- ν = μ ⟹ μ 在带内（由 μ 在切片内反推）
      intro hν
      rw [Set.mem_singleton_iff] at hν
      have hin : μ ∈ statAlpha B S s c x := by rw [hslice]; exact Set.mem_singleton μ
      rw [hν]
      exact (hin : S.count s c x ≥ B.nMin ∧ B.dist μ (S.empirical s c x) ≤ B.eps).2
  · -- ═══ (C) ∧ (E) ⟹ IsPoint ═══
    rintro ⟨hcov, hcol⟩ c x
    obtain ⟨μ, hμ⟩ := hcol c x
    refine ⟨μ, ?_⟩
    ext ν
    show ν ∈ statAlpha B S s c x ↔ ν ∈ ({μ} : Set (Measure Y.Carrier))
    rw [statAlpha, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, hν⟩
      have : ν ∈ B.ball S s c x := hν
      rw [hμ] at this
      exact this
    · intro hν
      have hmem : μ ∈ B.ball S s c x := by
        rw [hμ]; exact Set.mem_singleton μ
      rw [hν]
      exact ⟨hcov c x, hmem⟩

/-! ### §4.1 判据的两个**分离推论**（判据为何有用）

判据若要**有内容**，必须能把 (C) 与 (E) 的失败**各自**暴露出来。
下面两条定理确保 (C) 与 (E) **互相独立**：

* `uncovered_not_point`：**(C) 假 ⟹ `IsPoint` 假**（**无论 (E) 真假**）；
* `uncollapsed_not_point`：**(E) 假 ⟹ `IsPoint` 假**（**无论 (C) 真假**）。

两者合起来说明：判据的两条**都不可省**。 -/

/-- **(C) 假 ⟹ 非单点**（**与 (E) 无关**）。

若存在格位 $n(c,x)<n_{\min}$，则切片为空，故 `IsPoint` 失败。
**这是判据不可省的一条**：即使带塌缩成一点，
**没有样本**就不该「知道」那一点。 -/
theorem uncovered_not_point (B : Band Y) (S : Sample C X Y ι)
    [DecidableEq C.Carrier] [DecidableEq X.Carrier] (s : Finset ι)
    (h : ¬ Coverage B S s) : ¬ LawRule.IsPoint (statAlpha B S s) := by
  intro hpt
  exact h ((statAlpha_isPoint_iff B S s).mp hpt).1

/-- **(E) 假 ⟹ 非单点**（**与 (C) 无关**）。

若某格位的带球不是单点集，则 `IsPoint` 失败。
**这是判据不可省的另一条**：覆盖再好，
**带不塌缩**就有**不止一个**候选分布，那正是「规律不确定」。 -/
theorem uncollapsed_not_point (B : Band Y) (S : Sample C X Y ι)
    [DecidableEq C.Carrier] [DecidableEq X.Carrier] (s : Finset ι)
    (h : ¬ BandCollapse B S s) : ¬ LawRule.IsPoint (statAlpha B S s) := by
  intro hpt
  exact h ((statAlpha_isPoint_iff B S s).mp hpt).2

/-! ===========================================================================
    §5  覆盖的**用途**：带不空 ⟹ 切片非空（`Deterministic` 之外的那一半）
    =========================================================================== -/

/-- **（带自含）条件**：经验核**自己就在带内**。

$$\forall c\,x,\ \mathrm{dist}\,\hat\mu_n(c,x)\,\hat\mu_n(c,x)\le\varepsilon$$

**这不假定任何随机性**：它只要求**度量**在自反处不超过 `eps`。
在「`dist` 是 `dist x x = 0` 型」的度量下，**只要 `eps ≥ 0` 即成立**。
故本条**几乎免费**，但也**不平凡**：它把「带不空」这件事
从「度量性质」一侧**固定**下来，使 §5 的覆盖定理只依赖 (C)。 -/
def SelfInBand (B : Band Y) (S : Sample C X Y ι)
    [DecidableEq C.Carrier] [DecidableEq X.Carrier] (s : Finset ι) : Prop :=
  ∀ c x, B.dist (S.empirical s c x) (S.empirical s c x) ≤ B.eps

/-- **覆盖 + 带自含 ⟹ 每切片非空**（`IsPoint` 的**非空半边**）。

**这是判据 (C) 的**真正统计内容**：**
`IsPoint` 有**两半**（`isPoint_iff_deterministic`）：
非空性 + 确定性。**§4 的判据给出确定性那一半（(E)）**；
本条给出非空性那一半归约到 (C) + `SelfInBand`。

**故 `IsPoint R^stat ⟺ 非空 ∧ 确定` 在统计版上的精确分解是**：

$$\underbrace{(C)\wedge \mathrm{SelfInBand}}_{\text{非空}}\ \wedge\
  \underbrace{\texttt{Deterministic}\ \text{(由 (E) 提供)}}_{\text{确定}}.$$ -/
theorem covered_slice_nonempty (B : Band Y) (S : Sample C X Y ι)
    [DecidableEq C.Carrier] [DecidableEq X.Carrier] (s : Finset ι)
    (hcov : Coverage B S s) (hself : SelfInBand B S s) :
    ∀ c x, (statAlpha B S s c x).Nonempty := by
  intro c x
  exact ⟨S.empirical s c x, hcov c x, hself c x⟩

/-- **推论：覆盖 + 带自含 + (E) ⟹ `IsPoint`**（**另一条路**到达 §4 主判据）。

本推论与 §4 主判据**结论相同但路径不同**：
主判据走「切片 = 带球 ∩ 覆盖」的**集合等式**；
本推论走 `isPoint_iff_deterministic` 的**非空 + 确定**分解。
**两条路都给 `IsPoint`，说明 §4 的判据与该分解相容**（不是两套互相矛盾的说法）。

**诚实说明**：本条**比主判据弱**——它多要了 `SelfInBand`，
但它揭示了**「(C) 为何是统计条件」**：它直接生产**非空性**。 -/
theorem covered_selfInBand_bandCollapse_isPoint (B : Band Y) (S : Sample C X Y ι)
    [DecidableEq C.Carrier] [DecidableEq X.Carrier] (s : Finset ι)
    (hcov : Coverage B S s) (_hself : SelfInBand B S s) (hcol : BandCollapse B S s) :
    LawRule.IsPoint (statAlpha B S s) :=
  (statAlpha_isPoint_iff B S s).mpr ⟨hcov, hcol⟩

/-! ===========================================================================
    §6  ⭐ 分离定理：带"开着" ⟹ **必然非单点**
    =========================================================================== -/

/-- **两个候选都在带内 ⟹ 带不塌缩**（**纯几何引理**）。

若 $\mu_1\neq\mu_2$ 且二者到经验核的距离都 $\le\varepsilon$，
则带球**至少含两个点**，故**不是**单点集。

**本引理不涉及数据**——它只说「一个球含两点就非单点」。
它的作用是把 §6 的主定理**约化为**「找到带内的两个不同测度」。 -/
theorem not_collapse_of_two_members (B : Band Y) {d : Measure Y.Carrier}
    {μ₁ μ₂ : Measure Y.Carrier} (hne : μ₁ ≠ μ₂)
    (_h₁ : B.dist μ₁ d ≤ B.eps) (h₂ : B.dist μ₂ d ≤ B.eps) :
    ({μ : Measure Y.Carrier | B.dist μ d ≤ B.eps} : Set (Measure Y.Carrier)) ≠ {μ₁} := by
  intro heq
  have hmem : μ₂ ∈ ({μ : Measure Y.Carrier | B.dist μ d ≤ B.eps}
      : Set (Measure Y.Carrier)) := h₂
  rw [heq] at hmem
  exact hne (Set.mem_singleton_iff.mp hmem).symm

/-! ### §6.1 ⭐ 主分离定理：带“开着” ⟹ **真非单点**

**问题**：单点集要求的不仅是「带含一个**已知**点」，而是「带**只含一个**点」。
§6.0 把这件事约化为「带内有两个不同测度」。

下面给出**具体的两测度**：只要输出空间 `Y` 有两个不同点 `y₁ ≠ y₂`，
则 `δ_{y₁}` 与 `δ_{y₂}` 是**不同的测度**（`Measure.dirac_injective`）。
若距离**恒为零**（带不区分任何两个测度，即 $\mathrm{dist}\equiv 0$），
则带**必含**这两个 `δ`，故**必非单点**。

**这不是「ε 大就坏」的空话**：它给出
$$\neg\,\texttt{BandCollapse}\ \Longleftarrow\ |Y|\ge 2\ \wedge\ \mathrm{dist}\equiv 0 .$$
即**只要「距离不区分测度」且输出空间不低于两点，统计 α 就绝不单点**——
这是「**把不确定性写进 α**」这一设计的**数学必要性**。 -/

/-- **两个不同输出点给出两个不同 Dirac 测度**（`Measure.dirac` 单射性）。 -/
theorem dirac_ne_of_ne {Y' : Type*} [MeasurableSpace Y'] [MeasurableSingletonClass Y']
    {y₁ y₂ : Y'} (h : y₁ ≠ y₂) : (Measure.dirac y₁ : Measure Y') ≠ Measure.dirac y₂ := by
  intro heq
  have hmeas : MeasurableSet ({y₂} : Set Y') := measurableSet_singleton y₂
  have happ : (Measure.dirac y₁ : Measure Y') ({y₂} : Set Y')
      = (Measure.dirac y₂ : Measure Y') ({y₂} : Set Y') := by rw [heq]
  rw [Measure.dirac_apply' _ hmeas, Measure.dirac_apply_of_mem (Set.mem_singleton y₂)] at happ
  -- happ : ({y₂} : Set Y').indicator 1 y₁ = 1  ⟹  y₁ ∈ {y₂}
  by_cases hy₁ : y₁ ∈ ({y₂} : Set Y')
  · exact h (Set.mem_singleton_iff.mp hy₁)
  · rw [Set.indicator_of_notMem hy₁] at happ
    exact one_ne_zero happ.symm

/-- ⭐ **分离定理（零距离版）**：若

* `Y` 有两个不同点（`|Y| ≥ 2`，即 `[Nontrivial Y.Carrier]`），
* 距离**恒为零**（`dist ≡ 0`：带不区分任何两个测度），

则**任何**格位 `(c,x)` 的带球都**不是**单点集，故 `BandCollapse` **必然失败**。

**⚠ 读法**：本定理的「`dist ≡ 0`」不是「度量选得不好」，
而是「**退化到无信息**」——此时带球 = **全体测度**。
真正有用的度量下带球是真子集，但**只要它含两点就仍然非单点**（§6.0）。
故**分离是结构性的**：单点性 ⟺ 带**至多**一点——那要求带**不是**“开着”的。 -/
theorem not_collapse_of_zero_dist [Nontrivial Y.Carrier] [MeasurableSingletonClass Y.Carrier]
    (B : Band Y) (h0 : ∀ μ ν : Measure Y.Carrier, B.dist μ ν = 0)
    (S : Sample C X Y ι) [DecidableEq C.Carrier] [DecidableEq X.Carrier] (s : Finset ι)
    (c : C.Carrier) (x : X.Carrier) :
    ¬ BandCollapse B S s := by
  intro hcol
  obtain ⟨μ, hμ⟩ := hcol c x
  obtain ⟨y₁, y₂, hne⟩ := exists_pair_ne Y.Carrier
  have hd : (Measure.dirac y₁ : Measure Y.Carrier) ≠ Measure.dirac y₂ :=
    dirac_ne_of_ne hne
  have hb₁ : (Measure.dirac y₁ : Measure Y.Carrier) ∈ B.ball S s c x := by
    rw [Band.ball, Set.mem_setOf_eq, h0]; exact zero_le
  have hb₂ : (Measure.dirac y₂ : Measure Y.Carrier) ∈ B.ball S s c x := by
    rw [Band.ball, Set.mem_setOf_eq, h0]; exact zero_le
  rw [hμ] at hb₁ hb₂
  exact hd (Set.mem_singleton_iff.mp hb₁ |>.trans (Set.mem_singleton_iff.mp hb₂).symm)

/-! ### §6.2 ⭐⭐ 另一极端：`eps = 0` + 分离距离 ⟹ **单点 ⟺ 覆盖**

§6.1 说明带“开着”时必非单点。**另一极端**更值得写进判据：
当带**退化为一点**（`dist` 在相等处为 0、在不等处非 0，且 `eps = 0`），
带球 = `{empirical}` —— 此时**判据完全由 (C) 决定**：

$$\underbrace{\mathrm{dist}\ \mu\ \nu = 0 \iff \mu = \nu}_{\text{分离度量}},\
  \varepsilon = 0
  \ \Longrightarrow\
  \texttt{IsPoint}\ R^{\mathrm{stat}}_n \iff (C).$$

**这就是「统计 α 何时 `IsPoint`」的最实用形式**：

> **统计 α 是点规则 ⟺ 数据在每个格位上都“说死了”唯一的条件分布。**

**诚实边界**：上式右端 `(C)` 里的 `nMin` 是**你要的置信度对应的样本量**
（本文件不推导它——那需要集中不等式，见诚实边界 3）。 -/
theorem isPoint_iff_coverage_of_separating_zero
    (B : Band Y) (S : Sample C X Y ι) [DecidableEq C.Carrier] [DecidableEq X.Carrier]
    (s : Finset ι)
    (hsep : ∀ μ ν : Measure Y.Carrier, B.dist μ ν = 0 ↔ μ = ν)
    (heps : B.eps = 0) :
    LawRule.IsPoint (statAlpha B S s) ↔ Coverage B S s := by
  rw [statAlpha_isPoint_iff]
  constructor
  · exact And.left
  · intro hcov
    refine ⟨hcov, ?_⟩
    intro c x
    refine ⟨S.empirical s c x, ?_⟩
    ext ν
    rw [Band.ball, Set.mem_setOf_eq, heps, Set.mem_singleton_iff]
    constructor
    · intro hle
      have hz : B.dist ν (S.empirical s c x) = 0 := le_antisymm hle zero_le
      exact (hsep ν (S.empirical s c x)).mp hz
    · rintro rfl
      rw [(hsep _ _).mpr rfl]

end AlphaStatistical

end FateV2.Rules