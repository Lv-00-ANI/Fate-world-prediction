import FateWorld.Legacy.KernelQuotientExtra

/-! ===========================================================================
  §16  ⭐⭐ **三种等价层级**：`∼_cf ⊆ ∼_int ⊆ ∼_obs`（原 `_probe_q13` 的正式化）

  **来源**：探针 `probes/_probe_q13.lean`（**不在构建内**）。
  本节把它**正式化**为 `Fate/` 的一等公民。

  ## 问题的来源

  「反事实的中间等价地带」是否有一个**具体的、可定义的**中项？

  ## ⭐ 答案：有 —— **干预分布等价** `∼_int`

  $$\sim_{\text{cf}} \ \subseteq\ \sim_{\text{int}} \ \subseteq\ \sim_{\text{obs}}$$

  | 等价 | 泛函 | 层级 |
  |---|---|---|
  | **`∼_obs`** | 观测分布 $P(V)$ | **L1 关联**（最粗）|
  | **`∼_int`** | **一切干预下的分布族** | **L2 干预**（中项）|
  | **`∼_cf`** | 逐个体反事实响应 | **L3 反事实**（最细）|

  **⟹ 即**：**`∼_int` 就是那个「中间地带」的具体见证** ——
  它**不是**抽象的「既非常值又非单射」，而是**有确切定义**的等价关系。

  ## 结构假设（把三者连成链）

  | 假设 | 内容 |
  |---|---|
  | **(H1)** | 干预分布是反事实的函数（边缘化）|
  | **(H2)** | 观测分布 = 某指定干预（「空干预」）下的干预分布 |

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate

namespace EquivalenceLevels

universe u v w

/-! ### §16.1 三个泛函（皆为「核」） -/

/-- **观测分布泛函**：`SCM → P(V)`。 -/
abbrev ObsFun (SCM ObsDist : Type*) : Type _ := SCM → ObsDist

/-- **干预分布泛函**：`SCM → (干预指标 → 该干预下的分布)`。

**⚠ `Int` 是干预指标集** —— 本节不指定其内部结构，只当类型用。 -/
abbrev IntFun (SCM Int IntDist : Type*) : Type _ := SCM → Int → IntDist

/-- **反事实响应泛函**：`SCM → 逐个体逐干预的响应`。 -/
abbrev CfFun (SCM Cf : Type*) : Type _ := SCM → Cf

/-! ### §16.2 三个等价关系（都是核） -/

/-- **观测等价 `∼_obs`**（L1）：诱导同一观测分布。 -/
def ObsEquiv {SCM ObsDist : Type*} (obsDist : ObsFun SCM ObsDist) (s t : SCM) : Prop :=
  obsDist s = obsDist t

/-- ⭐ **干预分布等价 `∼_int`**（L2，**本节的中间项**）：
对**每个**干预，分布相同。 -/
def IntEquiv {SCM Int IntDist : Type*} (intDist : IntFun SCM Int IntDist) (s t : SCM) : Prop :=
  ∀ i : Int, intDist s i = intDist t i

/-- **反事实等价 `∼_cf`**（L3）：逐个体逐干预响应相同。 -/
def CfEquiv {SCM Cf : Type*} (cfObs : CfFun SCM Cf) (s t : SCM) : Prop :=
  cfObs s = cfObs t

/-! ### §16.3 三者都是等价关系 -/

theorem obsEquiv_refl {SCM ObsDist : Type*} (obsDist : ObsFun SCM ObsDist) (s : SCM) :
    ObsEquiv obsDist s s := rfl

theorem obsEquiv_symm {SCM ObsDist : Type*} {obsDist : ObsFun SCM ObsDist} {s t : SCM}
    (h : ObsEquiv obsDist s t) : ObsEquiv obsDist t s := h.symm

theorem obsEquiv_trans {SCM ObsDist : Type*} {obsDist : ObsFun SCM ObsDist} {s t u : SCM}
    (h₁ : ObsEquiv obsDist s t) (h₂ : ObsEquiv obsDist t u) : ObsEquiv obsDist s u :=
  h₁.trans h₂

theorem intEquiv_refl {SCM Int IntDist : Type*} (intDist : IntFun SCM Int IntDist) (s : SCM) :
    IntEquiv intDist s s := fun _ => rfl

theorem intEquiv_symm {SCM Int IntDist : Type*} {intDist : IntFun SCM Int IntDist} {s t : SCM}
    (h : IntEquiv intDist s t) : IntEquiv intDist t s := fun i => (h i).symm

theorem intEquiv_trans {SCM Int IntDist : Type*} {intDist : IntFun SCM Int IntDist} {s t u : SCM}
    (h₁ : IntEquiv intDist s t) (h₂ : IntEquiv intDist t u) : IntEquiv intDist s u :=
  fun i => (h₁ i).trans (h₂ i)

theorem cfEquiv_refl {SCM Cf : Type*} (cfObs : CfFun SCM Cf) (s : SCM) :
    CfEquiv cfObs s s := rfl

theorem cfEquiv_symm {SCM Cf : Type*} {cfObs : CfFun SCM Cf} {s t : SCM}
    (h : CfEquiv cfObs s t) : CfEquiv cfObs t s := h.symm

theorem cfEquiv_trans {SCM Cf : Type*} {cfObs : CfFun SCM Cf} {s t u : SCM}
    (h₁ : CfEquiv cfObs s t) (h₂ : CfEquiv cfObs t u) : CfEquiv cfObs s u :=
  h₁.trans h₂

/-! ### §16.4 ⭐⭐ 主定理：夹逼 -/

/-- ⭐ **左半边**：`∼_cf ⊆ ∼_int`（**反事实决定干预分布**）。

**抽象刻画**：若存在 `cfToInt` 使 `intDist s = cfToInt (cfObs s)`（即**干预分布是反事实的函数**），
则反事实相同 ⟹ 干预分布相同。 -/
theorem cf_subset_int {SCM Int IntDist Cf : Type*}
    {intDist : IntFun SCM Int IntDist} {cfObs : CfFun SCM Cf}
    (cfToInt : Cf → Int → IntDist) (hcfInt : ∀ s, intDist s = cfToInt (cfObs s))
    {s t : SCM} (h : CfEquiv cfObs s t) : IntEquiv intDist s t := by
  intro i
  rw [hcfInt s, hcfInt t, h]

/-- ⭐ **右半边**：`∼_int ⊆ ∼_obs`（**观测是干预的特例**）。

**抽象刻画**：若存在 `intToObs` 与 `i₀`（「空干预」）
使 `intToObs (intDist s i₀) = obsDist s`，则干预分布相同 ⟹ 观测分布相同。 -/
theorem int_subset_obs {SCM ObsDist Int IntDist : Type*}
    {obsDist : ObsFun SCM ObsDist} {intDist : IntFun SCM Int IntDist}
    (intToObs : IntDist → ObsDist)
    (i₀ : Int) (hobs : ∀ s : SCM, intToObs (intDist s i₀) = obsDist s)
    {s t : SCM} (h : IntEquiv intDist s t) : ObsEquiv obsDist s t := by
  show obsDist s = obsDist t
  rw [← hobs s, ← hobs t, h i₀]

/-- ⭐⭐ **主定理（夹逼）**：`∼_cf ⊆ ∼_int ⊆ ∼_obs`。

**⟹ 即**：**「反事实的中间等价地带」有一个具体的、可定义的中项 `∼_int`** ——
它**不是**抽象的「既非常值又非单射」，而是**干预分布等价**。

**证明仅用两条结构事实**：
1. **干预分布是反事实的函数**（`hcfInt`）
2. **观测 = 空干预**（`hobs`） -/
theorem cf_le_int_le_obs {SCM ObsDist Int IntDist Cf : Type*}
    {obsDist : ObsFun SCM ObsDist} {intDist : IntFun SCM Int IntDist} {cfObs : CfFun SCM Cf}
    (cfToInt : Cf → Int → IntDist) (hcfInt : ∀ s, intDist s = cfToInt (cfObs s))
    (intToObs : IntDist → ObsDist)
    (i₀ : Int) (hobs : ∀ s : SCM, intToObs (intDist s i₀) = obsDist s)
    {s t : SCM} (h : CfEquiv cfObs s t) : ObsEquiv obsDist s t :=
  int_subset_obs intToObs i₀ hobs (cf_subset_int cfToInt hcfInt h)

/-! ### §16.5 严格性（把 `⊆` 升级为 `⊊`） -/

/-- **左侧严格的形态**：存在 `s t` 使 `∼_int` 但**非** `∼_cf`。

**具体见证**：`Fate/CounterfactualStrictness.lean` 的 `tag` 反例
（分布层对齐、逐个体层不对齐）。 -/
def IntStrictlyFinerThanCf {SCM Int IntDist Cf : Type*}
    (intDist : IntFun SCM Int IntDist) (cfObs : CfFun SCM Cf) : Prop :=
  ∃ s t : SCM, IntEquiv intDist s t ∧ ¬ CfEquiv cfObs s t

/-- **右侧严格的形态**：存在 `s t` 使 `∼_obs` 但**非** `∼_int`。

**具体见证**：马尔可夫等价类非单值（观测定不到方向）。 -/
def ObsStrictlyCoarserThanInt {SCM ObsDist Int IntDist : Type*}
    (obsDist : ObsFun SCM ObsDist) (intDist : IntFun SCM Int IntDist) : Prop :=
  ∃ s t : SCM, ObsEquiv obsDist s t ∧ ¬ IntEquiv intDist s t

/-- **两侧严格 ⟹ 三明治严格**。

**⚠ 诚实标注**：本定理只是把两个假设**合并陈述**；
它**不产生**具体见证 —— 见证由 `CounterfactualStrictness` 与马尔可夫等价类提供。 -/
theorem sandwich_strict {SCM ObsDist Int IntDist Cf : Type*}
    {obsDist : ObsFun SCM ObsDist} {intDist : IntFun SCM Int IntDist} {cfObs : CfFun SCM Cf}
    (hl : IntStrictlyFinerThanCf intDist cfObs)
    (hr : ObsStrictlyCoarserThanInt obsDist intDist) :
    (∃ s t : SCM, ObsEquiv obsDist s t ∧ ¬ IntEquiv intDist s t) ∧
      (∃ s t : SCM, IntEquiv intDist s t ∧ ¬ CfEquiv cfObs s t) :=
  ⟨hr, hl⟩

/-! ### §16.6 ⭐ 与统一框架的关系 -/

/-- ⭐⭐ **三个等价都是核**（统一框架的实例）。

$$\sim_{\text{obs}} = \ker(\text{obsDist}),\quad
  \sim_{\text{int}} = \ker(\text{intDist}),\quad
  \sim_{\text{cf}} = \ker(\text{cfObs})$$

**⟹ 即**：本节的三种层级**不是孤立构造** ——
它们都是 `KernelQuotientTheory` 中「核」的实例，
故**直接继承**一般理论的定理（第一同构、最优性等）。 -/
theorem three_levels_are_kernels {SCM ObsDist Int IntDist Cf : Type*}
    (obsDist : ObsFun SCM ObsDist) (intDist : IntFun SCM Int IntDist) (cfObs : CfFun SCM Cf) :
    (∀ s t, ObsEquiv obsDist s t ↔ (obsDist s = obsDist t)) ∧
      (∀ s t, IntEquiv intDist s t ↔ (intDist s = intDist t)) ∧
      (∀ s t, CfEquiv cfObs s t ↔ (cfObs s = cfObs t)) :=
  ⟨fun _ _ => Iff.rfl,
   fun _ _ => ⟨fun h => funext h, fun h i => congrFun h i⟩,
   fun _ _ => Iff.rfl⟩

end EquivalenceLevels

end Fate
