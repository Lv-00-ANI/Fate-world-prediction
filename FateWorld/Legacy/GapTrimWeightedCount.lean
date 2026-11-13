import FateWorld.Legacy.BridgeKernel

/-! ===========================================================================
  §99  ⭐⭐⭐⭐ **缺口 A：`trim` 与 `weightedCount` 的对接**

  ## ⚠⚠ 先说结论（数学审查）

  被要求证明的命题

  ```
  (weightedCount p).trim ... {ω} = (weightedCount p) {ω}
  ```

  **在一般情形下是假的**。原因恰恰是任务提示里指出的那一点：

  > `{ω}` 是**单点**，而 `trim` 只在 `m'`-可测集上等于原测度。
  > 单点 `{ω}` **不一定** `m'`-可测（`m' = comap projZ`）。

  **⟹ **`{ω}` 不是 `m'`-可测 ⟹ `trim {ω} = μ {ω}`` 完全可能失效**。

  ### 反例（本文件已形式化，见 §99.7）

  取 `α = β = γ = Unit` 之外最简单的退化情形
  `α = Bool, β = Unit, γ = Unit`，`p ≡ 1`（即良构性无关，纯测度计算）：

  * `projZ` 是常函数（`γ = Unit`）⟹ `m' = comap projZ = ⊥`（**平凡 σ-代数**）；
  * `m'` 下方的可测集只有 `∅` 与 `univ` ⟹ **任何单点都不是 `m'`-可测**；
  * `(weightedCount p) {ω} = ofReal 1 = 1`；
  * `(weightedCount p).trim {ω} = (weightedCount p) (fiber ()) = (weightedCount p) univ = 2`。

  **⟹ `1 ≠ 2`，命题为假。**

  ⭐ 这个反例还给出了**正确的值**：`trim` 把单点 `{ω}` 送成它的
  **整个 `projZ`-纤维**的质量 `μ (fiber ω.2)`。

  ## ⭐⭐⭐⭐ 正确的形式（本文件已证，**无 `sorry`**）

  | 定理 | 内容 |
  |---|---|
  | `fiber_subset_of_measurable` | `m'`-可测 `t` 含 `ω` ⟹ `fiber ω.2 ⊆ t`（**纤维饱和**）|
  | `singleton_measurable_iff` | `{ω}` `m'`-可测 **⟺** `fiber ω.2 = {ω}` |
  | ⭐ `trim_singleton_eq_fiber` | **`μ.trim hm {ω} = μ (fiber ω.2)`**（**主定理**）|
  | `trim_singleton_eq_of_measurable` | **`{ω}` `m'`-可测 ⟹ 原命题成立**（补齐缺失假设的正确版本）|
  | `trim_fiber_eq` | `μ.trim hm (fiber c) = μ (fiber c)`（纤维版，**恒成立**）|
  | `trim_singleton_ne_zero_iff` | `μ.trim hm {ω} ≠ 0 ↔ μ (fiber ω.2) ≠ 0` |
  | `trim_singleton_nonzero_of_ne_zero` | `μ {ω} ≠ 0 → μ.trim hm {ω} ≠ 0`（`le_trim` 推论）|
  | `weightedCount_trim_singleton` | `(weightedCount p).trim {ω} = ∑x∑y ofReal (p ((x,y),ω.2))` |
  | `weightedCount_trim_singleton_ne_zero_iff` | `… ≠ 0 ↔ margZ p ω.2 ≠ 0` |
  | `weightedCount_trim_singleton_counterexample` | **原命题的反例（形式化）** |

  ## ⚠ 一个技术前提

  任务给的假设里有 `[MeasurableSingletonClass ((α × β) × γ)]`，
  **但它推不出 `[MeasurableSingletonClass γ]`**（**实测**：`fiber c` 的可测性需要后者）。
  **故本文件的定理一律显式要求 `[MeasurableSingletonClass γ]`** ——
  这是**数学上必需**的（`γ` 的单点必须可测，`fiber c` 才是 `projZ`-原像的可测集）。
  在 `Fate/_step11_Z3.lean` 的上下文里它由 `[DiscreteMeasurableSpace γ]` 提供。
  =========================================================================== -/

namespace Fate

namespace GapTrimWeightedCount

open MeasureTheory ProbabilityTheory
open scoped Classical

universe u

variable {α β γ : Type u}

/-! ### §99.1 基本信息：`projZ` 与 `fiber` -/

/-- **`m'`-可测 ⟹ 纤维饱和**：任何 `m'`-可测集合含 `ω` 就含整个 `fiber ω.2`。

**⚠ 这是「单点不是 `m'`-可测」的定量版本** ——
**因为 `m'`-可测集是纤维的并，故它要么含整个纤维，要么完全不含 `ω`。** -/
theorem fiber_subset_of_measurable [MeasurableSpace γ] {t : Set ((α × β) × γ)}
    (ht : MeasurableSet[MeasurableSpace.comap
      (FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance] t)
    {ω : (α × β) × γ} (hω : ω ∈ t) :
    FinMeasureBridge.fiber ω.2 ⊆ t := by
  obtain ⟨S, _hS, rfl⟩ := MeasurableSpace.measurableSet_comap.mp ht
  intro w hw
  have h1 : ω.2 ∈ S := hω
  show w.2 ∈ S
  rw [show w.2 = ω.2 from hw]
  exact h1

/-- **`fiber c` 是 `m'`-可测的**（它是 `{c}` 在 `projZ` 下的原像）。

**⚠ 需要 `[MeasurableSingletonClass γ]`** —— `α`、`β` 上的单点可测性**不需要**。 -/
theorem fiber_measurable [MeasurableSpace γ] [MeasurableSingletonClass γ] (c : γ) :
    MeasurableSet[MeasurableSpace.comap
      (FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance]
      (FinMeasureBridge.fiber c) := by
  rw [FinMeasureBridge.fiber]
  exact MeasurableSpace.measurableSet_comap.mpr ⟨{c}, measurableSet_singleton c, rfl⟩

/-! ### §99.2 ⭐⭐⭐ **单点何时 `m'`-可测**（**精确判据**） -/

/-- ⭐⭐⭐ **`{ω}` 是 `m'`-可测 ⟺ 它的纤维恰是单点。**

**⟹ 即**：单点 `m'`-可测**只**发生在「纤维本来就退化为一点」的**退化情形**。
**一般情形下 `{ω}` **不是** `m'`-可测** ——
**这正是原命题失效的根源。** -/
theorem singleton_measurable_iff [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ] (ω : (α × β) × γ) :
    MeasurableSet[MeasurableSpace.comap
      (FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance]
      ({ω} : Set ((α × β) × γ)) ↔ FinMeasureBridge.fiber ω.2 = {ω} := by
  constructor
  · intro h
    refine Set.Subset.antisymm (fiber_subset_of_measurable h (Set.mem_singleton ω)) ?_
    intro w hw
    have hw' : w = ω := hw
    subst hw'
    rfl
  · intro h
    have hm := fiber_measurable (α := α) (β := β) ω.2
    rwa [h] at hm

/-! ### §99.3 ⭐⭐⭐⭐ **主定理：`trim` 在单点上 = 纤维质量** -/

/-- ⭐⭐⭐⭐ **`trim` 作用在单点上 = 该点所在纤维的质量**（**主定理**）。

$$\bigl(\mu.\mathrm{trim}\ h_{m'}\bigr)\bigl(\{\omega\}\bigr) = \mu\bigl(\text{fiber}\ \omega_2\bigr)$$

**⚠ 为什么不是 `μ {ω}`**：`trim` 是 `μ` 在 `m'` 上的「**纤维化**」——
它把每个 `m'`-原子（= 一个纤维）的**总质量**赋给该纤维。
**单点 `{ω}` 不是 `m'`-可测 ⟹ `trim` 只能把它「撑」到整个纤维**，
**这是 `Measure.trim` 的 `⨅`-定义（对 `m'`-可测覆盖取下确界）的直接后果。**

**⚠ 证明思路（两条不等式）**：
* `≤`：`{ω} ⊆ fiber ω.2`，且 `fiber ω.2` 是 `m'`-可测的
  ⟹ `trim {ω} ≤ trim (fiber ω.2) = μ (fiber ω.2)`（`trim_measurableSet_eq`）。
* `≥`：`(μ.trim hm) {ω} = OuterMeasure.trim μ.toOuterMeasure {ω}`
  （`toOuterMeasure_trim_eq_trim_toOuterMeasure`），
  而 `OuterMeasure.trim s = ⨅ over m'-measurable supersets t ⊇ s of μ t`
  （`OuterMeasure.trim_eq_iInf`）；
  每个这样的 `t ⊇ {ω}` 都纤维饱和 ⟹ `t ⊇ fiber ω.2` ⟹ `μ t ≥ μ (fiber ω.2)`。
  **⟹ 下确界 ≥ `μ (fiber ω.2)`。**

**⚠ 技术要点（实测）**：`toOuterMeasure_trim_eq_trim_toOuterMeasure` 与
`OuterMeasure.trim_eq_iInf` 的 `MeasurableSpace` 是**隐式类型类参数**，
**在 `trim` 改变了 σ-代数时会实例不匹配** ⟹
⭐ **须用 `@` 显式给出 `m'` 作为该实例**（见下面的 `hexp`）。 -/
theorem trim_singleton_eq_fiber [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure ((α × β) × γ)) (ω : (α × β) × γ) :
    μ.trim (MeasurableSpace.comap_le_iff_le_map.mpr
      (FinCondIndepMeasure.measurable_projZ (α := α) (β := β) (γ := γ))) {ω}
      = μ (FinMeasureBridge.fiber ω.2) := by
  obtain hm : MeasurableSpace.comap
        (FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance
      ≤ (inferInstance : MeasurableSpace ((α × β) × γ)) :=
    MeasurableSpace.comap_le_iff_le_map.mpr FinCondIndepMeasure.measurable_projZ
  refine le_antisymm ?_ ?_
  · calc (μ.trim hm) {ω}
        ≤ (μ.trim hm) (FinMeasureBridge.fiber ω.2) := by
          refine measure_mono ?_
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          subst hw
          rfl
      _ = μ (FinMeasureBridge.fiber ω.2) :=
          trim_measurableSet_eq hm (fiber_measurable ω.2)
  · -- 下界：`(μ.trim hm) {ω} = OuterMeasure.trim μ.toOuterMeasure {ω}`，再取 `⨅`
    have hkey : (μ.trim hm) {ω} = @OuterMeasure.trim ((α × β) × γ)
        (MeasurableSpace.comap
          (FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)
        μ.toOuterMeasure {ω} := by
      have h1 := toOuterMeasure_trim_eq_trim_toOuterMeasure μ hm
      have h2 : (@Measure.toOuterMeasure _ (MeasurableSpace.comap
            (FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)
          (μ.trim hm)) {ω} = (μ.trim hm) {ω} := rfl
      rw [← h2, h1]
    have hexp : @OuterMeasure.trim ((α × β) × γ)
        (MeasurableSpace.comap
          (FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)
        μ.toOuterMeasure {ω}
        = ⨅ (t : Set ((α × β) × γ)), ⨅ (_ : {ω} ⊆ t),
            ⨅ (_ : MeasurableSet[MeasurableSpace.comap
              (FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance] t), μ t :=
      @OuterMeasure.trim_eq_iInf _ (MeasurableSpace.comap
        (FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance) μ.toOuterMeasure {ω}
    rw [hkey, hexp]
    refine le_iInf fun t => le_iInf fun hsub => le_iInf fun ht => ?_
    exact measure_mono (fiber_subset_of_measurable ht (hsub (Set.mem_singleton_iff.mpr rfl)))

/-! ### §99.4 ⭐⭐⭐ **补齐假设后的正确版本 + 纤维版** -/

/-- ⭐⭐⭐ **原命题的**正确版本**：`{ω}` 是 `m'`-可测时，`trim` 不变。**

**⚠ 这就是任务命题真正需要的假设** ——
**而由 `singleton_measurable_iff`，它等价于 `fiber ω.2 = {ω}`（纤维退化）。** -/
theorem trim_singleton_eq_of_measurable [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure ((α × β) × γ)) (ω : (α × β) × γ)
    (hω : MeasurableSet[MeasurableSpace.comap
      (FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance]
      ({ω} : Set ((α × β) × γ))) :
    μ.trim (MeasurableSpace.comap_le_iff_le_map.mpr
      (FinCondIndepMeasure.measurable_projZ (α := α) (β := β) (γ := γ))) {ω}
      = μ {ω} :=
  trim_measurableSet_eq _ hω

/-- ⭐⭐⭐ **`trim` 在纤维上 = 原测度**（**纤维版，恒成立，无需额外假设**）。

**⟹ 即**：**`trim` 真正保持不变的是纤维** ——
**这是「`trim` 与 `weightedCount` 对接」的正确接口**，
**而 `trim_singleton_eq_fiber` 就是它的「单点包装」。** -/
theorem trim_fiber_eq [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure ((α × β) × γ)) (c : γ) :
    μ.trim (MeasurableSpace.comap_le_iff_le_map.mpr
      (FinCondIndepMeasure.measurable_projZ (α := α) (β := β) (γ := γ)))
      (FinMeasureBridge.fiber c)
      = μ (FinMeasureBridge.fiber c) :=
  trim_measurableSet_eq _ (fiber_measurable c)

/-- ⭐⭐⭐ **`trim` 在单点上的零性判据**。

$$\bigl(\mu.\mathrm{trim}\ h\bigr)\bigl(\{\omega\}\bigr) \ne 0
  \iff \mu\bigl(\text{fiber}\ \omega_2\bigr) \ne 0$$

**⚠ 这是任务里建议的「`≠ 0` 版本」的**精确形式**** ——
**注意右端是**纤维**质量，而不是单点质量。** -/
theorem trim_singleton_ne_zero_iff [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure ((α × β) × γ)) (ω : (α × β) × γ) :
    μ.trim (MeasurableSpace.comap_le_iff_le_map.mpr
      (FinCondIndepMeasure.measurable_projZ (α := α) (β := β) (γ := γ))) {ω} ≠ 0
      ↔ μ (FinMeasureBridge.fiber ω.2) ≠ 0 := by
  rw [trim_singleton_eq_fiber]

/-- ⭐⭐⭐ **单点质量非零 ⟹ `trim` 非零**（`le_trim` 的直接推论）。

**⚠ 方向的澄清（本任务中我的第一版写反了，此处如实登记）**：
`le_trim : μ s ≤ (μ.trim hm) s`，故由 `μ {ω} ≠ 0` 可得 `(μ.trim hm) {ω} ≠ 0`；
**反之不成立**（`μ {ω} = 0` 时 `trim` 完全可能非零 —— 见 §99.7 的反例：
那里 `μ {((false,()),())} = 1 ≠ 0` 但纤维质量是 2）。

**⚠ 本定理无需 `MeasurableSingletonClass γ`**（只用 `le_trim`）。 -/
theorem trim_singleton_nonzero_of_ne_zero [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ]
    (μ : Measure ((α × β) × γ)) (ω : (α × β) × γ) :
    μ {ω} ≠ 0
      → μ.trim (MeasurableSpace.comap_le_iff_le_map.mpr
          (FinCondIndepMeasure.measurable_projZ (α := α) (β := β) (γ := γ))) {ω} ≠ 0 := by
  intro h h0
  exact h (le_antisymm (h0 ▸ MeasureTheory.le_trim _) bot_le)

/-! ### §99.5 ⭐⭐⭐⭐⭐ **`weightedCount` 的专门版本** -/

/-- ⭐⭐⭐⭐ **`(weightedCount p).trim` 在单点上 = 该纤维的系数和。**

$$\bigl(\mathrm{weightedCount}\ p\bigr).\mathrm{trim}\ h\ \{\omega\}
  = \sum_{x,y}\ \mathrm{ofReal}\bigl(p((x,y),\omega_2)\bigr)$$

**⟹ 这是把 `trim` 与 `weightedCount` 的**显式值**（`weightedCount_fiber`）接起来的结果。** -/
theorem weightedCount_trim_singleton [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)] [MeasurableSingletonClass γ]
    (p : FiniteCondIndep.FinJoint α β γ) (ω : (α × β) × γ) :
    letI : IsFiniteMeasure (FinMeasureBridge.weightedCount p) :=
      FinMeasureBridge.weightedCount_isFiniteMeasure p
    (FinMeasureBridge.weightedCount p).trim
      (MeasurableSpace.comap_le_iff_le_map.mpr FinCondIndepMeasure.measurable_projZ) {ω}
      = ∑ x : α, ∑ y : β, ENNReal.ofReal (p ((x, y), ω.2)) := by
  letI : IsFiniteMeasure (FinMeasureBridge.weightedCount p) :=
    FinMeasureBridge.weightedCount_isFiniteMeasure p
  rw [trim_singleton_eq_fiber]
  exact FinMeasureBridge.weightedCount_fiber p ω.2

/-- ⭐⭐⭐ **`trim` 在单点上非零 ⟺ `margZ` 在 `ω.2` 处非零**（纯代数判据）。

**⚠ 需要 `hp : ∀ a, 0 ≤ p a`**（非负性）——
**否则 `ofReal` 会把负数折成 0，判据失效**（见 `FinMeasureBridge.fiber_ne_zero_iff` 的说明）。 -/
theorem weightedCount_trim_singleton_ne_zero_iff [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)] [MeasurableSingletonClass γ]
    (p : FiniteCondIndep.FinJoint α β γ) (hp : ∀ a, 0 ≤ p a)
    (ω : (α × β) × γ) :
    letI : IsFiniteMeasure (FinMeasureBridge.weightedCount p) :=
      FinMeasureBridge.weightedCount_isFiniteMeasure p
    (FinMeasureBridge.weightedCount p).trim
      (MeasurableSpace.comap_le_iff_le_map.mpr FinCondIndepMeasure.measurable_projZ) {ω} ≠ 0
      ↔ (∑ x : α, ∑ y : β, p ((x, y), ω.2)) ≠ 0 := by
  letI : IsFiniteMeasure (FinMeasureBridge.weightedCount p) :=
    FinMeasureBridge.weightedCount_isFiniteMeasure p
  rw [trim_singleton_eq_fiber]
  exact FinMeasureBridge.fiber_ne_zero_iff p hp ω.2

/-! ### §99.6 原文命题**在纤维退化时**成立 -/

/-- ⭐⭐ **退化情形：纤维是单点 ⟹ 原文命题成立。**

**⚠ 这是原文命题**唯一无条件成立的场景**** ——
**它同时说明了「为什么原文命题看似对」：在 `γ` 充分细分（每个 `z` 只对应一个 `(x,y)`）时，
`m'` 就接近整个 σ-代数，`trim` 几乎不改动东西。** -/
theorem trim_singleton_eq_of_fiber_singleton [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure ((α × β) × γ)) (ω : (α × β) × γ)
    (h : FinMeasureBridge.fiber ω.2 = {ω}) :
    μ.trim (MeasurableSpace.comap_le_iff_le_map.mpr
      (FinCondIndepMeasure.measurable_projZ (α := α) (β := β) (γ := γ))) {ω}
      = μ {ω} := by
  rw [trim_singleton_eq_fiber, h]

/-! ### §99.7 ⭐⭐⭐⭐⭐ **反例：原文命题为假**（**形式化**）

**⚠⚠ 本节给出原文命题的**形式化反例**** ——
**取 `α = Bool`、`β = γ = Unit`、`p ≡ 1`。**

**计算**：
* `m' = comap projZ = ⊥`（`projZ` 是常函数）；
* `(weightedCount p) {((true,()),())} = ofReal 1 = 1`；
* `(weightedCount p).trim {((true,()),())} = (weightedCount p) (fiber ()) = 2`。

**⟹ `1 ≠ 2`。** -/

section Counterexample

/-- 反例用的有限律：`p ≡ 1`（**不**归一，但这与命题的真假无关）。 -/
noncomputable def counterexampleP : FiniteCondIndep.FinJoint Bool Unit Unit := fun _ => 1

/-- 反例测度：`weightedCount counterexampleP`。 -/
noncomputable def counterMu : Measure ((Bool × Unit) × Unit) :=
  FinMeasureBridge.weightedCount counterexampleP

instance counterMu_isFiniteMeasure : IsFiniteMeasure counterMu :=
  FinMeasureBridge.weightedCount_isFiniteMeasure counterexampleP

/-- 反例中单点的质量 = 1。 -/
theorem counterMu_singleton : counterMu {((true, ()), ())} = 1 := by
  rw [counterMu, FinMeasureBridge.weightedCount_singleton]
  norm_num [counterexampleP]

/-- 反例中纤维的质量 = 2（纤维是整个空间）。 -/
theorem counterMu_fiber : counterMu (FinMeasureBridge.fiber ()) = 2 := by
  rw [counterMu, FinMeasureBridge.weightedCount_fiber]
  simp [counterexampleP]

/-- ⭐⭐⭐⭐⭐ **反例：`trim` 在单点上 ≠ 原测度**。

**⟹ 原文命题 `trim {ω} = μ {ω}` **为假**。** -/
theorem counterMu_trim_singleton :
    (counterMu.trim (MeasurableSpace.comap_le_iff_le_map.mpr
      (FinCondIndepMeasure.measurable_projZ (α := Bool) (β := Unit) (γ := Unit))))
      {((true, ()), ())} = 2 := by
  rw [trim_singleton_eq_fiber, counterMu_fiber]

/-- ⭐⭐⭐⭐⭐ **原文命题的否证**（`1 ≠ 2`）。 -/
theorem trim_singleton_eq_false :
    ¬ ((counterMu.trim (MeasurableSpace.comap_le_iff_le_map.mpr
        (FinCondIndepMeasure.measurable_projZ (α := Bool) (β := Unit) (γ := Unit))))
        {((true, ()), ())} = counterMu {((true, ()), ())}) := by
  rw [counterMu_trim_singleton, counterMu_singleton]
  norm_num

end Counterexample

/-! ### §99.8 **本节完成的与未完成的**（**精确登记**）

**✅ 已证（全部无 `sorry`）**：

| 构件 | 状态 |
|---|---|
| `fiber_subset_of_measurable` | 已证 |
| `fiber_measurable` | 已证 |
| `singleton_measurable_iff` | 已证（**精确判据**）|
| `trim_singleton_eq_fiber` | 已证（**主定理**）|
| `trim_singleton_eq_of_measurable` | 已证（**原命题的正确版本**）|
| `trim_fiber_eq` | 已证（**纤维版，恒成立**）|
| `trim_singleton_ne_zero_iff` | 已证 |
| `trim_singleton_nonzero_of_ne_zero` | 已证（**桥需要的方向**）|
| `weightedCount_trim_singleton` | 已证 |
| `weightedCount_trim_singleton_ne_zero_iff` | 已证 |
| `trim_singleton_eq_of_fiber_singleton` | 已证 |
| `trim_singleton_eq_false` | 已证（**原命题的反例**）|

**⚠⚠ 数学结论**：

> **缺口 A 的原陈述是假的**（§99.7 给出形式化反例）。
> **正确的形式是**：
> * **`trim {ω} = μ (fiber ω.2)`**（主定理），
> * 等价地 **`trim {ω} ≠ 0 ↔ μ (fiber ω.2) ≠ 0`**，
> * 若真要 `trim {ω} = μ {ω}`，**必须加假设 `{ω}` 是 `m'`-可测（⟺ 纤维退化）**。

**⚠ 对桥的影响**：`Fate/_step11_Z3.lean:349` 里原有的 `trim_singleton`
（号称「有限支撑测度的 `trim` 不改变单点质量」）**正是本节的假命题**，
**且它当前**编译失败****（`trim_measurableSet_eq` 的参数顺序 + 缺 `MeasurableSingletonClass` 实例，实测）。
**⟹ 该引理应当删除或用本节的主定理替换。**
（**注意它此前唯一「能用」的原因是旧版隐含了 `DiscreteMeasurableSpace`，
从而使 `m'` 被迫等于 `mΩ`；那不是数学，而是实例的巧合。**）

**⚠ 未做**：把 `trim_singleton_nonzero_of_ne_zero` 接进
`Fate/_step11_Z3.lean` 的 `ae_iff_of_countable` 链 ——
**这属于缺口 B（`∀ᵐ` 与零测点的处理），不在本任务（T5）范围内。** -/

/-! ===========================================================================
  §99.9  ⭐⭐ **`weightedCount` 的纤维级 `trim` 接口**（R-41 接线）

  ## 背景（真实缺口，实测）

  §99.5 只给了**单点版**：`weightedCount_trim_singleton`
  （`trim {omega} = sum ofReal p`）。
  而 §99.4 的 `trim_fiber_eq` 说明 **`trim` 真正保持不变的是纤维**；
  §99.5 从未把这两者组合成**纤维版**的 `weightedCount` 定理。

  **⚠ 这个缺口是实质的**：`trim {omega}` 与 `trim (fiber omega.2)`
  在纤维退化时要相等，但在一般情况下**不相等**
  （§99.7 的反例正是 `trim {omega} = 2` 而 `weightedCount {omega} = 1`）。

  ## 本节做什么

  | # | 名称 | 内容 |
  |---|---|---|
  | **W1** | `weightedCount_trim_fiber` | ⭐ `weightedCount.trim (fiber c) = sum_x sum_y ofReal p` |
  | **W2** | `weightedCount_trim_fiber_ne_zero_iff` | ⭐ `... != 0 ↔ sum_x sum_y p != 0` |
  | **W3** | `weightedCount_trim_singleton_eq_trim_fiber` | 单点 `trim` = 同纤维的 `trim` |
  | **W4** | `weightedCount_trim_singleton_eq_of_fiber_singleton` | 纤维退化时单点 `trim` = 原测度 |

  **⚠ 防同义反复检查（逐条）**：
  * W1 的前件只有 `p`、`c`（无测度假设）；结论左端是 §99.4 的 `trim_fiber_eq`
    实例，右端是 `FinMeasureBridge.weightedCount_fiber`（`Fate/FinMeasureBridge.lean`
    的独立定理），两条来源不同，合成后是**新等式**。
  * W2 的前件是 `hp : forall a, 0 <= p a`（非负性，`FinMeasureBridge` 侧要求），
    结论是 `trim` 的**非零判据**；由 W1 + `fiber_ne_zero_iff` 得出。
  * W3 的前件只有 `p`、`omega`；左右两端是**两个不同的集合**（`{omega}` 与 `fiber omega.2`）
    上的 `trim` —— 这不是定义展开能得到的，须用 §99.4 + §99.3。
  * W4 的前件是 `fiber omega.2 = {omega}`（**退化条件，`omega` 侧的信息**），
    结论是 `trim {omega} = weightedCount {omega}` —— 正是 §99.7 反例所否定的命题
    在退化情形下的**成立版**，与 `trim_singleton_eq_of_fiber_singleton` 一致。
  =========================================================================== -/

/-- **W1**：⭐⭐ **`weightedCount` 的 `trim` 在纤维上 = 双求和。**

**⟹ 这是「`trim` 与 `weightedCount` 对接」在**纤维级**的正确形式**：
单点版（§99.5）是它的特例（经 W3），而纤维版**无需**任何可测性假设。 -/
theorem weightedCount_trim_fiber {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSingletonClass ((A × B) × C)] [MeasurableSingletonClass C]
    (p : FiniteCondIndep.FinJoint A B C) (c : C) :
    letI : IsFiniteMeasure (FinMeasureBridge.weightedCount p) :=
      FinMeasureBridge.weightedCount_isFiniteMeasure p
    (FinMeasureBridge.weightedCount p).trim
      (MeasurableSpace.comap_le_iff_le_map.mpr FinCondIndepMeasure.measurable_projZ)
      (FinMeasureBridge.fiber c) = ∑ x : A, ∑ y : B, ENNReal.ofReal (p ((x, y), c)) := by
  letI : IsFiniteMeasure (FinMeasureBridge.weightedCount p) :=
    FinMeasureBridge.weightedCount_isFiniteMeasure p
  rw [trim_fiber_eq]
  exact FinMeasureBridge.weightedCount_fiber p c

/-- **W2**：⭐⭐ **纤维级 `trim` 的非零判据**（测度论条件 ⟹ 纯代数条件）。

**⚠ 需要 `hp : forall a, 0 <= p a`**（非负性），
理由与 `FinMeasureBridge.fiber_ne_zero_iff` 相同：否则 `ofReal` 折负数会失效。 -/
theorem weightedCount_trim_fiber_ne_zero_iff {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSingletonClass ((A × B) × C)] [MeasurableSingletonClass C]
    (p : FiniteCondIndep.FinJoint A B C) (hp : ∀ a, 0 ≤ p a) (c : C) :
    letI : IsFiniteMeasure (FinMeasureBridge.weightedCount p) :=
      FinMeasureBridge.weightedCount_isFiniteMeasure p
    (FinMeasureBridge.weightedCount p).trim
        (MeasurableSpace.comap_le_iff_le_map.mpr FinCondIndepMeasure.measurable_projZ)
        (FinMeasureBridge.fiber c) ≠ 0
      ↔ (∑ x : A, ∑ y : B, p ((x, y), c)) ≠ 0 := by
  letI : IsFiniteMeasure (FinMeasureBridge.weightedCount p) :=
    FinMeasureBridge.weightedCount_isFiniteMeasure p
  rw [trim_fiber_eq]
  exact FinMeasureBridge.fiber_ne_zero_iff p hp c

/-- **W3**：⭐⭐ **单点 `trim` = 同纤维的 `trim`**（`weightedCount` 版）。

**⟹ 把 §99.3 的 `trim_singleton_eq_fiber` 与 §99.4 的 `trim_fiber_eq` 合成**：
单点上取的 `trim` 实际上只依赖其纤维，**这解释了 §99.7 反例的全部内容**
（`{omega}` 与 `fiber omega.2` 的 `trim` 相等，而**原测度**不相等）。 -/
theorem weightedCount_trim_singleton_eq_trim_fiber {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSingletonClass ((A × B) × C)] [MeasurableSingletonClass C]
    (p : FiniteCondIndep.FinJoint A B C) (omega : (A × B) × C) :
    letI : IsFiniteMeasure (FinMeasureBridge.weightedCount p) :=
      FinMeasureBridge.weightedCount_isFiniteMeasure p
    (FinMeasureBridge.weightedCount p).trim
        (MeasurableSpace.comap_le_iff_le_map.mpr FinCondIndepMeasure.measurable_projZ) {omega}
      = (FinMeasureBridge.weightedCount p).trim
        (MeasurableSpace.comap_le_iff_le_map.mpr FinCondIndepMeasure.measurable_projZ)
        (FinMeasureBridge.fiber omega.2) := by
  letI : IsFiniteMeasure (FinMeasureBridge.weightedCount p) :=
    FinMeasureBridge.weightedCount_isFiniteMeasure p
  rw [trim_singleton_eq_fiber, trim_fiber_eq]

/-- **W4**：⭐⭐ **纤维退化 ⟹ 原文命题对 `weightedCount` 成立**。

**⚠ 这是原文命题**唯一无条件成立的场景****（延续 §99.6 的结论，改为 `weightedCount` 实例）：
在 `fiber omega.2 = {omega}` 时，单点 `trim` 确实等于原测度。 -/
theorem weightedCount_trim_singleton_eq_of_fiber_singleton {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSingletonClass ((A × B) × C)] [MeasurableSingletonClass C]
    (p : FiniteCondIndep.FinJoint A B C) (omega : (A × B) × C)
    (h : FinMeasureBridge.fiber omega.2 = {omega}) :
    letI : IsFiniteMeasure (FinMeasureBridge.weightedCount p) :=
      FinMeasureBridge.weightedCount_isFiniteMeasure p
    (FinMeasureBridge.weightedCount p).trim
        (MeasurableSpace.comap_le_iff_le_map.mpr FinCondIndepMeasure.measurable_projZ) {omega}
      = (FinMeasureBridge.weightedCount p) {omega} := by
  letI : IsFiniteMeasure (FinMeasureBridge.weightedCount p) :=
    FinMeasureBridge.weightedCount_isFiniteMeasure p
  exact trim_singleton_eq_of_fiber_singleton (FinMeasureBridge.weightedCount p) omega h


end GapTrimWeightedCount

end Fate
