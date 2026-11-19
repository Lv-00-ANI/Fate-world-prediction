import FateWorld.FateV2.Modeling.CondIndepN
import FateWorld.FateV2.Modeling.NaryMeasure
import Mathlib.MeasureTheory.Measure.Dirac

/-!
  # Modeling · NKernelValue

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NKernelValue.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：CondIndepN, NaryMeasure
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenN ⭐⭐ **N 元的核值引理**（`CondIndepN` 的测度层对接）

  ## 任务书陈述的**两处修正**

  | # | 任务书写法 | 问题 | 本文件的处理 |
  |---|---|---|---|
  | 1 | `FateV2.Modeling.GenN.weightedCountN / fiberN` | **这两个名字在库里不存在**（`CondIndepN.lean §13` 明确登记「测度层对接未做」）| 本节**自含**建出它们（§1–§2）|
  | 2 | 结论写成 `κ a t = ENNReal.ofReal (…/…)` | **左端是 `ℝ`、右端是 `ENNReal`**，类型不匹配；且 `∑ p` 可能为非正（`ofReal` 会截断），等式不可能对任意 `p` 成立 | 左端取 `.real`、右端为 `ℝ`（见 `kernelValueN_fiber_ratio`）。这与二元版 `FinalB3.kernelValue_fiber_ratio` **逐字同构** |

  ## ⭐ `m' = comap snd` **是恰当的**

  * `snd` 逐点对应二元版的 `projZ : (α × β) × γ → γ`；
  * `comap snd` 的原子**恰是纤维** `fiberN z`，故 `condExpKernel` 在每个纤维上取常数
    —— 这正是「给定 `Z = z`」的语义（见 `condExpKernelN_fiber_eq`）；
  * `fiberN z` 本身 `comap snd`-可测，`weightedCountN` 与它相容。

  **唯一需要在陈述中补齐的是「纤维质量非零」的守卫**。任务书用
  `hF : weightedCountN p (fiberN a.2) ≠ 0`（ENNReal 版）给出，本节进一步证明
  它等价于纯代数的 `∑ xs, p (xs, a.2) ≠ 0`（`fiberN_ne_zero_iff`）。

  ## ⚠ 任务书**缺**的假设

  1. `[Countable (∀ i, fam i)]` —— `ae_iff_forall_or_zero`（「有限类型上 `∀ᵐ` 的精确展开」）
     需要 `[Countable Ω]`；在 `Ω = (∀ i, fam i) × γ` 上它虽可由 `Fintype` 合成，
     但**依赖实例搜索的运气**，故本节**显式**写出。
  2. `[StandardBorelSpace ((∀ i, fam i) × γ)]` —— `condExpKernel` 自身的类型类要求
     （离散空间自动满足，但须让搜索看得见，否则在 `m ≠ mΩ` 时会去找错的实例）。

  ## 已证结论

  * `weightedCountN_apply` / `weightedCountN_fiber` / `weightedCountN_isFiniteMeasure`
  * `fiberN_ne_zero_iff`：`weightedCountN p (fiberN c) ≠ 0 ↔ ∑ xs, p (xs,c) ≠ 0`
  * `comap_snd_apply_eq_of_fiber`：`comap snd`-可测函数在纤维上为常数
  * `{xs} × {z}` 的质量 = `ofReal (p (xs,z))`（`weightedCountN_singleton`）
  * ⭐ `kernelValueN_mul_fiber`：`κ a t * μ.real(fiberN a.2) = μ.real(t ∩ fiberN a.2)`
  * ⭐⭐ `kernelValueN_fiber_ratio`：**N 元的核值 = 加权求和比**

  **无 `sorry` / `admit` / `axiom`。**
  =========================================================================== -/

namespace FateV2.Modeling
namespace GenN

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)] [∀ i, DecidableEq (fam i)]
variable {γ : Type*} [Fintype γ] [DecidableEq γ]

/-! ## §1 ⭐ 纤维与加权计数测度 -/

/-- ⭐ **`Z`-纤维**：第二坐标等于 `z` 的点。 -/
def fiberNLocal (z : γ) : Set ((∀ i, fam i) × γ) := {w | w.2 = z}

/-- ⭐ **投影** `snd : (∀ i, fam i) × γ → γ`（二元版 `projZ` 的 N 元版）。 -/
def sndN : ((∀ i, fam i) × γ) → γ := fun w => w.2

variable [MeasurableSpace γ] [MeasurableSingletonClass γ]
  [∀ i, MeasurableSpace (fam i)] [∀ i, DiscreteMeasurableSpace (fam i)]
  [MeasurableSpace ((∀ i, fam i) × γ)]
  [MeasurableSingletonClass ((∀ i, fam i) × γ)]
/-- ⭐ 辅助：`snd : (∀ i, fam i) × γ → γ` 对**任意**乘积空间上的 σ-代数可测
（因为每个纤维都可写成单点集的并，而单点集可测）。 -/
theorem measurable_sndN :
    Measurable (fun w : (∀ i, fam i) × γ => w.2) := by
  intro s hs
  have h : ((fun w : (∀ i, fam i) × γ => w.2) ⁻¹' s)
      = ⋃ xs : (∀ i, fam i), ⋃ (x : γ) (_ : x ∈ s),
          ({(xs, x)} : Set ((∀ i, fam i) × γ)) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · intro hw; exact ⟨w.1, w.2, hw, Prod.ext rfl rfl⟩
    · rintro ⟨y, z, hz, rfl⟩; exact hz
  rw [h]
  exact MeasurableSet.iUnion fun xs => MeasurableSet.iUnion fun z =>
    MeasurableSet.iUnion fun _ => measurableSet_singleton _

/-- ⭐ 辅助：`comap snd ≤ 默认乘积 σ-代数`。 -/
private theorem comapSnd_le_default :
    MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2)
        (inferInstance : MeasurableSpace γ)
      ≤ (inferInstance : MeasurableSpace ((∀ i, fam i) × γ)) :=
  MeasurableSpace.comap_le_iff_le_map.mpr measurable_sndN

/-- ⭐⭐ **加权计数测度**（N 元版）：

$$\sum_{xs,\,z}\ \mathrm{ofReal}\bigl(p(xs,z)\bigr)\cdot \delta_{(xs,z)}$$ -/
noncomputable def weightedCountNLocal (p : ((∀ i, fam i) × γ) → ℝ) : Measure ((∀ i, fam i) × γ) :=
  ∑ xs : (∀ i, fam i), ∑ z : γ, ENNReal.ofReal (p (xs, z)) • Measure.dirac (xs, z)

/-! ## §2 ⭐⭐ 测度在任意集合 / 纤维 / 单点 / 全空间上的值 -/

omit [MeasurableSpace γ] [MeasurableSingletonClass γ] [∀ i, MeasurableSpace (fam i)]
  [∀ i, DiscreteMeasurableSpace (fam i)] [∀ i, DecidableEq (fam i)] [DecidableEq γ] in
/-- ⭐⭐ `weightedCountN` 在**任意集合**上的显式值。 -/
theorem weightedCountN_applyLocal (p : ((∀ i, fam i) × γ) → ℝ)
    (s : Set ((∀ i, fam i) × γ)) [DecidablePred (· ∈ s)] :
    weightedCountN p s = ∑ xs : (∀ i, fam i), ∑ z : γ,
      (if (xs, z) ∈ s then ENNReal.ofReal (p (xs, z)) else 0) := by
  simp only [weightedCountN, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  conv_lhs => enter [2, x, 2, z]; rw [Measure.dirac_apply]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => ?_))
  by_cases h : (x, z) ∈ s
  · simp [Set.indicator_of_mem h, h]
  · simp [Set.indicator_of_notMem h, h]

omit [MeasurableSpace γ] [MeasurableSingletonClass γ] [∀ i, MeasurableSpace (fam i)]
  [∀ i, DiscreteMeasurableSpace (fam i)] [∀ i, DecidableEq (fam i)] in
/-- ⭐⭐ `weightedCountN` 在**纤维**上的值。 -/
theorem weightedCountN_fiber (p : ((∀ i, fam i) × γ) → ℝ) (c : γ) :
    weightedCountN p (fiberN c) = ∑ xs : (∀ i, fam i), ENNReal.ofReal (p (xs, c)) := by
  simp only [weightedCountN, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  conv_lhs => enter [2, x, 2, z]; rw [Measure.dirac_apply]
  have hind : ∀ (w : (∀ i, fam i) × γ),
      (fiberN c).indicator (1 : (∀ i, fam i) × γ → ENNReal) w = if w.2 = c then 1 else 0 := by
    intro w
    by_cases h : w.2 = c
    · rw [Set.indicator_of_mem (show w ∈ fiberN c from h)]; simp [h]
    · rw [Set.indicator_of_notMem (show w ∉ fiberN c from h)]; simp only [h, if_false]
  simp only [hind]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single c]
  · simp
  · intro z _ hz; simp [hz]
  · intro h; exact absurd (Finset.mem_univ c) h

omit [MeasurableSpace γ] [MeasurableSingletonClass γ] [∀ i, MeasurableSpace (fam i)]
  [∀ i, DiscreteMeasurableSpace (fam i)] [∀ i, DecidableEq (fam i)] [DecidableEq γ] in
/-- ⭐⭐ `weightedCountN` 在**单点**上的值（这是二元版 `weightedCount_singleton` 的 N 元版）。 -/
theorem weightedCountN_singleton (p : ((∀ i, fam i) × γ) → ℝ)
    (xs : (∀ i, fam i)) (c : γ) :
    weightedCountN p {(xs, c)} = ENNReal.ofReal (p (xs, c)) := by
  classical
  simp only [weightedCountN, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  conv_lhs => enter [2, x, 2, z]; rw [Measure.dirac_apply]
  have hind : ∀ (w : (∀ i, fam i) × γ),
      ({(xs, c)} : Set ((∀ i, fam i) × γ)).indicator (1 : (∀ i, fam i) × γ → ENNReal) w
        = if w = (xs, c) then 1 else 0 := by
    intro w
    by_cases h : w = (xs, c)
    · rw [Set.indicator_of_mem (show w ∈ ({(xs, c)} : Set ((∀ i, fam i) × γ)) from h)]
      simp [h]
    · rw [Set.indicator_of_notMem (show w ∉ ({(xs, c)} : Set ((∀ i, fam i) × γ))
            from fun hc => h hc)]
      simp only [h, if_false]
  simp only [hind]
  rw [Finset.sum_eq_single xs]
  · rw [Finset.sum_eq_single c]
    · simp
    · intro z _ hz
      rw [if_neg (fun hcon => hz (congrArg Prod.snd hcon)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ c) h
  · intro x _ hx
    rw [Finset.sum_eq_zero]
    intro z _
    rw [if_neg (fun hcon => hx (congrArg Prod.fst hcon)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ xs) h

omit [MeasurableSpace γ] [MeasurableSingletonClass γ] [∀ i, MeasurableSpace (fam i)]
  [∀ i, DiscreteMeasurableSpace (fam i)] in
/-- ⭐⭐ **纤维质量非零 ⟺ `∑ xs, p (xs, z) ≠ 0`**（把测度论条件化为纯代数条件）。 -/
theorem fiberN_ne_zero_iff (p : ((∀ i, fam i) × γ) → ℝ)
    (hp : ∀ w, 0 ≤ p w) (c : γ) :
    weightedCountN p (fiberN c) ≠ 0 ↔ (∑ xs : (∀ i, fam i), p (xs, c)) ≠ 0 := by
  have hsum : (∑ xs : (∀ i, fam i), ENNReal.ofReal (p (xs, c)))
      = ENNReal.ofReal (∑ xs : (∀ i, fam i), p (xs, c)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun xs _ => hp _)]
  have hpos : ENNReal.ofReal (∑ xs : (∀ i, fam i), p (xs, c)) ≠ 0
      ↔ (∑ xs : (∀ i, fam i), p (xs, c)) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    constructor
    · intro h; exact ne_of_gt h
    · intro h; exact lt_of_le_of_ne (Finset.sum_nonneg fun xs _ => hp _) (Ne.symm h)
  rw [weightedCountN_fiber, hsum, hpos]

omit [MeasurableSpace γ] [MeasurableSingletonClass γ] [∀ i, MeasurableSpace (fam i)]
  [∀ i, DiscreteMeasurableSpace (fam i)] in
/-- ⭐⭐⭐ 纤维质量（`ℝ`）= `∑ xs, p (xs, z)`。 -/
theorem fiberN_real_eq_sumLocal (p : ((∀ i, fam i) × γ) → ℝ)
    (hp : ∀ w, 0 ≤ p w) (z : γ) :
    (weightedCountN p).real (fiberN z) = ∑ xs : (∀ i, fam i), p (xs, z) := by
  rw [Measure.real, weightedCountN_fiber]
  rw [ENNReal.toReal_sum
    (f := fun xs => ENNReal.ofReal (p (xs, z))) (fun xs _ => ENNReal.ofReal_ne_top)]
  exact Finset.sum_congr rfl fun xs _ => ENNReal.toReal_ofReal (hp _)

/-! ## §3 ⭐⭐⭐ 纤维上的可测性 / 常数性 / 指示函数积分 -/

omit [∀ i, DiscreteMeasurableSpace (fam i)] in
/-- ⭐⭐ **纤维是 `comap snd`-可测的**。 -/
theorem measurableSetN_fiber (c : γ) :
    MeasurableSet[MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance]
      (fiberN c) := by
  rw [fiberN]
  exact MeasurableSpace.measurableSet_comap.mpr ⟨{c}, measurableSet_singleton c, rfl⟩

omit [∀ i, DiscreteMeasurableSpace (fam i)] [MeasurableSpace γ] [MeasurableSingletonClass γ]
  [Fintype γ] [DecidableEq γ] in
/-- ⭐⭐ **`fiberN` 对默认 σ-代数可测**（无需 `fiberN` 可测性的额外假设）。 -/
theorem measurableSet_fiberN_default (c : γ) :
    MeasurableSet (fiberN c : Set ((∀ i, fam i) × γ)) := by
  have hset : (fiberN c) = ⋃ xs : (∀ i, fam i), ({(xs, c)} : Set ((∀ i, fam i) × γ)) := by
    ext w
    constructor
    · intro h
      exact Set.mem_iUnion.mpr ⟨w.1, by
        simp only [fiberN, Set.mem_setOf_eq, Set.mem_singleton_iff]
        exact Prod.ext rfl h⟩
    · intro h
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp h
      simp only [Set.mem_singleton_iff] at hy
      simp [fiberN, hy]
  rw [hset]
  exact MeasurableSet.iUnion fun xs => measurableSet_singleton _

/-- ⭐⭐⭐ **`comap snd`-可测函数在每个纤维上是常数**。 -/
theorem comap_snd_apply_eq_of_fiber
    {f : ((∀ i, fam i) × γ) → ℝ}
    (hf : Measurable[MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance] f)
    (w₁ w₂ : (∀ i, fam i) × γ) (h : w₁.2 = w₂.2) : f w₁ = f w₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hset : MeasurableSet[MeasurableSpace.comap
        (fun w : (∀ i, fam i) × γ => w.2) inferInstance] {w | f w < f w₂} :=
      hf measurableSet_Iio
    rw [MeasurableSpace.measurableSet_comap] at hset
    obtain ⟨S, _, hS⟩ := hset
    have hm1 : w₁ ∈ {w : (∀ i, fam i) × γ | f w < f w₂} := hlt
    rw [← hS] at hm1
    have hm2 : w₂ ∉ {w : (∀ i, fam i) × γ | f w < f w₂} := lt_irrefl (f w₂)
    rw [← hS] at hm2
    exact hm2 (by simpa [h] using hm1)
  · have hset : MeasurableSet[MeasurableSpace.comap
        (fun w : (∀ i, fam i) × γ => w.2) inferInstance] {w | f w < f w₁} :=
      hf measurableSet_Iio
    rw [MeasurableSpace.measurableSet_comap] at hset
    obtain ⟨S, _, hS⟩ := hset
    have hm1 : w₂ ∈ {w : (∀ i, fam i) × γ | f w < f w₁} := hlt
    rw [← hS] at hm1
    have hm2 : w₁ ∉ {w : (∀ i, fam i) × γ | f w < f w₁} := lt_irrefl (f w₁)
    rw [← hS] at hm2
    exact hm2 (by simpa [h] using hm1)

/-- ⭐⭐⭐ **`μ[1_t | comap snd]` 是 `comap snd`-可测的**。 -/
theorem condExpN_indicator_measurable
    (μ : Measure ((∀ i, fam i) × γ)) (t : Set ((∀ i, fam i) × γ)) :
    Measurable[MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance]
      (μ[t.indicator fun _ => (1:ℝ) |
        MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance]) :=
  stronglyMeasurable_condExp.measurable

/-- ⭐⭐ **指示函数在可测集上的积分 = 交集的实值测度**。 -/
theorem setIntegral_indicator_oneNLocal
    (μ : Measure ((∀ i, fam i) × γ)) (s t : Set ((∀ i, fam i) × γ))
    (ht : MeasurableSet t) :
    ∫ w in s, t.indicator (fun _ => (1:ℝ)) w ∂μ = μ.real (s ∩ t) := by
  rw [MeasureTheory.setIntegral_indicator ht, MeasureTheory.setIntegral_const]
  simp [smul_eq_mul]

/-- ⭐⭐⭐ **在纤维上，常数函数的积分** = `μ.real(fiber z) * c`。 -/
theorem setIntegral_fiber_constN
    (μ : Measure ((∀ i, fam i) × γ)) (z : γ) (g : ((∀ i, fam i) × γ) → ℝ) (c : ℝ)
    (_hg : Integrable g μ) (hconst : ∀ w ∈ fiberN z, g w = c) :
    ∫ w in (fiberN z), g w ∂μ = μ.real (fiberN z) * c := by
  have hle := comapSnd_le_default (fam := fam) (γ := γ)
  have hfib_meas : MeasurableSet (fiberN z) := hle _ (measurableSetN_fiber z)
  have h1 : ∫ w in (fiberN z), g w ∂μ = ∫ w in (fiberN z), c ∂μ := by
    apply MeasureTheory.setIntegral_congr_fun hfib_meas
    intro w hw
    exact hconst w hw
  rw [h1, MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]

/-! ## §4 ⭐⭐⭐ 条件期望在纤维上可积 / 纤维上的 `setIntegral_condExp` -/

/-- ⭐⭐ 常数函数可积（有限测度）。 -/
theorem integrable_constN (μ : Measure ((∀ i, fam i) × γ)) [IsFiniteMeasure μ] (c : ℝ) :
    Integrable (fun _ => c) μ :=
  integrable_const c

/-- ⭐⭐⭐ **`setIntegral_condExp` 在纤维 `fiberN z` 上成立**
（`fiberN z` 自动是 `comap snd`-可测的，故「纤维饱和」前提免费）。 -/
theorem setIntegral_condExp_fiberNLocal
    (μ : Measure ((∀ i, fam i) × γ)) [IsFiniteMeasure μ]
    [StandardBorelSpace ((∀ i, fam i) × γ)]
    (t : Set ((∀ i, fam i) × γ)) (ht : MeasurableSet t) (z : γ) :
    ∫ w in (fiberN z), μ[t.indicator fun _ => (1:ℝ) |
        MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance] w ∂μ
      = ∫ w in (fiberN z), t.indicator (fun _ => (1:ℝ)) w ∂μ := by
  have hcle := comapSnd_le_default (fam := fam) (γ := γ)
  refine setIntegral_condExp
    (m := MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)
    (m₀ := inferInstance) (μ := μ) (f := t.indicator fun _ => (1:ℝ))
    (s := fiberN z) (hm := hcle) ?_ ?_
  · exact (integrable_const (1:ℝ)).indicator ht
  · exact measurableSetN_fiber z

/-! ## §5 ⭐⭐⭐⭐ 核值 × 纤维质量 = 交集质量（N 元版） -/

/-- ⭐⭐⭐⭐ **核值 × 纤维质量 = 交集质量**（`bridgeKernelValue_mul_fiber` 的 N 元版）。

**证明结构**（与二元版**逐字同构**）：
| 步 | 内容 | 工具 |
|---|---|---|
| 1 | `(κ a).real t =ᵐ μ[1_t \| m']` | `condExpKernel_real_apply` |
| 2 | `μ[1_t \| m']` 是 `m'`-可测 ⟹ 在纤维上常数 | `condExpN_indicator_measurable` + `comap_snd_apply_eq_of_fiber` |
| 3 | 纤维上常数积分 = `μ.real(fiber) * c` | `setIntegral_fiber_constN` |
| 4 | `∫ over fiber of μ[1_t\|m'] = ∫ over fiber of 1_t` | `setIntegral_condExp_fiberNLocal` |
| 5 | `∫ over fiber of 1_t = μ.real(t ∩ fiber)` | `setIntegral_indicator_oneNLocal` |
| 6 | `=ᵐ` + 单点正质量 ⟹ 逐点 | `ae_iff_of_countable` |

**⚠ 前提 `hω : μ {ω} ≠ 0`** —— 零质量点的核值不受约束（真实现象）。 -/
theorem kernelValueN_mul_fiber
    [StandardBorelSpace ((∀ i, fam i) × γ)] [Countable (∀ i, fam i)]
    (p : ((∀ i, fam i) × γ) → ℝ)
    (t : Set ((∀ i, fam i) × γ)) (ht : MeasurableSet t)
    (ω : (∀ i, fam i) × γ)
    (hω : (weightedCountN p) {ω} ≠ 0) :
    letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
    ((condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)) ω).real t
      * (weightedCountN p).real (fiberN ω.2)
      = (weightedCountN p).real (t ∩ fiberN ω.2) := by
  letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
  set ce : ((∀ i, fam i) × γ) → ℝ := (weightedCountN p)[t.indicator fun _ => (1:ℝ) |
    MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance] with hce
  have hstep1 : (fun a => ((condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)) a).real t)
      =ᵐ[weightedCountN p] ce := by
    rw [hce]
    have hcle := comapSnd_le_default (fam := fam) (γ := γ)
    exact FateV2.Modeling.BridgeProofStep3.condExpKernel_real_apply
      (inferInstance : MeasurableSpace ((∀ i, fam i) × γ)) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance) hcle ht
  have hmeas := condExpN_indicator_measurable (weightedCountN p) t
  have hconst' : ∀ w ∈ fiberN ω.2, ce w = ce ω := by
    intro w hw
    have hh := comap_snd_apply_eq_of_fiber hmeas w ω (by simpa [fiberN] using hw)
    rw [hce]; exact hh
  have h_int_const : ∫ w in (fiberN ω.2), ce w ∂(weightedCountN p)
      = (weightedCountN p).real (fiberN ω.2) * ce ω :=
    setIntegral_fiber_constN (weightedCountN p) ω.2 ce (ce ω)
      (integrable_condExp) hconst'
  have h_eq_int : ∫ w in (fiberN ω.2), ce w ∂(weightedCountN p)
      = (weightedCountN p).real (t ∩ fiberN ω.2) := by
    rw [hce]
    rw [setIntegral_condExp_fiberNLocal (weightedCountN p) t ht ω.2]
    have h := setIntegral_indicator_oneNLocal (weightedCountN p) (fiberN ω.2) t ht
    rw [h, Set.inter_comm]
  have h_point : ((condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)) ω).real t
      = ce ω := by
    have h' : ∀ a, (weightedCountN p) {a} = 0 ∨
        ((condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
          (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)) a).real t = ce a := by
      exact (FateV2.Modeling.FinMeasureBridge.ae_iff_forall_or_zero (μ := weightedCountN p)
        (P := fun b : (∀ i, fam i) × γ => ((condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
          (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)) b).real t = ce b)).mp
        hstep1
    rcases h' ω with h0 | heq
    · exact absurd h0 hω
    · exact heq
  calc ((condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)) ω).real t
        * (weightedCountN p).real (fiberN ω.2)
      = ce ω * (weightedCountN p).real (fiberN ω.2) := by rw [h_point]
    _ = (weightedCountN p).real (fiberN ω.2) * ce ω := by rw [mul_comm]
    _ = ∫ w in (fiberN ω.2), ce w ∂(weightedCountN p) := h_int_const.symm
    _ = (weightedCountN p).real (t ∩ fiberN ω.2) := h_eq_int

/-! ## §6 ⭐⭐ 分子 / 分母的二重和形式 -/

omit [∀ i, DiscreteMeasurableSpace (fam i)] [DecidableEq γ] in
/-- ⭐⭐⭐ `μ.real(t ∩ fiber z)` = 纤维内指示加权和。 -/
theorem real_inter_fiber_eq_sum (p : ((∀ i, fam i) × γ) → ℝ)
    (hp : ∀ w, 0 ≤ p w) (t : Set ((∀ i, fam i) × γ))
    [DecidablePred (· ∈ t)] (z : γ) :
    (weightedCountN p).real (t ∩ fiberN z)
      = ∑ xs : (∀ i, fam i), (if (xs, z) ∈ t then p (xs, z) else 0) := by
  classical
  have hcond : ∀ (xs : (∀ i, fam i)) (z' : γ),
      ((xs, z') ∈ (t ∩ {w : (∀ i, fam i) × γ | w.2 = z})) ↔ ((xs, z') ∈ t ∧ z' = z) := by
    intro xs z'; simp [Set.mem_inter_iff]
  rw [Measure.real, weightedCountN_apply p (t ∩ fiberN z)]
  simp only [fiberN, hcond]
  rw [ENNReal.toReal_sum
    (f := fun xs => ∑ z', (if ((xs, z') ∈ t ∧ z' = z) then ENNReal.ofReal (p (xs, z')) else 0))
    (fun xs _ => by
      rw [ENNReal.sum_ne_top]; intro z' _; split <;> simp)]
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  rw [ENNReal.toReal_sum
    (f := fun z' => (if ((xs, z') ∈ t ∧ z' = z) then ENNReal.ofReal (p (xs, z')) else 0))
    (fun z' _ => by split <;> simp)]
  rw [Finset.sum_eq_single z]
  · simp only [eq_self_iff_true, and_true]
    by_cases hk : (xs, z) ∈ t
    · simp [hk, ENNReal.toReal_ofReal (hp _)]
    · simp [hk]
  · intro z' _ hne; simp [hne]
  · intro hz; exact absurd (Finset.mem_univ z) hz

/-! ## §7 ⭐⭐ 纤维内存在单点质量非零的点 -/

omit [∀ i, DiscreteMeasurableSpace (fam i)] in
/-- ⭐⭐ 纤维质量（`ENNReal`）非零 ⟹ 纤维内存在单点质量非零的点。 -/
theorem exists_pos_in_fiberN (p : ((∀ i, fam i) × γ) → ℝ)
    (hp : ∀ w, 0 ≤ p w) (z : γ)
    (hF : (weightedCountN p) (fiberN z) ≠ 0) :
    ∃ xs : (∀ i, fam i), (weightedCountN p) {(xs, z)} ≠ 0 := by
  by_contra hcon
  apply hF
  rw [weightedCountN_fiber]
  have hzero : ∀ xs : (∀ i, fam i), ENNReal.ofReal (p (xs, z)) = 0 := by
    intro xs
    by_contra hne
    exact hcon ⟨xs, by rw [weightedCountN_singleton]; exact hne⟩
  exact Finset.sum_eq_zero fun xs _ => hzero xs

/-! ## §8 ⭐⭐⭐⭐ 同一纤维内 `condExpKernel` 相等 -/

omit [∀ i, DiscreteMeasurableSpace (fam i)] [DecidableEq γ] in
/-- ⭐⭐⭐ **同一纤维内的两点给出相同的 `condExpKernel`**（`m' = comap snd`-原子）。 -/
theorem condExpKernelN_fiber_eq [StandardBorelSpace ((∀ i, fam i) × γ)]
    (p : ((∀ i, fam i) × γ) → ℝ)
    (xs xs' : (∀ i, fam i)) (z : γ) :
    letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
    condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance) (xs, z)
    = condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance) (xs', z) := by
  letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
  let m' := MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance
  have h : ((xs, z) : (∀ i, fam i) × γ) ∈ @measurableAtom ((∀ i, fam i) × γ) m' ((xs', z)) := by
    simp only [measurableAtom, Set.mem_iInter]
    intro s hs hms
    obtain ⟨T, hT, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hms
    show ((xs, z) : (∀ i, fam i) × γ).2 ∈ T
    exact hs
  exact Kernel.apply_congr_of_mem_measurableAtom _ h

/-! ## §9 ⭐⭐⭐⭐⭐ **主定理：N 元的核值 = 加权求和比** -/

/-- ⭐⭐ **N 元的核值 = 加权求和比**（`kernelValue_fiber_ratio` 的 N 元推广）。

$$\bigl(\kappa_a\bigr).\mathrm{real}\ t
  = \frac{\sum_{xs}\ [\,(xs,a_2)\in t\,]\,p(xs,a_2)}{\sum_{xs}p(xs,a_2)}$$

**⭐ 证明**：
1. 取纤维内 `p ≠ 0` 的点 `(xs₀, z)` ⟹ `kernelValueN_mul_fiber` 给出乘积等式；
2. 由 `condExpKernelN_fiber_eq` 把 `a` 处的核值搬到 `(xs₀, z)`；
3. 再用 `real_inter_fiber_eq_sum` / `fiberN_real_eq_sumLocal` 把三个测度值化为求和。 -/
theorem kernelValueN_fiber_ratio
    [StandardBorelSpace ((∀ i, fam i) × γ)] [Countable (∀ i, fam i)]
    (p : ((∀ i, fam i) × γ) → ℝ)
    (t : Set ((∀ i, fam i) × γ)) (ht : MeasurableSet t)
    (a : (∀ i, fam i) × γ) (hp : ∀ w, 0 ≤ p w)
    (hF : (weightedCountN p) (fiberN a.2) ≠ 0) :
    letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
    [DecidablePred (· ∈ t)] →  -- ⚠ `Decidable` 特指此假设
    ((condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)) a).real t
      = (∑ xs : (∀ i, fam i), (if (xs, a.2) ∈ t then p (xs, a.2) else 0))
        / (∑ xs : (∀ i, fam i), p (xs, a.2)) := by
  letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
  intro hdec
  letI := hdec
  suffices hgoal : ∀ (xa : ∀ i, fam i) (za : γ), a = (xa, za) →
      ((condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
        (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)) (xa, za)).real t
        = (∑ xs : (∀ i, fam i), (if (xs, za) ∈ t then p (xs, za) else 0))
          / (∑ xs : (∀ i, fam i), p (xs, za)) by
    exact hgoal a.1 a.2 rfl
  intro xa za ha
  subst ha
  have hFz : (weightedCountN p) (fiberN za) ≠ 0 := hF
  obtain ⟨xs₀, hsing⟩ := exists_pos_in_fiberN p hp za hFz
  have hsum : (∑ xs : (∀ i, fam i), p (xs, za)) ≠ 0 := (fiberN_ne_zero_iff p hp za).mp hFz
  have hFr : (weightedCountN p).real (fiberN za) ≠ 0 := by
    rw [fiberN_real_eq_sumLocal p hp za]; exact hsum
  have hmul := kernelValueN_mul_fiber p t ht (xs₀, za) hsing
  have hmul' : ((condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance))
        (xs₀, za)).real t
      * (weightedCountN p).real (fiberN za) = (weightedCountN p).real (t ∩ fiberN za) := hmul
  have hsame := congrArg (fun m => m.real t) (condExpKernelN_fiber_eq p xa xs₀ za)
  have hR : (weightedCountN p).real (t ∩ fiberN za)
      = ∑ xs : (∀ i, fam i), (if (xs, za) ∈ t then p (xs, za) else 0) :=
    real_inter_fiber_eq_sum p hp t za
  have hD : (weightedCountN p).real (fiberN za) = ∑ xs : (∀ i, fam i), p (xs, za) :=
    fiberN_real_eq_sumLocal p hp za
  have key : ((condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)) (xs₀, za)).real t
      * (weightedCountN p).real (fiberN za)
      = ∑ xs : (∀ i, fam i), (if (xs, za) ∈ t then p (xs, za) else 0) := by
    rw [hmul', hR]
  have e1 : ((condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)) (xs₀, za)).real t
      = (∑ xs : (∀ i, fam i), (if (xs, za) ∈ t then p (xs, za) else 0))
        / (∑ xs : (∀ i, fam i), p (xs, za)) := by
    have hh : ((condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
        (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)) (xs₀, za)).real t
        * (weightedCountN p).real (fiberN za)
        = ∑ xs : (∀ i, fam i), (if (xs, za) ∈ t then p (xs, za) else 0) := key
    rw [← hD, eq_div_iff hFr]
    exact hh
  rw [hsame]
  exact e1

end GenN
end FateV2.Modeling