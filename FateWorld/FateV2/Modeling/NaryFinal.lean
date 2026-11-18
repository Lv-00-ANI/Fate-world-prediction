import FateWorld.FateV2.Modeling.NaryKernel2
/-!
  # Modeling · NaryFinal

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NaryFinal.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NaryKernel2
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenNFinal ⭐⭐⭐⭐⭐ **N 元核值引理**（**N 元桥的最终一块砖**，第 184 轮）

  ## 目标

  `(κ a).real t * μ.real(fiberN a.2) = μ.real(t ∩ fiberN a.2)`

  ## 组装链（与二元 `bridgeKernelValue_mul_fiber` 同构）

  | 步 | 内容 | 工具 |
  |---|---|---|
  | 1 | `(κ ·).real t =ᵐ μ[1_t \| m']` | `bridgeKernelStep1N` |
  | 2 | `μ[1_t \| m']` 是 `m'`-可测 ⟹ 纤维上常数 | `condExp_indicator_measurable` + `comap_snd_apply_eq_of_fiberN` |
  | 3 | 纤维上的常数积分 | `setIntegral_fiberN_const` |
  | 4 | `∫ over fiberN of 1_t = μ.real(t ∩ fiberN)` | `setIntegral_indicator_oneN` |
  | 5 | `=ᵐ` + 正质量 ⟹ 逐点 | `ae_iff_forall_or_zero` |
  =========================================================================== -/

/-! ## ⚠⚠ 语义警告（第 186 轮补，依对抗性审核 J4）

**本文件的结论在 `p` 有负值时不表达「p` 的条件概率」** ——
因为 `weightedCountN` 用 `ENNReal.ofReal`，**负值被截断为 0**
（见第 177 轮 `GuardNecessary.lean` 的**反例** `p = (4,-2;-2,1)`）。

- 定理**本身为真**（它只谈 `ofReal` 之后的测度）
- 但**要表达「`p` 的条件概率」语义，必须加前提 `hp : ∀ w, 0 ≤ p w`**
  （这与二元桥第 171 轮结论**完全一致**）

本文件的 `bridgeKernelValue_mul_fiberN` **没有** `hp` 前提 ——
这是**有意的**（使它更一般），但**使用者必须自己补 `hp`**。 -/

namespace FateV2.Modeling.GenN

open MeasureTheory ProbabilityTheory

section CondExpMeasurable

variable {ι : Type*} {fam : ι → Type*} {γ : Type*} [MeasurableSpace γ]
variable [MeasurableSpace ((∀ i, fam i) × γ)]

/-- ⭐ **`μ[1_s | m']` 是 `m'`-可测的**（**N 元版**）。

**⚠ 二元版 `condExp_indicator_measurable` 的证明只有**一行****
（`stronglyMeasurable_condExp.measurable`），**N 元版同样**。 -/
theorem condExp_indicator_measurableN
    (μ : Measure ((∀ i, fam i) × γ)) (s : Set ((∀ i, fam i) × γ)) :
    Measurable[MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance]
      (μ[s.indicator fun _ => (1:ℝ) | MeasurableSpace.comap
        (fun w : (∀ i, fam i) × γ => w.2) inferInstance]) :=
  stronglyMeasurable_condExp.measurable

end CondExpMeasurable
section CondExpFiberIntegral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
variable [MeasurableSpace ((∀ i, fam i) × γ)]
variable [MeasurableSingletonClass ((∀ i, fam i) × γ)]

omit [MeasurableSingletonClass ((∀ i, fam i) × γ)] in
/-- ⭐⭐⭐ **N 元**: `∫ over fiberN z of μ[1_t | m'] = ∫ over fiberN z of 1_t`

**⚠ 这是二元 `setIntegral_condExp_fiber` 的 N 元版** ——
**关键**：`fiberN z` 是 `m'`-可测的（`fiberN_measurable_comap`），故可用 `setIntegral_condExp`。 -/
theorem setIntegral_condExp_fiberN
    (p : ((∀ i, fam i) × γ) → ℝ)
    (t : Set ((∀ i, fam i) × γ)) (ht : MeasurableSet t)
    (hsnd : Measurable (fun w : (∀ i, fam i) × γ => w.2)) (z : γ) :
    letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
    ∫ w in (fiberN z), (weightedCountN p)[t.indicator fun _ => (1:ℝ)
        | MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance] w
      ∂(weightedCountN p)
      = ∫ w in (fiberN z), t.indicator (fun _ => (1:ℝ)) w ∂(weightedCountN p) := by
  letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
  exact setIntegral_condExp
    (m := MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)
    (m₀ := inferInstance)
    (μ := weightedCountN p)
    (f := t.indicator fun _ => (1:ℝ)) (s := fiberN z)
    (hm := MeasurableSpace.comap_le_iff_le_map.mpr hsnd)
    (hf := (integrable_const (μ := weightedCountN p) (1:ℝ)).indicator ht)
    (hs := fiberN_measurable_comap z)

end CondExpFiberIntegral
section FinalAssembly

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
variable [MeasurableSpace ((∀ i, fam i) × γ)]
variable [MeasurableSingletonClass ((∀ i, fam i) × γ)]
variable [StandardBorelSpace ((∀ i, fam i) × γ)]

omit [MeasurableSingletonClass ((∀ i, fam i) × γ)] in
/-- ⭐⭐⭐⭐⭐ **N 元核值引理**：`(κ a).real t * μ.real(fiberN a.2) = μ.real(t ∩ fiberN a.2)`。

**⭐ 这与二元 `bridgeKernelValue_mul_fiber` **完全同构**，只是把
`fiber` 换成 `fiberN`、`weightedCount` 换成 `weightedCountN`。** -/
theorem bridgeKernelValue_mul_fiberN
    (p : ((∀ i, fam i) × γ) → ℝ)
    (t : Set ((∀ i, fam i) × γ)) (ht : MeasurableSet t)
    (hsnd : Measurable (fun w : (∀ i, fam i) × γ => w.2))
    (ω : (∀ i, fam i) × γ)
    (hω : (weightedCountN p) {ω} ≠ 0) :
    letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
    ((condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)) ω).real t
      * (weightedCountN p).real (fiberN ω.2)
      = (weightedCountN p).real (t ∩ fiberN ω.2) := by
  letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
  set ce : (∀ i, fam i) × γ → ℝ := (weightedCountN p)[t.indicator fun _ => (1:ℝ)
    | MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance] with hce
  have hstep1 : (fun a => ((condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)) a).real t)
      =ᵐ[weightedCountN p] ce := by
    rw [hce]; exact bridgeKernelStep1N p t ht hsnd
  have hmeas := condExp_indicator_measurableN (weightedCountN p) t
  have hconst' : ∀ w ∈ fiberN ω.2, ce w = ce ω := by
    intro w hw
    have hh := comap_snd_apply_eq_of_fiberN hmeas w ω (by simpa [fiberN] using hw)
    rw [hce]; exact hh
  have h_int_const : ∫ w in (fiberN ω.2), ce w ∂(weightedCountN p)
      = (weightedCountN p).real (fiberN ω.2) * ce ω :=
    setIntegral_fiberN_const (weightedCountN p) hsnd ce ω.2 (ce ω) hconst'
  have h_eq_int : ∫ w in (fiberN ω.2), ce w ∂(weightedCountN p)
      = (weightedCountN p).real (t ∩ fiberN ω.2) := by
    calc ∫ w in (fiberN ω.2), ce w ∂(weightedCountN p)
        = ∫ w in (fiberN ω.2), t.indicator (fun _ => (1:ℝ)) w ∂(weightedCountN p) :=
          setIntegral_condExp_fiberN p t ht hsnd ω.2
      _ = (weightedCountN p).real (fiberN ω.2 ∩ t) :=
          setIntegral_indicator_oneN (weightedCountN p) (fiberN ω.2) t ht
      _ = (weightedCountN p).real (t ∩ fiberN ω.2) := by rw [Set.inter_comm]
  have h_point : ((condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)) ω).real t = ce ω := by
    have h' : ∀ᵐ a ∂(weightedCountN p),
        ((condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
          (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)) a).real t = ce a := hstep1
    have hz := FateV2.Modeling.FinMeasureBridge.ae_iff_forall_or_zero (weightedCountN p)
      (fun a => ((condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
        (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)) a).real t = ce a)
    rw [hz] at h'
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

end FinalAssembly

end FateV2.Modeling.GenN
