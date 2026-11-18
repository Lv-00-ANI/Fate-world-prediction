import FateWorld.FateV2.Modeling.NaryKernel
import FateWorld.FateV2.Modeling.BridgeProofStep3
/-!
  # Modeling · NaryKernel2

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NaryKernel2.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NaryKernel, BridgeProofStep3
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenNKernel2 ⭐⭐⭐⭐⭐ **N 元核值引理**（**N 元桥的第四块砖**，第 184 轮）

  ## 目标

  `(κ a).real t * μ.real(fiberN a.2) = μ.real(t ∩ fiberN a.2)`

  其中 `κ = condExpKernel (weightedCountN p) m'`、`m' = comap (取第二分量)`。

  ## ⭐⭐ 关键洞察（本轮）

  **二元的 `bridgeKernelStep1` 调用的 `condExpKernel_real_apply` **完全一般****
  （`{Ω : Type}`、`[StandardBorelSpace Ω]`、`m ≤ mΩ`）——
  **⟹ N 元版只需把它**重新实例化****，不需要重证。

  ## 二元 → N 元的对应

  | 二元（`BridgeKernel`）| N 元（本文件）|
  |---|---|
  | `bridgeKernelStep1` | `bridgeKernelStep1N` |
  | `comap_projZ_apply_eq_of_fiber` | `comap_snd_apply_eq_of_fiberN`（本例）|
  | `setIntegral_fiber_const_direct` | `setIntegral_fiberN_const`（`NaryKernel`）|
  | `setIntegral_indicator_one` | `setIntegral_indicator_oneN`（`NaryKernel`）|
  | `setIntegral_condExp_fiber` | `setIntegral_condExp_fiberN`（本例）|
  =========================================================================== -/

namespace FateV2.Modeling.GenN

open MeasureTheory ProbabilityTheory

section FiberConst

variable {ι : Type*} {fam : ι → Type*} {γ : Type*} [MeasurableSpace γ]


/-- ⭐⭐⭐ **N 元**: `m'`-可测函数在每个「纤维」上取常数值。

**⚠ 证明与二元版 `comap_projZ_apply_eq_of_fiber` **逐字同构**** ——
它只用到 `fun w => w.2`，与 `α × β` 的二元结构无关。 -/
theorem comap_snd_apply_eq_of_fiberN
    {f : (∀ i, fam i) × γ → ℝ}
    (hf : Measurable[MeasurableSpace.comap
      (fun w : (∀ i, fam i) × γ => w.2) inferInstance] f)
    (w₁ w₂ : (∀ i, fam i) × γ) (h : w₁.2 = w₂.2) :
    f w₁ = f w₂ := by
  by_contra hne
  have hlt : f w₁ < f w₂ ∨ f w₂ < f w₁ := lt_or_gt_of_ne hne
  rcases hlt with hlt | hlt
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

end FiberConst

section Step1

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*} [Fintype γ] [MeasurableSpace γ]
variable [MeasurableSpace ((∀ i, fam i) × γ)] [StandardBorelSpace ((∀ i, fam i) × γ)]

/-- ⭐⭐⭐⭐ **N 元**: `(κ ω).real s =ᵐ μ[1_s | m']`

**⭐⭐ 关键**：二元版调用的 `condExpKernel_real_apply` **完全一般**，
**故 N 元版只需**重新实例化****。 -/
theorem bridgeKernelStep1N
    (p : ((∀ i, fam i) × γ) → ℝ)
    (s : Set ((∀ i, fam i) × γ)) (hs : MeasurableSet s)
    (hsnd : Measurable (fun w : (∀ i, fam i) × γ => w.2)) :
    letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
    (fun ω => (((condExpKernel (Ω := (∀ i, fam i) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)) ω).real s))
      =ᵐ[weightedCountN p]
      (weightedCountN p)[s.indicator fun _ => 1
        | MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance] := by
  letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
  exact FateV2.Modeling.BridgeProofStep3.condExpKernel_real_apply
    (inferInstance : MeasurableSpace ((∀ i, fam i) × γ))
    (weightedCountN p)
    (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)
    (MeasurableSpace.comap_le_iff_le_map.mpr hsnd) hs

end Step1

end FateV2.Modeling.GenN