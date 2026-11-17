import FateWorld.FateV2.Modeling.NaryTrim
/-!
  # Modeling · NaryKernel

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NaryKernel.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NaryTrim
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenNKernel ⭐⭐⭐⭐ **N 元的核值工具**（**N 元桥的第三块砖**，第 183 轮）

  **这是第 178 轮代理 G4 缺口清单的**最后一项**。**

  ## 二元 → N 元的对应表

  | 二元（`BridgeKernel`） | N 元（本文件） |
  |---|---|
  | `setIntegral_indicator_one` | `setIntegral_indicator_oneN` |
  | `setIntegral_fiber_const_direct` | `setIntegral_fiberN_const` |
  | `integral_const_over_set` | **原样可用**（不依赖二元结构）|

  ## ⚠ 实例陷阱

  与 `NaryTrim` 相同：`MeasurableSpace ((∀ i, fam i) × γ)` 是**独立声明的实例**，
  故 `Measurable (·.2)` 作为**显式前提** `hsnd` 传入。

  ## ⚠ `omit` 的正确用法（第 182 轮确立）

  `omit [...] in` **必须放在 doc-comment 之前**：
  ```
  omit [...] in
  /-- 文档 -/
  theorem ...
  ```
  =========================================================================== -/

namespace FateV2.Modeling.GenN

open MeasureTheory

section IndicatorIntegral

variable {ι : Type*}
variable {fam : ι → Type*}
variable {γ : Type*} [MeasurableSpace γ]
variable [MeasurableSpace ((∀ i, fam i) × γ)]

omit [MeasurableSpace γ] in
/-- ⭐ **指示函数在可测集上的积分 = 交集的实值测度**（N 元版）。

**⚠ 这是二元 `setIntegral_indicator_one` 的**逐字推广**** ——
它只依赖 `Set.indicator` 与 `Measure.real`，**与 `α × β` 的二元结构无关**。 -/
theorem setIntegral_indicator_oneN
    (μ : Measure ((∀ i, fam i) × γ)) (s t : Set ((∀ i, fam i) × γ))
    (ht : MeasurableSet t) :
    ∫ w in s, t.indicator (fun _ => (1:ℝ)) w ∂μ = μ.real (s ∩ t) := by
  rw [MeasureTheory.setIntegral_indicator ht]
  rw [MeasureTheory.setIntegral_const]
  simp [smul_eq_mul]

end IndicatorIntegral

section FiberConstIntegral

variable {ι : Type*}
variable {fam : ι → Type*}
variable {γ : Type*} [MeasurableSpace γ] [MeasurableSingletonClass γ]
variable [MeasurableSpace ((∀ i, fam i) × γ)]
variable [MeasurableSingletonClass ((∀ i, fam i) × γ)]

omit [MeasurableSingletonClass ((∀ i, fam i) × γ)] in
/-- ⭐⭐ **纤维上的常数积分**（N 元版）：`∫ over fiberN z of g = μ.real(fiberN z) * c`。

**⚠ 这是二元 `setIntegral_fiber_const_direct` 的**逐字推广****。 -/
theorem setIntegral_fiberN_const
    (μ : Measure ((∀ i, fam i) × γ))
    (hsnd : Measurable (fun w : (∀ i, fam i) × γ => w.2))
    (g : (∀ i, fam i) × γ → ℝ) (z : γ) (c : ℝ)
    (hconst : ∀ w ∈ fiberN z, g w = c) :
    ∫ w in (fiberN z), g w ∂μ = μ.real (fiberN z) * c := by
  have hmeas : @MeasurableSet ((∀ i, fam i) × γ) (inferInstance) (fiberN z) := by
    have : MeasurableSet[MeasurableSpace.comap
        (fun w : (∀ i, fam i) × γ => w.2) inferInstance] (fiberN z) :=
      MeasurableSpace.measurableSet_comap.2 ⟨{z}, measurableSet_singleton z, rfl⟩
    exact (MeasurableSpace.comap_le_iff_le_map.mpr hsnd) _ this
  have h1 : ∫ w in (fiberN z), g w ∂μ = ∫ w in (fiberN z), c ∂μ := by
    apply MeasureTheory.setIntegral_congr_fun hmeas
    intro w hw
    exact hconst w hw
  rw [h1, MeasureTheory.setIntegral_const]
  simp [smul_eq_mul]

end FiberConstIntegral

end FateV2.Modeling.GenN
