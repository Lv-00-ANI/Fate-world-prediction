import FateWorld.FateV2.Modeling.NaryMeasure
/-!
  # Modeling · NaryTrim

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NaryTrim.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NaryMeasure
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenNTrim ⭐⭐⭐⭐⭐ **N 元的 `trim` 判据**（**N 元桥的第二块砖**，第 182 轮）

  **这是第 178 轮代理 G4 缺口清单的**第二项**。**

  ## 核心事实

  `(μ.trim m') {a} = μ (fiberN a.2)`，其中 `m' = comap (取第二分量)`。

  ## ⚠ 关键实例陷阱

  `measurable_snd` **要求完整的 `Prod.instMeasurableSpace`**，
  而项目的 `MeasurableSpace ((∀ i, fam i) × γ)` 是**独立声明的实例**
  ⟹ **`measurable_snd` 在 N 元情形**不能直接用****，
  故 `trimN_singleton_eq_fiberN` 把 `hsnd : Measurable (·.2)` 作为**显式前提**。

  ## 证明结构（照搬二元版 `BridgeFinal.trim_singleton_eq_fiber`）

  - **`≤`**：`trim {a} ≤ trim (fiberN a.2) = μ (fiberN a.2)`（后者 `m'`-可测）
  - **`≥`**：外测度下确界 —— 任何含 `a` 的 `m'`-可测集含整条纤维
  =========================================================================== -/

namespace FateV2.Modeling.GenN

open MeasureTheory

section Structural

variable {ι : Type*}
variable {fam : ι → Type*}
variable {γ : Type*} [MeasurableSpace γ]

/-- ⭐⭐ **N 元的纤维饱和结构引理**：任何含 `a` 的 `m'`-可测集必含整条 `fiberN a.2`。

**⚠ 因为 `m' = comap (取第二分量)`，其可测集都是**纤维的并****。 -/
theorem comap_snd_mem_fiberN
    {s : Set ((∀ i, fam i) × γ)}
    (hs : MeasurableSet[MeasurableSpace.comap
      (fun w : (∀ i, fam i) × γ => w.2) inferInstance] s)
    {a : (∀ i, fam i) × γ} (ha : a ∈ s) :
    {w : (∀ i, fam i) × γ | w.2 = a.2} ⊆ s := by
  obtain ⟨S, _, hS⟩ := (MeasurableSpace.measurableSet_comap).mp hs
  rw [← hS] at ha ⊢
  intro w hw
  have hw2 : w.2 = a.2 := by simpa [fiberN] using hw
  show w.2 ∈ S
  rw [hw2]
  exact ha

end Structural

section FiberMeasurable

variable {ι : Type*}
variable {fam : ι → Type*}
variable {γ : Type*} [MeasurableSpace γ] [MeasurableSingletonClass γ]

/-- ⭐ **`fiberN c` 是 `m'`-可测的**（它是 `{c}` 的原像）。 -/
theorem fiberN_measurable_comap (c : γ) :
    MeasurableSet[MeasurableSpace.comap
      (fun w : (∀ i, fam i) × γ => w.2) inferInstance] (fiberN c) :=
  MeasurableSpace.measurableSet_comap.2 ⟨{c}, measurableSet_singleton c, rfl⟩

end FiberMeasurable

section TrimCriterion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*} [MeasurableSpace γ] [MeasurableSingletonClass γ]
variable [MeasurableSpace ((∀ i, fam i) × γ)]

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (fam i)] in
/-- ⭐⭐⭐⭐⭐ **N 元的 `trim` 判据**：`(μ.trim m'){a} = μ(fiberN a.2)`。 -/
theorem trimN_singleton_eq_fiberN
    (hsnd : Measurable (fun w : (∀ i, fam i) × γ => w.2))
    (μ : Measure ((∀ i, fam i) × γ)) (a : (∀ i, fam i) × γ) :
    μ.trim (MeasurableSpace.comap_le_iff_le_map.mpr hsnd) {a}
      = μ {w : (∀ i, fam i) × γ | w.2 = a.2} := by
  obtain hm : MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance
      ≤ (inferInstance : MeasurableSpace ((∀ i, fam i) × γ)) :=
    MeasurableSpace.comap_le_iff_le_map.mpr hsnd
  refine le_antisymm ?_ ?_
  · calc (μ.trim hm) {a}
        ≤ (μ.trim hm) {w : (∀ i, fam i) × γ | w.2 = a.2} := by
          refine measure_mono ?_
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          subst hw
          rfl
      _ = μ {w : (∀ i, fam i) × γ | w.2 = a.2} := trim_measurableSet_eq hm (fiberN_measurable_comap a.2)
  · have hkey : (μ.trim hm) {a} = @OuterMeasure.trim ((∀ i, fam i) × γ)
        (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)
        μ.toOuterMeasure {a} := by
      have h1 := toOuterMeasure_trim_eq_trim_toOuterMeasure μ hm
      have h2 : (@Measure.toOuterMeasure _ (MeasurableSpace.comap
            (fun w : (∀ i, fam i) × γ => w.2) inferInstance)
          (μ.trim hm)) {a} = (μ.trim hm) {a} := rfl
      rw [← h2, h1]
    have hexp : @OuterMeasure.trim ((∀ i, fam i) × γ)
        (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance)
        μ.toOuterMeasure {a}
        = ⨅ (t : Set ((∀ i, fam i) × γ)), ⨅ (_ : {a} ⊆ t),
            ⨅ (_ : MeasurableSet[MeasurableSpace.comap
              (fun w : (∀ i, fam i) × γ => w.2) inferInstance] t), μ t :=
      @OuterMeasure.trim_eq_iInf _ (MeasurableSpace.comap
        (fun w : (∀ i, fam i) × γ => w.2) inferInstance) μ.toOuterMeasure {a}
    rw [hkey, hexp]
    refine le_iInf fun t => le_iInf fun hsub => le_iInf fun ht => ?_
    exact measure_mono (comap_snd_mem_fiberN ht (hsub (Set.mem_singleton a)))

end TrimCriterion

end FateV2.Modeling.GenN
