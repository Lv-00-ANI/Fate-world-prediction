import FateWorld.FateV2.Modeling.BridgeEquiv
open MeasureTheory ProbabilityTheory

/-!
  # Modeling · BridgeSingleFiber

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeSingleFiber.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BridgeEquiv
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §D2  ⭐⭐ **单纤维版逆方向**：`bridgeStatement p ⟹ CondIndepFin` 的逐 `z` 形式

  第 174 轮代理 C1 的观察：`Fate.BridgeReverse.bridge_to_condIndepFin` 中的
  `hz : ∀ z, (∑ x ∑ y, p ((x,y),z)) ≠ 0` **够用但偏强**。
  真正必要的是**单纤维**条件：只需对要证的那条 `z` 有纤维非零。

  本文件给出：
  1. `bridge_to_condIndepFin_at`：单纤维版本（`hz` 只对一个 `z` 要求）；
  2. `bridge_to_condIndepFin'`：由 (1) **推出** `∀ z` 版本 —— 验证 (1) 是推广。

  **证明**：逐点照搬 `Fate.BridgeReverse.lean` 的论证，唯一改动是把每一处
  `exact hz z` 换成 `exact hz`（因为 `z` 已经固定）。逐点等式在 `z` 处的
  两个 `≠ 0` 前提（`trim {a} ≠ 0` 与 `(weightedCount p).real (fiber z) ≠ 0`）
  都只依赖这一个纤维非零。
  =========================================================================== -/

namespace FateV2.Modeling
variable {α β γ : Type}
  [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
  [Countable α] [Countable β] [Countable γ]
  [MeasurableSingletonClass ((α × β) × γ)]

open FateV2.Modeling.FinMeasureBridge FateV2.Modeling.FinalB3

/-- ⭐⭐ **单纤维版**：`bridgeStatement p` ⟹ `CondIndepFin` 在固定 `z` 处的逐点等式，
    只需 `p` 的 `z` 纤维非零。 -/
theorem bridge_to_condIndepFin_at
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (hp : ∀ w, 0 ≤ p w)
    (z : γ) (hz : (∑ x : α, ∑ y : β, p ((x, y), z)) ≠ 0)
    (h : FateV2.Modeling.FinCondIndepMeasure.bridgeStatement p) :
    ∀ x y, p ((x, y), z) * (∑ x' : α, ∑ y' : β, p ((x', y'), z))
      = (∑ y' : β, p ((x, y'), z)) * (∑ x' : α, p ((x', y), z)) := by
  classical
  letI : IsFiniteMeasure (weightedCount p) := weightedCount_isFiniteMeasure p
  -- 桥的逐点形式
  have hunfold := (bridgeStatement_unfold_def (α := α) (β := β) (γ := γ) p).mp h
  intro x y
  set t1 : Set ((α × β) × γ) := (FateV2.Modeling.FinCondIndepMeasure.projX : (α × β) × γ → α) ⁻¹' {x} with ht1def
  set t2 : Set ((α × β) × γ) := (FateV2.Modeling.FinCondIndepMeasure.projY : (α × β) × γ → β) ⁻¹' {y} with ht2def
  have ht1 : MeasurableSet[MeasurableSpace.comap
      (FateV2.Modeling.FinCondIndepMeasure.projX : (α × β) × γ → α) inferInstance] t1 :=
    MeasurableSpace.measurableSet_comap.mpr ⟨{x}, measurableSet_singleton x, rfl⟩
  have ht2 : MeasurableSet[MeasurableSpace.comap
      (FateV2.Modeling.FinCondIndepMeasure.projY : (α × β) × γ → β) inferInstance] t2 :=
    MeasurableSpace.measurableSet_comap.mpr ⟨{y}, measurableSet_singleton y, rfl⟩
  have hae := hunfold t1 t2 ht1 ht2
  -- `∀ᵐ` 展开（对 `trim`）
  let hm' : MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ)
      (inferInstance : MeasurableSpace γ) ≤ (inferInstance : MeasurableSpace ((α × β) × γ)) :=
    MeasurableSpace.comap_le_iff_le_map.mpr
      (FateV2.Modeling.FinCondIndepMeasure.measurable_projZ (α := α) (β := β) (γ := γ))
  have hae' : ∀ a : (α × β) × γ,
      (@Measure.trim ((α × β) × γ)
        (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ)
          (inferInstance : MeasurableSpace γ))
        (inferInstance : MeasurableSpace ((α × β) × γ)) (weightedCount p) hm') {a} = 0 ∨
      ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
          (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
          a) (t1 ∩ t2)
        = ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
            (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
            a) t1
          * ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
            (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
            a) t2 :=
    (@FateV2.Modeling.FinalB3.ae_iff_forall_or_zero ((α × β) × γ)
      (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ)
        (inferInstance : MeasurableSpace γ))
      _
      (@Measure.trim ((α × β) × γ)
        (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ)
          (inferInstance : MeasurableSpace γ))
        (inferInstance : MeasurableSpace ((α × β) × γ)) (weightedCount p) hm')
      (fun a => ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
          (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
          a) (t1 ∩ t2)
        = ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
            (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
            a) t1
          * ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
            (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
            a) t2)).mp hae
  -- 在 `a = ((x,y),z)` 处取值
  have hpoint := hae' ((x, y), z)
  have htrim : (@Measure.trim ((α × β) × γ)
      (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ)
        (inferInstance : MeasurableSpace γ))
      (inferInstance : MeasurableSpace ((α × β) × γ)) (weightedCount p) hm')
      {((x, y), z)} ≠ 0 := by
    rw [FateV2.Modeling.FinalB3.trim_singleton_eq_fiber]
    rw [FateV2.Modeling.FinMeasureBridge.fiber_ne_zero_iff p hp z]
    exact hz
  have heq : ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
        (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
        ((x, y), z)) (t1 ∩ t2)
      = ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
          (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
          ((x, y), z)) t1
        * ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
          (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
          ((x, y), z)) t2 := by
    rcases hpoint with h0 | hP
    · exact absurd h0 htrim
    · exact hP
  -- 取 `real` 版等式
  have hrealeq : ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
        (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
        ((x, y), z)).real (t1 ∩ t2)
      = ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
          (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
          ((x, y), z)).real t1
        * ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
          (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
          ((x, y), z)).real t2 := by
    rw [Measure.real, Measure.real, Measure.real, heq, ENNReal.toReal_mul]
  -- 三个 `real` 层的商
  have hF : (weightedCount p).real (fiber z) ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]
    refine ⟨?_, measure_ne_top _ _⟩
    rw [fiber_ne_zero_iff p hp z]
    exact hz
  have hA : MeasurableSet t1 := by
    rw [ht1def]
    exact FateV2.Modeling.FinCondIndepMeasure.measurable_projX (measurableSet_singleton x)
  have hB : MeasurableSet t2 := by
    rw [ht2def]
    exact FateV2.Modeling.FinCondIndepMeasure.measurable_projY (measurableSet_singleton y)
  have hAB : MeasurableSet (t1 ∩ t2) := hA.inter hB
  have r1 := FateV2.Modeling.FinalB3.kernelValue_fiber_ratio p (t1 ∩ t2) hAB hp ((x, y), z) hF
  have r2 := FateV2.Modeling.FinalB3.kernelValue_fiber_ratio p t1 hA hp ((x, y), z) hF
  have r3 := FateV2.Modeling.FinalB3.kernelValue_fiber_ratio p t2 hB hp ((x, y), z) hF
  -- 简化三个分子
  have hn1 : (∑ x' : α, ∑ y' : β,
      (if ((x', y'), z) ∈ t1 ∩ t2 then p ((x', y'), z) else 0)) = p ((x, y), z) := by
    rw [ht1def, ht2def]
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
      FateV2.Modeling.FinCondIndepMeasure.projX, FateV2.Modeling.FinCondIndepMeasure.projY]
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single y]
      · simp
      · intro y' _ hy'; simp [hy']
      · intro hy; exact absurd (Finset.mem_univ y) hy
    · intro x' _ hx'
      exact Finset.sum_eq_zero fun y' _ => by simp [hx']
    · intro hx; exact absurd (Finset.mem_univ x) hx
  have hn2 : (∑ x' : α, ∑ y' : β,
      (if ((x', y'), z) ∈ t1 then p ((x', y'), z) else 0))
      = ∑ y' : β, p ((x, y'), z) := by
    rw [ht1def]
    simp only [Set.mem_preimage, Set.mem_singleton_iff, FateV2.Modeling.FinCondIndepMeasure.projX]
    rw [Finset.sum_eq_single x]
    · simp
    · intro x' _ hx'
      exact Finset.sum_eq_zero fun y' _ => by simp [hx']
    · intro hx; exact absurd (Finset.mem_univ x) hx
  have hn3 : (∑ x' : α, ∑ y' : β,
      (if ((x', y'), z) ∈ t2 then p ((x', y'), z) else 0))
      = ∑ x' : α, p ((x', y), z) := by
    rw [ht2def]
    simp only [Set.mem_preimage, Set.mem_singleton_iff, FateV2.Modeling.FinCondIndepMeasure.projY]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [Finset.sum_eq_single y]
    · simp
    · intro y' _ hy'; simp [hy']
    · intro hy; exact absurd (Finset.mem_univ y) hy
  have hM : (∑ x' : α, ∑ y' : β, p ((x', y'), z)) ≠ 0 := hz
  -- 合成 ℝ 层的等式
  rw [r1, r2, r3, hn1, hn2, hn3] at hrealeq
  -- `p/M = (A/M)*(B/M)` ⟹ `p*M = A*B`
  have h := hrealeq
  field_simp at h
  linarith [h]

/-- ⭐⭐ **由单纤维版推出 `∀ z` 版本**（验证前面的定理是推广）。 -/
theorem bridge_to_condIndepFin'
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (hp : ∀ w, 0 ≤ p w)
    (hz : ∀ z : γ, (∑ x : α, ∑ y : β, p ((x, y), z)) ≠ 0)
    (h : FateV2.Modeling.FinCondIndepMeasure.bridgeStatement p) :
    FateV2.Modeling.FiniteCondIndep.CondIndepFin p := by
  intro x y z
  rw [FateV2.Modeling.FiniteCondIndep.margZ, FateV2.Modeling.FiniteCondIndep.margXZ,
    FateV2.Modeling.FiniteCondIndep.margYZ]
  exact bridge_to_condIndepFin_at p hp z (hz z) h x y

end FateV2.Modeling