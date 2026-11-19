import FateWorld.FateV2.Modeling.BridgeFinal
open MeasureTheory ProbabilityTheory

/-!
  # Modeling · BridgeEquiv

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeEquiv.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BridgeFinal
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §C2  ⭐⭐ **`CondIndepFin` 与 `bridgeStatement` 的等价**

  `→` 方向：`condIndepFin_to_bridge`（B3 已证）。

  `←` 方向（C1 的部分，本文件自含证明）：
  `bridgeStatement p` ⟹ `CondIndepFin p`（在 `hp : 0 ≤ p` 与
  `hz : ∀ z, ∑x∑y p ≠ 0` 之下）。

  **思路**：
  1. `bridgeStatement_unfold_def`：把桥化为对 `μ.trim hm'` 的逐点乘积等式；
  2. `ae_iff_forall_or_zero` + `trim_singleton_eq_fiber`：在单点
     `a = ((x,y),z)` 处，`trim {a} = μ(fiber z) ≠ 0` ⟹ 乘积等式在 `a` 处成立；
  3. `kernelValue_fiber_ratio`：三个核值 = 三个二重和之比；
  4. 取 `S1 = {x}`、`S2 = {y}` ⟹ `p((x,y),z)·M = A x · B y`，即
     `condIndepFin_pointwise_sum`，逐点即 `CondIndepFin`。
  =========================================================================== -/

namespace FateV2.Modeling
namespace GenC2

variable {α β γ : Type}
  [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
  [Countable α] [Countable β] [Countable γ]
  [MeasurableSingletonClass ((α × β) × γ)]

open FateV2.Modeling.FinMeasureBridge FateV2.Modeling.FinalB3

/-- ⭐⭐ **`bridgeStatement` ⟹ `CondIndepFin`**（`hp` 非负 + 纤维非零）。 -/
theorem bridge_to_condIndepFin
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (hp : ∀ w, 0 ≤ p w)
    (hz : ∀ z : γ, (∑ x : α, ∑ y : β, p ((x, y), z)) ≠ 0)
    (hb : FateV2.Modeling.FinCondIndepMeasure.bridgeStatement p) :
    FateV2.Modeling.FiniteCondIndep.CondIndepFin p := by
  classical
  letI : IsFiniteMeasure (weightedCount p) := weightedCount_isFiniteMeasure p
  -- 桥的逐点形式
  have hunfold := (bridgeStatement_unfold_def (α := α) (β := β) (γ := γ) p).mp hb
  -- 固定 `x y z`，取 `S1 = {x}`、`S2 = {y}`
  intro x y z
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
    exact hz z
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
    exact hz z
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
  have hM : (∑ x' : α, ∑ y' : β, p ((x', y'), z)) ≠ 0 := hz z
  -- 合成 ℝ 层的等式
  rw [r1, r2, r3, hn1, hn2, hn3] at hrealeq
  -- `p/M = (A/M)*(B/M)` ⟹ `p*M = A*B`
  have key : p ((x, y), z) * (∑ x' : α, ∑ y' : β, p ((x', y'), z))
      = (∑ y' : β, p ((x, y'), z)) * (∑ x' : α, p ((x', y), z)) := by
    have h := hrealeq
    field_simp at h
    linarith [h]
  -- 最终：`CondIndepFin` 的逐点形式
  rw [FateV2.Modeling.FiniteCondIndep.margZ, FateV2.Modeling.FiniteCondIndep.margXZ,
    FateV2.Modeling.FiniteCondIndep.margYZ]
  exact key

end GenC2

end FateV2.Modeling
/-! ## §顶层 **任务书要求的等价定理** -/

section TopLevel

open MeasureTheory ProbabilityTheory

/-! **⚠ universe 说明**：
1. `FateV2.Modeling.FinCondIndepMeasure.bridgeStatement`（`FinCondIndepMeasure.lean`）
   的定义只对 `α β γ` **处于同一个 universe** 的情形可陈述
   （内部 `StandardBorelSpace` 等实例要求同 universe）；
2. `FateV2.Modeling.FinalB3.condIndepFin_to_bridge`（`BridgeFinal.lean`）建立在
   `universe 0`（`{α β γ : Type}`）上。

⟹ 本等价定理也落在 **`universe 0`** 上，**这是 `bridgeStatement`
与 B3 定理的共同定义域，而非本定理额外添加的限制**。
-/

variable {α β γ : Type}

/-- ⭐⭐ **`CondIndepFin` 与 `bridgeStatement` 在非负 + 纤维非零条件下等价**。

- `→`：`condIndepFin_to_bridge`（B3 已证）
- `←`：`FateV2.Modeling.GenC2.bridge_to_condIndepFin`（本文件自含证明）
-/
theorem condIndepFin_iff_bridge [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
    [Countable α] [Countable β] [Countable γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (hp : ∀ w, 0 ≤ p w)
    (hz : ∀ z : γ, (∑ x : α, ∑ y : β, p ((x, y), z)) ≠ 0) :
    FateV2.Modeling.FiniteCondIndep.CondIndepFin p ↔ FateV2.Modeling.FinCondIndepMeasure.bridgeStatement p := by
  constructor
  · intro hcond
    exact FateV2.Modeling.FinalB3.condIndepFin_to_bridge p hp hcond
  · intro hb
    exact FateV2.Modeling.GenC2.bridge_to_condIndepFin p hp hz hb

end TopLevel
