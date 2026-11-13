/-
=============================================================================
_step9_R1.lean  —  ⚠ **本文件的两个结论**（诚实的失败报告 + 修正后的真定理）

## 结论 1：题目给出的定理是**假的**（已用 Lean 验证出 `False`）

题目要求证明

    ∫ w in T, μ[t.indicator 1 | comap projZ] w ∂μ = ∫ w in T, t.indicator 1 w ∂μ

对**任意** `MeasurableSet T`（全 σ-代数 `m₀ = inferInstance`）。

**但 `setIntegral_condExp` 需要 `MeasurableSet[m] T`，其中 `m = comap projZ`**，
而 `m ≤ m₀` 是**单向**的（`LE MeasurableSpace` 的定义就是
`m₁ ≤ m₂ := ∀ s, MeasurableSet[m₁] s → MeasurableSet[m₂] s`），
**故 `MeasurableSet T` 不能反向推出 `MeasurableSet[m] T`**。

这**不是**技术障碍，而是**数学上命题本身为假**。反例见证：

* `α = Bool`、`β = Unit`、`γ = Unit`（全部离散、单点可测，满足全部假设）；
* `projZ : (Bool × Unit) × Unit → Unit` 是**常函数** ⟹ `comap projZ = ⊥`
  （见 `comap_projZ_unit_eq_bot`）；
* `p ≡ 1/2` ⟹ `weightedCount p = 2⁻¹·δ_((true,()),()) + 2⁻¹·δ_((false,()),())`
  是**概率测度**（见 `pBool_wc_eq`, `pBool_isProbabilityMeasure`）；
* 取 `t = T = {((true,()),())}`：

  - LHS `= ∫_{T} (∫_T 1 ∂μ) ∂μ = μ(T) · μ(T) = 1/4`
  - RHS `= ∫_{T} 1_T ∂μ = μ(T) = 1/2`
  - `1/4 ≠ 1/2` ⟹ 矛盾（见 `claim_implies_false`）。

**⚠ 这正是 §95 系列一直没有跨过的那道坎的根源**：`T` 必须是**纤维饱和**的
（即 `comap projZ`-可测），否则左右两边一般不等。

## 结论 2：**修正后的**真定理（本文件已完整证明，无 sorry）

把 `T` 的可测性换到 `m = comap projZ` 上，定理即成立 —— 且是
`setIntegral_condExp` 的**直接实例**：`test_setIntegral_condExp_fixed`。

（`hT` 在 `comap projZ` 下时**仍是**全 σ-代数可测的，故与项目的用法兼容：
`MeasurableSet[m] T → MeasurableSet T` 由 `m ≤ m₀` 给出。）

## 附：题目原本想写的那种"八种写法"为什么全失败

不是实例推断问题（`m₀ := inferInstance` 已经钉死），而是
**最后一步 `hT` 的类型根本对不上**：

      hT : @MeasurableSet _ Prod.instMeasurableSpace T
      需要 : @MeasurableSet _ (comap projZ inferInstance) T

这是**把不可测集当可测集**的要求，任何 `letI` / `@` / `subst` 都变不出来。
=============================================================================
-/
import FateWorld.Legacy.BridgeKernel
open MeasureTheory ProbabilityTheory

/-! ## 0. 修正后的**真**定理（`setIntegral_condExp` 的直接实例，无 sorry） -/

/-- ⭐⭐⭐ **修正版**：把 `T` 的可测性放到 `m = comap projZ` 上，命题成立。

**这是 `setIntegral_condExp` 的直接实例**（关键：`m₀ := inferInstance` 钉死，
`m := comap projZ`，`hm` 由 `measurable_projZ` 给出）。 -/
theorem test_setIntegral_condExp_fixed [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : Fate.FiniteCondIndep.FinJoint α β γ)
    (t T : Set ((α × β) × γ)) (ht : MeasurableSet t)
    (hT : MeasurableSet[MeasurableSpace.comap
      (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance] T) :
    letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
      Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
    ∫ w in T, (Fate.FinMeasureBridge.weightedCount p)[t.indicator fun _ => (1:ℝ)
        | MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance] w
        ∂(Fate.FinMeasureBridge.weightedCount p)
      = ∫ w in T, t.indicator (fun _ => (1:ℝ)) w ∂(Fate.FinMeasureBridge.weightedCount p) := by
  letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
    Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
  exact setIntegral_condExp
    (m := MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)
    (m₀ := inferInstance)
    (μ := Fate.FinMeasureBridge.weightedCount p)
    (f := t.indicator fun _ => (1:ℝ)) (s := T)
    (hm := MeasurableSpace.comap_le_iff_le_map.mpr Fate.FinCondIndepMeasure.measurable_projZ)
    (hf := (integrable_const (μ := Fate.FinMeasureBridge.weightedCount p) (1:ℝ)).indicator ht)
    (hs := hT)

/-! ## 1. 反例的组件（全部已证，无 sorry） -/

namespace Fate.Step9R1

/-- 反例用的有限律：`Bool × Unit × Unit` 上均匀分布。 -/
noncomputable def pBool : Fate.FiniteCondIndep.FinJoint Bool Unit Unit := fun _ => (1:ℝ)/2

/-- `weightedCount pBool = 2⁻¹·δ_{true} + 2⁻¹·δ_{false}`。 -/
theorem pBool_wc_eq : (Fate.FinMeasureBridge.weightedCount pBool)
    = (2:ENNReal)⁻¹ • Measure.dirac ((true,()),())
      + (2:ENNReal)⁻¹ • Measure.dirac ((false,()),()) := by
  simp only [Fate.FinMeasureBridge.weightedCount, pBool]
  rw [Fintype.sum_bool]
  have h12 : ENNReal.ofReal (1/2 : ℝ) = (2:ENNReal)⁻¹ := by
    rw [show ((2:ENNReal)) = ENNReal.ofReal (2:ℝ) by norm_num]
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2)]
    norm_num
  simp only [h12]
  ext s
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  congr 1 <;> congr 1 <;> (first | rfl | simp)

/-- ⭐ **关键结构事实**：`γ = Unit` 时 `projZ` 是常函数，故 `comap projZ = ⊥`。 -/
theorem comap_projZ_unit_eq_bot :
    (MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (Bool × Unit) × Unit → Unit)
      inferInstance) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro s hs
  rw [MeasurableSpace.measurableSet_comap] at hs
  obtain ⟨t, -, rfl⟩ := hs
  by_cases ht : t = ∅
  · simp [ht]
  · obtain ⟨u, hu⟩ := Set.eq_empty_or_nonempty t |>.resolve_left ht
    have ht' : t = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true]
      rwa [Subsingleton.elim x u]
    simp [ht']

/-- `weightedCount pBool` 是概率测度。 -/
theorem pBool_isProbabilityMeasure :
    IsProbabilityMeasure (Fate.FinMeasureBridge.weightedCount pBool) := by
  constructor
  rw [pBool_wc_eq]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply, smul_eq_mul, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, mul_one]
  rw [← two_mul, ENNReal.mul_inv_cancel] <;> norm_num

/-- 单点质量。 -/
theorem pBool_singleton_true :
    (Fate.FinMeasureBridge.weightedCount pBool) {((true,()),())} = (2:ENNReal)⁻¹ := by
  rw [pBool_wc_eq]; simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul]

/-- ⭐⭐⭐ **题目原命题蕴涵 `False`**（故原命题**为假**）。

**反例**：`α = Bool`、`β = γ = Unit`、`p ≡ 1/2`、`t = T = {((true,()),())}`。
则 `comap projZ = ⊥`，`condExp_bot` 把条件期望压成常函数 `∫_T 1 ∂μ = 1/2`，
两边分别算得 `1/4` 与 `1/2`。 -/
theorem claim_implies_false
    (hclaim : ∀ (t T : Set ((Bool × Unit) × Unit)) (_ : MeasurableSet t)
        (_ : MeasurableSet T),
      letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount pBool) :=
        Fate.FinMeasureBridge.weightedCount_isFiniteMeasure pBool
      ∫ w in T, (Fate.FinMeasureBridge.weightedCount pBool)[t.indicator fun _ => (1:ℝ)
          | MeasurableSpace.comap
            (Fate.FinCondIndepMeasure.projZ : (Bool × Unit) × Unit → Unit) inferInstance] w
          ∂(Fate.FinMeasureBridge.weightedCount pBool)
        = ∫ w in T, t.indicator (fun _ => (1:ℝ)) w
          ∂(Fate.FinMeasureBridge.weightedCount pBool)) : False := by
  have hmeas : MeasurableSet ({((true,()),())} : Set ((Bool × Unit) × Unit)) :=
    MeasurableSet.singleton _
  have hkey := hclaim {((true,()),())} {((true,()),())} hmeas hmeas
  simp only [comap_projZ_unit_eq_bot] at hkey
  haveI := pBool_isProbabilityMeasure
  rw [condExp_bot] at hkey
  simp only [integral_indicator hmeas] at hkey
  simp only [setIntegral_const, smul_eq_mul, Measure.restrict_apply hmeas,
    Set.inter_self, pBool_singleton_true, Measure.real] at hkey
  norm_num [ENNReal.toReal_inv, ENNReal.toReal_ofNat] at hkey

end Fate.Step9R1
