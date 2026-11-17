import FateWorld.FateV2.Modeling.CondIndepN
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Measure.Dirac

/-!
  # Modeling · NaryMeasure

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NaryMeasure.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：CondIndepN
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenN ⭐⭐⭐ **N 元加权计数测度**（**N 元桥的第一块砖**，第 180 轮）

  **参考** `Fate/FinMeasureBridge.lean` 的 `weightedCount`（二元）。
  **本文件把它推广到任意有限下标族 `ι`**（含 `ι` 为空的情形）。

  ## ⚠ 两个实例陷阱（本轮查明）

  1. **`import Mathlib.Data.Fintype.Pi` 是必需的** ——
     否则 `Fintype ((∀ i, fam i))` **无法合成**。
  2. **`[DecidableEq ι]` 是必需的** ——
     因为 `DecidableEq ((∀ i, fam i))` 依赖它。

  ## ⭐ 关于实例的谨慎处理

  每个引理包在**独立的 `section`**，只声明它**实际需要**的实例 ——
  这样**不会**引入「未使用的 section 变量」警告，
  **也不必用** `set_option linter.unusedSectionVars false`
  （第 173 轮代理 C5 审核指出该设置会导致**签名漂移无人察觉**）。
  =========================================================================== -/

namespace FateV2.Modeling.GenN

open MeasureTheory

section Def

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*} [Fintype γ] [MeasurableSpace γ]
variable [MeasurableSpace ((∀ i, fam i) × γ)]

/-- ⭐ **N 元加权计数测度**：每个点 `(xs, z)` 上的质量是 `ofReal (p (xs, z))`。 -/
noncomputable def weightedCountN
    (p : ((∀ i, fam i) × γ) → ℝ) : Measure ((∀ i, fam i) × γ) :=
  ∑ xs : (∀ i, fam i), ∑ z : γ, ENNReal.ofReal (p (xs, z)) • Measure.dirac (xs, z)

end Def

section FiniteMeasure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*} [Fintype γ] [MeasurableSpace γ]
variable [MeasurableSpace ((∀ i, fam i) × γ)]

omit [MeasurableSpace γ] in
/-- ⭐ `weightedCountN` 是**有限测度**。 -/
theorem weightedCountN_isFiniteMeasure (p : ((∀ i, fam i) × γ) → ℝ) :
    IsFiniteMeasure (weightedCountN p) := by
  rw [isFiniteMeasure_iff]
  simp only [weightedCountN]
  simp only [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _),
    mul_one]
  exact ENNReal.sum_lt_top.mpr (fun xs _ =>
    ENNReal.sum_lt_top.mpr (fun z _ => ENNReal.ofReal_lt_top))

end FiniteMeasure

section ApplyValue

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*} [Fintype γ] [MeasurableSpace γ]
variable [MeasurableSpace ((∀ i, fam i) × γ)]
variable [MeasurableSingletonClass ((∀ i, fam i) × γ)]

omit [MeasurableSpace γ] in
/-- ⭐ **任意集合上的显式值**（**核心工具**）。 -/
theorem weightedCountN_apply (p : ((∀ i, fam i) × γ) → ℝ)
    (s : Set ((∀ i, fam i) × γ)) [DecidablePred (· ∈ s)] :
    weightedCountN p s = ∑ xs, ∑ z, (if (xs, z) ∈ s then ENNReal.ofReal (p (xs, z)) else 0) := by
  simp only [weightedCountN]
  simp only [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Measure.dirac_apply]
  by_cases h : (xs, z) ∈ s
  · simp [h]
  · simp [h]

end ApplyValue

/-- ⭐ **N 元纤维**：给定 `z`，即「第二分量为 `z`」。

⚠ 这是二元 `fiber`（`{w | w.2 = c}`）的**逐字推广** ——
`projZ` 在 N 元情形仍是「取第二分量」（`(∀ i, fam i) × γ → γ`）。 -/
def fiberN {ι : Type*} {fam : ι → Type*} {γ : Type*} (z : γ) :
    Set ((∀ i, fam i) × γ) := {w | w.2 = z}

end FateV2.Modeling.GenN
