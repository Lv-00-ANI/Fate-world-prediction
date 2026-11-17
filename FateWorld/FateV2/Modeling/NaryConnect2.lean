import FateWorld.FateV2.Modeling.NaryConnect
open MeasureTheory ProbabilityTheory
namespace FateV2.Modeling.GenN

/-!
  # Modeling · NaryConnect2

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NaryConnect2.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NaryConnect
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-- ⭐ **`coordSet` 上的可判定性**。 -/
instance coordSet_decidablePred {ι : Type*} {fam : ι → Type*} {γ : Type*}
    (i : ι) (S : Set (fam i)) [DecidablePred (· ∈ S)] :
    DecidablePred (· ∈ (coordSet i S : Set ((∀ j, fam j) × γ))) :=
  fun w => inferInstanceAs (Decidable (w.1 i ∈ S))

section WeightedCountOnCoordSet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*} [Fintype γ] [MeasurableSpace γ]
variable [MeasurableSpace ((∀ j, fam j) × γ)]
variable [MeasurableSingletonClass ((∀ j, fam j) × γ)]

omit [MeasurableSpace γ] in
/-- ⭐⭐ **`weightedCountN` 在 `coordSet` 上的显式求值**（**填补缺口 1**）。 -/
theorem weightedCountN_coordSet
    (p : ((∀ j, fam j) × γ) → ℝ)
    (i : ι) (S : Set (fam i)) [DecidablePred (· ∈ S)] :
    weightedCountN p (coordSet i S) =
      ∑ xs : (∀ j, fam j), ∑ z : γ,
        (if xs i ∈ S then ENNReal.ofReal (p (xs, z)) else 0) := by
  rw [weightedCountN_apply]
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  refine Finset.sum_congr rfl (fun z _ => ?_)
  show (if (xs i ∈ S) then ENNReal.ofReal (p (xs, z)) else 0)
      = (if xs i ∈ S then ENNReal.ofReal (p (xs, z)) else 0)
  rfl

end WeightedCountOnCoordSet

end FateV2.Modeling.GenN
