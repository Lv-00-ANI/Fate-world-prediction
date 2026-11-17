import FateWorld.FateV2.Modeling.NaryBridgeMulti
/-!
  # Modeling · NaryRealSum

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NaryRealSum.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NaryBridgeMulti
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenNRealSum ⭐⭐⭐⭐ **`μ.real` = 真实求和**（**N 元桥的关键桥梁**，第 189 轮）

  ## 核心定理

  `(weightedCountN p).real t = ∑ xs, ∑ z, (if (xs,z) ∈ t then p (xs,z) else 0)`

  ## ⚠⚠ 为什么需要 `hp : ∀ w, 0 ≤ p w`

  **这**正是 `hp` **真正必需**的地方**（第 177 轮 `GuardNecessary` 的反例佐证）：

  - `weightedCountN` 用 `ENNReal.ofReal`
  - 而 `ENNReal.toReal (ENNReal.ofReal x) = max x 0`
  - **只有当 `x ≥ 0` 时它才等于 `x`**

  ⟹ **若 `p` 在某点为负，`μ.real` 会把该点的系数**变成 `0`（而非保留负值）**，
  「核值 = 条件概率」的语义随之崩塌。

  ## ⭐ 证明

  1. `Measure.real` 展开为 `ENNReal.toReal`
  2. `weightedCountN_apply` 给出嵌套求和的显式形式
  3. `ENNReal.toReal_sum`（两层）把 `toReal` 提进求和（需每项有限）
  4. 每个项上 `ENNReal.toReal_ofReal (hp _)` 消去 `ofReal ∘ toReal`
  =========================================================================== -/

namespace FateV2.Modeling.GenN

open MeasureTheory ProbabilityTheory

section RealEqSum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*} [Fintype γ] [MeasurableSpace γ]
variable [MeasurableSpace ((∀ j, fam j) × γ)]
variable [MeasurableSingletonClass ((∀ j, fam j) × γ)]

omit [MeasurableSpace γ] in
/-- ⭐⭐⭐⭐ **`μ.real` = 真实求和**（**需要 `hp : ∀ w, 0 ≤ p w`**）。

**⚠⚠ 这是 `hp` **真正必需**的地方** ——
`ENNReal.toReal (ENNReal.ofReal x) = max x 0`，**只有 `x ≥ 0` 时才等于 `x`**。 -/
theorem weightedCountN_real_eq_sum
    (p : ((∀ j, fam j) × γ) → ℝ)
    (hp : ∀ w, 0 ≤ p w)
    (t : Set ((∀ j, fam j) × γ)) [DecidablePred (· ∈ t)] :
    (weightedCountN p).real t
      = ∑ xs : (∀ j, fam j), ∑ z : γ,
          (if (xs, z) ∈ t then p (xs, z) else 0) := by
  rw [Measure.real, weightedCountN_apply]
  rw [ENNReal.toReal_sum]
  swap
  · intro xs _
    exact ENNReal.sum_ne_top.mpr (fun z _ => by
      by_cases h : (xs, z) ∈ t
      · rw [if_pos h]; exact ENNReal.ofReal_ne_top
      · rw [if_neg h]; exact ENNReal.zero_ne_top)
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  rw [ENNReal.toReal_sum]
  swap
  · intro z _
    by_cases h : (xs, z) ∈ t
    · rw [if_pos h]; exact ENNReal.ofReal_ne_top
    · rw [if_neg h]; exact ENNReal.zero_ne_top
  refine Finset.sum_congr rfl (fun z _ => ?_)
  by_cases h : (xs, z) ∈ t
  · simp only [h, if_true, ENNReal.toReal_ofReal (hp _)]
  · simp only [h, if_false, ENNReal.toReal_zero]

end RealEqSum

end FateV2.Modeling.GenN
