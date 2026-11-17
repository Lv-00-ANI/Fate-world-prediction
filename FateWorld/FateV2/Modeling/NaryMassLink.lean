import FateWorld.FateV2.Modeling.NaryAssembly
import Mathlib.Data.Fintype.Pi
import FateWorld.FateV2.Modeling.NaryMargSum
import FateWorld.FateV2.Modeling.NaryFinalBridge
import FateWorld.FateV2.Modeling.NaryAlgebra
/-!
  # Modeling · NaryMassLink

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NaryMassLink.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NaryAssembly, NaryMargSum, NaryFinalBridge, NaryAlgebra
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenNMass  `NMass` in slice form (round 197)

  ## Result

    NMass p z = sum xs, p xs z

  definitionally (unfolding `NMass`).

  This is the bridge between the **algebraic** side (`CondIndepN`, `NMass`,
  `marg`, all `Finset`-based) and the **measure** side (`weightedCountN`,
  `mu.real`), where `fiberN_real_eq_sum'` (round 196) gives

    mu.real(fiberN z) = sum xs, p (xs, z)

  So numerically, when `p >= 0`,

    NMass p z = mu.real(fiberN z)

  which is exactly the factor that appears in `condIndepN_sum_factorize`
  as `M^(n-1)` and in the kernel formulas as `M`.
  =========================================================================== -/

namespace FateV2.Modeling.GenN

open MeasureTheory ProbabilityTheory

section NMass

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)] [∀ i, DecidableEq (fam i)]
variable {γ : Type*}

omit [∀ i, DecidableEq (fam i)] in
/-- ⭐⭐⭐ **`NMass p z` is the sum of `p` over the slice** (definitional). -/
theorem NMass_eq_sum (p : Fate.GenC3.NJoint (ι := ι) fam γ) (z : γ) :
    Fate.GenC3.NMass p z = ∑ xs : (∀ j, fam j), p xs z :=
  rfl

end NMass

end FateV2.Modeling.GenN
