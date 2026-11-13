import FateWorld.Legacy.NaryIndex
import FateWorld.Legacy.NaryFin2

/-! ===========================================================================
  §GenNIndexCheck  machine check that every theorem named in `NaryIndex` exists

  A documentation module is only trustworthy if its claims are checked.  This
  file `#check`s every declaration cited in the `NaryIndex` docstring, so that a
  rename or removal anywhere in the chain breaks the build here.

  Note: `#check` only verifies that the *name* resolves; it does not re-prove
  anything.  Each cited theorem is separately proved in its own module and
  audited in `SigCheck.lean`.
  =========================================================================== -/

namespace Fate.GenN

open MeasureTheory ProbabilityTheory

-- ⭐ Step 1: the joint numerator as an indicator sum.
#check @Fate.GenN.joint_real_eq_indicator_sum

-- ⭐ Step 1 (ingredient): fiber decomposition of `mu.real`.
#check @Fate.GenN.real_eq_sum_of_fiber

-- ⭐ Step 1 (ingredient): the joint set's membership identity.
#check @Fate.GenN.mem_iInter_coordSet_finset

-- ⭐ Step 2: the single-coordinate numerator as a marginal sum.
#check @Fate.GenN.coordSet_real_eq_marg_sum

-- ⭐ Step 2 (ingredient): marginal sums become fiber sums.
#check @Fate.GenN.sum_marg_eq_fiberwise

-- ⭐ Step 3: the algebraic factorisation.
#check @Fate.GenN.product_factorize

-- ⭐ Step 3 (ingredient): `CondIndepN` sum factorisation.
#check @Fate.GenC3.condIndepN_sum_factorize

-- ⭐ Step 4: the fiber mass is the sum of `p` over the fiber (uses `hp`).
#check @Fate.GenN.fiberN_real_eq_sum'

-- ⭐ Step 4 (ingredient): `NMass` as a slice sum.
#check @Fate.GenN.NMass_eq_sum

-- ⭐ Step 5: the joint kernel value times the mass.
#check @Fate.GenN.kernelValue_iInter_coordSet_mul

-- ⭐ Step 5: the single-coordinate kernel value times the mass.
#check @Fate.GenN.kernelValue_coordSet_mul

-- ⭐ Step 6: the closing algebraic step.
#check @Fate.GenN.bridge_close

-- ⭐ Step 6 (ingredient): the cancellation.
#check @Fate.GenN.cancel_mass_pow

-- ⭐⭐ Layer 1: single anchor, finset parameters.
#check @Fate.GenN.nary_bridge_final_one_line

-- ⭐⭐ Layer 2: `∀ a`, finset parameters.
#check @Fate.GenN.nary_bridge_pointwise_all

-- ⭐⭐ Layer 3: `∀ a`, arbitrary set parameters.
#check @Fate.GenN.nary_bridge_generic

end Fate.GenN

/-! ## §Wire R-27 跨模块组合定理（`NaryIndex` §GenNWire）的机器核对

本节 `#check` 的每一条都由 `Fate/NaryIndex.lean` 证明；它们把 N 元链中
彼此孤立的模块**串联消费**（`NaryAssembly` × `NaryMassLink`、
`NaryFiberDecomp`、`NaryAlgebra`、`NaryClose` × `NaryCancel`、
`NaryTrim` × `NaryKernel2`、`NaryMargSum`）。
-/

namespace Fate.GenN

-- ⭐⭐ 测度层纤维质量 = 代数层 `NMass`（`NaryAssembly` + `NaryMassLink`）。
#check @Fate.GenN.fiberN_real_eq_NMass

-- ⭐⭐ `coordSet` 的实值测度 = 双层切片和（`NaryRealSum`）。
#check @Fate.GenN.coordSet_real_eq_double_sum

-- ⭐⭐ `NMass` 逐点非负（`NaryMassLink`）。
#check @Fate.GenN.NMass_nonneg_of_nonneg

-- ⭐⭐ `|ι| = 2` 时求和因子化退化为一次幂（`NaryAlgebra`）。
#check @Fate.GenN.condIndepN_sum_factorize_card_two

-- ⭐⭐⭐ produced 形状 ⟹ `M^n` 乘法形状（`NaryClose` × `NaryCancel`）。
#check @Fate.GenN.mul_pow_card_of_produced

-- ⭐⭐⭐ 两条闭合路径汇合于同一恒等式。
#check @Fate.GenN.produced_shape_meets_cancel_shape

-- ⭐⭐⭐ produced 闭合与 `M^n` 形式的合取形式。
#check @Fate.GenN.bridge_close_produced_and_pow

-- ⭐⭐⭐⭐ `m'`-可测函数在纤维上取常值（`NaryTrim` × `NaryKernel2`）。
#check @Fate.GenN.fiberN_subset_of_comap_measurable

-- ⭐⭐⭐ 指示和 = 边际和（`NaryMargSum`，方向相反）。
#check @Fate.GenN.sum_ite_mem_eq_sum_marg

-- ⭐⭐⭐ 过滤器嵌套吸收（`NaryMargSum`）。
#check @Fate.GenN.sum_filter_mem_filter_eq

end Fate.GenN

/-! ## §Wire2 `NaryFin2` 的声明进入核对链（R-27）

`NaryFin2` 自身 `import Fate.NaryIndex`，故它**不能**被 `NaryIndex` 反向消费
（会形成循环）。它的唯一自然下游是 `NaryIndex`，因此本文件是能引用它的
最上层模块；下面把它唯一的定理纳入机器核对。
-/

namespace Fate.GenN

-- ⭐⭐⭐ `|ι| = 2` 时 `CondIndepN` 的逐点乘积形状（`NaryFin2`）。
#check @Fate.GenN.condIndepN_fin2_shape

end Fate.GenN
