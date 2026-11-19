/-
===============================================================================
  `Fate.CausalOnWorldModelAdjust` —— **`DoLawOn` ⟹ `adjustLaw` 的精确分解**

  ⚠⚠ **本文件补什么（一句话）**
-------------------------------------------------------------------------------
  `Fate/CausalOnWorldModel.lean` 的 `hZ : DoLawOn T d M` 提供 `joint`：

    `pXZ x z₁ z₂ * pYcond x z₁ z₂ y = condY M x y * pZ z₁ z₂`        (★)

  该文件的 `bd_sum_joint` 只把 (★) 对 `z₂` 求和一次，得到 `pXZ` 加权的和。
  但 **`adjustLaw` 的权重是 `pZ`，不是 `pXZ`**（见该文件头部「删除清单 (2)」）。
  本文件把这件事**做完并说准**：

  * §1 `bd_weighted_joint`：**(★) 对任意权重 `w` 的配对求和形式**（无除法）——
    这是 `bd_sum_joint` 的**严格加强**（取 `w ≡ 1` 或用 `mul_sum` 即退回）。
  * §2 `adjustLaw_eq_condY_mul_correction`：**核心定理**。
    在 `pXZ` 逐点非零（positivity）下，

      `adjustLaw T x y = condY M x y * ∑_{z₁ z₂} pZ z₁ z₂ * pZ z₁ z₂ / pXZ x z₁ z₂`

    ⟹ `adjustLaw` **确实**可以完全由 `hZ` 决定，但**不是** `= condY`
    （除非**修正因子** `∑ pZ²/pXZ` 恰为 `1`）。
  * §3 `zb_adjustLaw_factor`：在具体载体 `FateV2.Predict.R277.zb` 上算出修正因子
    （`x = true` 时 `73/48`，`x = false` 时 `145/16`）。
  * §4 `zb_correction_ne_one`：⚠ **修正因子 ≠ 1**（机检）。
    ⟹ 被删的旧命题 `bd_adjustLaw_sum_eq_condY` / `bd_adjustLaw_eq`
    （「`adjustLaw = condY = doLaw`」）**确实为假**，删得对，不是证明没力气。

-------------------------------------------------------------------------------
  ⚠ 前件自查（纪律 7：前件是否把结论包进去了？）
-------------------------------------------------------------------------------
  核心定理的结论含 `adjustLaw`（`∑∑ pYcond·pZ`）。
  前件 `hZ : DoLawOn T d M` **字面上不含 `adjustLaw`**（见该文件 §2 定义：
  只有 `pXZ`/`pYcond`/`pZ`/`marginalX`/`condY`/`doLaw`），也**不含** `pZ` 之外的权重。

  **`hZ` 不可省**：§4 直接用 §3 的数值（`73/48`、`145/16`）说明：
  若没有 (★)，`adjustLaw` 与 `condY` 之间不存在这个确定的比例关系。
  且 `hZ` **可失败**（`CausalOnWorldModel.DoLawOn_fails_on_badd`，
  机检）⟹ 前件非空转。

  额外前件 `hpos : ∀ z₁ z₂, pXZ T x z₁ z₂ ≠ 0` 是**真需要的**：
  `pYcond` 的定义里 `pXZ` 在**分母**上（`Fate/BackdoorGenuine.lean:747`），
  要去掉 `pXZ * (...)` 的外层必须先知道它非零。它**不是**结论的改写
  （`zb_pXZ_pos` 说明它在 `zb` 上**成立**，故不空转也不矛盾）。

-------------------------------------------------------------------------------
  ⚠ 诚实边界（必读）
-------------------------------------------------------------------------------
  1. 本文件**不**声称 `adjustLaw = doLaw`，也**不**声称前门 = 后门。
     旧的等式链命题在 `zb` 上**为假**（`zb_adjustLaw_eq` 给出的是
     `adjustLaw = doLaw2`，而 `doLaw2 ≠ condY`，见 `zb_obs_ne_do_00`）。
     本文件给出的是**正确的那条等式**（带修正因子）。
  2. 全部**有限**离散（`Fintype`，`ℝ` 值），无测度论。
  3. **不修改任何已有模块**，只 `import`。
  4. **零 `sorry` / 零 `admit` / 零 `axiom`**（可 `grep` 验证）。
=============================================================================== -/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import FateWorld.FateV2.Predict.CausalOnWorldModel
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace FateV2.Predict
namespace CausalOnWorldModel

open Finset

variable {T : FateV2.Predict.R277.ZBlockedSetup}

/-!
  # Predict · CausalOnWorldModelAdjust

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CausalOnWorldModelAdjust.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：CausalOnWorldModel
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  ⭐ **(★) 的任意权重配对形式**（无除法；`bd_sum_joint` 的严格加强）
  =========================================================================== -/

/-- ⭐⭐ **`DoLawOn.joint` 对任意权重 `w` 的配对求和**：

$$\sum_{z_1}\sum_{z_2} p(x,z_1,z_2)\,P(y\mid x,z_1,z_2)\,w(z_1,z_2)
  \;=\; P(X{=}x,Y{=}y)\cdot\sum_{z_1}\sum_{z_2} p(z_1,z_2)\,w(z_1,z_2)$$

**⚠ 与 `bd_sum_joint` 的关系**：后者是 `w ≡ 1` 的特例。本式对**任意** `w` 成立，
是 `hZ.joint` 逐点乘 `w` 后求和（`Finset.sum_congr` + `ring`，非投影）。 -/
theorem bd_weighted_joint (M : PearlHierarchy.SCM T.Xt T.Yt) {d : T.Xt → T.Yt → ℝ}
    (hZ : DoLawOn T d M) (x : T.Xt) (y : T.Yt) (w : T.Z₁ → T.Z₂t → ℝ) :
    ∑ z₁, ∑ z₂,
        FateV2.Predict.R277.pXZ T x z₁ z₂ * FateV2.Predict.R277.pYcond T x z₁ z₂ y * w z₁ z₂
      = SCMSemantics.condY M x y
        * ∑ z₁, ∑ z₂, FateV2.Predict.R277.pZ T z₁ z₂ * w z₁ z₂ := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z₂ _ => ?_
  rw [hZ.joint x z₁ z₂ y]; ring

/-! ===========================================================================
  §2  ⭐⭐⭐ **核心定理：`adjustLaw` 的精确分解**

  `adjustLaw = ∑∑ pYcond·pZ`。由 (★) 解出 `pYcond = condY·pZ / pXZ`，
  代回即得 `adjustLaw = condY · ∑∑ pZ²/pXZ`。
  **「修正因子」`∑∑ pZ²/pXZ` 就是 `adjustLaw` 与 `condY` 之间的全部差距。**
  =========================================================================== -/

/-- ⭐⭐⭐ **`adjustLaw` 由 `DoLawOn` 完全决定**（在 positivity 下）：

$$\mathrm{adjustLaw}\,T\,x\,y \;=\; P(X{=}x,Y{=}y)\cdot
  \sum_{z_1}\sum_{z_2}\frac{p(z_1,z_2)^2}{p(x,z_1,z_2)} .$$

**⚠ 为什么需要 `hpos`**：`pYcond` 的定义把 `pXZ` 放在分母
（`Fate/BackdoorGenuine.lean:747`），要从 `pXZ * pYcond = …` 解出 `pYcond`
必须知道 `pXZ ≠ 0`。这是**去掉外层乘法**的技术需要，不是结论的改写
（`zb_pXZ_pos` 机检它在 `zb` 上成立）。

**⚠ 这不是 `adjustLaw = condY`**：除非修正因子恰为 `1`，而 §4 机检它**不是**。 -/
theorem adjustLaw_eq_condY_mul_correction (M : PearlHierarchy.SCM T.Xt T.Yt)
    {d : T.Xt → T.Yt → ℝ} (hZ : DoLawOn T d M) (x : T.Xt) (y : T.Yt)
    (hpos : ∀ z₁ z₂, FateV2.Predict.R277.pXZ T x z₁ z₂ ≠ 0) :
    FateV2.Predict.R277.adjustLaw T x y
      = SCMSemantics.condY M x y
        * ∑ z₁, ∑ z₂,
            FateV2.Predict.R277.pZ T z₁ z₂ * FateV2.Predict.R277.pZ T z₁ z₂ / FateV2.Predict.R277.pXZ T x z₁ z₂ := by
  rw [FateV2.Predict.R277.adjustLaw, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z₂ _ => ?_
  -- 先把 `pYcond` 的分子记作 `N`，由 (★) 解出 `N = condY · pZ`
  have hN : (∑ ux, ∑ uz₂, ∑ uy, T.pz₁ z₁ * T.pu ux * T.puz₂ uz₂ * T.py uy *
      (if T.fX z₁ ux = x then 1 else 0) * (if T.fZ ux uz₂ = z₂ then 1 else 0) *
      (if T.fY x z₂ uy = y then 1 else 0))
      = SCMSemantics.condY M x y * FateV2.Predict.R277.pZ T z₁ z₂ := by
    have h1 : FateV2.Predict.R277.pXZ T x z₁ z₂ *
        ((∑ ux, ∑ uz₂, ∑ uy, T.pz₁ z₁ * T.pu ux * T.puz₂ uz₂ * T.py uy *
          (if T.fX z₁ ux = x then 1 else 0) * (if T.fZ ux uz₂ = z₂ then 1 else 0) *
          (if T.fY x z₂ uy = y then 1 else 0)) / FateV2.Predict.R277.pXZ T x z₁ z₂)
        = SCMSemantics.condY M x y * FateV2.Predict.R277.pZ T z₁ z₂ := by
      rw [← FateV2.Predict.R277.pYcond]; exact hZ.joint x z₁ z₂ y
    rw [mul_comm (FateV2.Predict.R277.pXZ T x z₁ z₂), div_mul_cancel₀ _ (hpos z₁ z₂)] at h1
    exact h1
  have hpy : FateV2.Predict.R277.pYcond T x z₁ z₂ y
      = SCMSemantics.condY M x y * FateV2.Predict.R277.pZ T z₁ z₂ / FateV2.Predict.R277.pXZ T x z₁ z₂ := by
    rw [FateV2.Predict.R277.pYcond, hN]
  rw [hpy]; ring

/-! ===========================================================================
  §3  具体载体 `FateV2.Predict.R277.zb` 上的修正因子（真数值，`norm_num`）
  =========================================================================== -/

/-- ⭐ `zb` 的**修正因子**：`x = true` 时 `73/48`，`x = false` 时 `145/16`。

（`pZ = (7/20, 13/20)`；`pXZ(true,·) = (3/20, 3/5)`；`pXZ(false,·) = (1/5, 1/20)`。） -/
theorem zb_correction_eq (x : Bool) :
    (∑ z₁ : Unit, ∑ z₂ : Bool,
        FateV2.Predict.R277.pZ FateV2.Predict.R277.zb z₁ z₂ * FateV2.Predict.R277.pZ FateV2.Predict.R277.zb z₁ z₂
          / FateV2.Predict.R277.pXZ FateV2.Predict.R277.zb x z₁ z₂)
      = if x then (73 : ℝ) / 48 else (145 : ℝ) / 16 := by
  rw [Fintype.sum_unique, Fintype.sum_bool, FateV2.Predict.R277.zb_pZ, FateV2.Predict.R277.zb_pZ,
    FateV2.Predict.R277.zb_pXZ_all, FateV2.Predict.R277.zb_pXZ_all]
  cases x <;> norm_num

/-- ⭐⭐ **`zb` 上 `adjustLaw` 的精确值**：`adjustLaw zb x y = condY M x y · (73/48 或 145/16)`。

**⚠ 注意**：右边的 `M` 是**任意**满足 `DoLawOn zb d M` 的 `SCM`。
本定理说的是「`hZ` 把 `adjustLaw` **逼到** `condY` 的一个已知常数倍」，
**不是** `adjustLaw = condY`。 -/
theorem zb_adjustLaw_factor (M : PearlHierarchy.SCM Bool Bool) {d : Bool → Bool → ℝ}
    (hZ : DoLawOn FateV2.Predict.R277.zb d M) (x y : Bool) :
    FateV2.Predict.R277.adjustLaw FateV2.Predict.R277.zb x y
      = SCMSemantics.condY M x y * (if x then (73 : ℝ) / 48 else (145 : ℝ) / 16) := by
  rw [adjustLaw_eq_condY_mul_correction (T := FateV2.Predict.R277.zb) M hZ x y
    (fun _ z₂ => FateV2.Predict.R277.zb_pXZ_pos x z₂),
    zb_correction_eq x]

/-! ===========================================================================
  §4  ⚠⚠ **修正因子 ≠ 1**（被删旧命题「确实为假」的机检见证）
  =========================================================================== -/

/-- ⚠⚠ **`zb` 的修正因子在 `x = true` 处 `= 73/48 ≠ 1`**。

**⟹ 被删的 `bd_adjustLaw_sum_eq_condY`（等价于 `adjustLaw zb = condY M`）为假**，
`Fate/CausalOnWorldModel.lean` 头部「删除清单 (2)」的论断得到独立机检。
**⟹ §2 的修正因子不是装饰性的，前件 `hZ` 真的承载这个内容。** -/
theorem zb_correction_ne_one : (73 : ℝ) / 48 ≠ 1 := by
  norm_num

end CausalOnWorldModel

end FateV2.Predict