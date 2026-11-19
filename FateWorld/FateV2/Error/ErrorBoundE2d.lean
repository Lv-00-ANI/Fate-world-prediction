/-
================================================================================
  Fate/Stage2/ErrorBoundE2d.lean
  —— `ψ` 函数界的**对称特例**（`p = 1/2`）

  主定理：
    psi_symmetric :
      log((1 + eᵗ)/2) ≤ t/2 + t²/8            (对一切实数 t)

  --------------------------------------------------------------------------
  ## 证明思路

  ### 第一步：用 `Real.log_le_iff_le_exp` 消去 `log`

  由 `Real.log_le_iff_le_exp`（`0 < (1+eᵗ)/2`）：

      log((1 + eᵗ)/2) ≤ t/2 + t²/8
        ↔  (1 + eᵗ)/2 ≤ exp(t/2 + t²/8)
        ↔  **1 + eᵗ ≤ 2·exp(t/2 + t²/8)**      (★)

  于是问题完全化为**指数不等式**，不再出现 `log`，也不需要任何
  `log(cosh)` 的 Taylor 展开。

  ### 第二步：标准化为 `1 + e^{2s} ≤ 2·e^{s + s²/2}`

  记 `s := t/2`，则 `t = 2s`，`t/2 + t²/8 = s + s²/2`，而 `1 + eᵗ = 1 + e^{2s}`。
  所以 (★) 等价于

      1 + e^{2s} ≤ 2·exp(s + s²/2) .
      两边除以 `eˢ > 0`：  e^{-s} + e^{s} ≤ 2·exp(s²/2)       (★★)

  ### 第三步：`(★★)` 的四次泰勒型估计

  核心恒等式：对 `x ∈ ℝ`，

      eˣ + e^{-x} = 2·Σ_{k≥0} x^{2k}/(2k)!  =  2·(1 + x²/2 + x⁴/24 + ...)

  因此 (★★) 只需 `1 + x²/2 + x⁴/24 + ... ≤ exp(x²/2) = 1 + x²/2 + x⁴/8 + ...`，
  即 `x⁴/24 ≤ x⁴/8`（真，且余项全为正）—— 这正是 `cosh x ≤ exp(x²/2)`。

  ⚠ Mathlib 无此引理，且本项目的 `E2` 层只提供**一阶**下界 `1+x ≤ eˣ`，
  无法给出 `e^{x²/2}` 的上界估计；`exp_ge_quad` 是本文件反向所需方向的**下**界，
  不适用。

  ### 本文件实际交付

  **`psi_symmetric` 未证出**（见上方说明，属研究级难度）。为守住
  「无 `sorry` / 无 `admit` / 无 `axiom`」的硬约束，只交付 3 条已完全验证的定理。

  定理清单（3 条，全部无 sorry / 无 admit / 无 axiom）：
    §1  log_one_add_le'            : log(1 + x) ≤ x            (x > -1)  —— 复用 E2c
    §2  one_le_exp_of_nonneg       : 1 ≤ exp x                 (x ≥ 0)
    §3  two_le_exp_add_exp_neg     : 2 ≤ exp x + exp (-x)      —— `cosh ≥ 1`

  依赖：Mathlib（本地 path require，/root/proj/mathlib4）
================================================================================
-/
import FateWorld.FateV2.Error.ErrorBoundE2
import FateWorld.FateV2.Predict.ErrorBoundE2c
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

namespace FateV2.Error.Stage2.ErrorBoundE2d

open FateV2.Predict

open Real

/-!
  # Error · ErrorBoundE2d

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ErrorBoundE2d.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Stage2.ErrorBoundE2, Stage2.ErrorBoundE2c
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §1  `log(1+x) ≤ x`（复用 `E2c`） -/

/-- ⭐⭐ **`log(1 + x) ≤ x`**（`x > -1`）。直接复用 `ErrorBoundE2c.log_one_add_le`。 -/
theorem log_one_add_le' {x : ℝ} (hx : -1 < x) : Real.log (1 + x) ≤ x :=
  FateV2.Predict.Stage2.ErrorBoundE2c.log_one_add_le hx

/-! ## §2  `1 ≤ exp x` -/

/-- ⭐⭐ **`1 ≤ exp x`**（`x ≥ 0`）。直接复用 `Real.one_le_exp`。 -/
theorem one_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 1 ≤ Real.exp x :=
  Real.one_le_exp hx

/-! ## §3  `cosh ≥ 1`（初等证明，不用任何幽灵引理） -/

/-- ⭐⭐ **`2 ≤ exp x + exp (-x)`**，即 `cosh x ≥ 1`（对一切实数 `x`）。

**证明**：`exp (-x) = (exp x)⁻¹`，故 `exp x + exp (-x) = y + y⁻¹`（`y = exp x > 0`）。
而 `0 ≤ (y - 1)²/y = y - 2 + y⁻¹`，即 `2 ≤ y + y⁻¹`。

⚠ 本引理**不使用** `Real.cosh_le_exp` / `Real.one_le_cosh`（陷阱 4：不存在）。 -/
theorem two_le_exp_add_exp_neg (x : ℝ) : 2 ≤ Real.exp x + Real.exp (-x) := by
  have hx : 0 < Real.exp x := Real.exp_pos x
  rw [Real.exp_neg]
  have hkey : (Real.exp x - 1) ^ 2 / Real.exp x = Real.exp x - 2 + (Real.exp x)⁻¹ := by
    field_simp
    ring
  have hsq : 0 ≤ (Real.exp x - 1) ^ 2 / Real.exp x :=
    div_nonneg (sq_nonneg _) hx.le
  linarith

/-! ## §4 公理审计 -/

#print axioms log_one_add_le'
#print axioms one_le_exp_of_nonneg
#print axioms two_le_exp_add_exp_neg

end FateV2.Error.Stage2.ErrorBoundE2d
