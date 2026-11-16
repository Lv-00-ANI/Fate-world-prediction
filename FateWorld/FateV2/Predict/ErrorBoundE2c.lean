import FateWorld.FateV2.Error.ErrorBoundE2
import FateWorld.FateV2.Error.ErrorBoundE2b
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
  # Predict · ErrorBoundE2c

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ErrorBoundE2c.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Stage2.ErrorBoundE2, Stage2.ErrorBoundE2b
  - 补充 open 域：FateV2.Error
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# `Fate/Stage2/ErrorBoundE2c` —— `𝖤₂` 的 `log` 基础

## 内容

Hoeffding 不等式的 `log` 侧基础工具。

**⚠ 完整的 `ψ` 函数界 `log((1-p)+p·eᵗ) ≤ tp + t²/8` 是**研究级**难度，未做。**
本文件只交付最基础的一条。
-/

namespace FateV2.Predict.Stage2.ErrorBoundE2c

open FateV2.Error

/-! ## §1 基础：`log(1+x) ≤ x` -/

/-- ⭐⭐ **`log(1+x) ≤ x`**（`x > -1`）。

**证明**：`log y ≤ y - 1`（`y > 0`），取 `y = 1+x`。 -/
theorem log_one_add_le {x : ℝ} (hx : -1 < x) : Real.log (1 + x) ≤ x := by
  have h1 : (0:ℝ) < 1 + x := by linarith
  have h2 := Real.log_le_sub_one_of_pos h1
  linarith

/-! ## §2 公理审计 -/

#print axioms log_one_add_le

end FateV2.Predict.Stage2.ErrorBoundE2c