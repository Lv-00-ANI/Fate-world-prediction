import FateWorld.Legacy.Stage2.ErrorBoundE2
import FateWorld.Legacy.Stage2.ErrorBoundE2b
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# `Fate/Stage2/ErrorBoundE2c` —— `𝖤₂` 的 `log` 基础

## 内容

Hoeffding 不等式的 `log` 侧基础工具。

**⚠ 完整的 `ψ` 函数界 `log((1-p)+p·eᵗ) ≤ tp + t²/8` 是**研究级**难度，未做。**
本文件只交付最基础的一条。
-/

namespace Fate.Stage2.ErrorBoundE2c

/-! ## §1 基础：`log(1+x) ≤ x` -/

/-- ⭐⭐ **`log(1+x) ≤ x`**（`x > -1`）。

**证明**：`log y ≤ y - 1`（`y > 0`），取 `y = 1+x`。 -/
theorem log_one_add_le {x : ℝ} (hx : -1 < x) : Real.log (1 + x) ≤ x := by
  have h1 : (0:ℝ) < 1 + x := by linarith
  have h2 := Real.log_le_sub_one_of_pos h1
  linarith

/-! ## §2 公理审计 -/

#print axioms log_one_add_le

end Fate.Stage2.ErrorBoundE2c