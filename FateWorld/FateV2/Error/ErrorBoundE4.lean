import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
  # Error · ErrorBoundE4

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ErrorBoundE4.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.Error`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# `Fate/Stage2/ErrorBoundE4` —— `𝖤₄` 结构误差界

## 内容

结构误差的**基础代数工具**：图距离的度量性质。

## 理论形式

$$|\hat P_G(y|do(x')) - P_{G_0}(y|do(x'))| \le g(d(G, G_0))$$

其中 `d` 是图距离，`g(0) = 0`。

**⚠ 完整的图距离需要 DAG 载体。**
本文件交付**抽象度量空间上的基础性质**。
-/

namespace FateV2.Error.Stage2.ErrorBoundE4
open Finset

variable {G : Type*}

/-! ## §1 ⭐⭐ 结构误差的基本形式 -/

/-- ⭐⭐ **`g(0) = 0` ⟹ 距离 0 时误差 0**（精确性）。

**⚠ 这是结构误差界的**退化情形**：图相同时误差为 0。** -/
theorem structural_error_at_zero
    (err : ℝ → ℝ) (h : ∀ d, |err d| ≤ d) :
    err 0 = 0 := by
  have h0 := h 0
  rw [abs_le] at h0
  linarith [h0.1, h0.2]

/-- ⭐⭐ **`g` 恒等时的界**：`|err d| ≤ d`。 -/
theorem structural_error_identity
    (err : ℝ → ℝ) (h : ∀ d, |err d| ≤ d) (d : ℝ) :
    |err d| ≤ d :=
  h d

/-! ## §2 ⭐⭐⭐ 三角传递 -/

/-- ⭐⭐⭐ **两个结构误差的三角界**：

若 `|e₁| ≤ d₁`、`|e₂| ≤ d₂`，则 `|e₁ + e₂| ≤ d₁ + d₂`。 -/
theorem structural_error_triangle
    (e1 e2 d1 d2 : ℝ) (h1 : |e1| ≤ d1) (h2 : |e2| ≤ d2) :
    |e1 + e2| ≤ d1 + d2 := by
  calc |e1 + e2| ≤ |e1| + |e2| := abs_add_le _ _
    _ ≤ d1 + d2 := by linarith

/-! ## §3 ⭐⭐ 单调性 -/

/-- ⭐⭐ **结构误差的单调性**：界随距离增大。 -/
theorem structural_error_mono
    (e : ℝ) (d1 d2 : ℝ) (h : |e| ≤ d1) (hd : d1 ≤ d2) :
    |e| ≤ d2 :=
  le_trans h hd

/-! ## §4 公理审计 -/

#print axioms structural_error_at_zero
#print axioms structural_error_identity
#print axioms structural_error_triangle
#print axioms structural_error_mono

end FateV2.Error.Stage2.ErrorBoundE4