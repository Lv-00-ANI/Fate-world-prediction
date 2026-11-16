/-!
  # Error · ErrorBoundE4Full

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ErrorBoundE4Full.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Stage2.ErrorBoundE4
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-
  Fate/Stage2/ErrorBoundE4Full.lean

  E4（结构误差）的完整化。

  理论形式：
    |P̂_G(y | do(x')) - P_{G₀}(y | do(x'))| ≤ g(d(G, G₀))

  其中 g(0) = 0 且 g 单调。本文件给出：
    * 第 1 条：g 的 Lipschitz 形式         `|g d| ≤ L * d`
    * 第 2 条：结构误差的传递界             `|err d| ≤ L * d`
    * 第 3 条：结构误差的三角分解/组合     `|e1 d1 + e2 d2| ≤ g1 + g2`
-/

import FateWorld.FateV2.Error.ErrorBoundE4
import Mathlib.Tactic

namespace FateV2.Error.Stage2.ErrorBoundE4Full

open FateV2.Error.Stage2.ErrorBoundE4

-- ⭐⭐⭐ 结构误差的 Lipschitz 形式：
--
-- 若 `g` 是 `L`-Lipschitz 且 `g(0) = 0`，则对 `d ≥ 0` 有 `|g d| ≤ L * d`。
--
-- 证明：把 Lipschitz 估计作用在点对 `(d, 0)` 上；`g 0 = 0` 且 `|d - 0| = d`。
--
-- 这是结构误差界的核心估计。
theorem structural_error_lipschitz
    (g : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hg0 : g 0 = 0)
    (hLip : ∀ a b, |g a - g b| ≤ L * |a - b|)
    (d : ℝ) (hd : 0 ≤ d) :
    |g d| ≤ L * d := by
  have h := hLip d 0
  rw [hg0, sub_zero] at h
  have habs : |d - 0| = d := by rw [sub_zero, abs_of_nonneg hd]
  rw [habs] at h
  exact h

-- ⭐⭐⭐⭐ 结构误差传递：
--
-- 若 `err` 被 `g` 控制（`∀ d, |err d| ≤ g d`），且 `g` 由 `L`-Lipschitz + `g 0 = 0`
-- 给出界 `|g d| ≤ L * d`，则 `|err d| ≤ L * d`。
--
-- 这是把「抽象界 g」收口成「显式界 L * d」的步骤。
--
-- 注：由 `|err d| ≤ g d` 可得 `g d ≥ 0`（因 `|err d| ≥ 0`），故 `g d = |g d|`，
-- 也可用 `abs_of_nonneg` 收口；此处用 `le_abs_self` + `linarith` 完成。
theorem structural_error_explicit
    (err g : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hg0 : g 0 = 0)
    (hLip : ∀ a b, |g a - g b| ≤ L * |a - b|)
    (hctrl : ∀ d, |err d| ≤ g d)
    (d : ℝ) (hd : 0 ≤ d) :
    |err d| ≤ L * d := by
  have h1 := hctrl d
  have h2 : |g d| ≤ L * d := structural_error_lipschitz g L hL hg0 hLip d hd
  have h3 : g d ≤ |g d| := le_abs_self (g d)
  linarith

-- ⭐⭐⭐ 结构误差的三角分解：
--
-- 两个结构误差的组合仍受控于两个界之和。
theorem structural_error_compose
    (e1 e2 : ℝ → ℝ) (g1 g2 d1 d2 : ℝ)
    (h1 : |e1 d1| ≤ g1) (h2 : |e2 d2| ≤ g2) :
    |e1 d1 + e2 d2| ≤ g1 + g2 := by
  calc |e1 d1 + e2 d2| ≤ |e1 d1| + |e2 d2| := abs_add_le _ _
    _ ≤ g1 + g2 := by linarith

-- 结构误差的非负性：界 `g` 在受控点处必然非负。
-- （由 `|err d| ≤ g d` 与 `|err d| ≥ 0` 直接得到。）
theorem structural_error_bound_nonneg
    (err g : ℝ → ℝ) (hctrl : ∀ d, |err d| ≤ g d) (d : ℝ) :
    0 ≤ g d := by
  have h := hctrl d
  have h' : (0 : ℝ) ≤ |err d| := abs_nonneg (err d)
  linarith

-- 结构误差在 `d = 0` 处 vanish：与底层 `structural_error_at_zero` 衔接。
-- 若 `|err d| ≤ L * d` 且 `L * 0 = 0`，则 `err 0 = 0`。
theorem structural_error_explicit_zero
    (err : ℝ → ℝ) (L : ℝ)
    (h : ∀ d, 0 ≤ d → |err d| ≤ L * d) :
    err 0 = 0 := by
  have h0 := h 0 le_rfl
  rw [mul_zero] at h0
  exact abs_eq_zero.mp (le_antisymm h0 (abs_nonneg (err 0)))

end FateV2.Error.Stage2.ErrorBoundE4Full

#print axioms FateV2.Error.Stage2.ErrorBoundE4Full.structural_error_lipschitz
#print axioms FateV2.Error.Stage2.ErrorBoundE4Full.structural_error_explicit
#print axioms FateV2.Error.Stage2.ErrorBoundE4Full.structural_error_compose
#print axioms FateV2.Error.Stage2.ErrorBoundE4Full.structural_error_bound_nonneg
#print axioms FateV2.Error.Stage2.ErrorBoundE4Full.structural_error_explicit_zero
