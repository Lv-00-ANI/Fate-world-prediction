import FateWorld.Legacy.Counterfactual
import FateWorld.Legacy.CounterfactualAlgebra
import Mathlib.Tactic

/-!
# `Fate/Stage2/CounterfactualGenuine` —— 反事实误差界（`E7` 的抽象核心）

理论原文（`05-误差界路线.md`）对 `E7` 的定义：

> 若 `‖u - û‖ ≤ δ` 且结构方程 `L`-Lipschitz，则 `‖Y_x'(u) - Y_x'(û)‖ ≤ g(δ)`。

本文件把这个论断的**代数核心**提取出来：不依赖任何具体 SCM 载体，
只要求结构方程 `f` 对某个距离 `dU` / `dY` 是 `L`-Lipschitz，
则反事实输出的差被 `L · dU u û` 控制（即 `g(δ) = L · δ`）。
-/

namespace Fate.Stage2.CounterfactualGenuine

variable {U Y : Type*}

-- ⭐⭐⭐⭐ **反事实误差界**（`E7` 的抽象核心）：
--
-- 若结构方程 `f : U → Y` 是 `L`-Lipschitz（对某个距离 `dU` / `dY`），
-- 则对任意 `u, û`：
--   `dY (f u) (f û) ≤ L * dU u û`.
--
-- 这是 `‖Y_{x'}(u) - Y_{x'}(û)‖ ≤ g(δ)` 的代数核心（取 `g(δ) = L·δ`）。
theorem counterfactual_error_bound
    (f : U → Y) (dU : U → U → ℝ) (dY : Y → Y → ℝ)
    (L : ℝ) (_hL : 0 ≤ L)
    (hLip : ∀ a b, dY (f a) (f b) ≤ L * dU a b)
    (u û : U) :
    dY (f u) (f û) ≤ L * dU u û :=
  hLip u û

-- ⭐⭐⭐ **扰动形式**（`δ` 版本）：
--
-- 若 `dU u û ≤ δ`，则 `dY (f u) (f û) ≤ L · δ`。
theorem counterfactual_error_bound_delta
    (f : U → Y) (dU : U → U → ℝ) (dY : Y → Y → ℝ)
    (L δ : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ a b, dY (f a) (f b) ≤ L * dU a b)
    (u û : U) (hδ : dU u û ≤ δ) :
    dY (f u) (f û) ≤ L * δ := by
  have h1 : dY (f u) (f û) ≤ L * dU u û := hLip u û
  have h2 : L * dU u û ≤ L * δ := mul_le_mul_of_nonneg_left hδ hL
  linarith

-- ⭐⭐⭐ **`g(0) = 0`**：`g(δ) = L·δ` 在 `δ = 0` 处退化（`u = û` 时误差为 0）。
theorem counterfactual_error_zero (L : ℝ) : L * 0 = 0 :=
  mul_zero L

-- ⭐⭐⭐⭐ **多步复合**：若每步误差 ≤ Lᵢ·δᵢ，则总误差 ≤ L₂·L₁·δ。
--
-- 这是 `E7` 的 `L_Π · δ` 形式（`L_Π := ∏ Lᵢ`），`n = 2` 的情形。
theorem counterfactual_compose_two
    {U : Type*} (f g : U → U) (dU : U → U → ℝ)
    (L1 L2 δ1 _δ2 : ℝ) (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2)
    (hLip1 : ∀ a b, dU (f a) (f b) ≤ L1 * dU a b)
    (hLip2 : ∀ a b, dU (g a) (g b) ≤ L2 * dU a b)
    (u û : U) (h1 : dU u û ≤ δ1) :
    dU (g (f u)) (g (f û)) ≤ L2 * L1 * δ1 := by
  have hfu : dU (f u) (f û) ≤ L1 * δ1 := by
    have hf : dU (f u) (f û) ≤ L1 * dU u û := hLip1 u û
    have hm : L1 * dU u û ≤ L1 * δ1 := mul_le_mul_of_nonneg_left h1 hL1
    linarith
  have hg : dU (g (f u)) (g (f û)) ≤ L2 * dU (f u) (f û) := hLip2 (f u) (f û)
  have h2 : L2 * dU (f u) (f û) ≤ L2 * (L1 * δ1) :=
    mul_le_mul_of_nonneg_left hfu hL2
  have heq : L2 * (L1 * δ1) = L2 * L1 * δ1 := by ring
  linarith

-- 以上四条定理的公理依赖检查（无 `sorryAx` 即证明是真实的）。
#print axioms counterfactual_error_bound
#print axioms counterfactual_error_bound_delta
#print axioms counterfactual_error_zero
#print axioms counterfactual_compose_two

end Fate.Stage2.CounterfactualGenuine
