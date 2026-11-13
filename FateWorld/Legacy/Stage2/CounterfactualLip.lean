import FateWorld.Legacy.Counterfactual
import FateWorld.Legacy.Stage2.CounterfactualGenuine
import Mathlib.Tactic

/-!
# `Fate/Stage2/CounterfactualLip` —— 从 `Model.Obs` 推出反事实 Lipschitz 性

`Fate/Stage2/CounterfactualGenuine` 只交了 `E7` 的**代数传递**（②）：
给定 `hLip : dY (f a) (f b) ≤ L * dU a b`，推出误差界。

本文件补上 `E7` 缺失的**另一半（①）**：在 `Fate.Counterfactual.Model`
的具体载体上，把反事实输出写成复合

  `Y_{x'}(u) = M.Obs (arm u)`，其中 `arm : U → M.SCM` 是 `do(x', ·)`，

并从 **两条结构性的 Lipschitz 假设**出发**推出** `hLip`：

* `hArm`：干预组装 `arm` 是 `L₁`-Lipschitz（对扰动距离 `dU`、机制距离 `dS`）；
* `hObs`：观测泛函 `M.Obs` 是 `L₂`-Lipschitz（对机制距离 `dS`、预测距离 `dY`）。

结论：`u ↦ M.Obs (arm u)` 是 `L₂ · L₁`-Lipschitz —— 这正是 `CounterfactualGenuine`
四条定理所需的 `hLip` 实例。E7 因此**闭合**：`g(δ) = L₂ · L₁ · δ`。
-/

namespace Fate.Stage2.CounterfactualLip

open Fate

variable {U : Type*}

-- ⭐⭐⭐⭐ **反事实 Lipschitz 性（从 `Model.Obs` 推出）**：
--
-- 若 `arm` 是 `L₁`-Lipschitz、`M.Obs` 是 `L₂`-Lipschitz，则反事实输出
-- `u ↦ M.Obs (arm u)` 是 `L₂ · L₁`-Lipschitz。
--
-- 证明链：
-- `dY (Obs (arm u)) (Obs (arm û)) ≤ L₂ · dS (arm u) (arm û) ≤ L₂ · (L₁ · dU u û) = (L₂·L₁) · dU u û`。
--
-- ⚠ 这是 `E7` 的 **① 从 SCM 语义推出 `hLip`**。
theorem counterfactual_lipschitz_from_model
    (M : Counterfactual.Model) (arm : U → M.SCM)
    (dU : U → U → ℝ) (dS : M.SCM → M.SCM → ℝ)
    (dY : M.CF → M.CF → ℝ)
    (L₁ L₂ : ℝ) (_hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hArm : ∀ a b, dS (arm a) (arm b) ≤ L₁ * dU a b)
    (hObs : ∀ s t, dY (M.Obs s) (M.Obs t) ≤ L₂ * dS s t) :
    ∀ u û, dY (M.Obs (arm u)) (M.Obs (arm û)) ≤ (L₂ * L₁) * dU u û := by
  intro u û
  -- ① `M.Obs` 的 `L₂`-Lipschitz 性
  have h1 : dY (M.Obs (arm u)) (M.Obs (arm û)) ≤ L₂ * dS (arm u) (arm û) :=
    hObs (arm u) (arm û)
  -- ② `arm` 的 `L₁`-Lipschitz 性，配上 `L₂ ≥ 0` 保序
  have h2 : L₂ * dS (arm u) (arm û) ≤ L₂ * (L₁ * dU u û) :=
    mul_le_mul_of_nonneg_left (hArm u û) hL₂
  -- ③ 常数合并
  have h3 : L₂ * (L₁ * dU u û) = (L₂ * L₁) * dU u û := by ring
  linarith

-- ⭐⭐⭐ **接线**：把 `counterfactual_lipschitz_from_model` 的结果直接喂给
-- `CounterfactualGenuine.counterfactual_error_bound_delta`，
-- 得 `E7` 的最终形态 `‖Y_{x'}(u) - Y_{x'}(û)‖ ≤ L₂·L₁·δ`（即 `g(δ) = L₂·L₁·δ`）。
theorem counterfactual_error_from_model
    (M : Counterfactual.Model) (arm : U → M.SCM)
    (dU : U → U → ℝ) (dS : M.SCM → M.SCM → ℝ)
    (dY : M.CF → M.CF → ℝ)
    (L₁ L₂ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hArm : ∀ a b, dS (arm a) (arm b) ≤ L₁ * dU a b)
    (hObs : ∀ s t, dY (M.Obs s) (M.Obs t) ≤ L₂ * dS s t)
    (u û : U) (δ : ℝ) (hδ : dU u û ≤ δ) :
    dY (M.Obs (arm u)) (M.Obs (arm û)) ≤ (L₂ * L₁) * δ :=
  CounterfactualGenuine.counterfactual_error_bound_delta (fun u => M.Obs (arm u)) dU dY
    (L₂ * L₁) δ (mul_nonneg hL₂ hL₁)
    (counterfactual_lipschitz_from_model M arm dU dS dY L₁ L₂ hL₁ hL₂ hArm hObs)
    u û hδ

-- 公理依赖检查（无 `sorryAx` 即证明是真实的）。
#print axioms counterfactual_lipschitz_from_model
#print axioms counterfactual_error_from_model

end Fate.Stage2.CounterfactualLip
