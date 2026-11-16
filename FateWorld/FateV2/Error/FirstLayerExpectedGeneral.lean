import FateWorld.FateV2.Error.FirstLayerExpectation
import FateWorld.FateV2.Error.ChainBudgetBound
import FateWorld.FateV2.Loop.ThetaConvergence
/-!
  # Error · FirstLayerExpectedGeneral

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FirstLayerExpectedGeneral.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FirstLayerExpectation, ChainBudgetBound, ThetaConvergence
  - 补充 open 域：FateV2.Loop
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/FirstLayerExpectedGeneral` —— **第 1 层：一般 `xhat` 的期望形式**
  ===========================================================================

  `FirstLayerExpectedFinal`（第 312 轮）把第 1 层做成了期望形式、`hest` 彻底消失，
  但只覆盖 `xhat = 1`。本文件把它推广到**任意 `xhat`**。

  ## 关键引理（都在盘上，直接引用不重证）

  ```
  e2e_abs_eq (θhat θn xhat) :
      |e2eResidual linWorld (θhat * xhat) θn ⋯ xhat| = ‖θn - θhat‖ * ‖xhat‖

  thetaN_closed (η θstar x θ₀) (hx : x ≠ 0) (n) :
      thetaN η θstar x θ₀ n - θstar = (1 - η)^n * (θ₀ - θstar)
  ```

  ## 推导

  `xhat ≠ 0` 时：
  ```
  |e2eResidual| = ‖θn - μ‖ * ‖xhat‖
                = |(1-η)^n * (θ₀ - μ)| * ‖xhat‖          （thetaN_closed）
                = |1-η|^n * |θ₀ - μ| * ‖xhat‖
  ```
  取期望（`‖xhat‖` 是常数，提出去）：
  ```
  E|e2eResidual| = |1-η|^n * ‖xhat‖ * E|θ₀ - μ|
                ≤ |1-η|^n * ‖xhat‖ * sigmaEst            （est_expected_dev_le_sigmaEst）
  ```

  **前件里没有 `hest`**，只有 `hP`（可积性）、`hn`（`n > 0`）、`hx`（`xhat ≠ 0`）。
-/

namespace FateV2.Error

open FateV2.Loop
namespace FirstLayerExpectedGeneral

open MeasureTheory

/-- ⭐ **残差的一般展开**：`|e2eResidual| = |1-η|^n * |θ₀ - μ| * ‖xhat‖`。

需要 `xhat ≠ 0`（`thetaN_closed` 的前提）。 -/
theorem e2e_expand_general (η μ θ₀ xhat : ℝ) (hx : xhat ≠ 0) (n : ℕ) :
    |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (μ * xhat)
        (ThetaConvergence.thetaN η μ xhat θ₀ n)
        PUnit.unit PUnit.unit PUnit.unit xhat|
      = |1 - η| ^ n * |θ₀ - μ| * ‖xhat‖ := by
  rw [ChainBudgetBound.e2e_abs_eq]
  rw [ThetaConvergence.thetaN_closed η μ xhat θ₀ hx n]
  rw [Real.norm_eq_abs, abs_mul, abs_pow]

/-- ⭐⭐⭐ **【第 1 层：一般 `xhat` 的期望形式】**

真参数取总体均值 `μ := ∫ y, y ∂P`，闭环初值取样本均值估计 `θ₀ := estHat ω`，
`xhat ≠ 0`。则
```
∫ ω, |e2eResidual linWorld (μ*xhat) (thetaN η μ xhat (estHat ω) n) ⋯ xhat| ∂(Measure.pi …)
  ≤ |1 - η|^n * ‖xhat‖ * sigmaEst P n
```

**前件：`hP`（可积性）、`hn`（`n > 0`）、`hx`（`xhat ≠ 0`）。没有 `hest`。** -/
theorem first_layer_bound_expected_general {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (η : ℝ) (n : ℕ) (hn : 0 < n)
    (xhat : ℝ) (hx : xhat ≠ 0) :
    ∫ ω : Fin n → ℝ,
        |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld
          (((∫ y, y ∂P)) * xhat)
          (ThetaConvergence.thetaN η ((∫ y, y ∂P)) xhat
            (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω) n)
          PUnit.unit PUnit.unit PUnit.unit xhat|
        ∂(Measure.pi (fun _ : Fin n => P))
      ≤ |1 - η| ^ n * ‖xhat‖ * ChainBudgetBound.sigmaEst P n := by
  have hpt : ∀ ω : Fin n → ℝ,
      |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (((∫ y, y ∂P)) * xhat)
        (ThetaConvergence.thetaN η ((∫ y, y ∂P)) xhat
          (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω) n)
        PUnit.unit PUnit.unit PUnit.unit xhat|
      = |1 - η| ^ n * ‖xhat‖ *
          |GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω - (∫ y, y ∂P)| := by
    intro ω
    rw [e2e_expand_general η ((∫ y, y ∂P))
      (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω) xhat hx n]
    ring
  simp only [hpt]
  rw [MeasureTheory.integral_const_mul]
  have hle := FirstLayerExpectation.est_expected_dev_le_sigmaEst hP n hn
  have hnn : (0 : ℝ) ≤ |1 - η| ^ n * ‖xhat‖ := by positivity
  exact mul_le_mul_of_nonneg_left hle hnn

/-- ⭐ **`η = 1` 时一般 `xhat` 的期望误差为零**（主定理的最优特例）。 -/
theorem expected_e2e_eta_one_zero_general {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (xhat : ℝ) (hx : xhat ≠ 0) :
    ∫ ω : Fin n → ℝ,
        |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld
          (((∫ y, y ∂P)) * xhat)
          (ThetaConvergence.thetaN 1 ((∫ y, y ∂P)) xhat
            (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω) n)
          PUnit.unit PUnit.unit PUnit.unit xhat|
        ∂(Measure.pi (fun _ : Fin n => P)) = 0 := by
  have hzero : ∀ ω : Fin n → ℝ,
      |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (((∫ y, y ∂P)) * xhat)
        (ThetaConvergence.thetaN 1 ((∫ y, y ∂P)) xhat
          (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω) n)
        PUnit.unit PUnit.unit PUnit.unit xhat| = 0 := by
    intro ω
    rw [e2e_expand_general 1 ((∫ y, y ∂P))
      (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω) xhat hx n]
    simp [hn.ne']
  simp only [hzero]
  simp

/-! ===========================================================================
  §3  诚实边界
  =========================================================================== -/

/-!
### ⚠ 本文件做到了什么

* **`xhat` 任意非零**（不再限制 `xhat = 1`）；
* **前件无 `hest`**：只有可积性、`n > 0`、`xhat ≠ 0`；
* 结论：`E|e2eResidual| ≤ |1-η|^n * ‖xhat‖ * sigmaEst`。

### ⚠ 本文件**没有**做到什么

* **仍然没有 `sigmaLearn` / `sigmaSteady` 的加项**。因为 `thetaN` 的闭式是
  **精确等式** `θ_n - μ = (1-η)^n * (θ₀ - μ)`，学习与稳态已经包含在
  `(1-η)^n` 里。这是与 `first_layer_bound_real` 三项相加**不同的分解**。
* **`xhat = 0` 时未处理**。此时 `thetaN_closed` 的前提 `x ≠ 0` 不成立
  （`linWorld` 在 `x = 0` 处退化），需要单独处理，本文件未做。
-/

end FirstLayerExpectedGeneral
end FateV2.Error