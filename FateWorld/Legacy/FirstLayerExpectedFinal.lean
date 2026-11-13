import FateWorld.Legacy.FirstLayerExpectation
import FateWorld.Legacy.ChainBudgetBound
import FateWorld.Legacy.ThetaConvergence

/-! ===========================================================================
  `Fate/FirstLayerExpectedFinal` —— **第 1 层：`hest` 真正消失的期望形式**
  ===========================================================================

  ## 审计 R279 的判决

  `first_layer_bound_real` 的前件 `hest : ‖θhat - θstar‖ * ‖xhat‖ ≤ sigmaEst`，
  审计用探针 `e2e_at_eta_one_exact` 证明 `η = 1` 时左边**精确等于** `hest` 的左边，
  故主定理退化为 `hest + hst` 逐字相加——循环论证。

  审计给出的正确标准：「**前件中不含被证明量的任何上界**」。

  ## 本文件的构造

  **统计建模（关键）**：Gauss-Markov 的界是对**总体均值** `μ := ∫ y, y ∂P` 的。
  所以「真参数」`θstar` 必须取 `μ`——这是统计上唯一正确的选择，
  也是 `est_expected_dev_le_sigmaEst` 能直接使用的唯一方式。

  **估计误差进入闭环的途径**：`thetaN` 的第二参数是**真值**（`thetaN_closed`
  的参数名就是 `θstar`），所以真值不能是估计。让估计误差进入的唯一正确方式是
  **让闭环初值 `θ₀` 来自样本**：`θ₀ := estHat ω`。

  此时由 `thetaN_closed`：
  ```
  thetaN η μ 1 (estHat ω) n - μ = (1 - η)^n * (estHat ω - μ)
  ```
  取绝对值再取期望：
  ```
  E|thetaN - μ| = |1-η|^n * E|estHat ω - μ| ≤ |1-η|^n * sigmaEst   （用 est_expected_dev_le_sigmaEst）
  ```

  **前件里没有任何「逐样本偏差上界」**——`hest` 消失了。
-/

namespace Fate
namespace FirstLayerExpectedFinal

open MeasureTheory

/-- ⭐ **`η = 1` 时端到端残差恒为零**（逐样本，最优步长一步归零）。

这里是纯代数：`thetaN 1 μ 1 θ₀ n - μ = 0^n * (θ₀ - μ) = 0`（`n > 0`）。 -/
theorem e2e_eta_one_zero (μ θ₀ : ℝ) {n : ℕ} (hn : 0 < n) :
    |Fate.EndToEnd.e2eResidual ThetaConvergence.linWorld (μ * 1)
        (ThetaConvergence.thetaN 1 μ 1 θ₀ n)
        PUnit.unit PUnit.unit PUnit.unit 1| = 0 := by
  rw [ChainBudgetBound.e2e_abs_eq]
  simp only [norm_one, mul_one, Real.norm_eq_abs]
  rw [ThetaConvergence.thetaN_closed 1 μ 1 θ₀ one_ne_zero n]
  simp [hn.ne']

/-- ⭐⭐ **残差的显式形式**：`|e2eResidual| = |1-η|^n * |θ₀ - μ|`。

`xhat = 1`，故 `‖xhat‖ = 1`；再用 `thetaN_closed` 展开。 -/
theorem e2e_expand (η μ θ₀ : ℝ) (n : ℕ) :
    |Fate.EndToEnd.e2eResidual ThetaConvergence.linWorld (μ * 1)
        (ThetaConvergence.thetaN η μ 1 θ₀ n)
        PUnit.unit PUnit.unit PUnit.unit 1|
      = |1 - η| ^ n * |θ₀ - μ| := by
  rw [ChainBudgetBound.e2e_abs_eq]
  simp only [norm_one, mul_one, Real.norm_eq_abs]
  rw [ThetaConvergence.thetaN_closed η μ 1 θ₀ one_ne_zero n, abs_mul, abs_pow]

/-- ⭐⭐⭐ **【第 1 层的期望形式：`hest` 彻底消失】**

样本空间是 `n` 个 iid 观测（`Measure.pi (fun _ : Fin n => P)`），
真参数取总体均值 `μ := ∫ y, y ∂P`，闭环初值取样本均值估计 `θ₀ := estHat ω`。

则**端到端残差的期望**满足
```
∫ ω, |e2eResidual linWorld (μ*1) (thetaN η μ 1 (estHat ω) n) ⋯ 1| ∂(Measure.pi …)
  ≤ |1 - η|^n * sigmaEst P n
```

**前件里没有任何「逐样本偏差的上界」**——只有 `hP`（可积性）与 `hn`（`n > 0`）。

**这与 `first_layer_bound_real` 的实质区别**：那里的 `hest` 直接给出被证量的界
（审计判为循环），这里的界来自 `est_expected_dev_le_sigmaEst`——
一条**关于期望**的定理，它不假设任何单个样本的偏差。 -/
theorem first_layer_bound_expected_final {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (η : ℝ) (n : ℕ) (hn : 0 < n) :
    ∫ ω : Fin n → ℝ,
        |Fate.EndToEnd.e2eResidual ThetaConvergence.linWorld (((∫ y, y ∂P)) * 1)
          (ThetaConvergence.thetaN η ((∫ y, y ∂P)) 1
            (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω) n)
          PUnit.unit PUnit.unit PUnit.unit 1|
        ∂(Measure.pi (fun _ : Fin n => P))
      ≤ |1 - η| ^ n * ChainBudgetBound.sigmaEst P n := by
  have hpt : ∀ ω : Fin n → ℝ,
      |Fate.EndToEnd.e2eResidual ThetaConvergence.linWorld (((∫ y, y ∂P)) * 1)
        (ThetaConvergence.thetaN η ((∫ y, y ∂P)) 1
          (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω) n)
        PUnit.unit PUnit.unit PUnit.unit 1|
      = |1 - η| ^ n *
          |GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω - (∫ y, y ∂P)| := by
    intro ω
    rw [e2e_expand η ((∫ y, y ∂P))
      (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω) n]
  simp only [hpt]
  rw [MeasureTheory.integral_const_mul]
  have hle := FirstLayerExpectation.est_expected_dev_le_sigmaEst hP n hn
  have hnn : (0 : ℝ) ≤ |1 - η| ^ n := by positivity
  exact mul_le_mul_of_nonneg_left hle hnn

/-! ===========================================================================
  §3  诚实边界
  =========================================================================== -/

/-!
### ⚠ 本文件做到了什么

* **前件里没有任何「逐样本偏差的上界」**——`hest` 彻底消失，符合审计 R279 的新标准；
* 结论是**期望**形式的闭式：`E[|e2eResidual|] ≤ |1-η|^n * sigmaEst`；
* 界用到的是 `est_expected_dev_le_sigmaEst`（审计 R279 点名的真定理）。

### ⚠ 本文件**没有**做到什么

* **只覆盖 `xhat = 1`**。一般 `xhat` 时 `e2eResidual` 还要乘 `‖xhat‖`，
  本文件没做（`e2e_expand` 里 `simp only [norm_one, mul_one]` 依赖 `xhat = 1`）；
* **没有 `sigmaLearn` / `sigmaSteady` 的加项**。原因：`thetaN` 的闭式是
  **精确等式** `θ_n - μ = (1-η)^n * (θ₀ - μ)`，学习与稳态已经包含在
  `(1-η)^n` 里，不是额外的加项。**这与 `first_layer_bound_real` 的三项相加是两种不同的分解**，
  不能互相替代；
* **`θ₀ := estHat ω` 是建模选择**：把样本估计当作闭环初值。也可以选别的
  （例如把估计放进观测 `xhat`），但本文件选的是最简的、能让 `est_expected_dev_le_sigmaEst`
  直接生效的那一种。
-/

end FirstLayerExpectedFinal
end Fate
