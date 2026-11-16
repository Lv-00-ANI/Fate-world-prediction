import FateWorld.FateV2.Error.FirstLayerExpectedGeneral
import FateWorld.FateV2.Error.ChainBudgetBound
/-!
  # Error · FirstLayerUnified

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FirstLayerUnified.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FirstLayerExpectedGeneral, ChainBudgetBound
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/FirstLayerUnified` —— **第 1 层两种分解的统一**
  ===========================================================================

  ## 两种分解

  **分解 A（`first_layer_bound_real`，第 264 轮）**：三项相加
  ```
  |e2eResidual| ≤ sigmaEst + sigmaLearn + sigmaSteady        （有 hest，逐样本）
  ```
  审计 R279 判：`η = 1` 时左边精确等于 `hest` 的左边，退化为 `hest + hst` 逐字相加。

  **分解 B（`first_layer_bound_expected_general`，第 314 轮）**：收缩因子乘估计误差
  ```
  E|e2eResidual| ≤ |1-η|^n * ‖xhat‖ * sigmaEst                 （无 hest，期望）
  ```

  主控第 315 轮曾把这个当成「需要裁决的问题」。**实际上不需要裁决**——本文件证明
  两者**是同一个量的两种写法**，通过 `sigmaLearn` 的定义直接连通。

  ## 关键：`sigmaLearn` 就是收缩因子乘以参数偏差

  ```
  sigmaLearn η θhat xhat θ₀ n = c η ^ n * ‖θ₀ - θhat‖ * ‖xhat‖
  ```

  而 `thetaN_closed` 给：
  ```
  thetaN η μ xhat θ₀ n - μ = (1 - η)^n * (θ₀ - μ)
  ```
  取绝对值乘 `‖xhat‖`：
  ```
  ‖thetaN η μ xhat θ₀ n - μ‖ * ‖xhat‖
    = |1-η|^n * ‖θ₀ - μ‖ * ‖xhat‖
    = sigmaLearn η μ xhat θ₀ n            （因为 c η = |1-η|）
  ```

  **所以 `sigmaLearn` 正是「逐样本的残差」，不是额外的加项。**
  分解 A 的三项相加与分解 B 的收缩乘积，在 `θhat := μ` 时**完全重合**。
-/

namespace FateV2.Error
namespace FirstLayerUnified

open MeasureTheory

/-- **`OptimalEta.c η = |1 - η|`**（定义直接展开，供下述引理使用）。 -/
theorem c_eq (η : ℝ) : OptimalEta.c η = |1 - η| := rfl

/-- ⭐⭐ **【统一的核心等式】**

在真值 `μ`、初值 `θ₀`、`xhat ≠ 0` 时，**逐样本残差等于 `sigmaLearn`**：
```
|e2eResidual linWorld (μ*xhat) (thetaN η μ xhat θ₀ n) ⋯ xhat|
  = sigmaLearn η μ xhat θ₀ n
```

**这把分解 A 里的「学习项」与分解 B 里的「收缩因子乘偏差」变成了同一个对象**：
`sigmaLearn` 不是一个额外的加项，它**就是**残差本身。 -/
theorem e2e_eq_sigmaLearn (η μ θ₀ xhat : ℝ) (hx : xhat ≠ 0) (n : ℕ) :
    |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (μ * xhat)
        (ThetaConvergence.thetaN η μ xhat θ₀ n)
        PUnit.unit PUnit.unit PUnit.unit xhat|
      = ChainBudgetBound.sigmaLearn η μ xhat θ₀ n := by
  rw [FirstLayerExpectedGeneral.e2e_expand_general η μ θ₀ xhat hx n]
  unfold ChainBudgetBound.sigmaLearn OptimalEta.c
  simp only [Real.norm_eq_abs, mul_comm]

/-- ⭐⭐ **【期望形式：残差的期望就等于学习项的期望】**

由 `e2e_eq_sigmaLearn`，残差的期望就是 `sigmaLearn` 在样本上的期望。 -/
theorem expectedE2E_eq_integral_sigmaLearn {P : Measure ℝ} [IsProbabilityMeasure P]
    (η : ℝ) (n : ℕ) (xhat : ℝ) (hx : xhat ≠ 0) :
    ∫ ω : Fin n → ℝ,
        |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (((∫ y, y ∂P)) * xhat)
          (ThetaConvergence.thetaN η ((∫ y, y ∂P)) xhat
            (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω) n)
          PUnit.unit PUnit.unit PUnit.unit xhat|
        ∂(Measure.pi (fun _ : Fin n => P))
      = ∫ ω : Fin n → ℝ,
          ChainBudgetBound.sigmaLearn η ((∫ y, y ∂P)) xhat
            (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω) n
          ∂(Measure.pi (fun _ : Fin n => P)) := by
  congr 1
  funext ω
  exact e2e_eq_sigmaLearn η ((∫ y, y ∂P))
    (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω) xhat hx n

/-- ⭐ **【分解 B 其实也是 `sigmaLearn` 的期望上界】**

`first_layer_bound_expected_general` 的结论可以重写为
「`sigmaLearn` 的期望 ≤ `|1-η|^n * ‖xhat‖ * sigmaEst`」。

这把两种分解的关系说清楚了：**分解 B 就是分解 A 里的学习项在期望意义下的界**。 -/
theorem sigmaLearn_expected_le {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (η : ℝ) (n : ℕ) (hn : 0 < n)
    (xhat : ℝ) (hx : xhat ≠ 0) :
    ∫ ω : Fin n → ℝ,
        ChainBudgetBound.sigmaLearn η ((∫ y, y ∂P)) xhat
          (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω) n
        ∂(Measure.pi (fun _ : Fin n => P))
      ≤ |1 - η| ^ n * ‖xhat‖ * ChainBudgetBound.sigmaEst P n := by
  rw [← expectedE2E_eq_integral_sigmaLearn η n xhat hx]
  exact FirstLayerExpectedGeneral.first_layer_bound_expected_general hP η n hn xhat hx

/-! ===========================================================================
  §3  诚实边界
  =========================================================================== -/

/-!
### ⚠ 本文件解决了什么

**主控第 315 轮提出的「第 1 层两种分解哪种对」这个「待裁决问题」其实不需要裁决。**

`e2e_eq_sigmaLearn` 证明：**`sigmaLearn` 不是额外加项，它就是逐样本残差本身**
（因为 `sigmaLearn η θhat xhat θ₀ n = c η^n * ‖θ₀ - θhat‖ * ‖xhat‖`，
而残差正是 `|1-η|^n * ‖θ₀ - μ‖ * ‖xhat‖`，两者在 `θhat := μ` 时相等）。

于是：
* **分解 A**（`sigmaEst + sigmaLearn + sigmaSteady`）是「估计项 + 残差项 + 稳态项」的预算；
* **分解 B**（`|1-η|^n * ‖xhat‖ * sigmaEst`）是「残差项在期望意义下的上界」；
* **两者不是竞争关系**，B 是 A 中 `sigmaLearn` 那一项的期望版界的另一种表达。

### ⚠ 本文件**没有**做到的

* **没有真正把两项加起来**：`sigmaEst + sigmaLearn` 的**和**的上界没证
  （只证了 `sigmaLearn` 的期望 ≤ `|1-η|^n * ‖xhat‖ * sigmaEst`）。
  要得到 `E|e2eResidual| ≤ sigmaEst + ...` 需要不同的模型（本文件的
  `thetaN` 在 `θhat := μ` 时 `sigmaLearn = |1-η|^n ‖θ₀-μ‖ ‖xhat‖`，
  和 `sigmaEst` 不是可加的独立项）；
* **`sigmaSteady` 完全没出现在本文件里**——因为 `linWorld` 是无噪声的
  （`thetaN` 的闭式里没有噪声项），`sigmaSteady` 属于 `ClosedLoopNoisy`
  那条线（见 `ChainBudgetBound.sigmaSteady_is_noisy_bound`）。
-/

end FirstLayerUnified
end FateV2.Error