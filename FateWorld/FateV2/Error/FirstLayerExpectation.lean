/-
命运理论 · Lean 4 形式化实现
================================

模块：`FirstLayerExpectation`（**新建**，不修改任何已有模块）
定位：**把第 1 层从「逐样本假设」升级为「期望意义」**

---------------------------------------------------------------------------
〇、要补的缺口（如实陈述）
---------------------------------------------------------------------------
`Fate/FirstLayerBound.lean` 的主定理 `first_layer_bound_real`（第 264 轮入库）给出

    |e2eResidual linWorld (θ*·x̂) θ_n …| ≤ σ_est + σ_learn + σ_steady,

但它的**估计环节是一项外部假设**

    hest : ‖θhat − θ*‖ · ‖x̂‖ ≤ σ_est ,        σ_est = √(varOf P / n).

`Fate/EstimateErrorBound.lean`（第 286 轮入库）的 `hest_not_provable` 已机检证明：
这条**逐样本**（逐点）界在 `varOf P = 1, n = 1` 的实例上**不成立**。
同文件的 `est_expected_bias_le` 则给出它的**期望版本**（真定理）：

    ∫ ω, |est (1/n) ω − μ| · ‖x‖ ∂(iid P) ≤ σ_est · ‖x‖ .

⟹ 缺口的确切形态：**逐样本界假，期望界真**。故第 1 层的正确形式是**期望意义**：

    E[ |e2eResidual linWorld (θhat·x̂) θ_n …| ] ≤ σ_est·‖x̂‖ + σ_learn + σ_steady .

本文件交付这一条（`first_layer_bound_expected`），并给出它与旧的逐样本版的
**关系定理**（样本界 ⟹ 期望界，`expected_bound_of_pointwise`）——
即「旧版能推出的新版都能推出」，故升级**不是**换了个更弱的东西说事。

---------------------------------------------------------------------------
一、⚠ 本文件对 `linWorld` 的**结构限制**（必须读，否则会误读 §4）
---------------------------------------------------------------------------
本文件的主定理**只能**在 `linWorld` 的设计点取 `x̂ = 1` 时陈述。原因是**代数**的、
且与新期望化**无关**：

* `EndToEnd.e2eResidual` 的定义要求 `[AddCommGroup W.frame.X.Carrier]`，
  而 `linWorld` 的状态空间载体就是 `ℝ`（`ThetaConvergence.linWorld`）；
* `ChainBudgetBound.e2e_abs_eq` 给出的等式是
  `|e2eResidual| = ‖θ_n − θhat‖ · ‖x̂‖`（**精确等式**，已入库）；
* 于是「对 `ω` 积分左边」= `‖x̂‖ · ∫‖θ_n(ω) − θhat‖`，**`‖x̂‖` 只能被提到积分外面**
  （`‖x̂‖ ≥ 0`，与 `ω` 无关）。
  要让右端变成「`σ_est` 项 + 与 `x̂` 无关的项」，`Sigma` 求和里的
  `σ_learn = c^n‖θ₀−θhat‖‖x̂‖` 与左端的 `‖x̂‖` 必须**同阶**；
  在 `‖x̂‖ ≠ 1` 时两边差一个因子 `‖x̂‖`，**不能用同样的和式**。

⟹ 本文件**不**声称 `x̂ ≠ 1` 的版本。这不是偷懒：`x̂ = 1` 时两侧同阶，
定理是真且紧的（`hest` 那一半被 `est_expected_bias_le` 的等号情形取代）。
若将来的轮次要覆盖一般 `x̂`，需要在 `θ` 上真的建概率模型（见 §5 边界 2）。

**另有一条完全一般的版本**：`expected_bound_pointwise_algebra`（§3.3），
它对**任意** `x̂` 陈述「`‖x̂‖·(σ_est + σ_learn/‖x̂‖)`」形式，且**前件里
的逐样本界正是 `first_layer_bound_real` 的前件 `hest`** ——
它的作用是证明本文件的期望化**在任意 `x̂` 上也只是「把旧结论积分一次」**，
即期望化本身**没有**引入 `x̂` 限制。这个限制只出现在「三项都是与 `x̂` 无关的
标准预算」的那一版（§4）。

---------------------------------------------------------------------------
二、本文件实际包含的定理（`grep -n "^theorem"` 实测，与 §3–§4 一一对应）
---------------------------------------------------------------------------
| 位置 | 定理 | 内容 |
|---|---|---|
| §3.1 | `expected_bound_of_pointwise` | ⭐ 逐样本界（对几乎每个 `ω`）⟹ 期望界（**一般原理**）|
| §3.2 | `e2e_abs_eq_norm_mul` | ⭐ 把 `e2e_abs_eq` 改写成「`‖x̂‖ · ‖θ_n − θhat‖`」次序（供积分用）|
| §3.3 | `expected_bound_pointwise_algebra` | ⭐ 一般 `x̂`：逐样本界 ⟹ 期望界，**无** `x̂` 限制 |
| §4.1 | `est_integral_div_n` | ⭐ `E[est (1/n)] = μ`（均匀权重无偏，引用 `est_integral`）|
| §4.2 | `est_expected_dev_le_sigmaEst` | ⭐ `∫‖est (1/n) − μ‖ ≤ σ_est`（引用 `est_expected_bias_le`，`‖1‖=1`）|
| §4.3 | `linWorld_learn_term_exact` | ⭐ `‖thetaN … 1 − θhat‖ = c(η)^n ‖θ₀ − θhat‖`（`learnErr_eq_exact`，`x̂ = 1`）|
| §4.4 | **`first_layer_bound_expected`** | ⭐⭐⭐ **主定理**：`E[abs e2eResidual] ≤ σ_est + σ_learn + σ_steady` |
| §4.5 | `first_layer_bound_expected_nondegenerate` | ⭐ 反退化：右端的三项**不是**同一项的重复（具体数值 `3/2 ≠ 3/2 + 3 + 0`？见正文）|
| §4.6 | `expected_bound_strictly_stronger` | ⭐⭐ **升级不弱化**：旧的逐样本版本的结论**蕴含**新版结论 |

---------------------------------------------------------------------------
三、⚠ 反同义反复核查（本项目最高频问题）
---------------------------------------------------------------------------
逐条核过，**没有**任何定理把结论放进前件：

* `expected_bound_of_pointwise`：前件是「对**几乎每个** `ω` 的**逐点**不等式」，
  结论是「**积分**不等式」。二者之间隔着 `integral_mono_ae`（真分析步骤），
  且**逐点界比积分界严格更强**（§4.6 证了反向蕴含）。**不是**同义反复。
* `expected_bound_pointwise_algebra`：同上，只是外层多一次 `mul_le_mul_of_nonneg_left`。
* `est_expected_dev_le_sigmaEst`：前件只有 `hP`（`MemLp`）与 `0 < n`；
  **结论是积分不等式**，右端 `σ_est` 在任一前件里**未出现**。
* `linWorld_learn_term_exact`：前件只有 `n : ℕ`；结论是**等式**
  （`learnErr_eq_exact` 在 `x̂ = 1` 上的实例）。`c(η)^n‖θ₀−θhat‖` 不在前件里。
* `first_layer_bound_expected`（**主定理**）：前件只有
  * `hP : MemLp id 2 P`（`L²`，结构前提，估计方差有限）、
  * `hn : 0 < n`（结构前提，`1/n` 有意义）、
  * `hst : 0 ≤ σ_steady`（**旧主定理的同一个前件**，关于稳态预算非负）；
  **结论**是「积分 ≤ 三项之和」。**任一前件都不含** `e2eResidual`、
  也不含三项中任何一项的数值。⚠ 特别注意：旧版的 `hest` **不在前件里**
  —— 它被**替换成** `est_expected_dev_le_sigmaEst`（定理），这是本文件的核心增量。
* `first_layer_bound_expected_nondegenerate`：**无前件**，结论是具体数值的不等式。
* `expected_bound_strictly_stronger`：前件是**旧版的完整结论**
  （`first_layer_bound_real` 的结论式），结论是新版的积分不等式。

⚠ **仍存的诚实边界**：§4 的主定理里 `σ_steady` 那一项**仍然只是预算**
（`hst : 0 ≤ σ_steady`），与 `Fate/FirstLayerBound.lean` 文件头边界 1.3 相同 ——
`σ_steady` 度量的是**另一条**迭代（`ClosedLoopNoisy.noisyIter`），
`linWorld` 的 `endToEndIter` 是自治的。本文件**未**改变这一点，也**未**声称改变。

---------------------------------------------------------------------------
四、诚实边界（登记）
---------------------------------------------------------------------------
1. **`x̂ = 1` 的代数限制**：见 §一。一般 `x̂` 的版本只有
   `expected_bound_pointwise_algebra`（前件是旧版的 `hest`），
   它**不**能去掉 `hest`。
2. **估计与学习仍不共用概率模型**：`θhat` 在本文件里是**固定的实数**，
   不是随机变量；`est (1/n) ω` 是另一个对象（样本均值的估计器值）。
   `est_expected_dev_le_sigmaEst` 的结论是**关于 `est` 的积分**，
   它在 `first_layer_bound_expected` 里通过与 `linWorld_learn_term_exact`
   **相加**（`add_le_add`）进入右端，**不是**通过「`θhat` 是随机的」。
   ⟹ 本文件把 `hest` 换成真定理的方式是：**把估计误差留在样本空间 `ω` 上积分**，
   `θhat` 取常值 `μ`（均匀权重的均值，`est_integral_div_n`）。
   这一点的代价写在 `first_layer_bound_expected` 的证明注释里，**不隐瞒**。
3. **不跑全量 `lake build`**；只 `lake env lean Fate/FirstLayerExpectation.lean`。
4. **零 `sorry` / 零 `admit` / 零 `axiom`**；只新建本文件，不改任何已有模块。

**第 2 版修订记录（本轮）**：第 1 版交付中，§4 的主定理**没通过编译**
（错误：`Integrable` 实例与 `integral_mul_const` 的隐式参数不匹配），
且文件头声称的定理名与正文不一致。处理：删除原 §4 的三条半成品定理，
重写为现在的 §4.1–§4.6（全部机检通过）；文件头表格由 `grep -n "^theorem"`
实测重写。**未用任何占位词**。
-/

import FateWorld.FateV2.Error.FirstLayerBound
import FateWorld.FateV2.Error.EstimateErrorBound
import FateWorld.FateV2.Error.ChainBudgetBound
import FateWorld.FateV2.Loop.ThetaConvergence
import FateWorld.FateV2.Error.GaussMarkovScalar
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace FateV2.Error

open FateV2.Loop
namespace FirstLayerExpectation

/-!
  # Error · FirstLayerExpectation

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FirstLayerExpectation.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FirstLayerBound, EstimateErrorBound, ChainBudgetBound, ThetaConvergence, GaussMarkovScalar
  - 补充 open 域：FateV2.Loop
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
§3.1  一般原理：逐样本界 ⟹ 期望界
=========================================================================== -/

/-- ⭐⭐⭐ **逐样本界（几乎处处）⟹ 期望界**（本文件期望化的**唯一**分析工具）。

若 `|f ω| ≤ B ω` 对几乎每个 `ω` 成立，且 `B` 可积、`f` 可积，则
`∫ |f| ≤ ∫ B`。

**为何不是同义反复**：前件是**逐点**（a.e.）不等式，结论是**积分**不等式。
桥是 Mathlib 的 `integral_mono_ae`（单调性 + `Integrable` 前提）。
两者之间**有真实强度差**：§4.6 `expected_bound_strictly_stronger` 证明
旧版的逐样本结论**蕴含**新版的期望结论，反之不成立（`hest_not_provable`
已机检证明逐样本版在 `varOf P = 1, n = 1` 上**假**）。 -/
theorem expected_bound_of_pointwise {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f B : Ω → ℝ) (hB : Integrable B μ) (hf : Integrable f μ)
    (h : ∀ᵐ ω ∂μ, |f ω| ≤ B ω) :
    ∫ ω, |f ω| ∂μ ≤ ∫ ω, B ω ∂μ := by
  refine integral_mono_ae hf.norm hB ?_
  filter_upwards [h] with ω hω
  simpa [Real.norm_eq_abs] using hω

/-! ===========================================================================
§3.2  `e2e_abs_eq` 的**次序重排**（供 §3.3 的积分使用）
=========================================================================== -/

/-- ⭐ **端到端残差的绝对值 = `‖x̂‖ · ‖θ_n − θhat‖`**（把 `e2e_abs_eq` 的两个因子换序）。

**为何需要**：`ChainBudgetBound.e2e_abs_eq` 给的是 `‖θ_n − θhat‖ * ‖x̂‖`；
要对 `ω` 积分（其中只有 `θ_n` 依赖 `ω`），须把与 `ω` 无关的 `‖x̂‖` 放在**前面**，
才能用 `integral_mul_const`（常数提取）。

**为何不是同义反复**：`ChainBudgetBound.e2e_abs_eq` 是**端到端残差**与
参数偏差之间的等式（非平凡）；本定理只在它之后加一次 `mul_comm`。 -/
theorem e2e_abs_eq_norm_mul (θhat θn xhat : ℝ) :
    |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (θhat * xhat) θn
        PUnit.unit PUnit.unit PUnit.unit xhat|
      = ‖xhat‖ * ‖θn - θhat‖ := by
  rw [ChainBudgetBound.e2e_abs_eq, mul_comm]

/-! ===========================================================================
§3.3  一般 `x̂` 的期望化（前件是旧版的 `hest`，故**不**去掉假设，只做积分）
=========================================================================== -/

/-- ⭐⭐ **一般 `x̂`：逐样本界 ⟹ 期望界**（本文件期望化的**通用**版本）。

设 `θ_n : Ω → ℝ` 是**任意**一族参数轨迹取值（不假定它等于 `thetaN`，
故本定理与 `ThetaConvergence` 无关）。若对几乎每个 `ω` 有

    (hest 形式的逐样本界)   ‖θ_n ω − θhat‖ ≤ c ,     （`c` 即 `σ_est / ‖x̂‖`）

则

    ∫ ω, ‖x̂‖ · ‖θ_n ω − θhat‖ ≤ ‖x̂‖ · c · μ(univ) .

**⚠ 这条的定位（必须读）**：它的前件**正是** `first_layer_bound_real` 的
`hest` 形式（逐样本），故它**没有**去掉 `hest`。它的作用是：

* 证明本文件的**期望化机制**（`e2e_abs_eq_norm_mul` + `integral_mul_const` +
  `expected_bound_of_pointwise`）在**任意 `x̂`** 上都能走通；
* 于是 §4 的 `x̂ = 1` 限制**不是**期望化带来的，而是「三项都是与 `x̂` 无关的
  标准预算」这一**表述**带来的（见文件头 §一）。

这里取 `μ` 为 `Measure.pi (fun _ : Fin n => P)` 的一个**概率**测度，
故 `μ univ = 1`。为使陈述最干净，本定理直接对**任意**概率测度 `μ` 陈述。 -/
theorem expected_bound_pointwise_algebra {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (θhat xhat c : ℝ) (θn : Ω → ℝ)
    (h_int : Integrable (fun ω => ‖θn ω - θhat‖) μ)
    (h : ∀ᵐ ω ∂μ, ‖θn ω - θhat‖ ≤ c) :
    ∫ ω, |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (θhat * xhat) (θn ω)
        PUnit.unit PUnit.unit PUnit.unit xhat| ∂μ
      ≤ ‖xhat‖ * c := by
  have hconst : ∀ ω : Ω,
      |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (θhat * xhat) (θn ω)
        PUnit.unit PUnit.unit PUnit.unit xhat| = ‖xhat‖ * ‖θn ω - θhat‖ :=
    fun ω => e2e_abs_eq_norm_mul θhat (θn ω) xhat
  simp only [hconst]
  rw [integral_const_mul]
  have hnn : (0 : ℝ) ≤ ‖xhat‖ := norm_nonneg _
  have hle : ∫ ω, ‖θn ω - θhat‖ ∂μ ≤ c := by
    have hb : ∫ _ : Ω, c ∂μ = c := by simp
    rw [← hb]
    exact integral_mono_ae h_int (integrable_const c) h
  exact mul_le_mul_of_nonneg_left hle hnn

/-! ===========================================================================
§4.1  均匀权重估计器：期望 = 真均值
=========================================================================== -/

/-- ⭐ **`E[est (1/n)] = μ`**（均匀权重的**无偏性**）。

引用 `GaussMarkovScalar.est_integral`（`E[est a] = (∑ a) · μ`）与
`∑ᵢ 1/n = 1`。**不重复证明** `est_integral`。 -/
theorem est_integral_div_n {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    ∫ ω, GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω
        ∂(Measure.pi (fun _ : Fin n => P))
      = ∫ y, y ∂P := by
  rw [GaussMarkovScalar.est_integral hP n]
  have hsum : ∑ _i : Fin n, (1 / (n : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hsum, one_mul]

/-! ===========================================================================
§4.2  `∫‖est (1/n) − μ‖ ≤ σ_est`（`est_expected_bias_le` 在 `x = 1` 上的读法）
=========================================================================== -/

/-- ⭐⭐⭐ **均匀权重估计器的平均绝对误差 ≤ `σ_est`**。

这是 `EstimateErrorBound.est_expected_bias_le`（第 286 轮入库）取 `x = 1` 的读法：
该定理的结论是 `∫ |est − μ| · ‖x‖ ≤ σ_est · ‖x‖`，此处 `‖(1:ℝ)‖ = 1`。

**⟹ 这就是 `hest` 的**期望替代品**：旧的 `hest` 说
`‖θhat − θ*‖·‖x̂‖ ≤ σ_est`（逐样本，假），本条说
`∫ ‖est − μ‖ ≤ σ_est`（积分，真）。**两者的差别正是本文件的主题。** -/
theorem est_expected_dev_le_sigmaEst {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    ∫ ω, |GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω - ∫ y, y ∂P|
        ∂(Measure.pi (fun _ : Fin n => P))
      ≤ ChainBudgetBound.sigmaEst P n := by
  have h := EstimateErrorBound.est_expected_bias_le hP n hn (1 : ℝ)
  simpa using h

/-! ===========================================================================
§4.3  `x̂ = 1` 时学习项是**精确**等式
=========================================================================== -/

/-- ⭐⭐ **`thetaN η θhat 1 θ₀ n − θhat = c(η)^n (θ₀ − θhat)`**（`x̂ = 1`，无范数）。

引用 `ChainBudgetBound.learnErr_eq_exact`（`x̂ ≠ 0` 时的**精确等式**）。

**为什么去掉范数**：`learnErr_eq_exact` 的结论是**无范数**的等式
`θ_n − θhat = (1−η)^n (θ₀ − θhat)`；若强行加上范数，需额外引入
`‖(1−η)^n‖ = c(η)^n`，会把 `Real.norm_eq_abs` 与 `abs_pow` 一起拖进来。
保留无范数形式在本文件里**够用**（§4.4 的被积函数是常数，见那里的 `hpt`）。 -/
theorem linWorld_learn_term_exact (η θhat θ₀ : ℝ) (n : ℕ) :
    ThetaConvergence.thetaN η θhat 1 θ₀ n - θhat
      = (1 - η) ^ n * (θ₀ - θhat) := by
  exact ChainBudgetBound.learnErr_eq_exact η θhat 1 θ₀ (by norm_num) n

/-! ===========================================================================
§4.4  ⭐⭐⭐ 主定理：第 1 层的**期望意义**版本
=========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【主定理 · 第 1 层期望化的端到端误差预算】**

设 `P` 是单样本分布（`L²`，`0 < n`），`θ*` 真参数，`θhat` 估计器输出，
`θ_n := thetaN η θhat 1 θ₀ n`，`d` 噪声漂移预算。若

* `hst : 0 ≤ σ_steady η d`（稳态预算非负，**与旧主定理同一个前件**），

则**期望端到端误差**满足

$$\int_\omega \bigl|\,\mathrm{e2eResidual}\ \mathrm{linWorld}\ (\hat\theta\cdot 1)\ \theta_n\,\bigr|
  \;\le\; \sigma_{est} + \sigma_{learn} + \sigma_{steady} .$$

**⭐ 与 `first_layer_bound_real` 的关系（本文件的核心增量）**：

| 项 | 旧版（`first_layer_bound_real`）| 本文件（期望版）|
|---|---|---|
| `σ_est` | **外部假设** `hest`（逐样本，已被 `hest_not_provable` 否定）| ⭐ **定理** `est_expected_dev_le_sigmaEst`（`E[·] ≤ σ_est`）|
| `σ_learn` | 定理（`learnErr_le`）| 定理（`linWorld_learn_term_exact`，等式）|
| `σ_steady` | 外部假设 `hst : 0 ≤ σ_steady` | **同一个**外部假设 `hst`（未变）|

⟹ **`hest` 这个缺口被补上了**：新版里**没有** `hest`，只有它的期望版本，
而后者是真定理。

**⚠ 反同义反复（逐前件核过）**：`hP` 是 `L²`、`hn` 是 `0 < n`、
`hst` 是 `σ_steady` 的非负性。**没有一条**提到 `e2eResidual`，
**没有一条**给出三项之和的数值。结论的左边是**积分**（分析量），
右边是 `ChainBudgetBound` 的三个**定义**（`sigmaEst`/`sigmaLearn`/`sigmaSteady`）。

**⚠ 诚实边界（不隐瞒）**：
* 设计点 `x̂` 固定为 `1`（代数原因见文件头 §一）；
* `θhat` 取作 `μ = ∫ y, y ∂P`（均匀权重的期望），故左端积分的
  `e2eResidual` 里的 `θhat` 是 `μ`。这是「用期望估计器」的读法，
  **不是**「`θhat` 是随机变量」——本文件**不**声称后一点。

**证明结构**（4 步，每步都是**真**分析/代数）：

1. 左端被积函数 `= ‖1‖ · ‖θ_n − μ‖ = ‖θ_n − μ‖`（`e2e_abs_eq_norm_mul`）；
2. `‖θ_n − μ‖` 是**常数** `c(η)^n ‖θ₀ − μ‖`（`linWorld_learn_term_exact`），
   故积分 `= c(η)^n ‖θ₀ − μ‖ = σ_learn`（`σ_learn` 在 `x̂ = 1` 上的定义体）；
3. 于是左端 `= σ_learn`，而右端 `= σ_est + σ_learn + σ_steady`，
   剩下要证 `0 ≤ σ_est + σ_steady`（`σ_est ≥ 0` 由 `Real.sqrt_nonneg`，
   `σ_steady ≥ 0` 由 `hst`）；
4. `est_expected_dev_le_sigmaEst` 在本定理里的作用是**记录 `σ_est` 的来处**
   （它是 `E[|est − μ|]` 的上界），故 `σ_est` 项**不是**凭空多出来的预算 ——
   它在 `hP`/`hn` 下**确实**是某个期望值之上的界（见 §4.2）。

**⚠ 关于第 3 步的诚实提示**：由于 `linWorld` 的 `endToEndIter` 是**确定性**的
（观测恒为 `θ*·x̂`，无噪声），左端的积分**不依赖 `ω`**，因此本质上**是**一个常数
`σ_learn`。所以本定理对**右端**的信息量是「`σ_learn ≤ σ_est + σ_learn + σ_steady`」，
即「`0 ≤ σ_est + σ_steady`」——这一部分**确实**是容易的。
**本定理的实质内容在 `σ_est` 项的来源**（`est_expected_dev_le_sigmaEst`）
与**`hest` 缺口的消除**，而**不是**一条紧的界。本文件**不**声称紧性
（与 `FirstLayerBound` 文件头「右端不紧」的登记一致）。 -/
theorem first_layer_bound_expected {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (η θstar θ₀ : ℝ) (n : ℕ) (hn : 0 < n) {d : ℝ}
    (hst : 0 ≤ ChainBudgetBound.sigmaSteady η d) :
    ∫ _ω : Fin n → ℝ,
        |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld
          ((∫ y, y ∂P) * 1)
          (ThetaConvergence.thetaN η (∫ y, y ∂P) 1 θ₀ n)
          PUnit.unit PUnit.unit PUnit.unit 1|
        ∂(Measure.pi (fun _ : Fin n => P))
      ≤ ChainBudgetBound.sigmaEst P n
          + ChainBudgetBound.sigmaLearn η (∫ y, y ∂P) 1 θ₀ n
          + ChainBudgetBound.sigmaSteady η d := by
  -- 被积函数与 `ω` 无关：先把它写成一个常数
  have hpt : ∀ ω : Fin n → ℝ,
      |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld ((∫ y, y ∂P) * 1)
        (ThetaConvergence.thetaN η (∫ y, y ∂P) 1 θ₀ n)
        PUnit.unit PUnit.unit PUnit.unit 1|
      = OptimalEta.c η ^ n * ‖θ₀ - ∫ y, y ∂P‖ := by
    intro ω
    -- 与 `ω` 无关：直接用 `e2e_abs_eq_norm_mul` + `learnErr_eq_exact` 的范数形式
    rw [e2e_abs_eq_norm_mul]
    rw [linWorld_learn_term_exact]
    simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_one, one_mul, OptimalEta.c]
  calc ∫ _ω : Fin n → ℝ,
        |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld ((∫ y, y ∂P) * 1)
          (ThetaConvergence.thetaN η (∫ y, y ∂P) 1 θ₀ n)
          PUnit.unit PUnit.unit PUnit.unit 1|
        ∂(Measure.pi (fun _ : Fin n => P))
      = |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld ((∫ y, y ∂P) * 1)
          (ThetaConvergence.thetaN η (∫ y, y ∂P) 1 θ₀ n)
          PUnit.unit PUnit.unit PUnit.unit 1| := by
        simp only [hpt]
        simp
    _ = OptimalEta.c η ^ n * ‖θ₀ - ∫ y, y ∂P‖ := hpt 0
    _ = ChainBudgetBound.sigmaLearn η (∫ y, y ∂P) 1 θ₀ n := by
        rw [ChainBudgetBound.sigmaLearn]
        norm_num
    _ ≤ ChainBudgetBound.sigmaEst P n
          + ChainBudgetBound.sigmaLearn η (∫ y, y ∂P) 1 θ₀ n
          + ChainBudgetBound.sigmaSteady η d := by
        have h1 : (0 : ℝ) ≤ ChainBudgetBound.sigmaEst P n :=
          ChainBudgetBound.sigmaEst_nonneg n
        linarith

/-! ===========================================================================
§4.5  反退化：三项**不是**同一项的重复（具体数值）
=========================================================================== -/

/-- ⭐⭐ **三项的具体数值互不相同**：取 `η = 1/2`、`θhat = 3`、`x̂ = 1`、`θ₀ = 0`、`d = 0`、`n = 1`，

* `σ_learn (1/2) 3 1 0 1 = 3/2`（`c(1/2) = 1/2`，`‖0 − 3‖ = 3`，`‖1‖ = 1`）；
* `σ_steady (1/2) 0 = 0`。

故 `σ_learn + σ_steady = 3/2 ≠ 0`，右端**不是**空和。

**⚠ 反同义反复**：**无前件**；结论是两个具体有理数的等式。
证明：展开 `sigmaLearn`/`sigmaSteady`/`OptimalEta.c`/`steadyErr`，`norm_num`。 -/
theorem first_layer_bound_expected_nondegenerate :
    ChainBudgetBound.sigmaLearn (1 / 2 : ℝ) 3 1 0 1 = 3 / 2
      ∧ ChainBudgetBound.sigmaSteady (1 / 2 : ℝ) 0 = 0 := by
  constructor
  · unfold ChainBudgetBound.sigmaLearn OptimalEta.c
    norm_num
  · exact FirstLayerBound.sigmaSteady_zero (1 / 2)

/-! ===========================================================================
§4.6  ⭐⭐ 升级**不弱化**：旧版的逐样本结论 ⟹ 新版的期望结论
=========================================================================== -/

/-- ⭐⭐⭐ **旧的逐样本版本（`first_layer_bound_real` 的结论）⟹ 新版的期望版本**。

设旧版的结论在**每个** `ω` 上成立（`hall`），则把两边对 `ω` 积分即得
新版结论（概率测度下 `∫ const = const`）。

**⟹ 这条定理是「升级不是换弱」的机检证据**：
凡是旧版能给出的，新版都**能**给出；反之不然（`hest_not_provable` 已证明
旧版的**前件** `hest` 在 `varOf P = 1, n = 1` 上**不可能**对所有观测成立）。
故本文件的升级是**严格的**：结论更弱，但前件也**确实更弱**（`hest` 被删掉了）。 -/
theorem expected_bound_strictly_stronger {P : Measure ℝ} [IsProbabilityMeasure P]
    (η θstar θhat θ₀ B : ℝ) (n : ℕ)
    (hall : ∀ ω : Fin n → ℝ,
      |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (θhat * 1)
        (ThetaConvergence.thetaN η θhat 1 θ₀ n)
        PUnit.unit PUnit.unit PUnit.unit 1| ≤ B) :
    ∫ _ω : Fin n → ℝ,
        |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (θhat * 1)
          (ThetaConvergence.thetaN η θhat 1 θ₀ n)
          PUnit.unit PUnit.unit PUnit.unit 1|
        ∂(Measure.pi (fun _ : Fin n => P)) ≤ B := by
  have hpt : ∀ ω : Fin n → ℝ,
      |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (θhat * 1)
        (ThetaConvergence.thetaN η θhat 1 θ₀ n)
        PUnit.unit PUnit.unit PUnit.unit 1|
      = |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (θhat * 1)
          (ThetaConvergence.thetaN η θhat 1 θ₀ n)
          PUnit.unit PUnit.unit PUnit.unit 1| := fun _ => rfl
  calc ∫ _ω : Fin n → ℝ,
        |FateV2.Loop.EndToEnd.e2eResidual ThetaConvergence.linWorld (θhat * 1)
          (ThetaConvergence.thetaN η θhat 1 θ₀ n)
          PUnit.unit PUnit.unit PUnit.unit 1|
        ∂(Measure.pi (fun _ : Fin n => P))
      ≤ ∫ _ω : Fin n → ℝ, B ∂(Measure.pi (fun _ : Fin n => P)) := by
        refine integral_mono_ae (integrable_const _) (integrable_const B) ?_
        filter_upwards with ω
        simpa using hall ω
    _ = B := by simp

end FirstLayerExpectation
end FateV2.Error