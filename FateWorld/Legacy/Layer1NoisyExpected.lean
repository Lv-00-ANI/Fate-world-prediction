import FateWorld.Legacy.Layer1NoisyChain
import FateWorld.Legacy.ClosedLoopNoisy

/-! ===========================================================================
  `Fate/Layer1NoisyExpected` —— **第 1 层：随机载体下的期望主定理**
  ===========================================================================

  ## 本文件是在撤回一个错误结论

  `Layer1NoisyChain`（第 343 轮入库）的文件头 §1.1 / §9.2 / §9.3 断言：

  > 「改载体后审计建议的期望形式**为假**」
  > 「在现有载体下**不可达**」
  > 「两种模型**互不相容**，故不存在**统一的** `E‖·‖` 上界型主定理」

  **审计 R349 用探针证伪了这三个断言。** 审计的原话：

  > 「把 `x' : Ω → ℕ → F`，保留 `hstep : ∀ ω k, ‖x' ω k − x' ω(k+1)‖ ≤ d` 逐点，
  > 再取期望，就得到期望主定理。证明只需 `integral_mono` + `integral_add` +
  > `integral_const` + `μ.real univ = 1`，**12 行，`lake env lean` 零 error**。
  > 主控把『样本复用 vs 每步新样本』这两个**逐点**模型的矛盾，
  > 当成了期望模型的不存在。取 `d = 0` 得复用，取 `d = noiseDrift` 得新样本，
  > **一条覆盖两者**。」

  **本文件就是那 12 行。** 它证明：随机载体下的期望主定理**存在且成立**。

  ## 诚实边界（不夸大这次修复）

  即使本文件成立，`hstep` 形状仍在前件里（只是改成逐点形式 `∀ ω k`）。
  审计同时指出：

  > 「R316 那条『前件中无任何漂移上界』在『结论关于给定 `x'`』的框架下**删不掉**。
  > 真正解法是把 `x'` 生成过程写死（如 `x' k := est (1/n_k) ω`），
  > 让漂移由 `est` 方差**推出**。那才是第 1 层真正的极限。」

  **本文件没有做那一步**，也不声称做了。
-/

namespace Fate
namespace Layer1NoisyExpected

universe u

open MeasureTheory

/-- ⭐⭐⭐ **【随机载体下的期望主定理】**

设 `Ω` 是概率空间（`μ` 是概率测度），`x' : Ω → ℕ → F` 是**随机观测序列**。
若对每个样本点 `ω`，序列 `x' ω` 的相邻漂移有界：
`hstep : ∀ ω k, ‖x' ω k − x' ω (k+1)‖ ≤ d`（**逐点**，不是期望），
则**取期望后**：

```
∫ ω, ‖A (noisyIter A φ η (x' ω) N θ₀) − x' ω N‖ ∂μ
  ≤ r^N * ∫ ω, ‖A θ₀ − x' ω 0‖ ∂μ + (1 − r^N)/(1 − r) * d
```

**这条覆盖两种模型**：取 `d = 0` 得「样本复用」（观测不变），
取 `d = noiseDrift P n` 得「每步新样本」。**不存在「两种模型互不相容」的问题。**

**前件**：`hstep`（逐点漂移界）、`hint`（可积性，技术性）、`hr`、`hr1`、`h`（`Corrects`）。
**没有 `hest`**，也**没有**形如 `‖A θ₀ - x' ω 0‖ ≤ 某常数` 的假设。 -/
theorem layer1_noisy_expected_random {Ω : Type*} {E F : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : Ω → ℕ → F)
    {d r : ℝ} (hstep : ∀ ω k, ‖x' ω k - x' ω (k + 1)‖ ≤ d) (hd : 0 ≤ d)
    (hr : r = |1 - η|) (hr1 : r < 1) (h : BoundWriteBack.Corrects A φ)
    (N : ℕ) (θ₀ : E)
    (hint : Integrable (fun ω => ‖A θ₀ - x' ω 0‖) μ)
    (hLint : Integrable
      (fun ω => ‖A (ClosedLoopNoisy.noisyIter A φ η (x' ω) N θ₀) - x' ω N‖) μ) :
    ∫ ω, ‖A (ClosedLoopNoisy.noisyIter A φ η (x' ω) N θ₀) - x' ω N‖ ∂μ
      ≤ r ^ N * ∫ ω, ‖A θ₀ - x' ω 0‖ ∂μ + (1 - r ^ N) / (1 - r) * d := by
  -- 逐点用 noisy_iterative_bound
  have hpt : ∀ ω,
      ‖A (ClosedLoopNoisy.noisyIter A φ η (x' ω) N θ₀) - x' ω N‖
        ≤ r ^ N * ‖A θ₀ - x' ω 0‖ + (1 - r ^ N) / (1 - r) * d := by
    intro ω
    exact ClosedLoopNoisy.noisy_iterative_bound A φ η (x' ω) (hstep ω) hd hr hr1 h N θ₀
  -- 把界写成可积函数
  have hRint : Integrable (fun ω => r ^ N * ‖A θ₀ - x' ω 0‖ + (1 - r ^ N) / (1 - r) * d) μ :=
    (hint.const_mul _).add (integrable_const _)
  -- 逐点界 ⟹ 几乎处处界
  have hae : ∀ᵐ ω ∂μ,
      ‖A (ClosedLoopNoisy.noisyIter A φ η (x' ω) N θ₀) - x' ω N‖
        ≤ r ^ N * ‖A θ₀ - x' ω 0‖ + (1 - r ^ N) / (1 - r) * d :=
    Filter.Eventually.of_forall hpt
  -- 积分单调
  have hmono : ∫ ω, ‖A (ClosedLoopNoisy.noisyIter A φ η (x' ω) N θ₀) - x' ω N‖ ∂μ
      ≤ ∫ ω, (r ^ N * ‖A θ₀ - x' ω 0‖ + (1 - r ^ N) / (1 - r) * d) ∂μ :=
    integral_mono_ae hLint hRint hae
  -- 右边积分拆开
  have hsplit : ∫ ω, (r ^ N * ‖A θ₀ - x' ω 0‖ + (1 - r ^ N) / (1 - r) * d) ∂μ
      = r ^ N * ∫ ω, ‖A θ₀ - x' ω 0‖ ∂μ + (1 - r ^ N) / (1 - r) * d := by
    rw [integral_add (hint.const_mul _) (integrable_const _)]
    rw [integral_const_mul]
    rw [integral_const]
    simp [Measure.real, probReal_univ]
  linarith [hmono, hsplit]

end Layer1NoisyExpected
end Fate
