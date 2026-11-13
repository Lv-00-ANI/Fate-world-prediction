import FateWorld.Legacy.PipelineAdaptiveEtaRobust
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-! ===========================================================================
  `Fate.PipelineAdaptiveEtaStochastic` —— **从确定性有界噪声到概率意义收敛**

  ## 0  本文件补什么

  `Fate/PipelineAdaptiveEtaRobust.lean` 证明的是**确定性**鲁棒收敛

      ‖e_{n+1}‖ ≤ c ‖e_n‖ + M   ⟹   limsup_n ‖e_n‖ ≤ M/(1-c),

  其中 `∀ᶠ n` 是**时间指标**上的滤子，**不是**概率。本文件补上**概率意义**的一端：
  在概率空间 `(Ω, μ)` 上把 `∀ᵐ ω ∂μ`（几乎必然）与逐样本轨迹的极限连接起来。

  ## 1  定理

  * `ae_tendsto_of_all_but_null` —— **定义级推导**：坏集 `Bad` 零测，
    坏集外逐点收敛 ⟹ `∀ᵐ ω, θ_n(ω) → θ*`。（`ae_iff` + `measure_mono_null`）
  * `measure_zero_of_le_all` —— **补充型**：若 `μ Bad ≤ δ` 对一切 `δ > 0`，则 `μ Bad = 0`。
    （`le_of_forall_pos_le_add` + `le_bot_iff`）
  * `ae_tendsto_zero_of_sample_contraction` —— **逐样本压缩 ⟹ 几乎必然收敛**：
    `M = 0` 的无噪递归 `e_{n+1} ≤ c e_n`（`0 ≤ c < 1`）逐样本成立 ⟹
    `‖e_n(ω)‖ → 0` 对几乎处处的 `ω`。这**组合**了 `noise_error_bound` 的几何界与
    `ae_tendsto_of_all_but_null`（这里直接把几何界重新归纳，避免依赖元组形式）。
  * `ae_tendsto_of_meas_le_all` —— `measure_zero_of_le_all` + `ae_tendsto_of_all_but_null`
    的**概率收敛 ⟹ 几乎必然**合成（"任意小概率坏集"版本）。

  ## 2  ⚠ 诚实边界（前件是否把结论包进去？）

  **2.1 不是同义反复。**
  * `ae_tendsto_of_all_but_null` 的前件是**逐点**（`∀ ω, ω ∉ Bad → ...`）
    加**测度**（`μ Bad = 0`）两条**互不相干**的假设；结论是 `∀ᵐ ω ∂μ`。
    从逐点得到「几乎处处」需要 `ae_iff`：`∀ᵐ ω, p ω ↔ μ {ω | ¬p ω} = 0`，
    并把 `{ω | ¬p ω} ⊆ Bad` 用 `measure_mono_null` 传递。结论里的 `∀ᵐ` **不在**前件中。
  * `measure_zero_of_le_all` 的前件是 `∀ δ > 0, μ Bad ≤ δ`，结论 `μ Bad = 0`。
    这需要 `ℝ≥0∞` 上的 `le_of_forall_pos_le_add` + `le_bot_iff`（即 `a ≤ 0 → a = 0`）。
    前件是**双向量化**（每个 `δ`），结论是**等式**，不是前件的特例。
  * `ae_tendsto_zero_of_sample_contraction` 的前件是**逐样本单步**不等式
    `en (n+1) ω ≤ c * en n ω`（加上非负性）；结论是**几乎处处的拓扑极限**
    `Tendsto (fun n => en n ω) atTop (nhds 0)`。中间需要
    (i) 对 `n` 归纳出几何闭合界 `en n ω ≤ c^n en 0 ω`，
    (ii) `c^n → 0`（`tendsto_pow_atTop_nhds_zero_of_lt_one`），
    (iii) 夹逼（`tendsto_of_tendsto_of_tendsto_of_le_of_le`），
    (iv) 再用 `ae_tendsto_of_all_but_null` 转成 `∀ᵐ`。
    前件**不含** `nhds`、`Tendsto`、`∀ᵐ`、`c^n` 中的任何一项。

  **2.2 本项目最高频问题（前件把结论包进去）已逐条核查**：见 §2.1。

  **2.3 `hnonneg` 是必要假设，不是弱化结论。**
  `hrec` 只给**上界**，推不出 `en n ω ≥ 0`；但夹逼需要下界。
  因此显式假设 `hnonneg : ∀ ω n, 0 ≤ en n ω`——在应用里 `en n ω = ‖e_n(ω)‖` 时
  自动成立（范数非负），把它作为前件是**如实的**，不是把结论藏进前件。

  **2.4 不做的事（如实声明）。**
  * **不证 Markov 不等式 / 条件期望 / 鞅收敛定理**。任务书提到的
    `E‖e_{n+1}‖ ≤ c‖e_n‖ + M ⟹ P(‖e_n‖ ≥ ε) ≤ .../ε` 需要 `lintegral`、
    Markov 不等式与可测性假设，本文件**未涉及**。
  * **不涉及 `Martingale` / `Supermartingale`**。Mathlib 的鞅收敛定理较重，
    且在 25 分钟预算内未尝试。
  * **不声称 `μ` 是概率测度**（`μ univ = 1` 未被使用也未被假设）。
  * **不声称 `TendstoInMeasure`**（概率收敛的 `Measure` 版本）；本文件只做
    「坏集零测 ⟹ 几乎必然」和它的「坏集测度任意小」变体。

  **2.5 未证明的条目**：无。**零** `sorry` / `admit` / `axiom` /
  `native_decide` / `maxHeartbeats` / `?_`。

  **2.6 不修改任何已有模块。** 只 `import Fate.PipelineAdaptiveEtaRobust`。
-/

namespace Fate
namespace PipelineAdaptiveEtaStochastic

open MeasureTheory Filter
open scoped Topology ENNReal

theorem ae_tendsto_of_all_but_null
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    (μ : Measure Ω) (Bad : Set Ω) (hBad : μ Bad = 0)
    (θn : ℕ → Ω → E) (θstar : E)
    (h : ∀ ω, ω ∉ Bad →
      Tendsto (fun n => θn n ω) atTop (nhds θstar)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => θn n ω) atTop (nhds θstar) := by
  rw [ae_iff]
  exact measure_mono_null (fun ω hω => by
    by_contra hnb
    exact hω (h ω hnb)) hBad

theorem measure_zero_of_le_all
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Bad : Set Ω)
    (h : ∀ δ : ℝ≥0∞, 0 < δ → μ Bad ≤ δ) : μ Bad = 0 := by
  have h0 : μ Bad ≤ 0 :=
    le_of_forall_pos_le_add (fun e he => by simpa using h e he)
  exact le_bot_iff.1 h0

theorem ae_tendsto_zero_of_sample_contraction
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1)
    (en : ℕ → Ω → ℝ) (hrec : ∀ ω, ∀ n, en (n + 1) ω ≤ c * en n ω)
    (hnonneg : ∀ ω, ∀ n, 0 ≤ en n ω) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => en n ω) atTop (nhds 0) := by
  have hconv : ∀ ω, ω ∉ (∅ : Set Ω) →
      Tendsto (fun n => en n ω) atTop (nhds 0) := by
    intro ω _
    have hbound : ∀ n, en n ω ≤ c ^ n * en 0 ω := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        have hstep : en (k + 1) ω ≤ c * en k ω := hrec ω k
        have hmul : c * en k ω ≤ c * (c ^ k * en 0 ω) :=
          mul_le_mul_of_nonneg_left ih hc0
        calc en (k + 1) ω ≤ c * en k ω := hstep
          _ ≤ c * (c ^ k * en 0 ω) := hmul
          _ = c ^ (k + 1) * en 0 ω := by ring
    have hnn : ∀ n, 0 ≤ en n ω := fun n => hnonneg ω n
    have hpow : Tendsto (fun n : ℕ => c ^ n * en 0 ω) atTop (nhds 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc).mul_const (en 0 ω)
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow
      hnn hbound
  exact ae_tendsto_of_all_but_null μ ∅ (by simp) en 0 hconv

theorem ae_tendsto_of_meas_le_all
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    (μ : Measure Ω) (Bad : Set Ω) (hBad : ∀ δ : ℝ≥0∞, 0 < δ → μ Bad ≤ δ)
    (θn : ℕ → Ω → E) (θstar : E)
    (h : ∀ ω, ω ∉ Bad →
      Tendsto (fun n => θn n ω) atTop (nhds θstar)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => θn n ω) atTop (nhds θstar) :=
  ae_tendsto_of_all_but_null μ Bad (measure_zero_of_le_all μ Bad hBad) θn θstar h

end PipelineAdaptiveEtaStochastic
end Fate
