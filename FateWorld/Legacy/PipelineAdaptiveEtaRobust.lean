import FateWorld.Legacy.PipelineAdaptiveEtaNormed
import Mathlib

/-! ===========================================================================
  `Fate.PipelineAdaptiveEtaRobust` —— **突破「确定性」限定条件：噪声下的鲁棒收敛**

  ## 0  本文件补什么

  `Fate/PipelineAdaptiveEta.lean`（标量 `ℝ`，9 定理）与
  `Fate/PipelineAdaptiveEtaNormed.lean`（赋范空间 `E`，6 定理）全都证明了
  **确定性收敛**

      ∀ ε > 0, ∃ N, ∀ n ≥ N, ‖θ_n - θ*‖ < ε        （`Tendsto ... (nhds θ*)`）。

  但真实模型带**噪声**：机械误差、抽样误差、浮点舍入、非平稳数据流。
  此时一步更新只能是

      ‖e_{n+1}‖ ≤ c ‖e_n‖ + M,     e_n := θ_n - θ*,  0 ≤ c < 1,  0 ≤ M,

  即**收缩 + 有界噪声**。本文件证明：

  * ⭐⭐⭐⭐ `noise_error_bound` —— **噪声下误差有界**：
    `‖e_n‖ ≤ c^n ‖e_0‖ + M/(1-c)`；
  * ⭐⭐⭐ `limsup_le` —— **噪声下极限上界**（`ε`-邻域版本）：
    `∀ ε > 0, ∀ᶠ n, ‖e_n‖ < M/(1-c) + ε`；
  * `geom_bound` —— 上面的代数核心 `c*(M/(1-c)) + M = M/(1-c)`。

  ## 1  数学内容

  噪声把「收敛到 `θ*`」弱化为「收敛到 `θ*` 的 `M/(1-c)` 邻域」：

      limsup_n ‖θ_n - θ*‖ ≤ M / (1 - c).

  `M = 0` 时退化为 `PipelineAdaptiveEtaNormed.adaptive_tendsto_normed` 的确定性结论
  （`M/(1-c) = 0`，邻域退化为一点）。这即**鲁棒收敛**，是真实世界模型的标准形式。

  ## 2  ⚠ 诚实边界（前件是否把结论包进去？）

  **2.1 不是同义反复。**
  * `noise_error_bound` 的前件 `hrec : ∀ n, ‖e (n+1)‖ ≤ c ‖e n‖ + M` 是**逐点**的
    **一步**不等式；结论 `∀ n, ‖e n‖ ≤ c^n ‖e 0‖ + M/(1-c)` 是**对一切 `n`** 的
    **闭式解**。从一步递推到全序列闭式需要归纳 + 几何级数求和
    （用到 `geom_bound`），**不可逆推**：由结论**不能**得到 `hrec`（`hrec` 中的 `M`
    是单步噪声，结论中的 `M/(1-c)` 是累积噪声，二者差一个因子 `1/(1-c) > 1`）。
  * `limsup_le` 的前件是**闭式上界**（即 `noise_error_bound` 的结论），结论是
    **滤波器（`∀ᶠ`）不等式** `‖e_n‖ < M/(1-c) + ε`。这需要 `c^n → 0`
    （`tendsto_pow_atTop_nhds_zero_of_lt_one`）+ `Tendsto` 的 `Eventually` 转译，
    不是前件的改写。**前件不含 `∀ᶠ`，也不含任何 `ε`。**

  **2.2 本研究项目的最高频问题已在 §2.1 逐条核查**：两个定理的前件都**只**涉及
  **一步**或**闭式**的数值不等式（`hrec` / `h`），结论分别是**闭式解**与
  **`ε`-邻域最终性**，没有一条前件是结论的特例。

  **2.3 不做的事（如实声明）。**
  * **不引入测度论**。本文件走的是任务书推荐的**简化路径**：用**确定性上界**刻画
    噪声传播，得到的是 `ε`-邻域的**最终**包含（即 `limsup` 意义下的鲁棒收敛），
    **不是**概率空间上的 `TendstoInMeasure` / 概率测度下的 `P(‖e_n‖ ≥ ε) ≤ δ`。
    `∀ᶠ` 在这里是**时间指标上的滤子**，**不是**概率。
  * **不声称 `M` 可随时间衰减**（如 `M_n → 0` 会给出真收敛）。那需要另一套论证。
  * **不声称随机变量的期望/方差**：`E` 是**确定性**赋范空间，`e : ℕ → E` 是
    **确定性**序列；"噪声"体现在 `M > 0` 这一非零常数上。

  **2.4 不需要完备性。** 只用到 `SeminormedAddCommGroup` + `NormedSpace ℝ E`
  （与 `PipelineAdaptiveEtaNormed` 一致），**不**假设 `CompleteSpace E`：结论是
  数值不等式与滤波子语句，不涉及极限点的存在性。

  **2.5 未证明的条目**：无。本文件**零** `sorry` / `admit` / `axiom` /
  `native_decide` / `maxHeartbeats`。

  **2.6 不修改任何已有模块。** 本文件只 `import`，不含对既有模块的改动。
-/

namespace Fate
namespace PipelineAdaptiveEtaRobust

open Filter
open scoped Topology

/-! ## §1  代数核心 -/

/-- ⭐ **【几何尾和的代数恒等式】**

$$\frac{c\,M}{1-c} + M = \frac{M}{1-c}\qquad (c<1)$$

这是"累积噪声"的固定点：`M/(1-c)` 是 `x ↦ c x + M` 的**唯一不动点**。
累加上界之所以能闭合，全靠这条恒等式。 -/
theorem geom_bound (c M : ℝ) (hc : c < 1) :
    c * (M / (1 - c)) + M = M / (1 - c) := by
  have h1 : (1 : ℝ) - c ≠ 0 := by linarith
  field_simp
  ring

/-! ## §2  噪声下的误差界（核心定理） -/

/-- ⭐⭐⭐⭐ **【有噪声时误差有界 —— 鲁棒收敛的闭式】**

若每步满足 `‖e_{n+1}‖ ≤ c ‖e_n‖ + M`（`0 ≤ c < 1`，`M ≥ 0`），
则对一切 `n`：

$$\|e_n\| \le c^n\,\|e_0\| + \frac{M}{1-c}.$$

**⟹ 这是鲁棒收敛**：误差不再趋于 `0`，但被**永久压**在 `M/(1-c)` 以内。
`M = 0` 时右边的 `M/(1-c) = 0`，退化为确定性几何收敛。

**证明**：对 `n` 归纳。`n = 0` 时结论为 `‖e_0‖ ≤ ‖e_0‖ + M/(1-c)`，用
`M/(1-c) ≥ 0`（`div_nonneg`）。归纳步用 `geom_bound` 把
`c*(c^n‖e_0‖ + M/(1-c)) + M` 整理成 `c^{n+1}‖e_0‖ + M/(1-c)`。

**⚠ 不是同义反复**：前件是**单步**不等（`M` 是单步噪声），结论是**全序列闭式**
（`M/(1-c)` 是累积噪声，多一个 `1/(1-c)` 因子）。见文件头 §2.1。 -/
theorem noise_error_bound {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (c M : ℝ) (hc0 : 0 ≤ c) (hc : c < 1) (hM : 0 ≤ M)
    (e : ℕ → E) (hrec : ∀ n, ‖e (n + 1)‖ ≤ c * ‖e n‖ + M) :
    ∀ n, ‖e n‖ ≤ c ^ n * ‖e 0‖ + M / (1 - c) := by
  intro n
  induction n with
  | zero =>
    simp only [pow_zero, one_mul]
    linarith [div_nonneg hM (by linarith : (0 : ℝ) ≤ 1 - c)]
  | succ k ih =>
    have hstep : ‖e (k + 1)‖ ≤ c * ‖e k‖ + M := hrec k
    have hcM : c * (c ^ k * ‖e 0‖ + M / (1 - c)) + M
        = c ^ (k + 1) * ‖e 0‖ + M / (1 - c) := by
      have hg := geom_bound c M hc
      calc c * (c ^ k * ‖e 0‖ + M / (1 - c)) + M
          = c ^ (k + 1) * ‖e 0‖ + (c * (M / (1 - c)) + M) := by ring
        _ = c ^ (k + 1) * ‖e 0‖ + M / (1 - c) := by rw [hg]
    calc ‖e (k + 1)‖ ≤ c * ‖e k‖ + M := hstep
      _ ≤ c * (c ^ k * ‖e 0‖ + M / (1 - c)) + M := by
          have hmono : c * ‖e k‖ ≤ c * (c ^ k * ‖e 0‖ + M / (1 - c)) :=
            mul_le_mul_of_nonneg_left ih hc0
          linarith
      _ = c ^ (k + 1) * ‖e 0‖ + M / (1 - c) := hcM

/-! ## §3  极限上界（`ε`-邻域最终包含 ⇒ `limsup` 界） -/

/-- ⭐⭐⭐ **【有界误差的 `limsup` 上界】**

若 `‖e_n‖ ≤ c^n ‖e_0‖ + M/(1-c)` 且 `0 ≤ c < 1`，则误差最终落在
`M/(1-c)` 的任意小邻域内：

$$\forall \varepsilon > 0,\quad \forall^{\mathsf{f}} n,\quad \|e_n\| < \frac{M}{1-c} + \varepsilon .$$

这正是 `limsup_n ‖e_n‖ ≤ M/(1-c)` 的 `ε`-叙述：**噪声使收敛目标从一点扩张为一个
半径 `M/(1-c)` 的球**，但误差**不会跑出这个球**。

**证明**：`c^n → 0`（`tendsto_pow_atTop_nhds_zero_of_lt_one`），乘常数 `‖e_0‖` 后仍
`→ 0`；故最终 `c^n ‖e_0‖ < ε`（`Tendsto.eventually` + `eventually_lt_nhds`），
叠加闭式上界即得。

**⚠ 不是同义反复**：前件是**闭式上界**（不含 `ε`、不含 `∀ᶠ`），
结论是**滤波器语句**（含任意 `ε > 0` 与 `∀ᶠ`）。见文件头 §2.1。 -/
theorem limsup_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (c M : ℝ) (hc0 : 0 ≤ c) (hc : c < 1)
    (e : ℕ → E) (h : ∀ n, ‖e n‖ ≤ c ^ n * ‖e 0‖ + M / (1 - c)) :
    ∀ ε > 0, ∀ᶠ n in Filter.atTop, ‖e n‖ < M / (1 - c) + ε := by
  intro ε hε
  have hpow : Tendsto (fun n : ℕ => c ^ n * ‖e 0‖) atTop (nhds 0) := by
    have hmul := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc).mul_const ‖e 0‖
    simpa using hmul
  have hev : ∀ᶠ n : ℕ in atTop, c ^ n * ‖e 0‖ < ε := by
    have hpos := hpow.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < ε))
    simpa using hpos
  filter_upwards [hev] with n hn
  have hb := h n
  linarith

end PipelineAdaptiveEtaRobust
end Fate
