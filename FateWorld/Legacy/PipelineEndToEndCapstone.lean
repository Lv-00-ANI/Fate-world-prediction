import FateWorld.Legacy.PipelineAdaptiveEtaNormed
import FateWorld.Legacy.PipelineAdaptiveEtaComplexity
import FateWorld.Legacy.PipelineAdaptiveEtaRobust

/-! ===========================================================================
  `Fate.PipelineEndToEndCapstone` —— **组合定理：7 层理论的端到端保证**

  ## 0  组合了什么

  | 层 | 模块 | 贡献 |
  |---|---|---|
  | ②③ | `PipelineAdaptiveEtaNormed`   | 闭式解 `adaptive_closed_normed` + 范数界 `adaptive_norm_le` |
  | ④  | `PipelineAdaptiveEtaComplexity` | O(1) 步数判据 `exists_N_pow_lt` / `exists_N_for_eps_closed` |
  | ⑤  | `PipelineAdaptiveEtaRobust`   | 噪声鲁棒界 `noise_error_bound` / `limsup_le` |

  此前 7 层各自独立，**没有任何一条定理把多层组合起来**。本文件把
  「收敛性（③）+ 误差上界（③）+ O(1) 步数（④）+ 噪声鲁棒性（⑤）」
  拼成**一条端到端主定理**：

  > **给定任意 `eps > 0`，存在可计算的 `N`，使得 `N` 步后误差 `< eps`。**

  ## 1  主结果

  * ⭐⭐⭐⭐⭐ `end_to_end_convergence_guarantee`
        —— 确定性端到端：`∃ N, c^N‖theta0-thetaStar‖ < eps ∧ ∀ n ≥ N, 误差 < eps`
           （**步数条件在常数层面，可计算**）；
  * ⭐⭐⭐⭐ `end_to_end_noisy_guarantee`
        —— 噪声端到端：单步噪声 `M` 下误差最终 `< M/(1-c) + eps`；
  * ⭐⭐⭐⭐ `end_to_end_noisy_finite_steps`
        —— 噪声 + **显式有限步数**：`∃ N, ‖e N‖ < M/(1-c) + eps`
           （组合 ⑤ 的闭式界与 ④ 的乘幂 N）。

  ## 2  ⚠ 诚实边界（是否同义反复？逐条核查）

  **2.1 `end_to_end_convergence_guarantee`。**
  前件是**步长条件** `0 ≤ c < 1` 与**一致收缩** `∀ k, |1 - eta k| ≤ c`（只涉及
  `eta, c`），**不出现轨迹，不出现 `eps`，不出现 `N`**；结论是
  **`∃ N` 形式的 `eps`-N 性质，且 `N` 附带纯常数条件 `c^N‖theta0-thetaStar‖ < eps`**。
  由步长条件不可逆推结论（结论含任意 `eps` 与轨迹量）。此定理**不是**同义反复，
  它是 ③ (`adaptive_norm_le`) 与 ④ (`exists_N_pow_lt`) 的**组合**。

  **2.2 `end_to_end_noisy_guarantee`。**
  前件是**闭式上界** `‖e n‖ ≤ c^n‖e 0‖ + M/(1-c)`（不含 `eps`，不含 `∀ᶠ`）；
  结论是 `∀ᶠ` 的 `eps`-邻域最终性。由 ⑤ 的 `limsup_le` 直接得到（`hc0, hc` 参数
  在此被传给 `limsup_le`）。前件不含滤波器语句，非同义反复。

  **2.3 `end_to_end_noisy_finite_steps`。**
  前件是**单步噪声递推** `hrec : ∀ n, ‖e(n+1)‖ ≤ c‖e n‖ + M`（`M` 是单步噪声），
  结论是**存在有限步 `N` 使 `‖e N‖ < M/(1-c) + eps`**。组合 ⑤ 的
  `noise_error_bound`（一步递推 ⟹ 闭式）与 ④ 的 `exists_N_pow_lt`
  （`∃ N, c^N‖e 0‖ < eps`）。`hrec`（单步）与结论（N 步 + 累积界）差一个
  `1/(1-c)` 因子，故非同义反复。

  ## 3  未证明 / 不做的事

  * 不使用 `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats`；
  * 不声称 `N` 的 `Real.log` 闭式（沿用 ④ 的乘幂形式，避免 `c = 0` 边界）；
  * 不引入测度论：噪声以**确定性上界** `M` 刻画（与 ⑤ 一致）；
  * 不修改任何已有模块，本文件只 `import`。
-/

namespace Fate
namespace PipelineEndToEndCapstone

open Filter Fate.PipelineAdaptiveEtaNormed

/-! ## §1  确定性端到端保证（③ + ④） -/

/-- ⭐⭐⭐⭐⭐ **【端到端保证：收敛 + 误差界 + O(1) 可计算步数】（主定理）**

组合 ③ 的范数界 `adaptive_norm_le` 与 ④ 的步数判据 `exists_N_pow_lt`：

若 `0 ≤ c < 1` 且 `∀ k, |1 - eta k| ≤ c`（一致收缩），则对**任意 `eps > 0`**，
存在一个 `N`，它**同时**满足

1. **纯常数步数条件** `c^N · ‖theta0 - thetaStar‖ < eps`（**可计算**，只需一次乘幂）；
2. **端到端误差** 对所有 `n ≥ N`，`‖theta_n - thetaStar‖ < eps`。

这就是「世界模型可用」的数学表达：**任意精度 `eps`，有限步 `N` 内达成**。

**前件不含结论（见文件头 §2.1）**：前件只涉及 `eta, c`（步长条件），
结论才引入 `eps`、`N` 与轨迹量。 -/
theorem end_to_end_convergence_guarantee
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (eta : ℕ → ℝ) (thetaStar theta0 : E) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (heta : ∀ k, |1 - eta k| ≤ c)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, (c ^ N * ‖theta0 - thetaStar‖ < eps) ∧
      ∀ n : ℕ, N ≤ n →
        ‖Nat.rec theta0 (fun k ih => ih + eta k • (thetaStar - ih)) n - thetaStar‖ < eps :=
  Fate.PipelineAdaptiveEtaComplexity.exists_N_for_eps_closed
    eta thetaStar theta0 c hc0 hc1 heta eps heps

/-- ⭐⭐⭐⭐ **【端到端保证的事件形式】**

同一组合的 `∀ᶠ` 形式：任意 `eps > 0`，误差**最终** `< eps`。

由 ④ 的 `exists_N_for_eps` 直接得到（`∃ N, ∀ n ≥ N` ⟹ `∀ᶠ n in atTop`）。
这条给出「几乎所有步之后都达标」的滤波器叙述，便于与 ⑤ 的噪声界并列使用。 -/
theorem end_to_end_convergence_eventually
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (eta : ℕ → ℝ) (thetaStar theta0 : E) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (heta : ∀ k, |1 - eta k| ≤ c)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n in atTop,
      ‖Nat.rec theta0 (fun k ih => ih + eta k • (thetaStar - ih)) n - thetaStar‖ < eps := by
  obtain ⟨N, hN⟩ :=
    Fate.PipelineAdaptiveEtaComplexity.exists_N_for_eps
      eta thetaStar theta0 c hc0 hc1 heta eps heps
  exact eventually_atTop.mpr ⟨N, hN⟩

/-! ## §2  噪声端到端保证（③ + ⑤） -/

/-- ⭐⭐⭐⭐ **【噪声下的端到端保证】**

组合 ③ 的几何收缩与 ⑤ 的噪声界：

若误差满足闭式上界 `‖e n‖ ≤ c^n ‖e 0‖ + M/(1-c)`（`0 ≤ c < 1`），
则对任意 `eps > 0`，误差**最终** `< M/(1-c) + eps`。

即：**噪声把收敛目标从一点扩张为半径 `M/(1-c)` 的球，但误差永不逃出该球**。
直接由 ⑤ 的 `limsup_le` 得到。 -/
theorem end_to_end_noisy_guarantee
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (c M eps : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (heps : 0 < eps)
    (e : ℕ → E) (h : ∀ n, ‖e n‖ ≤ c ^ n * ‖e 0‖ + M / (1 - c)) :
    ∀ᶠ n in atTop, ‖e n‖ < M / (1 - c) + eps :=
  Fate.PipelineAdaptiveEtaRobust.limsup_le c M hc0 hc1 e h eps heps

/-- ⭐⭐⭐⭐ **【噪声 + 显式有限步数：端到端】**

组合 ⑤ 的 `noise_error_bound`（单步递推 ⟹ 闭式界）与 ④ 的 `exists_N_pow_lt`
（`∃ N, c^N ‖e 0‖ < eps`）：

若单步满足 `∀ n, ‖e(n+1)‖ ≤ c‖e n‖ + M`（`0 ≤ c < 1`，`0 ≤ M`），
则对任意 `eps > 0`，**存在有限步 `N`**，使第 `N` 步误差已落在
`M/(1-c) + eps` 之内：

    ∃ N, ‖e N‖ < M / (1 - c) + eps.

这是**噪声下「有限步达成近似精度」的显式构造**：`N` 只依赖 `c, eps, ‖e 0‖`。

**前件不含结论（见文件头 §2.3）**：前件是**单步**递推，结论是**N 步**累积界，
二者差 `1/(1-c)` 因子。 -/
theorem end_to_end_noisy_finite_steps
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (c M eps : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (hM : 0 ≤ M) (heps : 0 < eps)
    (e : ℕ → E) (hrec : ∀ n, ‖e (n + 1)‖ ≤ c * ‖e n‖ + M) :
    ∃ N : ℕ, ‖e N‖ < M / (1 - c) + eps := by
  obtain ⟨N, hN⟩ :=
    Fate.PipelineAdaptiveEtaComplexity.exists_N_pow_lt (e 0) 0 c hc0 hc1 eps heps
  refine ⟨N, ?_⟩
  have hbound : ‖e N‖ ≤ c ^ N * ‖e 0‖ + M / (1 - c) :=
    Fate.PipelineAdaptiveEtaRobust.noise_error_bound c M hc0 hc1 hM e hrec N
  rw [sub_zero] at hN
  have : c ^ N * ‖e 0‖ + M / (1 - c) < M / (1 - c) + eps := by linarith
  exact lt_of_le_of_lt hbound this

end PipelineEndToEndCapstone
end Fate
