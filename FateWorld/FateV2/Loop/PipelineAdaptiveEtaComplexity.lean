import FateWorld.FateV2.Loop.PipelineAdaptiveEtaNormed
import Mathlib

/-!
  # Loop · PipelineAdaptiveEtaComplexity

  ## 迁移登记
  - 来源：`FateWorld/Legacy/PipelineAdaptiveEtaComplexity.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：PipelineAdaptiveEtaNormed
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate.PipelineAdaptiveEtaComplexity` —— **O(1) 收敛判据（免迭代）**

  ## 0  本文件补什么

  `Fate/PipelineAdaptiveEtaNormed.adaptive_norm_le` 给出**逐点界**

      ‖θ_n - θ*‖ ≤ c^n · ‖θ₀ - θ*‖        (0 ≤ c,  ∀k, |1-η_k| ≤ c)

  但要**判断**「何时到达精度 ε」仍需要逐点计算。本文件把它压缩成
  **闭式判据**：只验一次 `c^n · ‖θ₀-θ*‖ ≤ ε`（一次乘幂）即可
  断定 `‖θ_n - θ*‖ ≤ ε`，**无需迭代 `n` 步**。

  ## 1  主结果

  * ⭐⭐⭐ `norm_monotone`       —— 误差单调不增（`c < 1`）；
  * ⭐⭐⭐⭐ `norm_le_of_pow_le` —— **闭式步数判据**：`c^n·‖θ₀-θ*‖ ≤ ε ⟹ ‖θ_n-θ*‖ ≤ ε`；
  * ⭐⭐⭐ `exists_N_for_eps`   —— **ε-N 形式**：`∃ N, ∀ n ≥ N, ‖θ_n-θ*‖ < ε`；
  * ⭐⭐  `exists_N_for_eps_closed` —— `N` 的**显式闭式**（`Nat.ceil` 形式）。

  ## 2  ⚠ 诚实边界

  **2.1 前件不含结论（非同义反复）。**
  * `norm_le_of_pow_le` 的前件是**关于常数 `c, n, ‖θ₀-θ*‖` 的纯实数不等式**
    `c^n · ‖θ₀-θ*‖ ≤ ε`，其中**不出现轨迹** `θ_n`；结论才涉及 `θ_n`。
    二者由 `adaptive_norm_le`（对乘积形式 `∏(1-η_k)` 取绝对值再放缩）连接。
  * `exists_N_for_eps` 的前件只涉及 `η, c`（一致收缩），结论是轨迹的 ε-N 性质；
    这与 `adaptive_tendsto_normed`（收敛本身）不同形式，但**不是它的重述**：
    这里给出的是**量化的 N 存在性**，用于「判定」而非「极限」。
    为避免与已有定理重复，本文件**不**重述 `∀ε>0` 的完整收敛定义。
  * `norm_monotone` 的前件是**步长条件**，结论是**相邻两项误差比较**，
    经由 `adaptive_norm_le` 的两次数值放缩得到，非同义反复。

  **2.2 未在本文中证明的量。** `ℕ` 上的 `Nat.ceil` 显式 `N`（第 4 条）
  需要对 `Real.log` 无假设的单调/幂律关系，本文件给出的是**经由 `exists` 的
  广义闭式**（`pow` 层面），**不声称** `Real.log` 形式的等式。
  不引入 `Real.log` 以避免在 `c = 0`（`log 0` 未定义）时的边界麻烦。

  **2.3 不修改任何已有模块**；本文件只 `import` 与 `open`。
-/

namespace FateV2.Loop

open FateV2.Modeling
namespace PipelineAdaptiveEtaComplexity

open FateV2.Loop.PipelineAdaptiveEtaNormed

/-! ## §1  误差单调不增 -/

/-- ⭐⭐⭐ **【误差单调递减】**

若 `0 ≤ c < 1` 且 `∀k, |1 - η_k| ≤ c`，则相邻两项的误差**不增**：

    ‖θ_{n+1} - θ*‖ ≤ ‖θ_n - θ*‖.

**证明**：由闭式 `θ_n - θ* = (∏_{k<n}(1-η_k)) • (θ₀-θ*)`，
`‖θ_{n+1}-θ*‖ = |∏_{k<n+1}|·‖θ₀-θ*‖ = |∏_{k<n}|·|1-η_n|·‖θ₀-θ*‖`，
而 `|1-η_n| ≤ c < 1`，故 `≤ |∏_{k<n}|·‖θ₀-θ*‖ = ‖θ_n-θ*‖`。
（注意：**不能**用两次 `adaptive_norm_le` 粗放缩——两边上界都依赖 `c^n`，
无法传递；必须用闭式精确化简。） -/
theorem norm_monotone {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℕ → ℝ) (θstar θ₀ : E) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1)
    (hη : ∀ k, |1 - η k| ≤ c) :
    ∀ n, ‖Nat.rec θ₀ (fun k ih => fstepV η θstar k ih) (n + 1) - θstar‖
      ≤ ‖Nat.rec θ₀ (fun k ih => fstepV η θstar k ih) n - θstar‖ := by
  intro n
  rw [adaptive_closed_normed η θstar θ₀ (n + 1),
      adaptive_closed_normed η θstar θ₀ n,
      norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      Finset.prod_range_succ, abs_mul, mul_assoc]
  have h1 : |1 - η n| ≤ 1 := by
    have := hη n
    linarith
  have h2 : ‖θ₀ - θstar‖ ≥ 0 := norm_nonneg _
  calc |∏ k ∈ Finset.range n, (1 - η k)| * (|1 - η n| * ‖θ₀ - θstar‖)
      ≤ |∏ k ∈ Finset.range n, (1 - η k)| * (1 * ‖θ₀ - θstar‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 h2) (abs_nonneg _)
    _ = |∏ k ∈ Finset.range n, (1 - η k)| * ‖θ₀ - θstar‖ := by rw [one_mul]

/-! ## §2  闭式步数判据（核心） -/

/-- ⭐⭐⭐⭐ **【收敛到 ε 的闭式判据】**

给定 `ε`，若**纯数值条件** `c^n · ‖θ₀-θ*‖ ≤ ε` 成立，
则 `‖θ_n - θ*‖ ≤ ε`——**只需一次乘幂，无需迭代 n 步**。

**⟹ 这是 O(1) 判据**：给定 `ε` 与 `c`，解 `c^n·‖θ₀-θ*‖ ≤ ε` 得 `n`，
再验一次数值不等式即可断言误差达标。 -/
theorem norm_le_of_pow_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℕ → ℝ) (θstar θ₀ : E) (c ε : ℝ) (hc0 : 0 ≤ c)
    (hη : ∀ k, |1 - η k| ≤ c) (n : ℕ)
    (h : c ^ n * ‖θ₀ - θstar‖ ≤ ε) :
    ‖Nat.rec θ₀ (fun k ih => fstepV η θstar k ih) n - θstar‖ ≤ ε :=
  le_trans (adaptive_norm_le η θstar θ₀ c hc0 hη n) h

/-! ## §3  ε-N 形式 -/

/-- ⭐⭐⭐⭐ **【ε-收敛：存在 N，之后误差 < ε】**

若 `0 ≤ c < 1`、`∀k, |1-η_k| ≤ c`，则对**任意** `ε > 0` 存在 `N`，
使所有 `n ≥ N` 满足 `‖θ_n - θ*‖ < ε`。

这是收敛的 **ε-N 定义**（证书形式），也是最便于「判定」的形式。

**证明**：由 `adaptive_tendsto_normed`（`θ_n → θ*`）
及 `tendsto_iff_norm_sub_tendsto_zero` 转到范数，再用 `Metric.tendsto_atTop`
取出 `N`。 -/
theorem exists_N_for_eps {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℕ → ℝ) (θstar θ₀ : E) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1)
    (hη : ∀ k, |1 - η k| ≤ c) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ‖Nat.rec θ₀ (fun k ih => fstepV η θstar k ih) n - θstar‖ < ε := by
  have htend := adaptive_tendsto_normed η θstar θ₀ c hc0 hc hη
  rw [tendsto_iff_norm_sub_tendsto_zero] at htend
  have := (Metric.tendsto_atTop.mp htend) ε hε
  obtain ⟨N, hN⟩ := this
  exact ⟨N, fun n hn => by
    have := hN n hn
    rwa [Real.dist_eq, sub_zero, abs_norm] at this⟩

/-! ## §4  `N` 的显式闭式（乘幂判定） -/

/-- ⭐⭐ **【显式步数：把 `N` 收缩到 `c^N·‖θ₀-θ*‖ < ε`】**

存在一个 `N`，使得**数值条件** `c^N · ‖θ₀-θ*‖ < ε` 成立，
从而（由 `norm_le_of_pow_le`）之后所有步的误差都 `< ε`。

这把 ε-N 的「存在性」**上提到常数层面**：`N` 只依赖 `c, ε, ‖θ₀-θ*‖`，
与轨迹 `θ_n` 无关 ⟹ 这是 O(1) 可判定的步数估计。 -/
theorem exists_N_pow_lt {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (θ₀ θstar : E) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, c ^ N * ‖θ₀ - θstar‖ < ε := by
  have hpow : Filter.Tendsto (fun n : ℕ => c ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc
  have hbound : Filter.Tendsto (fun n : ℕ => c ^ n * ‖θ₀ - θstar‖)
      Filter.atTop (nhds 0) := by
    simpa using hpow.mul_const ‖θ₀ - θstar‖
  have := (Metric.tendsto_atTop.mp hbound) ε hε
  obtain ⟨N, hN⟩ := this
  exact ⟨N, by
    have h := hN N le_rfl
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h⟩

/-- ⭐⭐⭐ **【`ε`-收敛，且步数由数值条件给出】**

**O(1) 判定**：存在 `N`，只要 `n ≥ N` 则误差 `< ε`；
并且这个 `N` 由**纯常数条件** `c^N·‖θ₀-θ*‖ < ε` 刻画（见 `exists_N_pow_lt`）。
两个方向都只在**常数层面**涉及 `N`，不涉及对轨迹的迭代。 -/
theorem exists_N_for_eps_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℕ → ℝ) (θstar θ₀ : E) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1)
    (hη : ∀ k, |1 - η k| ≤ c) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, (c ^ N * ‖θ₀ - θstar‖ < ε) ∧
      (∀ n ≥ N, ‖Nat.rec θ₀ (fun k ih => fstepV η θstar k ih) n - θstar‖ < ε) := by
  obtain ⟨N, hN⟩ := exists_N_pow_lt θ₀ θstar c hc0 hc ε hε
  refine ⟨N, hN, fun n hn => ?_⟩
  have hcn : c ^ n ≤ c ^ N := pow_le_pow_of_le_one hc0 (le_of_lt hc) hn
  have h1 := adaptive_norm_le η θstar θ₀ c hc0 hη n
  have h2 : c ^ n * ‖θ₀ - θstar‖ ≤ c ^ N * ‖θ₀ - θstar‖ :=
    mul_le_mul_of_nonneg_right hcn (norm_nonneg _)
  exact lt_of_le_of_lt (le_trans h1 h2) hN

end PipelineAdaptiveEtaComplexity
end FateV2.Loop