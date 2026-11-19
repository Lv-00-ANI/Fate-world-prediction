import FateWorld.FateV2.Loop.ThetaConvergence
/-!
  # Loop · PipelineAdaptiveEta

  ## 迁移登记
  - 来源：`FateWorld/Legacy/PipelineAdaptiveEta.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ThetaConvergence
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `PipelineAdaptiveEta` —— **变步长（自适应步长）的端到端收敛**

  ## 0  本文件补什么

  既有端到端收敛（`Fate/ThetaConvergence.lean`、`Fate/EndToEndUnconditionalQ.lean`、
  `Fate/EndToEndQConsumer.lean`）**全部是固定步长 `η`** 的结论：
  `θ_n - θ* = (1-η)^n (θ₀ - θ*)`。

  本文件推广到**步长随步数变化** `η : ℕ → ℝ`：

      θ_{n+1} = θ_n + η_n (θ* - θ_n)  =  (1 - η_n) θ_n + η_n θ*
      ⟹  θ_n - θ* = (∏_{k<n} (1 - η_k)) (θ₀ - θ*)

  ## 1  主结果（3 条，全部无条件 / 条件仅关于步长本身）

  * `thetaN_adaptive_closed` —— 变步长 `n` 步**闭式**（乘积形式）；
  * `thetaN_adaptive_tendsto` —— 若 `∀ k, |1 - η_k| ≤ c` 且 `0 ≤ c < 1`，
    则 `θ_n → θ*`（**收敛**）；
  * `thetaN_harmonic_tendsto` —— 经典特例 `η_k = 1/(k+1)`：
    此时 `∏_{k<n} (1-η_k) = 1/(n+1)`，故 `θ_n → θ*`。

  ## 2  ⚠ 诚实边界

  **2.1 前件不含结论。** `thetaN_adaptive_tendsto` 的前件只关于**步长序列** `η`
  （`|1-η_k| ≤ c < 1`）和常数 `c`；结论是关于**轨迹** `θ_n` 的收敛。
  二者由 §3 的闭式连接，**不是同义反复**。（对比：若前件写成
  「`θ_n → θ*`」则为同义反复；本文件没有这样写。）

  **2.2 本文件不声称 `Σ η_k = ∞ ∧ η_k → 0 ⟹ 收敛` 的完整调和判据。**
  那需要「无穷乘积 → 0」的数学分析；本文件只给出该判据的**最简单特例**
  `η_k = 1/(k+1)`（此时乘积可**显式**算成 `1/(n+1)`），
  以及在**一致收缩**假设下的通用定理。**完整的调和判据不在本文件中**。

  **2.3 与固定步长的关系。** 取 `η` 为常函数 `η_k ≡ η` 时，
  `thetaN_adaptive_tendsto` 退化为 `|1-η| ≤ c < 1` 条件下的固定步长收敛
  （与 `ThetaConvergence.linWorld_tendsto_thetaStar` 同结论，条件是它的弱化版）。
  **本文件不修改任何已有模块。**
-/

namespace FateV2.Loop
namespace PipelineAdaptiveEta

open Filter

/-- ⭐⭐ **【变步长的一步更新】**：`θ ↦ (1 - η_n) θ + η_n θ*`。

以 `θ + η_n (θ* - θ)` 的形式给出，与「沿残差方向走一步」的语义直接对应。 -/
noncomputable def fstepN (η : ℕ → ℝ) (θstar : ℝ) (n : ℕ) (θ : ℝ) : ℝ :=
  θ + η n * (θstar - θ)

/-- ⭐ **一步更新的偏差形式**：`fstepN η θ* n θ - θ* = (1 - η_n)(θ - θ*)`。 -/
theorem fstepN_sub (η : ℕ → ℝ) (θstar : ℝ) (n : ℕ) (θ : ℝ) :
    fstepN η θstar n θ - θstar = (1 - η n) * (θ - θstar) := by
  simp only [fstepN]; ring

/-- ⭐ **`n` 步迭代的偏差 = 一步偏差乘以前缀乘积的递推**（辅助）。 -/
theorem thetaN_adaptive_closed_aux (η : ℕ → ℝ) (θstar θ₀ : ℝ) :
    ∀ n : ℕ, (Nat.rec θ₀ (fun k ih => fstepN η θstar k ih) n) - θstar
      = ((Finset.range n).prod (fun k => (1 - η k))) * (θ₀ - θstar)
  | 0 => by simp
  | n + 1 => by
    have ih := thetaN_adaptive_closed_aux η θstar θ₀ n
    rw [show Nat.rec θ₀ (fun k ih => fstepN η θstar k ih) (n + 1)
          = fstepN η θstar n (Nat.rec θ₀ (fun k ih => fstepN η θstar k ih) n) from rfl,
      fstepN_sub, ih, Finset.prod_range_succ]
    ring

/-- ⭐⭐⭐ **【变步长的 n 步闭式】**

$$\boxed{\;\theta_n - \theta^* = \Bigl(\prod_{k<n} (1-\eta_k)\Bigr)(\theta_0-\theta^*)\;}$$

**这是固定步长 `fstep_iterate_closed` 的推广**：取 `η` 为常函数即退化回去。
**收敛性完全由「乘积 → 0」决定**（见下一条）。 -/
theorem thetaN_adaptive_closed (η : ℕ → ℝ) (θstar θ₀ : ℝ) (n : ℕ) :
    (Nat.rec θ₀ (fun k ih => fstepN η θstar k ih) n) - θstar
      = ((Finset.range n).prod (fun k => (1 - η k))) * (θ₀ - θstar) :=
  thetaN_adaptive_closed_aux η θstar θ₀ n

/-- ⭐⭐ **【乘积的绝对值上界】**：若每步 `|1-η_k| ≤ c`，则
`|∏_{k<n} (1-η_k)| ≤ c^n`。 -/
theorem prod_abs_le_pow (η : ℕ → ℝ) (c : ℝ)
    (hη : ∀ k, |1 - η k| ≤ c) (n : ℕ) :
    |(Finset.range n).prod (fun k => (1 - η k))| ≤ c ^ n := by
  rw [Finset.abs_prod]
  calc ∏ k ∈ Finset.range n, |1 - η k|
      ≤ ∏ _k ∈ Finset.range n, c := Finset.prod_le_prod (fun k _ => abs_nonneg _) (fun k _ => hη k)
    _ = c ^ n := by simp

/-- ⭐⭐⭐⭐ **【主定理：一致收缩步长 ⟹ 收敛到真值 `θ*`】**

若存在 `c` 使 `0 ≤ c < 1` 且 `∀ k, |1 - η_k| ≤ c`，则变步长轨迹
`θ_n` 收敛到 `θ*`。

**前件只关于步长序列 `η` 与常数 `c`**，结论是关于轨迹的收敛 —— **非同义反复**。
证明：闭式 + `|∏| ≤ c^n` + `c^n → 0` + 乘常数。 -/
theorem thetaN_adaptive_tendsto (η : ℕ → ℝ) (θstar θ₀ : ℝ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1) (hη : ∀ k, |1 - η k| ≤ c) :
    Tendsto (fun n => Nat.rec θ₀ (fun k ih => fstepN η θstar k ih) n)
      atTop (nhds θstar) := by
  -- 偏差 → 0
  have hpow : Tendsto (fun n : ℕ => c ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc
  have hbound : Tendsto (fun n : ℕ =>
      ((Finset.range n).prod (fun k => (1 - η k))) * (θ₀ - θstar)) atTop (nhds 0) := by
    have hc' : Tendsto (fun n : ℕ => c ^ n * |θ₀ - θstar|) atTop (nhds 0) := by
      simpa using hpow.mul_const |θ₀ - θstar|
    refine squeeze_zero_norm (fun n => ?_) hc'
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (prod_abs_le_pow η c hη n) (abs_nonneg _)
  have h2 : Tendsto (fun n : ℕ =>
      θstar + ((Finset.range n).prod (fun k => (1 - η k))) * (θ₀ - θstar))
      atTop (nhds (θstar + 0)) := hbound.const_add θstar
  rw [add_zero] at h2
  refine h2.congr (fun n => ?_)
  have h := thetaN_adaptive_closed η θstar θ₀ n
  linarith

/-- ⭐⭐ **【调和步长的望远镜乘积，平移形式】**

`∏_{k≤n} (1 - 1/(k+2)) = ∏_{k≤n} (k+1)/(k+2) = 1/(n+2)`。

**⚠ 为什么用 `η_k = 1/(k+2)` 而不是 `1/(k+1)`**：
`η_k = 1/(k+1)` 在 `k = 0` 处是 `1`，故因子 `1 - 1 = 0`，
乘积对**所有** `n ≥ 1` 恒为 `0`（见 `prod_harmonic_zero`）—— 那是平凡情形。
平移一位后乘积真正望远镜化，得到非平凡且显式的 `1/(n+2)`。 -/
theorem prod_harmonic_shift (n : ℕ) :
    (Finset.range (n + 1)).prod (fun k => (1 - (1 : ℝ) / (k + 2))) = 1 / ((n : ℝ) + 2) := by
  have key : ∀ k : ℕ, (1 : ℝ) - 1 / ((k : ℝ) + 2) = ((k : ℝ) + 1) / ((k : ℝ) + 2) := by
    intro k
    have h : ((k : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring
  simp only [key]
  induction n with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    have h1 : ((m : ℝ) + 1 + 1) ≠ 0 := by positivity
    have h2 : ((m : ℝ) + 1 + 1 + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- ⭐⭐ **【`η_k = 1/(k+1)` 的前缀乘积】**：对 `n ≥ 1` 恒为 `0`
（因 `k = 0` 的因子 `1 - 1/1 = 0`）。 -/
theorem prod_harmonic_zero (n : ℕ) :
    (Finset.range n).prod (fun k => (1 - (1 : ℝ) / (k + 1))) = if n = 0 then 1 else 0 := by
  rcases n with _ | m
  · simp
  · rw [Finset.prod_range_succ']
    simp

/-- ⭐⭐⭐ **【经典特例：平移调和步长 `η_k = 1/(k+2)` 收敛】**

`η_k = 1/(k+2)` 满足 `Σ η_k = ∞` 且 `η_k → 0`；前缀乘积
`∏_{k≤n}(1-η_k) = 1/(n+2) → 0`，故 `θ_{n+1} → θ*`（`n=0` 项并入，不影响极限）。 -/
theorem thetaN_harmonic_tendsto (θstar θ₀ : ℝ) :
    Tendsto (fun n => Nat.rec θ₀
        (fun k ih => fstepN (fun k => 1 / (k + 2)) θstar k ih) (n + 1))
      atTop (nhds θstar) := by
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1)
    refine h.congr (fun n => ?_)
    norm_num
    ring
  have hbound : Tendsto (fun n : ℕ =>
      ((Finset.range (n + 1)).prod (fun k => (1 - (1 : ℝ) / (k + 2)))) * (θ₀ - θstar))
      atTop (nhds 0) := by
    have h1 := hinv.mul_const (θ₀ - θstar)
    rw [zero_mul] at h1
    refine h1.congr (fun n => ?_)
    rw [prod_harmonic_shift n]
  have h2 : Tendsto (fun n : ℕ =>
      θstar + ((Finset.range (n + 1)).prod (fun k => (1 - (1 : ℝ) / (k + 2)))) * (θ₀ - θstar))
      atTop (nhds (θstar + 0)) := hbound.const_add θstar
  rw [add_zero] at h2
  refine h2.congr (fun n => ?_)
  have h := thetaN_adaptive_closed (fun k => 1 / (k + 2)) θstar θ₀ (n + 1)
  linarith

/-- ⭐⭐ **【`η_k = 1/(k+1)`：一步即达真值】**

按要求给出的 `η_k = 1/(k+1)` 形式：因子 `k=0` 为 `0`，故 `θ_1 = θ*`；
一般地 `θ_n = θ*` 对一切 `n ≥ 1`，故**当然**收敛（平凡机制，如实标注）。 -/
theorem thetaN_harmonic_one_tendsto (θstar θ₀ : ℝ) :
    Tendsto (fun n => Nat.rec θ₀
        (fun k ih => fstepN (fun k => 1 / (k + 1)) θstar k ih) n)
      atTop (nhds θstar) := by
  have hclosed : ∀ n : ℕ, Nat.rec θ₀ (fun k ih => fstepN (fun k => 1 / (k + 1)) θstar k ih) n
      = if n = 0 then θ₀ else θstar := by
    intro n
    have h := thetaN_adaptive_closed (fun k => 1 / (k + 1)) θstar θ₀ n
    rw [prod_harmonic_zero n] at h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · rw [if_neg (by omega)]
      have : (Nat.rec θ₀ (fun k ih => fstepN (fun k => 1 / (k + 1)) θstar k ih) n) - θstar
          = 0 * (θ₀ - θstar) := by
        rw [h]; simp [Nat.pos_iff_ne_zero.mp hn]
      linarith
  have hev : Tendsto (fun n : ℕ => Nat.rec θ₀
      (fun k ih => fstepN (fun k => 1 / (k + 1)) θstar k ih) n) atTop (nhds θstar) := by
    refine (tendsto_const_nhds (x := θstar)).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [hclosed n, if_neg (by omega)]
  exact hev

end PipelineAdaptiveEta
end FateV2.Loop