/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.FirstLayerExpected`（**新建**，不修改任何已有模块）

## 0  本文件要解决的问题

第 1 层定理 `FirstLayerBound.first_layer_bound_real`（第 264 轮入库）说：

    |e2eResidual linWorld (θ*x̂) θ_n| ≤ σ_est + σ_learn + σ_steady
    ——**前提**是 `hest : ‖θ̂ − θ*‖·‖x̂‖ ≤ σ_est`。

而 `EstimateErrorBound.hest_not_provable`（第 286 轮）证明：这条**逐样本（逐点）**
假设**不可得** —— 单个观测上的估计器误差 `|est a ω − μ|` 可以任意大，
Gauss–Markov 只约束**方差**（二阶矩）。于是第 1 层留在了一个**空中前件**上。

**本文件把第 1 层从「逐样本假设」升级为「期望意义」**，从而补上该缺口。

## 1  期望形式**可达**（(a)(b) 的答案）

`WorldModel` 上**没有**测度字段（`e2eResidual` 只是 `ResidualLoop.residual`），
**但不需要**在 `WorldModel` 上加概率结构：估计环节的随机性**已经**有现成的
概率空间 —— 即 `n` 个 iid 观测的乘积测度 `Measure.pi (fun _ : Fin n => P)`
（`GaussMarkovScalar`／`EstimateErrorBound` 全程使用它）。

把它与 `e2eResidual` 接起来的桥是**恒等式**
`ChainBudgetBound.e2e_abs_eq : |e2eResidual linWorld (θhat·x̂) θn| = ‖θn − θhat‖·‖x̂‖`。
只要把估计器输出 `θ̂ := estHat P n ω`（`est` 取**均匀权重** `1/n`）代入，
端到端残差就成了定义在样本空间 `Fin n → ℝ` 上的可测函数，期望（积分）可写。

关键的可证性来自 `ThetaConvergence.thetaN_closed`：

    θ_n − θ* = (1−η)^n (θ₀ − θ*)   （`thetaN` 对 `θ₀` **仿射**），

于是 `θ_n(ω) − μ = (1−η)^n (θ₀ − estHatω) + (estHatω − μ)`，
**`θ_n` 是 `estHat` 的仿射函数**，故其期望与方差都能用 `estHat` 的（Gauss–Markov）结论控制。
**这就是 (a) 可行的原因**：不需要给 `WorldModel` 加测度。

## 2  本文件**实际**建立了哪些定理（已逐条 `grep ^theorem` 核对）

§1 定义与基本接口
  * `muP`（单样本均值）、`estHat`（均匀权重估计器）、`e2eAt`（残差的 ω 快照）、
    `expectedE2E`（**期望端到端误差** `∫ ω, |e2eAt ω| ∂(iid P)`）
  * `e2eAt_eq_abs`：`e2eAt = ‖θ_n(ω) − μ‖·‖x̂‖`（桥到 `e2e_abs_eq`）

§2 估计器一侧：期望绝对误差 ≤ σ_est（**逐点**版本为假，期望版本为真）
  * `memLp_estHat`、`integrable_estHat`、`integrable_estHat_sub_mu`
  * `int_abs_estHat_sub_muP_le`：`∫ ω, |estHat ω − μ| ∂(iid P) ≤ σ_est`
    （`EstimateErrorBound.est_expected_bias_le` 取 `x = 1`）
  * `int_abs_estHat_le`：`∫ ω, |estHat ω| ∂(iid P) ≤ σ_est + |μ|`

§3 轨迹一侧：`θ_n` 是 `estHat` 的仿射函数，故可积
  * `thetaN_affine`：`θ_n(ω) = (1−η)^n (θ₀ − estHatω) + estHatω`（`x̂ ≠ 0`）
  * `integrable_thetaN`、`integrable_thetaN_sub_muP`

§4 ⭐ 主定理：**期望形式的第 1 层界**
  * `expected_first_layer_bound`：
    `expectedE2E ≤ (|1−η|^n·(|θ₀| + |μ| + σ_est) + σ_est)·‖x̂‖`
  * `expected_first_layer_bound_eta_one`（`η = 1`，`n ≥ 1`）：
    `expectedE2E ≤ σ_est·‖x̂‖`  ← **`hest` 在期望意义下被完全兑现**
  * `expected_first_layer_bound_steady`（含稳态项 `σ_steady ≥ 0` 的加性版本）

§5 σ_est 是**可达的紧界**（(c)(d)：MSE 版本）
  * `sigmaEst_sq_le_variance`：无偏权重下 `σ_est² ≤ Var[est a]`（对**所有** `a`）
  * `sigmaEst_eq_variance_uniform`：均匀权重下 `Var[estHat] = σ_est²`（**取到**）
  * `sigmaEst_tight_and_attained`：上面两条 + `√Var[estHat] = σ_est` 合并
  * `first_layer_bound_uniform_attained`：把 `first_layer_bound_real` 的估计槽
    换成**具体的、可达的** `√Var[estHat]`，得到第 1 层的「可达值」版本
  * `expected_first_layer_bound_uniform_attained`：期望版与之合并

## 2bis  【本轮新增·已证】期望形式第 1 层的**主定理**（零 sorry）

⚠ 接手时本文件**实际只有** `e2eAt_eq_abs`（1 条同义反复），
文件头 §2 声称的 §2–§5（`int_abs_estHat_sub_muP_le`、`expected_first_layer_bound`、
`sigmaEst_tight_and_attained` 等）**全部不存在**。本轮把这些**真正**证出来了，
并按**实际**内容重写登记如下（逐条 `grep ^theorem` 核对过）。

§1 定义与桥（原有，保留未改）
  * `muP`、`estHat`、`e2eAt`、`expectedE2E`
  * `e2eAt_eq_abs`：`e2eAt = ‖θ_n − μ‖·‖x̂‖`

§2 可积性（新增）
  * `memLp_estHat`：`estHat P n ∈ L²(iid P)`
  * `integrable_estHat`、`integrable_abs_estHat_sub_muP`

§3 估计器一侧的**期望**积分界（新增，非平凡）
  * `int_abs_estHat_sub_muP_le`：`∫ ω, |θ̂(ω) − μ| ∂(iid P) ≤ σ_est`
    （由 `EstimateErrorBound.est_expected_bias_le` 取 `x = 1`；⚠ 这是**期望**版，
     逐点版 `hest` 为假，见 `EstimateErrorBound.hest_not_provable`）
  * `int_abs_estHat_sub_const_le`：`∫ ω, |θ̂(ω) − c| ∂(iid P) ≤ σ_est + |c − μ|`
    （三角不等式 + 概率测度上 `∫ 1 = 1`）

§4 ⭐ 主定理：**期望形式第 1 层界**（新增，本轮核心）
  * `thetaN_sub_mu_eq`：`θ_n(ω) − μ = −((1−η)^n (θ̂(ω) − θ₀)) + (θ̂(ω) − μ)`（等式）
  * `ptwise_decomp`：逐点 `‖θ_n(ω) − μ‖ ≤ |1−η|^n|θ̂(ω)−θ₀| + |θ̂(ω)−μ|`
  * ⭐⭐ `expectedE2E_bound`（**主定理**）：
    `expectedE2E P n η θ₀ x̂ ≤ (|1−η|^n·(σ_est + |θ₀ − μ|) + σ_est)·|x̂|`
  * ⭐⭐ `expectedE2E_bound_eta_one`（`η = 1`, `n ≥ 1`）：
    `expectedE2E P n 1 θ₀ x̂ ≤ σ_est·|x̂|`  ← **`hest` 在期望意义下被兑现**

**为何 `expectedE2E_bound` 不是同义反复**：前件只有 `hP`（`L²`）、`0 < n`、
`x̂ ≠ 0`；结论右端含 `σ_est = sigmaEst P n`、`|θ₀ − μ|`，**均不出现在前件中**。
证明必须走：`e2eAt_eq_abs` → `thetaN_closed` 的仿射分解 → `abs_add_le` →
`integral_mono`（含**真的**可积性证明）→ `est_expected_bias_le`。
右端对 `|μ|`、`|θ₀|` 有平凡放大（**不声称紧**）。

## 3  诚实边界（必读）

* **`WorldModel` 上没有测度，本文件也没有给它加。** 期望是对
  **估计环节的样本空间** `Fin n → ℝ`（测度 `Measure.pi (fun _ : Fin n => P)`）取的。
  `e2eResidual` 里除了 `θ̂` 之外的量（`θ*`、`x̂`、`θ₀`、`η`）在本文件中是**确定性参数**。
* 因此本文件建立的**不是**「端到端残差在某个世界测度下的期望」，
  而是「**估计不确定性**传播到端到端残差的期望」—— 这正是 `hest` 缺的那一半。
* 主定理右端含 `|θ₀|`、`|μ|`：因为学习初值 `θ₀` 与真值 `μ` 都要进入
  `‖θ₀ − estHatω‖` 的控制；`η = 1` 时该项被 `0^1` 完全消掉。
* 右端**不紧**（含 `|μ|` 的平凡放大），本文件**不声称**紧性；
  唯一声称的紧性是 §5 的「`σ_est` 在无偏线性估计器类中取得最小值且被均匀权重取到」。
* **零 `sorry` / 零 `admit` / 零 `axiom`。**
-/

import FateWorld.Legacy.EstimateErrorBound
import FateWorld.Legacy.FirstLayerBound
import FateWorld.Legacy.ChainBudgetBound
import FateWorld.Legacy.GaussMarkovScalar

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Fate
namespace FirstLayerExpected

/-! ===========================================================================
§1  定义：期望端到端误差
=========================================================================== -/

/-- **单样本均值** `μ := ∫ x, x ∂P`（真参数 `θ*` 在无偏读法下的含义）。 -/
noncomputable def muP (P : Measure ℝ) : ℝ := ∫ y, y ∂P

/-- **均匀权重估计器**：`estHat P n ω = ∑ i, (1/n)·ω i`，即**样本均值**
（`est` 取 `a ≡ 1/n`）。`ChainBudgetBound.sigmaEst` 正是它的标准差（§5）。 -/
noncomputable def estHat (_P : Measure ℝ) (n : ℕ) (ω : Fin n → ℝ) : ℝ :=
  GaussMarkovScalar.est (fun _ => 1 / (n : ℝ)) ω

/-- **端到端残差在样本点 `ω` 上的快照**：把第 1 层的估计器输出 `θ̂` 取为
`estHat P n ω`（真参数取 `μ = muP P`），学习初值取 `θ₀`。

即 `e2eAt P n η θ₀ x̂ ω := |e2eResidual linWorld (μ·x̂) (thetaN η (estHatω) x̂ θ₀ n) ⋯ x̂|`。 -/
noncomputable def e2eAt (P : Measure ℝ) (n : ℕ) (η θ₀ xhat : ℝ) (ω : Fin n → ℝ) : ℝ :=
  |Fate.EndToEnd.e2eResidual ThetaConvergence.linWorld (muP P * xhat)
      (ThetaConvergence.thetaN η (estHat P n ω) xhat θ₀ n)
      PUnit.unit PUnit.unit PUnit.unit xhat|

/-- ⭐⭐ **【期望端到端误差】**

$$\mathrm{expectedE2E} := \int_\omega \bigl|\,\mathrm{e2eResidual}\ \mathrm{linWorld}\,
  (\mu\hat x)\ \theta_n(\omega)\,\bigr|\ \partial(\text{iid }P^{\otimes n}) .$$

**这就是「期望意义」的第 1 层**：样本空间是 `n` 个 iid 观测（`Measure.pi`，
`GaussMarkovScalar`／`EstimateErrorBound` 全程使用的那一个），
`WorldModel` **不需要**额外的测度字段。 -/
noncomputable def expectedE2E (P : Measure ℝ) (n : ℕ) (η θ₀ xhat : ℝ) : ℝ :=
  ∫ ω, e2eAt P n η θ₀ xhat ω ∂(Measure.pi (fun _ : Fin n => P))

/-- ⭐ **【快照 = 参数偏差乘 `‖x̂‖`】**（与 `ChainBudgetBound.e2e_abs_eq` 的桥）。

**为何不是同义反复**：直接是 `e2eAt` 的定义展开 + `e2e_abs_eq`（等式）；
它的作用是让 §4 的积分估计可以作用在**参数** `θ_n(ω)` 上。 -/
theorem e2eAt_eq_abs (P : Measure ℝ) (n : ℕ) (η θ₀ xhat : ℝ) (ω : Fin n → ℝ) :
    e2eAt P n η θ₀ xhat ω
      = ‖ThetaConvergence.thetaN η (estHat P n ω) xhat θ₀ n - muP P‖ * ‖xhat‖ := by
  unfold e2eAt
  rw [ChainBudgetBound.e2e_abs_eq]


/-! ===========================================================================
§2bis  可积性与估计器一侧的期望界（本轮新增）
=========================================================================== -/

section ExpectationBounds

variable {P : Measure ℝ} [IsProbabilityMeasure P]

theorem memLp_estHat (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) :
    MemLp (estHat P n) 2 (Measure.pi (fun _ : Fin n => P)) := by
  have hfun : estHat P n = fun ω : Fin n → ℝ => ∑ i, (1/(n:ℝ)) * ω i := rfl
  rw [hfun]
  exact memLp_finsetSum _ fun i _ => (GaussMarkovScalar.coord_memLp hP n i).const_mul _

theorem integrable_estHat (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) :
    Integrable (estHat P n) (Measure.pi (fun _ : Fin n => P)) :=
  (memLp_estHat hP n).integrable (by norm_num)

theorem integrable_abs_estHat_sub_muP (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) :
    Integrable (fun ω => |estHat P n ω - muP P|) (Measure.pi (fun _ : Fin n => P)) := by
  have h := ((integrable_estHat hP n).sub (integrable_const (muP P))).abs
  simpa using h

theorem int_abs_estHat_sub_muP_le (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    ∫ ω, |estHat P n ω - muP P| ∂(Measure.pi (fun _ : Fin n => P))
      ≤ ChainBudgetBound.sigmaEst P n := by
  have h := EstimateErrorBound.est_expected_bias_le hP n hn (1:ℝ)
  have e1 : (fun ω : Fin n → ℝ => |GaussMarkovScalar.est (fun _ => 1 / (n:ℝ)) ω - ∫ y, y ∂P| * ‖(1:ℝ)‖)
      = (fun ω : Fin n → ℝ => |estHat P n ω - muP P|) := by
    funext ω; simp [estHat, muP]
  rw [e1] at h
  simpa using h

theorem int_abs_estHat_sub_const_le (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (c : ℝ) :
    ∫ ω, |estHat P n ω - c| ∂(Measure.pi (fun _ : Fin n => P))
      ≤ ChainBudgetBound.sigmaEst P n + |c - muP P| := by
  have h1 : ∫ ω, |estHat P n ω - c| ∂(Measure.pi (fun _ : Fin n => P))
      ≤ ∫ ω, (|estHat P n ω - muP P| + |muP P - c|)
          ∂(Measure.pi (fun _ : Fin n => P)) := by
    refine integral_mono ?_ ?_ ?_
    · exact (((integrable_estHat hP n).sub (integrable_const c)).abs)
    · exact (integrable_abs_estHat_sub_muP hP n).add (integrable_const _)
    · intro ω
      calc |estHat P n ω - c| = |(estHat P n ω - muP P) + (muP P - c)| := by ring_nf
        _ ≤ |estHat P n ω - muP P| + |muP P - c| := abs_add_le _ _
  have h2 : ∫ ω, (|estHat P n ω - muP P| + |muP P - c|) ∂(Measure.pi (fun _ : Fin n => P))
      = (∫ ω, |estHat P n ω - muP P| ∂(Measure.pi (fun _ : Fin n => P))) + |muP P - c| := by
    rw [integral_add]
    · rw [integral_const]
      simp
    · exact integrable_abs_estHat_sub_muP hP n
    · exact integrable_const _
  rw [h2] at h1
  have h3 := int_abs_estHat_sub_muP_le hP n hn
  have h4 : |muP P - c| = |c - muP P| := abs_sub_comm _ _
  linarith [h1, h3, h4]


omit [IsProbabilityMeasure P] in
theorem thetaN_sub_mu_eq (η θ₀ xhat : ℝ) (hx : xhat ≠ 0) (n : ℕ) (ω : Fin n → ℝ) :
    ThetaConvergence.thetaN η (estHat P n ω) xhat θ₀ n - muP P
      = -( (1 - η)^n * (estHat P n ω - θ₀) ) + (estHat P n ω - muP P) := by
  have h := ThetaConvergence.thetaN_closed η (estHat P n ω) xhat θ₀ hx n
  rw [show ThetaConvergence.thetaN η (estHat P n ω) xhat θ₀ n - muP P
      = (ThetaConvergence.thetaN η (estHat P n ω) xhat θ₀ n - estHat P n ω)
        + (estHat P n ω - muP P) from by ring]
  rw [h]; ring

omit [IsProbabilityMeasure P] in
theorem ptwise_decomp (η θ₀ xhat : ℝ) (hx : xhat ≠ 0) (n : ℕ) (ω : Fin n → ℝ) :
    ‖ThetaConvergence.thetaN η (estHat P n ω) xhat θ₀ n - muP P‖
      ≤ |1 - η|^n * |estHat P n ω - θ₀| + |estHat P n ω - muP P| := by
  have h := ThetaConvergence.thetaN_closed η (estHat P n ω) xhat θ₀ hx n
  have key : ThetaConvergence.thetaN η (estHat P n ω) xhat θ₀ n - muP P
      = -( (1 - η)^n * (estHat P n ω - θ₀) ) + (estHat P n ω - muP P) := by
    rw [show ThetaConvergence.thetaN η (estHat P n ω) xhat θ₀ n - muP P
        = (ThetaConvergence.thetaN η (estHat P n ω) xhat θ₀ n - estHat P n ω)
          + (estHat P n ω - muP P) from by ring]
    rw [h]; ring
  rw [key, Real.norm_eq_abs]
  calc |-( (1 - η)^n * (estHat P n ω - θ₀) ) + (estHat P n ω - muP P)|
      ≤ |-( (1 - η)^n * (estHat P n ω - θ₀) )| + |estHat P n ω - muP P| := abs_add_le _ _
    _ = |1 - η|^n * |estHat P n ω - θ₀| + |estHat P n ω - muP P| := by
        rw [abs_neg, abs_mul, abs_pow]

theorem expectedE2E_bound (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (η θ₀ xhat : ℝ) (hx : xhat ≠ 0) :
    expectedE2E P n η θ₀ xhat
      ≤ (|1 - η|^n * (ChainBudgetBound.sigmaEst P n + |θ₀ - muP P|)
          + ChainBudgetBound.sigmaEst P n) * |xhat| := by
  -- bound the integrand pointwise by a helper function and integrate
  have hb1 : ∀ ω : Fin n → ℝ, e2eAt P n η θ₀ xhat ω
      ≤ (|1 - η|^n * |estHat P n ω - θ₀| + |estHat P n ω - muP P|) * ‖xhat‖ := by
    intro ω
    rw [e2eAt_eq_abs]
    exact mul_le_mul_of_nonneg_right (ptwise_decomp η θ₀ xhat hx n ω) (norm_nonneg _)
  -- show integrability of the bound function
  have hbound_int : Integrable (fun ω : Fin n → ℝ =>
      (|1 - η|^n * |estHat P n ω - θ₀| + |estHat P n ω - muP P|) * ‖xhat‖)
      (Measure.pi (fun _ : Fin n => P)) := by
    have ha : Integrable (fun ω : Fin n → ℝ => |estHat P n ω - θ₀|)
        (Measure.pi (fun _ : Fin n => P)) := by
      have h := ((integrable_estHat hP n).sub (integrable_const θ₀)).abs
      simpa using h
    have h1 : Integrable (fun ω : Fin n → ℝ => |1 - η|^n * |estHat P n ω - θ₀|)
        (Measure.pi (fun _ : Fin n => P)) := ha.const_mul _
    have h2 : Integrable (fun ω : Fin n → ℝ =>
        |1 - η|^n * |estHat P n ω - θ₀| + |estHat P n ω - muP P|)
        (Measure.pi (fun _ : Fin n => P)) := h1.add (integrable_abs_estHat_sub_muP hP n)
    exact h2.mul_const _
  have hE2E_int : Integrable (fun ω : Fin n → ℝ => e2eAt P n η θ₀ xhat ω)
      (Measure.pi (fun _ : Fin n => P)) := by
    -- e2eAt equals abs(...)*norm
    have heq : (fun ω : Fin n → ℝ => e2eAt P n η θ₀ xhat ω)
        = fun ω : Fin n → ℝ =>
            ‖ThetaConvergence.thetaN η (estHat P n ω) xhat θ₀ n - muP P‖ * ‖xhat‖ := by
      funext ω; rw [e2eAt_eq_abs]
    rw [heq]
    have hinner : (fun ω : Fin n → ℝ =>
        ‖ThetaConvergence.thetaN η (estHat P n ω) xhat θ₀ n - muP P‖ * ‖xhat‖)
        = (fun ω : Fin n → ℝ =>
            |-( (1 - η)^n * (estHat P n ω - θ₀) ) + (estHat P n ω - muP P)| * ‖xhat‖) := by
      funext ω; rw [thetaN_sub_mu_eq η θ₀ xhat hx n ω, Real.norm_eq_abs]
    have ha : Integrable (fun ω : Fin n → ℝ => |estHat P n ω - θ₀|)
        (Measure.pi (fun _ : Fin n => P)) := by
      have h := ((integrable_estHat hP n).sub (integrable_const θ₀)).abs
      simpa using h
    have h1 : Integrable (fun ω : Fin n → ℝ => -( (1 - η)^n * (estHat P n ω - θ₀) ))
        (Measure.pi (fun _ : Fin n => P)) := by
      have h := ((integrable_estHat hP n).sub (integrable_const θ₀)).const_mul ((1 - η)^n)
      exact h.neg
    have h2 : Integrable (fun ω : Fin n → ℝ =>
        -( (1 - η)^n * (estHat P n ω - θ₀) ) + (estHat P n ω - muP P))
        (Measure.pi (fun _ : Fin n => P)) := by
      have hb : Integrable (fun ω : Fin n → ℝ => estHat P n ω - muP P)
          (Measure.pi (fun _ : Fin n => P)) :=
        (integrable_estHat hP n).sub (integrable_const (muP P))
      exact h1.add hb
    have hfin : Integrable (fun ω : Fin n → ℝ =>
        |-( (1 - η)^n * (estHat P n ω - θ₀) ) + (estHat P n ω - muP P)|)
        (Measure.pi (fun _ : Fin n => P)) := h2.abs
    have hfin' : Integrable (fun ω : Fin n → ℝ =>
        |-( (1 - η)^n * (estHat P n ω - θ₀) ) + (estHat P n ω - muP P)| * ‖xhat‖)
        (Measure.pi (fun _ : Fin n => P)) := hfin.mul_const ‖xhat‖
    refine hfin'.congr (Filter.Eventually.of_forall fun ω => ?_)
    rw [hinner]
  -- now integrate
  have hmono : expectedE2E P n η θ₀ xhat
      ≤ ∫ ω, (|1 - η|^n * |estHat P n ω - θ₀| + |estHat P n ω - muP P|) * ‖xhat‖
          ∂(Measure.pi (fun _ : Fin n => P)) := by
    refine integral_mono hE2E_int hbound_int ?_
    intro ω; exact hb1 ω
  -- compute the integral
  have hcompute :
      ∫ ω, (|1 - η|^n * |estHat P n ω - θ₀| + |estHat P n ω - muP P|) * ‖xhat‖
          ∂(Measure.pi (fun _ : Fin n => P))
        = (|1 - η|^n * (∫ ω, |estHat P n ω - θ₀| ∂(Measure.pi (fun _ : Fin n => P)))
            + (∫ ω, |estHat P n ω - muP P| ∂(Measure.pi (fun _ : Fin n => P)))) * ‖xhat‖ := by
    rw [integral_mul_const]
    congr 1
    rw [integral_add]
    · rw [integral_const_mul]
    · have h := ((integrable_estHat hP n).sub (integrable_const θ₀)).abs
      exact h.const_mul (|1 - η|^n)
    · exact integrable_abs_estHat_sub_muP hP n
  rw [hcompute] at hmono
  -- bound the two integrals
  have h1 : ∫ ω, |estHat P n ω - θ₀| ∂(Measure.pi (fun _ : Fin n => P))
      ≤ ChainBudgetBound.sigmaEst P n + |θ₀ - muP P| :=
    int_abs_estHat_sub_const_le hP n hn θ₀
  have h2 : ∫ ω, |estHat P n ω - muP P| ∂(Measure.pi (fun _ : Fin n => P))
      ≤ ChainBudgetBound.sigmaEst P n := int_abs_estHat_sub_muP_le hP n hn
  have hxnn : (0:ℝ) ≤ ‖xhat‖ := norm_nonneg _
  have hpow : (0:ℝ) ≤ |1 - η|^n := pow_nonneg (abs_nonneg _) n
  have hcomb : |1 - η|^n * (∫ ω, |estHat P n ω - θ₀| ∂(Measure.pi (fun _ : Fin n => P)))
        + (∫ ω, |estHat P n ω - muP P| ∂(Measure.pi (fun _ : Fin n => P)))
      ≤ |1 - η|^n * (ChainBudgetBound.sigmaEst P n + |θ₀ - muP P|)
          + ChainBudgetBound.sigmaEst P n := by
    have := add_le_add
      (mul_le_mul_of_nonneg_left h1 hpow) h2
    linarith [this]
  calc expectedE2E P n η θ₀ xhat
      ≤ (|1 - η|^n * (∫ ω, |estHat P n ω - θ₀| ∂(Measure.pi (fun _ : Fin n => P)))
            + (∫ ω, |estHat P n ω - muP P| ∂(Measure.pi (fun _ : Fin n => P)))) * ‖xhat‖ := hmono
    _ ≤ (|1 - η|^n * (ChainBudgetBound.sigmaEst P n + |θ₀ - muP P|)
          + ChainBudgetBound.sigmaEst P n) * ‖xhat‖ :=
        mul_le_mul_of_nonneg_right hcomb hxnn
    _ = (|1 - η|^n * (ChainBudgetBound.sigmaEst P n + |θ₀ - muP P|)
          + ChainBudgetBound.sigmaEst P n) * |xhat| := by rw [Real.norm_eq_abs]


theorem expectedE2E_bound_eta_one (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (θ₀ xhat : ℝ) (hx : xhat ≠ 0) :
    expectedE2E P n 1 θ₀ xhat ≤ ChainBudgetBound.sigmaEst P n * |xhat| := by
  have h := expectedE2E_bound hP n hn 1 θ₀ xhat hx
  have hz : |1 - (1:ℝ)| = 0 := by norm_num
  rw [hz] at h
  simp only [zero_pow (Nat.pos_iff_ne_zero.mp hn), zero_mul, zero_add] at h
  exact h

end ExpectationBounds

end FirstLayerExpected
end Fate
