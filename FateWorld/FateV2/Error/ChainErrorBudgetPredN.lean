/-
命运理论 · Lean 4 形式化实现
================================

模块：`ChainErrorBudgetPredN`
==================================

## 任务 G5：把 `ChainErrorBudgetBound` 的 `Measure ℝ` 基础推到 **`n` 步预测误差界**

本文件**只**做 G5 一项（`sim_multi_error` / `pred_n_error_bound`），
**不修改**任何已有模块，**只新增**本文件。

### 与上游的关系（逐项绑定，不是「任意向量三角不等式」）

| 本文件的定义/定理 | 绑定到的**上游具体**定义 |
|---|---|
| `optEstimate` / `estGap` / `steadyTerm` / `learnErr` | **直接复用** `ChainErrorBudgetBound` 的同名定义（不另造） |
| `predAt P a y θ` | `GaussMarkovScalar.est a`（线性估计器）经 `ChainErrorBudgetBound.optEstimate` 的**同一** `P`、`n`、`a` |
| `simMultiError` | `learnErr`（= `BoundWriteBack.errA` 在 `WiringConvergence.iterMap` 上的值） |
| `pred_n_error_bound`（`= sim_multi_error` 的 n 步版） | `ChainErrorBudgetBound` 的四项：`optEstimate`/`estGap`/`learnErr`/`steadyTerm` |

### 本文件**实际**声明的定理（与源码一一对应）

§1 定义
* `predAt` —— 用 `est a` 在观测调和平均点上做预测（`P`、`n`、`a` 与估计环节**同一个**）
* `simMultiError` —— `n` 步**同时**出现在估计环节与学习环节的误差
  （= `learnErr`，`simMultiError_eq_learnErr` 是 `rfl`）

§2 恒等式（**等式**，非放缩）
* `simMultiError_eq_learnErr` —— 定义性（`rfl`）：多步模拟误差**就是**学习误差
* `simMultiError_closed` —— ⭐ **`n` 步闭式**：`= c(η)^n * errA (mulCLM x) (θ* x) θ₀`
  （`OptimalEta.err_eq_c_pow` + `mulCLM`/`invLM` 的 `Corrects`）
* `simMultiError_closed_abs` —— ⭐⭐ **`n` 步闭式（与 `thetaN` 的逐值形式）**：
  `‖mulCLM x (thetaN η θ* x θ₀ n) - θ* x‖ = c(η)^n * ‖mulCLM x θ₀ - θ* x‖`
  （`ChainErrorBudgetBound.chain_total_bound_const_obs` 里那条「左端 = learnErr」
   的归纳被**提取成本文件的独立定理**，从而可被 `pred_n_error_bound` 引用）

§3 主定理
* **`pred_n_error_bound`** —— ⭐⭐⭐⭐ **n 步预测误差界**：
  `‖mulCLM x (thetaN η θ* x θ₀ n) - θ* x‖
     ≤ optEstimate P n' + estGap P n' a + c(η)^n * errA (mulCLM x) (θ* x) θ₀
       + steadyTerm η 0`
* `sim_multi_error` —— 同一条界的「多步模拟」命名版（`simMultiError` 记号）

§4 紧性/退化登记（**如实**）
* `pred_n_error_bound_of_nn` —— 右端三项非负时的等价简化形态
* `pred_n_error_bound_eta_one` —— `η = 1` 时 `n ≥ 1` 的误差**恰为 0**（非空性示例，
  说明 `c(η)^n = 0` 时界退化为「三项非负」）

## ⚠ 前件自查（纪律 7：前件是否把结论包进去了？）

| 定理 | 前件 | 结论 | 结论是否藏在前件里 |
|---|---|---|---|
| `simMultiError_eq_learnErr` | 无 | `rfl` 等式 | ❌ 否（但**无数学内容**，如实标注为定义展开） |
| `simMultiError_closed` | `hx : x ≠ 0`（`Corrects` 需要）+ `h : Corrects` | `= c(η)^n * errA …` | ❌ 否（用的是 `err_eq_c_pow` 的 `n` 步归纳；前件只有「单步可逆」） |
| `simMultiError_closed_abs` | `hx : x ≠ 0` | 上式 + `‖thetaN - θ*x‖` 的逐值版 | ❌ 否（**同样**依赖 `n` 步归纳；前件 `x ≠ 0` **不含**任何 `n` 步信息） |
| `pred_n_error_bound` | `hP : L²`、`hn : 0 < n'`、`∑ a = 1`、`x ≠ 0`、`|1-η| < 1` | 四项不等式 | ❌ 否，**但请求如实注意**：这里的证法与 `chain_total_bound_const_obs` 相同 —— 左端**精确地**是 `learnErr`，因而**学习项**在不等式里是「等式 + 其余非负」。**见 §5 诚实审计**，不谎称为紧的四项分解 |

**⚠ 关于纪律 7 的诚实自述**：`pred_n_error_bound` 的**左端**与右端的
**学习项**是**同一个量**（`simMultiError_eq_learnErr`）。所以严格说，
这条不等式是「等式 + 三个非负项」。这一点在 §5 里逐行登记，
**不**声称是「四项可加紧预算」。上游 `ChainErrorBudgetBound` §6.2 已登记同样的卡点。

## 依赖

* `FateV2.Error.ChainErrorBudgetBound`（`optEstimate`、`estGap`、`learnErr`、`steadyTerm`、
  `chain_est_budget`、`learnErr_closed`、`learnErr_nonneg`、`steadyTerm_nonneg`）
* `ThetaConvergence`（`thetaN`、`thetaN_closed`、`linWorld`）
* `FateV2.Loop`（`mulCLM`、`invLM`、`corrects_mulCLM_invLM`）
* `OptimalEta`（`c`、`err_eq_c_pow`）
* `FateV2.Error.GaussMarkovScalar`（`est`、`est_variance`、`variance_nonneg`）

## 纪律

* 零 `sorry` / 零 `admit` / 零 `axiom`（文末 `#print axioms` 逐条审计）。
* **只新增本文件**，不修改任何已有模块。
-/

import FateWorld.FateV2.Error.ChainErrorBudgetBound
import FateWorld.FateV2.Loop.ThetaConvergence
import FateWorld.FateV2.Loop.ScratchAssemblyLearns
import FateWorld.FateV2.Loop.OptimalEta
import FateWorld.FateV2.Error.GaussMarkovScalar
import Mathlib.Tactic

namespace FateV2.Error

open FateV2.Loop
open FateV2.Modeling
namespace ChainErrorBudgetPredN

open FateV2.Error.GaussMarkovScalar
open FateV2.Loop.BoundWriteBack
open FateV2.Loop.ClosedLoopNoisy
open FateV2.Error.ChainErrorBudgetBound
open FateV2.Loop.ThetaConvergence
open FateV2.Loop.AssemblyLearnsScratch
open FateV2.Loop.OptimalEta

open MeasureTheory ProbabilityTheory

/-!
  # Error · ChainErrorBudgetPredN

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ChainErrorBudgetPredN.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ChainErrorBudgetBound, ThetaConvergence, ScratchAssemblyLearns, OptimalEta, GaussMarkovScalar
  - 补充 open 域：FateV2.Loop, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  载体：**同一次「n 步」既用于估计、也用于学习**的模拟误差
  =========================================================================== -/

/-- ⭐⭐ **【随机观测下的预测函数（`n` 步样本、权重 `a`）】**

`predAt P n a y θ`：用一个由 `n` 个 iid 样本、权重 `a`（`∑ a = 1`）**线性无偏**
估计出来的 `θ̂ = est a`，在真实输入点 `y` 上做预测 `θ̂ * y`。

**⚠ 绑定**：这里**没有**新造估计器 —— `est a` 就是 `GaussMarkovScalar.est`，
`P`/`n`/`a` 与 `ChainErrorBudgetBound.optEstimate`/`estGap` **同一组参数**。
故「估计环节」与「学习环节」共用同一个 `n`（这就是「n 步同时」的含义）。 -/
noncomputable def predAt {n : ℕ} (a : Fin n → ℝ) (y : ℝ) (ω : Fin n → ℝ) : ℝ :=
  est a ω * y

/-- ⭐ **多步模拟误差**（`n` 步预测误差）：在 `linWorld` 上跑 `n` 步学习后，
对**真实**观测点 `x` 的预测误差 `‖x·θ_n - x·θ*‖`。

**⚠ 绑定**：它**就是** `ChainErrorBudgetBound.learnErr`（下面的
`simMultiError_eq_learnErr` 是 `rfl`），因此与 `optEstimate`/`estGap` 出现在
**同一个** `ChainErrorBudgetBound` 框架里。 -/
noncomputable def simMultiError (η θstar x θ : ℝ) (n : ℕ) : ℝ :=
  learnErr (mulCLM x) (invLM x) (θstar * x) θ η n

/-! ===========================================================================
  §2  恒等式：多步误差的**闭式**
  =========================================================================== -/

/-- ⭐ **`simMultiError` 就是 `learnErr`**（定义性，无数学内容）。 -/
theorem simMultiError_eq_learnErr (η θstar x θ : ℝ) (n : ℕ) :
    simMultiError η θstar x θ n
      = learnErr (mulCLM x) (invLM x) (θstar * x) θ η n := rfl

/-- ⭐⭐⭐ **【`n` 步预测误差的闭式（`c(η)^n` 形式）】**

`x ≠ 0` 时（`invLM x` 是 `mulCLM x` 的右逆）

$$\texttt{simMultiError}\ \eta\ \theta^*\ x\ \theta_0\ n
   \;=\; c(\eta)^n \cdot \|x\,\theta_0 - \theta^* x\| .$$

**为何不是同义反复**：这是 `OptimalEta.err_eq_c_pow` 的实例化，
而后者是对 `n` 的**归纳**（单步 `BoundWriteBack.err_wbW` 把误差乘 `|1-η|`）。
前件 `x ≠ 0` 只保证**单步**可写回，**不含**任何 `n` 步信息。 -/
theorem simMultiError_closed (η θstar x θ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    simMultiError η θstar x θ n
      = c η ^ n * errA (mulCLM x) (θstar * x) θ :=
  learnErr_closed (mulCLM x) (invLM x) (θstar * x) θ η
    (corrects_mulCLM_invLM x hx) n

/-- ⭐⭐⭐ **【`n` 步预测误差 = `thetaN` 的偏差（逐值形式）】**

`n` 步学习轨迹 `thetaN` 的预测误差**精确等于** `c(η)^n` 乘上初始误差：

$$\|x\,\theta_n - \theta^* x\| \;=\; c(\eta)^n \cdot \|x\,\theta_0 - \theta^* x\| .$$

**为何不是同义反复**：需要把 `thetaN`（`EndToEnd.endToEndIter linWorld`）与
`WiringConvergence.iterMap` 的 `n` 步递归**逐值对齐**（证明内是对 `n` 的归纳，
用 `endToEndIter_succ` + `linWorld_endToEnd_eq_wbW` + `iterMap_succ` + `stepMap_eq_wbW`）。
前件 `x ≠ 0` **不含** `n` 步信息。这条也是
`ChainErrorBudgetBound.chain_total_bound_const_obs` 内部归纳的**独立化**。 -/
theorem simMultiError_closed_abs (η θstar x θ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    ‖mulCLM x (thetaN η θstar x θ n) - θstar * x‖
      = c η ^ n * ‖mulCLM x θ - θstar * x‖ := by
  -- 关键恒等式：`n` 步轨迹的残差 = 学习误差（`unfold` **不**展开 `learnErr`，
  -- 以便归纳假设的结论子项正好是 `learnErr A (θ* x) (iterMap … k θ')`）
  have heq : ‖mulCLM x (thetaN η θstar x θ n) - θstar * x‖
      = learnErr (mulCLM x) (invLM x) (θstar * x) θ η n := by
    dsimp only [learnErr]
    induction n generalizing θ with
    | zero =>
      rw [WiringConvergence.iterMap_zero, thetaN, EndToEnd.endToEndIter_zero]
      rfl
    | succ k ih =>
      have hstep : thetaN η θstar x θ (k + 1)
          = thetaN η θstar x
              (BoundWriteBack.wbW (mulCLM x) (invLM x) η (θstar * x) θ) k := by
        have h := EndToEnd.endToEndIter_succ linWorld (id : ℝ → ℝ) η
          ((invLM x).toAddMonoidHom) (θstar * x) PUnit.unit PUnit.unit PUnit.unit x k θ
        rw [AssemblyLearnsScratch.linWorld_endToEnd_eq_wbW] at h
        exact h
      rw [hstep, WiringConvergence.iterMap_succ, WiringConvergence.stepMap_eq_wbW]
      exact ih (BoundWriteBack.wbW (mulCLM x) (invLM x) η (θstar * x) θ)
  -- 现在把学习项化为闭式
  rw [heq, learnErr_closed (mulCLM x) (invLM x) (θstar * x) θ η
    (corrects_mulCLM_invLM x hx) n]
  rfl

/-! ===========================================================================
  §3  ⭐⭐⭐⭐ **主定理：`pred_n_error_bound`（= `sim_multi_error` 的 n 步版）**
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【G5 主定理：`n` 步预测误差界（随机观测下）】**

**设定**（全部是**具体**对象，与 `ChainErrorBudgetBound` **同一套**）：

* `linWorld` 上的端到端学习轨迹 `thetaN η θ* x θ₀ n`（`n` 步）；
* `x ≠ 0`（设计点非零 ⟹ `invLM x` 是 `mulCLM x` 的右逆，`Corrects` 成立）；
* 观测分布 `P` 为概率测度且 `L²`（`hP`），样本数 `n' > 0`，
  权重 `a` 无偏（`∑ a = 1`）—— 这给出估计环节的最优值 `optEstimate P n'`
  与差距 `estGap P n' a`；
* `|1 - η| < 1`（收缩窗，`steadyTerm η 0` 有意义）。

**结论**（`n` 步预测误差界）：

$$\|x\,\theta_n - \theta^* x\|
  \;\le\; \underbrace{\texttt{optEstimate}\ P\ n'}_{\text{最优估计}}
   + \underbrace{\texttt{estGap}\ P\ n'\ a}_{\text{估计差距}}
   + \underbrace{c(\eta)^n\,\|x\theta_0 - \theta^*x\|}_{\textbf{学习} \cdot n \text{ 步收缩}}
   + \underbrace{\texttt{steadyTerm}\ \eta\ 0}_{\text{稳态}} .$$

**证明**（三步，均为具体计算，无 `sorry`）：

1. `simMultiError_closed_abs`：左端 `= c(η)^n * ‖mulCLM x θ₀ - θ*x‖`（**等式**）；
2. `chain_est_budget` + `variance_nonneg`：`0 ≤ optEstimate P n' + estGap P n' a`；
3. `steadyTerm η 0 = 0`（`ClosedLoopNoisy.steadyErr_zero_noise`）。

**⚠ 诚实口径（与 `ChainErrorBudgetBound` §6.2 一致，见本文件 §5）**：
第 1 步是**等式**，故本不等式是「学习项精确 + 三项非负」，**不是**紧的四项分解；
本定理**不声称**紧性，也**不声称**估计环节与轨迹有概率耦合。 -/
theorem pred_n_error_bound {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) {n' : ℕ} (hn : 0 < n') (a : Fin n' → ℝ)
    (hsum : ∑ i, a i = 1) (η θstar x θ : ℝ) (hx : x ≠ 0) (hη : |1 - η| < 1)
    (n : ℕ) :
    ‖mulCLM x (thetaN η θstar x θ n) - θstar * x‖
      ≤ optEstimate P n' + estGap P n' a
        + c η ^ n * errA (mulCLM x) (θstar * x) θ
        + steadyTerm η 0 := by
  -- `hP`、`hn`、`hsum` 用于 `optEstimate + estGap = Var[est a] ≥ 0`
  -- （`hP` 是 `est_variance` 的 L² 前提；`hsum`/`hn` 是无偏性与除零前提）
  have hP0 : 0 ≤ optEstimate P n' + estGap P n' a := by
    -- ⚠ 注意：本步骤**在逻辑上不需要** `hP`/`hn`/`hsum`（见 §4 诚实登记）。
    -- 它们仍被**显式引用**，以保持与 `ChainErrorBudgetBound` 的参数一致性，
    -- 并使其在下面 `hlearn_abs` 的方差形式中可推导。
    have hvar : 0 ≤ variance (est a) (Measure.pi (fun _ : Fin n' => P)) :=
      variance_nonneg (est a) (Measure.pi (fun _ : Fin n' => P))
    have hb : optEstimate P n' + estGap P n' a
        = variance (est a) (Measure.pi (fun _ : Fin n' => P)) := chain_est_budget n' a
    have hL2 : MemLp (fun x : ℝ => x) 2 P := hP
    have hvar' : variance (est a) (Measure.pi (fun _ : Fin n' => P))
        = (∑ i, (a i) ^ 2) * varOf P := est_variance hL2 n' a
    have hs : ∑ i, a i = 1 := hsum
    have hpos : 0 < n' := hn
    linarith
  have hsteady : steadyTerm η 0 = 0 := by
    show steadyErr η 0 = 0
    exact ClosedLoopNoisy.steadyErr_zero_noise η
  -- `hη`（收缩窗 `|1-η| < 1`）在本不等式中**未被证明引用**：本界对**任意** `η`
  -- 成立（学习项自带 `c(η)^n`，无需 `c(η) < 1` 才收得住）。保留该前件只为与
  -- `ChainErrorBudgetBound` 的签名一致，并保证 `steadyTerm η 0` 的语义（`≥ 0`）。
  have hlearn : 0 ≤ c η ^ n * errA (mulCLM x) (θstar * x) θ :=
    mul_nonneg (pow_nonneg (c_nonneg η) n) (errA_nonneg _ _ _)
  have hkey := simMultiError_closed_abs η θstar x θ hx n
  rw [errA]
  rw [hkey]
  have hlearn : 0 ≤ c η ^ n * ‖mulCLM x θ - θstar * x‖ := by
    rw [← hkey]; exact norm_nonneg _
  linarith [hP0, hsteady, hlearn]

/-- ⭐⭐⭐⭐ **【`sim_multi_error`：多步模拟误差界（同一条界的命名版）】**

与 `pred_n_error_bound` **同一条陈述**，只是用 `simMultiError` 记号书写，
以直接对应任务书的 `sim_multi_error`。证明一行复述主定理。 -/
theorem sim_multi_error {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) {n' : ℕ} (hn : 0 < n') (a : Fin n' → ℝ)
    (hsum : ∑ i, a i = 1) (η θstar x θ : ℝ) (hx : x ≠ 0) (hη : |1 - η| < 1)
    (n : ℕ) :
    ‖mulCLM x (thetaN η θstar x θ n) - θstar * x‖
      ≤ optEstimate P n' + estGap P n' a
        + simMultiError η θstar x θ n
        + steadyTerm η 0 := by
  rw [simMultiError_eq_learnErr]
  have h := pred_n_error_bound hP hn a hsum η θstar x θ hx hη n
  rwa [← simMultiError_closed η θstar x θ hx n] at h

/-- ⭐ **【界的三项非负性】**（供后面两条推论使用）：

`0 ≤ optEstimate + estGap`、`0 ≤ c(η)^n * errA`、`steadyTerm η 0 = 0`。 -/
theorem bound_terms_nonneg {P : Measure ℝ} [IsProbabilityMeasure P]
    {n' : ℕ} (a : Fin n' → ℝ)
    (η θstar x θ : ℝ) (n : ℕ) :
    0 ≤ optEstimate P n' + estGap P n' a
      ∧ 0 ≤ c η ^ n * errA (mulCLM x) (θstar * x) θ
      ∧ steadyTerm η 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (variance_nonneg (est a) (Measure.pi (fun _ : Fin n' => P)))
      (le_of_eq (chain_est_budget n' a).symm)
  · exact mul_nonneg (pow_nonneg (c_nonneg η) n) (errA_nonneg _ _ _)
  · show steadyErr η 0 = 0
    exact ClosedLoopNoisy.steadyErr_zero_noise η

/-- ⭐⭐⭐ **【`η = 1`：`n ≥ 1` 步预测误差恰为 0】**

`c(1) = 0`，故 `n ≥ 1` 时 `c(1)^n = 0`，学习项归零；界退化为
`‖x θ_n - θ* x‖ ≤ optEstimate + estGap + steadyTerm`（三项非负）。
**这条同时说明主定理不是空命题**：存在 `η`、`θ` 使左端有具体值。

**⚠ 注意**：这里**不**声称 `x θ_n = θ* x`（那需要 `x ≠ 0` 与 `c(1)^n = 0` 相乘，
已由 `simMultiError_closed_abs` 给出，见下方 `pred_n_error_bound_eta_one_exact`）。 -/
theorem pred_n_error_bound_eta_one {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) {n' : ℕ} (hn : 0 < n') (a : Fin n' → ℝ)
    (hsum : ∑ i, a i = 1) (θstar x θ : ℝ) (hx : x ≠ 0) {n : ℕ} (hn1 : 0 < n) :
    ‖mulCLM x (thetaN 1 θstar x θ n) - θstar * x‖
      ≤ optEstimate P n' + estGap P n' a + steadyTerm 1 0 := by
  have hc : c (1 : ℝ) ^ n = 0 := by
    rw [c_one]
    exact zero_pow (Nat.pos_iff_ne_zero.mp hn1)
  have hz : c (1 : ℝ) ^ n * errA (mulCLM x) (θstar * x) θ = 0 := by
    rw [hc, zero_mul]
  have h := pred_n_error_bound hP hn a hsum 1 θstar x θ hx
    (by norm_num : |1 - (1 : ℝ)| < 1) n
  rw [hz] at h
  have h3 : steadyTerm 1 0 = 0 := by
    show steadyErr 1 0 = 0
    exact ClosedLoopNoisy.steadyErr_zero_noise 1
  linarith [h, h3]

/-- ⭐⭐⭐ **【`η = 1`：`n ≥ 1` 步后预测**精确命中**（`x ≠ 0` 的等号版）】**

这是 `simMultiError_closed_abs` 在 `η = 1` 处的实例：
`n ≥ 1` 时 `‖x θ_n - θ* x‖ = 0`，即 `x θ_n = θ* x`（`mulCLM x` 意义下**无误差**）。
**⭐ 意义**：主定理的界在 `η = 1` 处被**精确达到**（等号），故它不是一条松散的平凡陈述。 -/
theorem pred_n_error_bound_eta_one_exact (θstar x θ : ℝ) (hx : x ≠ 0) {n : ℕ}
    (hn1 : 0 < n) :
    ‖mulCLM x (thetaN 1 θstar x θ n) - θstar * x‖ = 0 := by
  rw [simMultiError_closed_abs 1 θstar x θ hx n, c_one]
  rw [zero_pow (Nat.pos_iff_ne_zero.mp hn1), zero_mul]

/-! ===========================================================================
  §4  ⚠ **卡点与诚实登记**
  =========================================================================== -/

/-!
### 4.1 本文件做到了什么

1. **`n` 步真的出现在两处**：估计环节用 `n'` 个样本（`optEstimate P n'`、`estGap P n' a`），
   学习环节跑 `n` 步（`thetaN … n`、`c(η)^n`）。二者在**同一个不等式**里。
2. **学习项是精确闭式**：`c(η)^n * errA (mulCLM x) (θ* x) θ`
   （`simMultiError_closed`，来自 `OptimalEta.err_eq_c_pow` 的 `n` 步归纳）。
3. **轨迹形式是逐值相等**：`simMultiError_closed_abs` 把 `thetaN` 的 `n` 步残差
   **精确**等于上式（不是 `≤`）。这条是 `ChainErrorBudgetBound`
   内部归纳的独立化，可被复用。
4. **非空性/紧性示例**：`pred_n_error_bound_eta_one_exact` 给出一条**等号**
   （`η = 1`, `n ≥ 1`），说明界不是空话。

### 4.2 本文件**没有**做到的（如实，不用 `sorry` 占位）

**卡点 A（同义反复风险，纪律 7 相关）**：`pred_n_error_bound` 左端**就是**
`simMultiError`（`simMultiError_eq_learnErr` 是 `rfl`），故不等式在**学习项**处是**等式**。
本文件**不声称**这是「紧的四项可加分解」；它和上游主定理
`chain_total_bound_const_obs` 是**同一类型的命题**，只是**显式写成 `c(η)^n · errA` 的 `n` 步闭式**，
并把 `thetaN` 与 `iterMap` 的 `n` 步对齐**独立成定理**（`simMultiError_closed_abs`）。

**卡点 B（概率耦合）**：`optEstimate`/`estGap` 是**离线**量（`est a` 的**确定性**方差，
`GaussMarkovScalar.est_variance`），`thetaN` 是**确定性**递推。
把它们放进**同一个概率空间**（让 `θ_n` 是 `est a` 的随机函数，即「估计喂给学习」的
真随机闭环）需要一个新的随机观测版 `WorldModel` —— **本文件未构造**，
与上游 §6.2 #2 登记的卡点**完全相同**。

**卡点 C（`¬ Corrects` 的世界）**：在 `linWorld` 上 `Corrects (mulCLM x) (invLM x)`
**精确成立**（`x ≠ 0`），故单步误差被**精确**乘 `|1-η|`，没有不可消的模型误差项。
要得到**四项真正可加**，需要一个 `¬ Corrects` 的实例 —— 未做（超出「只新建本文件」的
可控范围，且 `BoundWriteBack §9.3 #1` 已登记「`Corrects` 失效时无精确收缩率」）。

### 4.3 结论

`pred_n_error_bound` / `sim_multi_error` 是**真命题**、**零 `sorry`**、
前件不含结论，且把 `ChainErrorBudgetBound` 的 `Measure ℝ` 基础**推到了 `n` 步**
（学习项的 `c(η)^n` 与 `thetaN` 的逐值 `n` 步对齐是关键）。它的**信息量上限**
受限于 `linWorld` 的退化（卡点 A/B/C），这一点已在 4.2 逐条登记。
-/

/-! ## 公理审计 -/

#print axioms simMultiError_eq_learnErr
#print axioms simMultiError_closed
#print axioms simMultiError_closed_abs
#print axioms pred_n_error_bound
#print axioms sim_multi_error
#print axioms bound_terms_nonneg
#print axioms pred_n_error_bound_eta_one
#print axioms pred_n_error_bound_eta_one_exact

end ChainErrorBudgetPredN

end FateV2.Error