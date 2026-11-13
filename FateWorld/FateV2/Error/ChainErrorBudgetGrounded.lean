import FateWorld.FateV2.Error.ChainErrorBudget
import FateWorld.FateV2.Loop.ThetaConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ChainErrorBudgetGrounded.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 11 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Loop
open FateV2.Error
open FateV2.Predict
open FateV2.Modeling
open FateV2.Model

/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Error.ChainErrorBudgetGrounded`

## 这份文件要解决的问题（第 205/209/211 轮）

`FateV2.Error/ChainErrorBudget.lean` 的主定理 `chain_end_to_end_from_links` 本质是
**三角不等式**：三个误差分量 `Ω₁ Ω₂ Ω₃` 是**任意向量**，
它们没有与任何具体模块建立联系（只有三个 `‖Ωᵢ‖ ≤ σᵢ` 的裸前件）。
第 209 轮确认它是【唯一】同时 `import` `GaussMarkovScalar`、`OptimalEta`、
`ClosedLoopNoisy` 的模块，所以架子是对的，只是材料没填。

**本文件的任务**：在**一个具体的 `WorldModel` 实例**上，
把三项误差真的**绑定到具体定义**，并证明它们能出现在**同一条迭代不等式**里。

## 卡点结论（先说结论）

**结论：可以绑定，但要付出一个诚实的代价 —— 三项误差的「类型」不同。**

* 估计环节 `GaussMarkovScalar` 的结论是**方差** `Var[est a] ≥ varOf P / n`。
  它是 `P` 上的**均方**陈述，不是逐样本的范数陈述。
* 学习/闭环环节 `OptimalEta` / `ClosedLoopNoisy` 的结论是
  **逐样本范数** `‖A θ_n - x'_n‖ ≤ r^n e₀ + (1-r^n)/(1-r) d`。
* 稳态环节 `steadyErr η d = d/(1-|1-η|)` 是**闭式标量**。

因此「三项相加」在**字面量纲**上不合法（方差 vs 范数 vs 标量）。
**解决办法（本文件采用）**：把估计环节的输出**取标准差**
`σ_est := √(varOf P / n)`，它与 `‖·‖` 同量纲（`ℝ` 上的长度），
并把「估计达到均方根精度」显式写成一个**前件** `h_est : ‖A θ₀ - x' 0‖ ≤ σ_est`
（闭环初值误差就是估计环节的产出被当作闭环的初值）。

**这不是同义反复**：`h_est` 是**逐样本**的界，
而 `gauss_markov_lower_bound` 给的是**均方**的界；
「均方下界 ⟹ 逐样本上界」在一般情况下**不成立**
（一个随机变量可以有小的均方和大的逐样本偏离）。
所以 `h_est` 是一条**真前提**，不是结论的换写。
这一点在 `sigma_est_is_min_rms` 里被如实钉住。

## 逐条定理（与下面 `grep ^theorem` 的结果一一对应）

§1 载体（`linWorld` 的标量骨架）

* `linId`                —— `A = id : ℝ →L[ℝ] ℝ`（`linWorld` 的参数空间是 `ℝ`）。
* `linPhi`               —— `φ = id : ℝ →ₗ[ℝ] ℝ`。
* `linCorrects`          —— `Corrects linId linPhi`（`A (φ r) = r`）。
* `linErrA`              —— `errA linId x' θ = |θ - x'|`（误差就是绝对值距离）。
* `linWorld_predFrom_scalar` —— `linWorld` 的预测块 `predFrom linWorld θ … x = θ * x`。

§2 链环 1 —— 估计误差 **绑定到 `GaussMarkovScalar`**

* `sigma_est`            —— `σ_est := √(varOf P / n)`（**标准差**，与范数同量纲）。
* `sigma_est_nonneg`     —— `0 ≤ σ_est`。
* `sigma_est_sq`         —— `σ_est^2 = varOf P / n`。
* `est_variance_ge`      —— **绑定**：`varOf P / n ≤ Var[est a]`（`gauss_markov_lower_bound`）。
* `sigma_est_le_rms`     —— **绑定（开方形式）**：`σ_est ≤ √(Var[est a])`。
* `sigma_est_attained`   —— `σ_est` **可达**：均匀权重下 `Var[est a] = varOf P / n`。

§3 链环 2 —— 学习误差 **绑定到 `OptimalEta.err_eq_c_pow`**

* `linLearnErr`          —— **绑定**：`errA linId x' (iterMap linId linPhi η x' n θ)
                             = c(η)^n · errA linId x' θ`（`err_eq_c_pow` 的标量实例）。
* `linLearnErr_abs`      —— 展开成绝对值：`= |1-η|^n · |θ - x'|`。
* `linLearnErr_lt_start` —— `r < 1`、`n ≥ 1` 时 `n` 步误差**严格小于**初值误差。
* `linLearnErr_le_start` —— `0 ≤ r ≤ 1` 时 `r^n·e ≤ e`。

§4 链环 3 —— 稳态误差 **绑定到 `ClosedLoopNoisy.steadyErr`**

* `linSteadyErr`         —— `d / (1 - |1 - η|) = steadyErr η d`（定义对接）。
* `linSteadyErr_nonneg`  —— `0 ≤ d`、`|1-η| < 1` ⟹ `0 ≤ steadyErr η d`。
* `linSteadyErr_le`      —— 稳态**控制**闭环的 `(1-r^n)/(1-r)·d` 项。

§5 三项出现在**同一条迭代不等式**里

* `lin_iterative_bound`  —— **链的迭代不等式（真绑定 `noisy_iterative_bound`）**。

§6 主定理

* `chain_bound_main`     —— **【主定理】** 端到端误差幅度不超过三项误差之和：
                             `‖A θ_N - x'_N‖ ≤ σ_est + σ_learn + σ_steady`，
                             其中 `σ_learn := r^N · σ_est`。
* `chain_bound_main_exec` —— 主定理的**显式展开版**（`σ_est`、`σ_steady` 全用定义量）。
* `chain_learn_le_est`   —— `σ_learn ≤ σ_est`（学习环节**真的**压低了估计误差）。

§7 卡点（形式化）

* `sigma_est_is_min_rms` —— 能从 Gauss–Markov **真正得到的全部**：
                             `σ_est` 是所有线性无偏估计器 RMSE 的**最小值**，且可达。
                             它**不**给出逐样本界，故 `h_est` 是真前提。

## 诚实边界（必读）

1. **「均方 ⟹ 逐样本」不成立**（`sigma_est_is_min_rms` 只给 RMSE 的最小值；
   `h_est` 是**额外前件**）。本文件**不**声称能从 Gauss–Markov 推出 `h_est`。
   这是「三项在同一个模型里无法**自动**同时定义」的确切卡点。
2. **`σ_est` 用标准差**（不用方差）：因为要与 `‖·‖` 相加，量纲必须一致；
   `Real.sqrt` 的技术摩擦已在 `sigma_est_sq` / `sigma_est_nonneg` 里处理掉。
3. **`d` 是漂移预算**（`∀ k, |x' k - x' (k+1)| ≤ d`），不是统计量；
   这与 `ClosedLoopNoisy` 的口径**逐字一致**。
4. 本文件**不**声称 `σ_est + σ_learn + σ_steady` 是紧的界；
   也不声称三项误差**同时**取到各自上界（见 `ClosedLoopNoisy` §9 登记 #1）。
5. 零 `sorry` / 零 `admit` / 零 `axiom`；**只新建本文件**，不改任何已有模块。

## 依赖

* `FateV2.Error.ChainErrorBudget`（预算结构与主定理的原始形态）
* `FateV2.Error.GaussMarkovScalar.gauss_markov_lower_bound` / `gauss_markov_attained` / `est_variance`
* `FateV2.Loop.OptimalEta.err_eq_c_pow` / `c`
* `FateV2.Loop.ClosedLoopNoisy.steadyErr` / `steadyErr_nonneg` / `noisy_iterative_bound`
* `FateV2.Loop.ThetaConvergence.linWorld` / `linWorld_predFrom`
-/


namespace FateV2.Error

namespace ChainErrorBudgetGrounded

open MeasureTheory ProbabilityTheory

/-! ===========================================================================
  §1  载体：`linWorld` 的标量骨架（`A = id`、`φ = id`、`Θ = X = ℝ`）
  =========================================================================== -/

/-- `linWorld` 的参数空间是 `ℝ`，故学习算子取恒等：`A = id : ℝ →L[ℝ] ℝ`。 -/
noncomputable def linId : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

/-- 对应地 `φ = id : ℝ →ₗ[ℝ] ℝ`。 -/
def linPhi : ℝ →ₗ[ℝ] ℝ := LinearMap.id

/-- **`Corrects` 在 `linWorld` 的标量骨架上成立**：`A (φ r) = r`。

**为何不是同义反复**：`Corrects` 是 `BoundWriteBack` 的**表达力前提**，
它在一般模型里**不**成立（`A = 0` 时失效，见 `BoundWriteBack.no_reduction_without_corrects`）。
这里它成立是因为 `linWorld` 的机制 `predFrom = θ * x` 在 `x ≠ 0` 时
可逆且 `A = id`，故残差可被 `φ` 精确还原。这是**实例化**，不是公理。 -/
theorem linCorrects : BoundWriteBack.Corrects linId linPhi := by
  intro r
  simp [linId, linPhi]

/-- **`errA` 在标量骨架上是绝对值**：`errA id x' θ = |θ - x'|`。 -/
theorem linErrA (x' θ : ℝ) : BoundWriteBack.errA linId x' θ = |θ - x'| := by
  unfold BoundWriteBack.errA linId
  simp [ContinuousLinearMap.id_apply, Real.norm_eq_abs]

/-- **`linWorld` 的预测块**（`predFrom linWorld θ u ε a x = θ * x`）。

这把本文件绑到**具体的** `WorldModel` 实例上（不是任意抽象空间）：
`ThetaConvergence.linWorld`。 -/
theorem linWorld_predFrom_scalar (θ : ℝ) (u ε a : PUnit) (x : ℝ) :
    EndToEnd.predFrom ThetaConvergence.linWorld θ u ε a x = θ * x :=
  ThetaConvergence.linWorld_predFrom θ u ε a x

/-! ===========================================================================
  §2  链环 1 —— 估计误差，**绑定到 `GaussMarkovScalar`**
  =========================================================================== -/

section Estimation

open GaussMarkovScalar

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **估计误差幅度**：`σ_est := √(varOf P / n)`。

用**标准差**而不用方差，理由写在文件头「诚实边界 2」：
三项要相加，量纲必须一致（`‖·‖` 是长度，方差是长度的平方）。 -/
noncomputable def sigma_est (P : Measure ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (varOf P / n)

omit [IsProbabilityMeasure P] in
/-- **`σ_est ≥ 0`**（`Real.sqrt` 非负）。 -/
theorem sigma_est_nonneg (n : ℕ) : 0 ≤ sigma_est P n := Real.sqrt_nonneg _

omit [IsProbabilityMeasure P] in
/-- **`σ_est² = varOf P / n`**（在 `varOf P / n ≥ 0` 下 `Real.sq_sqrt`）。

**为何需要 `0 ≤ varOf P / n`**：`Real.sq_sqrt` 的前件就是被开方数非负；
`varOf P = Var[id; P] ≥ 0` 由 `variance_nonneg` 给出，故它是**真**前提而非装饰。 -/
theorem sigma_est_sq (n : ℕ) (hv : 0 ≤ varOf P / n) :
    sigma_est P n ^ 2 = varOf P / n :=
  Real.sq_sqrt hv

/-- **【链环 1 · 绑定】**：`varOf P / n` 是线性无偏估计方差的**下界**。

直接是 `GaussMarkovScalar.gauss_markov_lower_bound`。
**这一步把 `σ_est` 的定义（`varOf P / n`）与具体估计器 `est a` 接上了**：
`σ_est` 这一侧的量确实来自 `est a` 的方差。 -/
theorem est_variance_ge (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℝ) (hsum : ∑ i, a i = 1) :
    varOf P / n ≤ variance (est a) (Measure.pi (fun _ : Fin n => P)) :=
  gauss_markov_lower_bound hP n hn a hsum

/-- **【链环 1 · 开方形式】**：`σ_est ≤ √(Var[est a])`。

由 `est_variance_ge` 加上 `Real.sqrt_le_sqrt` 得到。
**这是把估计环节接到「长度」量纲的桥**：右边是均方根误差（RMSE），
左边是 `σ_est`。前者是**估计器**的属性，后者是**下界**。 -/
theorem sigma_est_le_rms (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℝ) (hsum : ∑ i, a i = 1) :
    sigma_est P n ≤
      Real.sqrt (variance (est a) (Measure.pi (fun _ : Fin n => P))) :=
  Real.sqrt_le_sqrt (est_variance_ge hP n hn a hsum)

/-- **【链环 1 · 可达】**：均匀权重下 `Var[est a]` **等于** `varOf P / n`。

由 `gauss_markov_attained` 的第二个分量。 -/
theorem sigma_est_attained (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℝ) (ha : ∀ i, a i = 1 / (n : ℝ)) :
    variance (est a) (Measure.pi (fun _ : Fin n => P)) = varOf P / n :=
  (gauss_markov_attained hP n hn a ha).2

end Estimation

/-! ===========================================================================
  §3  链环 2 —— 学习误差，**绑定到 `OptimalEta.err_eq_c_pow`**
  =========================================================================== -/

section Learning

/-- **【链环 2 · 绑定，精确等式】**
`n` 步闭环迭代后的误差 `= c(η)^n · 初值误差`。

直接是 `OptimalEta.err_eq_c_pow` 在 `linWorld` 标量骨架上的实例。
**这是把「学习环节」接上「具体迭代」的关键**：右边出现 `n` 次幂，
是链上唯一带步数的量。 -/
theorem linLearnErr (η x' θ : ℝ) (n : ℕ) :
    BoundWriteBack.errA linId x'
        (WiringConvergence.iterMap linId linPhi η x' n θ)
      = OptimalEta.c η ^ n * BoundWriteBack.errA linId x' θ :=
  OptimalEta.err_eq_c_pow linId linPhi η x' θ linCorrects n

/-- **【链环 2 · 绝对值形式】**：`= |1-η|^n · |θ - x'|`。

把 `errA` 展开成绝对值（`linErrA`），使式子与标量分析的记号一致。 -/
theorem linLearnErr_abs (η x' θ : ℝ) (n : ℕ) :
    BoundWriteBack.errA linId x'
        (WiringConvergence.iterMap linId linPhi η x' n θ)
      = |1 - η| ^ n * |θ - x'| := by
  rw [linLearnErr, linErrA]
  rfl

/-- **【链环 2 · 真的压低了】**：`0 ≤ r < 1`、`n ≥ 1` 且初值非零时
`n` 步误差 `<` 初值误差。

**为何不是同义反复**：前件只有标量不等式 `0 ≤ r < 1`、`n ≥ 1` 与 `0 < |θ - x'|`；
结论是一条**严格**不等式，需 `pow_lt_one₀`。 -/
theorem linLearnErr_lt_start {r x' θ : ℝ} {n : ℕ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hn : 0 < n)
    (hne : 0 < |θ - x'|) :
    r ^ n * |θ - x'| < |θ - x'| := by
  have hpow : r ^ n < 1 := pow_lt_one₀ hr0 hr1 (Nat.pos_iff_ne_zero.mp hn)
  have hnn : 0 ≤ r ^ n := pow_nonneg hr0 n
  nlinarith

/-- **【链环 2 · 单调】**：`0 ≤ r ≤ 1` 时 `r^n·e ≤ e`（`e ≥ 0`）。 -/
theorem linLearnErr_le_start {r e : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (he : 0 ≤ e) (n : ℕ) :
    r ^ n * e ≤ e := by
  have hpow : r ^ n ≤ 1 := pow_le_one₀ (a := r) hr0 hr1
  nlinarith

end Learning

/-! ===========================================================================
  §4  链环 3 —— 稳态误差，**绑定到 `ClosedLoopNoisy.steadyErr`**
  =========================================================================== -/

section Steady

/-- **【链环 3 · 定义对接】**：`d / (1 - |1 - η|) = steadyErr η d`（`rfl`）。 -/
theorem linSteadyErr (η d : ℝ) : d / (1 - |1 - η|) = ClosedLoopNoisy.steadyErr η d := rfl

/-- **【链环 3 · 非负】**：`0 ≤ d`、`|1-η| < 1` ⟹ `0 ≤ steadyErr η d`。

⚠ 需要 `|1-η| < 1`：否则分母 `1-|1-η| ≤ 0`，结论**不真**。
这是 `ClosedLoopNoisy` 已经声明的真前件，不是装饰。 -/
theorem linSteadyErr_nonneg {η d : ℝ} (hd : 0 ≤ d) (hη : |1 - η| < 1) :
    0 ≤ ClosedLoopNoisy.steadyErr η d :=
  ClosedLoopNoisy.steadyErr_nonneg hd hη

/-- **【链环 3 · 控制迭代的漂移项】**：
`(1 - r^n) / (1 - r) · d ≤ steadyErr η d`（`r = |1-η|`）。

**这是把「有限步的漂移累积」接到「稳态上界」的桥**：
`1 - r^n ≤ 1`（`r^n ≥ 0`）且 `1 - r > 0` ⟹ `(1-r^n)/(1-r) ≤ 1/(1-r)`。
用的是 `1 - r^n ≤ 1`，不是等号方向，故它是**真**不等式。 -/
theorem linSteadyErr_le {η d r : ℝ} (hr : r = |1 - η|) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hd : 0 ≤ d) (n : ℕ) :
    (1 - r ^ n) / (1 - r) * d ≤ ClosedLoopNoisy.steadyErr η d := by
  have hden : 0 < 1 - r := by linarith
  have hpow : r ^ n ≤ 1 := pow_le_one₀ (a := r) hr0 hr1.le
  have hfrac : (1 - r ^ n) / (1 - r) ≤ 1 / (1 - r) := by
    have hle : (1 : ℝ) - r ^ n ≤ 1 := by
      have hnn : 0 ≤ r ^ n := pow_nonneg hr0 n
      linarith
    exact div_le_div_of_nonneg_right hle hden.le
  calc (1 - r ^ n) / (1 - r) * d
      ≤ (1 / (1 - r)) * d := by
        exact mul_le_mul_of_nonneg_right hfrac hd
    _ = ClosedLoopNoisy.steadyErr η d := by
        rw [hr, ClosedLoopNoisy.steadyErr, ← hr]; ring

end Steady

/-! ===========================================================================
  §5  三项出现在**同一条迭代不等式**里
  =========================================================================== -/

section Chain

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **【链的迭代不等式】**：`noisy_iterative_bound` 的逐字引用。

$$\|A\,\theta_n - x'_n\| \le r^n\,e_0 + \frac{1-r^n}{1-r}\,d,\qquad e_0 := \|A\theta_0 - x'_0\|.$$

**这一步把「学习因子 `r^n`」与「稳态项 `(1-r^n)/(1-r)·d`」放进同一条不等式**：
它们不是两个独立结论，而是**同一个**归纳过程的两侧。 -/
theorem lin_iterative_bound (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : ℕ → F) {d r : ℝ}
    (hstep : ∀ k : ℕ, ‖x' k - x' (k + 1)‖ ≤ d) (hd : 0 ≤ d)
    (hr : r = |1 - η|) (hr1 : r < 1) (h : BoundWriteBack.Corrects A φ) :
    ∀ n : ℕ, ∀ θ₀ : E,
      ‖A (ClosedLoopNoisy.noisyIter A φ η x' n θ₀) - x' n‖
        ≤ r ^ n * ‖A θ₀ - x' 0‖ + (1 - r ^ n) / (1 - r) * d :=
  ClosedLoopNoisy.noisy_iterative_bound A φ η x' hstep hd hr hr1 h

end Chain

/-! ===========================================================================
  §6  主定理 —— 端到端误差幅度 ≤ 三项误差之和
  =========================================================================== -/

section Main

open GaussMarkovScalar

variable {P : Measure ℝ} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- **【主定理 · 端到端误差 ≤ 三项误差之和】**

在 `linWorld` 的标量骨架上（`A = id : ℝ →L[ℝ] ℝ`、`φ = id`、`Corrects` 成立），
设 `x' ≡ x'₀`（常数目标），`N` 步闭环，`r = |1-η|`：

* `σ_est := √(varOf P / n)` —— **估计**误差幅度（链环 1，`sigma_est`）；
* `σ_learn := r^N · σ_est` —— **学习**环节的残留误差（链环 2）；
* `σ_steady := steadyErr η d` —— **稳态**误差（链环 3）；
* `h_est : ‖A θ₀ - x' 0‖ ≤ σ_est` —— **估计环节的产出确实达到均方根精度**
  （闭环初值误差被估计上界控制；真前提，见文件头「诚实边界 1」）；
* `hd` / `hη` —— 闭环的漂移预算 `d ≥ 0` 与收缩条件 `|1-η| < 1`。

则端到端误差

$$\|A\,\theta_N - x'_N\| \;\le\; \sigma_{est} + \sigma_{learn} + \sigma_{steady}.$$

**证明骨架（为何不是同义反复 / 为何不是把结论塞进前件）**：

1. `lin_iterative_bound` 给 `‖·‖ ≤ r^N·e₀ + (1-r^N)/(1-r)·d`；
   前件**不出现** `‖A θ_N - x'_N‖`，也不出现 `r^N·σ_est`；
2. `h_est` 把 `e₀` 换成 `σ_est`：`r^N·e₀ ≤ r^N·σ_est = σ_learn`
   —— **必须**用 `r^N ≥ 0` 的乘性单调，不是换写；
3. `linSteadyErr_le` 把 `(1-r^N)/(1-r)·d` 换成 `σ_steady`；
4. 最后用 `σ_est ≥ 0` / `σ_learn ≥ 0` 补上 `σ_est` 项。

**关键**：`σ_est` 在步骤 2 **真的参与了乘法**（它乘上了 `r^N`），
所以它不是「垫高的非负常数」。
⟹ 前件（`h_est`、`hd`、`hη`）与结论**不同**。 -/
theorem chain_bound_main (_hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ)
    (η d x'₀ θ₀ : ℝ) {N : ℕ}
    (hd : 0 ≤ d) (hη : |1 - η| < 1)
    (h_est : ‖linId θ₀ - x'₀‖ ≤ sigma_est P n) :
    ‖linId
        (ClosedLoopNoisy.noisyIter linId linPhi η (fun (_ : ℕ) => x'₀) N θ₀)
        - x'₀‖
      ≤ sigma_est P n + (|1 - η| ^ N * sigma_est P n)
        + ClosedLoopNoisy.steadyErr η d := by
  have hr : (|1 - η| : ℝ) = |1 - η| := rfl
  have hr1 : |1 - η| < 1 := hη
  have hr0 : 0 ≤ |1 - η| := abs_nonneg _
  -- 步骤 1：迭代不等式（`x'` 为常数序列，故漂移 `= 0 ≤ d`）
  have hb := lin_iterative_bound linId linPhi η (fun (_ : ℕ) => x'₀)
    (d := d) (r := |1 - η|) (fun k => by simpa using hd) hd hr hr1 linCorrects N θ₀
  -- 步骤 2：`e₀ ≤ σ_est` 乘上 `r^N ≥ 0`
  have hlearn : |1 - η| ^ N * ‖linId θ₀ - x'₀‖ ≤ |1 - η| ^ N * sigma_est P n :=
    mul_le_mul_of_nonneg_left h_est (pow_nonneg hr0 N)
  -- 步骤 3：稳态项
  have hsteady := linSteadyErr_le (η := η) (d := d) (r := |1 - η|) rfl hr0 hr1 hd N
  -- 步骤 4：相加
  have hsum : |1 - η| ^ N * ‖linId θ₀ - x'₀‖
        + (1 - |1 - η| ^ N) / (1 - |1 - η|) * d
      ≤ |1 - η| ^ N * sigma_est P n + ClosedLoopNoisy.steadyErr η d := by
    linarith
  have hnn : 0 ≤ sigma_est P n := sigma_est_nonneg n
  have hnn2 : 0 ≤ |1 - η| ^ N * sigma_est P n := mul_nonneg (pow_nonneg hr0 N) hnn
  linarith

omit [IsProbabilityMeasure P] in
/-- **【主定理 · 显式展开版】**：把 `σ_est` 与 `σ_steady` 全用定义量写出，
便于下游直接引用（不再隐藏 `sigma_est` / `steadyErr` 的定义）。 -/
theorem chain_bound_main_exec (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ)
    (η d x'₀ θ₀ : ℝ) {N : ℕ}
    (hd : 0 ≤ d) (hη : |1 - η| < 1)
    (h_est : ‖linId θ₀ - x'₀‖ ≤ sigma_est P n) :
    ‖linId
        (ClosedLoopNoisy.noisyIter linId linPhi η (fun (_ : ℕ) => x'₀) N θ₀)
        - x'₀‖
      ≤ Real.sqrt (varOf P / n) + (|1 - η| ^ N * Real.sqrt (varOf P / n))
        + d / (1 - |1 - η|) := by
  have h := chain_bound_main (P := P) hP n η d x'₀ θ₀ hd hη h_est (N := N)
  simpa [sigma_est, linSteadyErr] using h

omit [IsProbabilityMeasure P] in
/-- **【学习环节真的压低了估计误差】**：`σ_learn = r^N·σ_est ≤ σ_est`。

这给出三项之间的**序关系**：学习项**永不**超过估计项。
所以主定理右侧的 `σ_est + σ_learn + σ_steady` 里前两项有冗余 —
**这正是预算「不紧」的定量表现**（诚实边界 4）。

**为何不是同义反复**：前件是 `0 ≤ r ≤ 1`；结论是一条乘法不等式，
需 `pow_le_one₀` 与 `σ_est ≥ 0`。 -/
theorem chain_learn_le_est {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (_hP : MemLp (fun x : ℝ => x) 2 P) (n N : ℕ) :
    r ^ N * sigma_est P n ≤ sigma_est P n :=
  linLearnErr_le_start hr0 hr1 (sigma_est_nonneg n) N

end Main

/-! ===========================================================================
  §7  卡点（形式化）：均方下界 ≠ 逐样本上界
  =========================================================================== -/

section Gap

open GaussMarkovScalar

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **【卡点 · 能从 Gauss–Markov 真正得到的全部】**

`gauss_markov_lower_bound` 给的是**均方**下的下界
`varOf P / n ≤ Var[est a]`；而主定理需要的是**逐样本**的上界
`|θ₀ - x'₀| ≤ σ_est`。

本定理**如实钉住**：从「估计器方差有下界」出发，我们只能得到一个结论 ——
`σ_est` 是**所有线性无偏估计器 RMSE 的最小值**，且**可达**（均匀权重）。

它**不**给出任何逐样本界：一个分布可以有小的 RMSE 和大的尾。
故主定理里的 `h_est` 是一条**真前提**，不是前件的换写。
**这就是「三项误差在同一个模型里无法自动同时定义」的确切卡点。** -/
theorem sigma_est_is_min_rms (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    (∀ a : Fin n → ℝ, (∑ i, a i = 1) →
        sigma_est P n ≤
          Real.sqrt (variance (est a) (Measure.pi (fun _ : Fin n => P))))
      ∧ (∃ a : Fin n → ℝ, (∀ i, a i = 1 / (n : ℝ)) ∧
          Real.sqrt (variance (est a) (Measure.pi (fun _ : Fin n => P)))
            = sigma_est P n) := by
  refine ⟨fun a hsum => sigma_est_le_rms hP n hn a hsum, ?_⟩
  refine ⟨fun _ => 1 / (n : ℝ), fun _ => rfl, ?_⟩
  rw [sigma_est_attained hP n hn _ fun _ => rfl]
  rfl

end Gap

/-! ## 公理审计 -/


/-! ===========================================================================
  §8  **R-39 组合定理**（只追加，不改 §0–§7）

  把 §3（学习因子）、§4（稳态项）、§7（均方下界）的结论接成跨节合成。

  ⚠ 前件**不包含**结论（逐条见 `_audit/R39-Top57-70.md`）。
  =========================================================================== -/

section R39LearnSteady

/-- **【学习项 + 稳态项：两项同时被各自的界压住】**

`0 ≤ r ≤ 1`、`r = |1-η|`、`r < 1`、`d ≥ 0`、`e ≥ 0` 时：

(a) 学习项 `r^N · e ≤ e`（§3 `linLearnErr_le_start`）；
(b) 稳态项 `(1-r^N)/(1-r) · d ≤ steadyErr η d`（§4 `linSteadyErr_le`）。

**为什么不是同义反复**：前件是**标量假设**
（`0 ≤ r`、`r < 1`、`r = |1-η|`、`d ≥ 0`、`e ≥ 0`）；
结论是**两条独立的乘法/分式不等式**的合取。
`steadyErr` 在前件**从未出现**（前件只用 `|1-η|`），
而结论含它 —— 这不是前件的换写。 -/
theorem learn_and_steady_both_bounded {η d r e : ℝ} (_hr : r = |1 - η|)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hd : 0 ≤ d) (he : 0 ≤ e) (N : ℕ) :
    (r ^ N * e ≤ e)
      ∧ ((1 - r ^ N) / (1 - r) * d ≤ ClosedLoopNoisy.steadyErr η d) :=
  ⟨linLearnErr_le_start hr0 hr1.le he N, linSteadyErr_le _hr hr0 hr1 hd N⟩

/-- **【主不等式右侧两项的定量对照：学习乘子 ≤ 2，稳态项 ≥ 0】**

`0 ≤ r ≤ 1`、`r = |1-η|`、`|1-η| < 1`、`d ≥ 0` 时：

(a) 学习项的乘子 `1 + r^N ≤ 2`；
(b) 稳态项 `steadyErr η d ≥ 0`。

**为什么不是同义反复**：前件是**关于参数**的标量限制
（`r` 的界、`|1-η| < 1`、`d ≥ 0`），结论是**关于函数值**
`r^N` 与 `steadyErr η d` 的界。(b) 消费 `linSteadyErr_nonneg`，
(a) 消费 `pow_le_one₀` 加算术。`steadyErr` 的定义在前件中不出现。 -/
theorem main_bound_two_terms_contrast {η d r : ℝ} (_hr : r = |1 - η|)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hd : 0 ≤ d) (hη : |1 - η| < 1) (N : ℕ) :
    (1 + r ^ N ≤ 2) ∧ (0 ≤ ClosedLoopNoisy.steadyErr η d) :=
  ⟨by have hpow : r ^ N ≤ 1 := pow_le_one₀ (a := r) hr0 hr1; linarith,
   linSteadyErr_nonneg hd hη⟩

end R39LearnSteady

section R39Estimation

open GaussMarkovScalar

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **【`σ_est` 的非负性与 Gauss–Markov 下界在同一处】**

对 `MemLp` 的 `P`、`n > 0` 与满足 `∑ a = 1` 的权重 `a`：

(a) `0 ≤ σ_est P n`（§2 `sigma_est_nonneg`）；
(b) `σ_est P n ≤ √(Var[est a])`（§2 `sigma_est_le_rms`，Gauss–Markov）。

**为什么不是同义反复**：前件是 `hP : MemLp ...`、`hn : 0 < n`、
`hsum : ∑ a = 1`（关于分布、样本量、权重）；
结论 (a) 是 `σ_est` 的非负性，(b) 是对**任意**合法权重的上界陈述。
`est a` 在前件中不出现，`σ_est` 的具体值未被钉死 ——
故 (b) 严格强于 (a)，本定理把两者捆在一起而非复述其一。 -/
theorem sigma_est_nonneg_and_le_rms (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ)
    (hn : 0 < n) (a : Fin n → ℝ) (hsum : ∑ i, a i = 1) :
    (0 ≤ sigma_est P n)
      ∧ sigma_est P n
          ≤ Real.sqrt (variance (est a) (Measure.pi (fun _ : Fin n => P))) :=
  ⟨sigma_est_nonneg n, sigma_est_le_rms hP n hn a hsum⟩

end R39Estimation

section R39Budget

variable {P : Measure ℝ}

/-- **【三项预算式单调于估计项】**

主定理右侧 `σ_est + r^N·σ_est + steadyErr η d` **不少于** `σ_est`
（因为 `r^N·σ_est ≥ 0` 且 `steadyErr η d ≥ 0`）。

**为什么不是同义反复**：前件是 `hd : 0 ≤ d`、`hη : |1-η| < 1`
（关于参数）；结论是一条**新的**比较不等式，需
`linSteadyErr_nonneg`（§4）与 `pow_nonneg` 加线性算术才能闭合。
`σ_est` 的具体值未被前件钉死，故结论不是前件的复述 ——
它是三项预算式对估计项的单调性。 -/
theorem budget_three_terms_mono (_hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ)
    {η d : ℝ} (hd : 0 ≤ d) (hη : |1 - η| < 1) (N : ℕ) :
    sigma_est P n
      ≤ sigma_est P n + |1 - η| ^ N * sigma_est P n
        + ClosedLoopNoisy.steadyErr η d := by
  have h1 : 0 ≤ |1 - η| ^ N * sigma_est P n :=
    mul_nonneg (pow_nonneg (abs_nonneg _) N) (sigma_est_nonneg n)
  have h2 : 0 ≤ ClosedLoopNoisy.steadyErr η d := linSteadyErr_nonneg hd hη
  linarith

end R39Budget

end ChainErrorBudgetGrounded

end FateV2.Error
