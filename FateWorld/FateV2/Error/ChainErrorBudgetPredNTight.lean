/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.ChainErrorBudgetPredNTight`
======================================

## ⚠⚠ 任务 B 结论：原「学习项消去」目标**是假命题**（相关定理已删除）

> **TL;DR**：`ChainErrorBudgetPredNTight.lean:157` 的 `linarith failed` **不是**缺一条等式，
> 而是**目标陈述本身为假**。原 §2 `capstone_bound_no_learn` 及其下游 §3 / §5 已被
> **删除**（不用 `sorry` 占位），保留两条真定理（§1、§4），并把反例**形式化证明**在
> §6.4 的 `no_learn_target_is_false` 里。

### 为什么这条线走不通（数学诊断）

原证明策略：由 `learn_term_eq_residual` 得 `c(η)^n·errA = E`（`E` 是左端范数），
代入上游 `pred_n_error_bound` 后作 `linarith` 消去两边共同的 `E`。

**这是错的**。代入后前件是

    E ≤ optEstimate + estGap + E + steadyTerm

它**只等价于** `0 ≤ optEstimate + estGap + steadyTerm`，**对 `E` 没有任何上界**。
所以「消去 `E`」根本得不到 `E ≤ optEstimate + estGap + steadyTerm`。
`linarith` 报告 failure 是**正确**的：补 `0 ≤ E` 也无用（反例：`E = 5`、`A = 0`、`steady = 1`）。

**具体反例**：`η = 1/2`、`θstar = 0`、`x = 1`、`n = 0`。由 `thetaN_closed`，
`thetaN (1/2) 0 1 θ 0 = θ`，故左端 `= |θ|`；而右端
`optEstimate P 1 + estGap P 1 a + steadyTerm (1/2) 0` **与 `θ` 无关**。
原结论要求 `|θ| ≤ A` 对**所有** `θ` 成立 —— 取 `θ = |A| + 1` 即矛盾。
（§6.4 已把它证成定理，`#print axioms` 干净。）

### 本文件**现在**声明的定理（2 条，均真，均无 `sorry`）

§1 `learn_term_eq_residual` —— `c(η)^n·errA` **精确等于**左端残差（真，等式形式）
§4 `capstone_bound_eta_one_no_learn` —— `η = 1`、`n ≥ 1` 时左端**恰为 0**（真）
§6.4 `no_learn_target_is_false` —— ⚠ **反例**：原 §2 的结论形状为假

### 已删除的定理（**陈述为假**，按纪律 6 删除，不用 `sorry` 占位）

* ~~`capstone_bound_no_learn`~~（原 §2）—— 缺 `E` 的上界，反例见上
* ~~`capstone_bound_no_learn_closed`~~（原 §3）—— 由上一条导出，同假
* ~~`noisyIter_bound_no_learn`~~（原 §5）—— 同上，同假

### 若要救活原目标（未做，仅登记）

需要**新增前件**给出 `E` 的上界，例如 `c η ^ n * errA (mulCLM x) (θstar * x) θ = 0`
（即 `η = 1` 或初始残差为零）。前者退化为 §4 那一族；
若直接假设 `‖x θ₀ - θ*x‖` 小于右端，则**把结论当假设**（违反纪律 7），不采纳。

## 前件自查（纪律 7）

| 定理 | 前件 | 结论 | 结论是否藏在前件里 |
|---|---|---|---|
| `learn_term_eq_residual` | `x ≠ 0` | 两条闭式的**相等** | ❌ 否（`x ≠ 0` 只保证单步可逆，不含 `n` 步信息） |
| `capstone_bound_eta_one_no_learn` | `θ*`、`x`、`θ`、`x ≠ 0`、`0 < n` | 左端 `= 0`（`η = 1`） | ❌ 否（结论是**轨迹的等号**，前件只有初始数据） |
| `no_learn_target_is_false` | 一条「三项界对所有 θ 成立」的假设 | `False` | ❌ 否（正是**否定**该假设） |

## 纪律

* 零 `sorry` / 零 `admit` / 零 `axiom`（文末 `#print axioms` 逐条审计）。
* 只新增/修改本文件，**不修改**任何其他已有模块。
-/


import FateWorld.FateV2.Error.ChainErrorBudgetPredN
import FateWorld.FateV2.Error.ChainErrorBudgetBound
import Mathlib.Tactic

namespace FateV2.Error

open FateV2.Modeling
namespace ChainErrorBudgetPredNTight

open FateV2.Error.GaussMarkovScalar
open FateV2.Loop.BoundWriteBack
open FateV2.Loop.ClosedLoopNoisy
open Fate.ChainErrorBudgetBound
open Fate.ChainErrorBudgetPredN
open FateV2.Loop.ThetaConvergence
open Fate.AssemblyLearnsScratch
open FateV2.Loop.OptimalEta

open MeasureTheory ProbabilityTheory

/-!
  # Error · ChainErrorBudgetPredNTight

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ChainErrorBudgetPredNTight.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ChainErrorBudgetPredN, ChainErrorBudgetBound
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  学习项 **精确等于** 左端残差
  =========================================================================== -/

/-- ⭐⭐⭐ **【学习项 = 残差（两条上游闭式拼合）】**

$$\underbrace{c(\eta)^n \cdot \texttt{errA}\ (\texttt{mulCLM}\ x)\ (\theta^* x)\ \theta_0}_{\text{预算里的学习项}}
  \;=\; \bigl\|\,x\,\theta_n - \theta^* x\,\bigr\| .$$

左边是 `pred_n_error_bound` 右端的**第三项**，右边是**同一个定理的左端**。

**为何不是同义反复**：左式中的 `errA` 展开后是 `‖x θ₀ - θ* x‖`（**初始**误差），
右式是**第 `n` 步**的误差。两者相等需要 `c(η)^n` 这条 `n` 步收缩律 ——
即 `ChainErrorBudgetPredN.simMultiError_closed_abs`（对 `n` 归纳，
用 `endToEndIter_succ` + `linWorld_endToEnd_eq_wbW` + `iterMap_succ` + `stepMap_eq_wbW`）。
前件 `x ≠ 0` **不含**任何 `n` 步信息。 -/
theorem learn_term_eq_residual (η θstar x θ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    c η ^ n * errA (mulCLM x) (θstar * x) θ
      = ‖mulCLM x (thetaN η θstar x θ n) - θstar * x‖ := by
  rw [errA]
  exact (ChainErrorBudgetPredN.simMultiError_closed_abs η θstar x θ hx n).symm

/-! ===========================================================================
  §2  ⚠ **已删除**：原 `capstone_bound_no_learn`（陈述为假，见文件头）
  =========================================================================== -/

/-! 原 §2 的 `capstone_bound_no_learn` 及其下游 `capstone_bound_no_learn_closed`
（§3）与 `noisyIter_bound_no_learn`（§5）**已被删除**，原因是它们的**陈述本身为假**，
无法在不引入 `sorry` 的前提下证明。反例与机器检查见文件头「⚠ 任务 B 结论」一节。

`linarith` 在 `Fate/ChainErrorBudgetPredNTight.lean:157` 报告
`failed to find a contradiction`，**不是**缺一条等式，而是缺一个**数学上不存在**的
不变量：`E ≤ A + estGap + E + steadyTerm` 在 ℝ 中**不能**推出 `E ≤ A + estGap + steadyTerm`
（取 `E = 5`、`A = 0`、`steadyTerm = 1` 即反例）。补 `0 ≤ E` 也无济于事 ——
结论对 `E` 没有上界约束。 -/

/-! ===========================================================================
  §4  紧性：`η = 1` 时界被**精确达到**
  =========================================================================== -/

/-- ⭐⭐⭐ **【`η = 1`、`n ≥ 1`：预算被精确达到（左端 = 0）】**

`η = 1` 时 `c(1)^n = 0`（`n ≥ 1`），故 `n` 步后残差**恰为 0`：

$$\bigl\|x\,\theta_n - \theta^*x\bigr\| = 0 .$$

**⭐ 意义（对卡点 #3 的回答）**：`capstone_bound_no_learn` 的右端
`optEstimate + estGap + steadyTerm = Var[est a]` 在 `η = 1` 处是**可达的**
（左端取到最小值 `0`）。这说明消去学习项后的界**不是空话**：
它在这一族参数上被**精确达到**。 -/
theorem capstone_bound_eta_one_no_learn (θstar x θ : ℝ) (hx : x ≠ 0) {n : ℕ}
    (hn1 : 0 < n) :
    ‖mulCLM x (thetaN 1 θstar x θ n) - θstar * x‖ = 0 :=
  ChainErrorBudgetPredN.pred_n_error_bound_eta_one_exact θstar x θ hx hn1


/-! ===========================================================================
  §6  ⚠ 诚实登记
  =========================================================================== -/

/-!
### 6.1 本文件**真的**接入了什么

1. **在证明体里调用了 `ChainErrorBudgetPredN` 的定理**：
   `simMultiError_closed_abs`（经 §1 `learn_term_eq_residual`）、
   `pred_n_error_bound_eta_one_exact`（§4）。
2. **原计划调用的 `ChainErrorBudgetBound` 定理**（`chain_est_budget`、
   `thetaN_eq_noisyIter_linWorld`）**已随假陈述一起删除**，不再出现。

### 6.2 ⚠ **任务 B 结论：原「学习项消去」目标是假命题，已删除相应定理**

原文件声称：由 `c(η)^n·errA = E`（精确等式）可从
`E ≤ optEstimate + estGap + c(η)^n·errA + steadyTerm`
**消去**学习项，得到 `E ≤ optEstimate + estGap + steadyTerm`。

**这是错的。** 代入等式后前件只是
`E ≤ optEstimate + estGap + E + steadyTerm`，
它等价于 `0 ≤ optEstimate + estGap + steadyTerm`，
**完全不约束 `E`**。要得到三项界必须另有 `E` 的上界，而前件中**没有**。

**反例（机器检查通过，见下）**：取 `η = 1/2`、`θstar = 0`、`x = 1`、`n = 0`。
由 `ThetaConvergence.thetaN_closed` 得 `thetaN (1/2) 0 1 θ 0 = θ`，
故左端 `= |θ|`；而右端 `optEstimate P 1 + estGap P 1 a + steadyTerm (1/2) 0`
**不含 `θ`**，是与 `θ` 无关的常数 `A`。
于是原结论要求 `|θ| ≤ A` 对**所有** `θ` 成立 —— 取 `θ = |A| + 1` 即得矛盾。
本节末尾的 `no_learn_target_is_false` 把这一反例**形式化地**证明出来
（只用上游真定理，无 `sorry`）。

**因此**：按任务纪律 6，删除了
`capstone_bound_no_learn`（§2）、`capstone_bound_no_learn_closed`（§3）、
`noisyIter_bound_no_learn`（§5）三条假陈述。**保留**两条真定理：
`learn_term_eq_residual`（§1，等式形式，真）与
`capstone_bound_eta_one_no_learn`（§4，`η = 1` 且 `n ≥ 1` 时左端确为 0，真）。

### 6.3 若要救活原目标，需要什么**新前件**（未做，仅登记）

必须额外假设一个对 `E` 的上界，例如 `c η ^ n * errA (mulCLM x) (θstar * x) θ = 0`
（即 `η = 1` 或初始残差为零），或直接把 `‖x θ₀ - θ*x‖` 限制在
`optEstimate + estGap + steadyTerm` 之内。前者使结论退化成
`capstone_bound_eta_one_no_learn` 一族；后者是**把结论当假设**（同义反复），
按纪律 7 均不采纳。
-/

/-! ### 6.4 反例的机器检查（**真证明**，无 `sorry`） -/

/-- ⚠ **原 §2 目标的结论形状为假**：若「消去学习项」后的三项界成立，
则对任意 `θ` 有 `|θ| ≤ A`（`A` 与 `θ` 无关），从而矛盾。

这里 `A := optEstimate P 1 + estGap P 1 a + steadyTerm (1/2) 0`。 -/
theorem no_learn_target_is_false
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (a : Fin 1 → ℝ)
    (hconcl : ∀ θ : ℝ,
      ‖mulCLM 1 (thetaN (1/2) 0 1 θ 0) - 0 * 1‖
        ≤ optEstimate P 1 + estGap P 1 a + steadyTerm (1/2) 0) :
    False := by
  have hleft : ∀ θ : ℝ, ‖mulCLM 1 (thetaN (1/2) 0 1 θ 0) - 0 * 1‖ = |θ| := by
    intro θ
    have h0 : thetaN (1/2) 0 1 θ 0 = θ := by
      have := thetaN_closed (1/2) 0 1 θ (by norm_num) 0
      simpa using this
    rw [h0, mulCLM_apply]
    simp
  set A := optEstimate P 1 + estGap P 1 a + steadyTerm (1/2) 0 with hA
  have h := hconcl (|A| + 1)
  rw [hleft] at h
  have habs : |(|A| + 1)| = |A| + 1 := abs_of_pos (by positivity)
  rw [habs] at h
  linarith [le_abs_self A]

/-! ## 公理审计 -/

#print axioms learn_term_eq_residual
#print axioms capstone_bound_eta_one_no_learn
#print axioms no_learn_target_is_false

end ChainErrorBudgetPredNTight
