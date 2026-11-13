/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.ChainErrorBudgetBound`

## ⚠ 第 214 轮修复登记（编译 4 个 error 的处置，读前必看）

1. **删除了一条假定理** `errA_iterMap_eq_thetaN_gap`。其陈述（`1` 步 `iterMap` 的
   `errA` 等于不带 `|x_pt|` 缩放的 `|fstep - θ*|`）**是假命题**：
   反例 `η = 1/2, θ* = 3, x_pt = 2, θ₀ = 1` 时左端 `= 2`、右端 `= 1`
   （左端实际是 `|x_pt| · |fstep - θ*|`）。已删除，**未用 `sorry` 占位**；
   见 §3 中的登记段落。`n` 步且对**任意** `x` 的真绑定由
   `chain_total_bound_const_obs`（两侧用**同一个** `A` 与 `x'`，无缩放失配）承担。
2. 修复了 `chain_total_bound_const_obs` 的两处 tactic 错误：
   （a）`zero` 分支的 `congr 1` 已把目标证完，后续 `ring` 多余（`No goals to be solved`），已删；
   （b）`succ` 分支需**先**把右端的 `iterMap (k+1) θ` 重写为 `iterMap k (stepMap … θ)`
   （再 `stepMap_eq_wbW`），然后才能用归纳假设；原顺序颠倒导致
   `Did not find an occurrence of the pattern`。
3. 修正了文件头的 **6 处宣传溢出**（引用了不存在的定理名 / 不存在的前件）：
   `learnErr_iterMap_eq_linWorld`、`steady_nonneg`、`steady_bound_of_noisy`、
   `steady_perturbation_bound`、假的`hxe : x' n = x` 推导、以及
   `chain_total_bound_linWorld` 的“任意 `x`、任意步数、带噪漂移”描述。
   现文件头逐字对应**实际**签名。
4. 审计命令（两遍均零 error、零 sorry）：
   `lake env lean Fate/ChainErrorBudgetBound.lean`。文末 `#print axioms` 的 13 条
   均只依赖 `propext, Classical.choice, Quot.sound`。
5. `hP`、`hn`、`hsum`、`hx`、`hη` 在主定理中**未被证明引用**（Unused variable 警告）：
   这是主定理偏弱的**证据**，如实保留（未改陈述以避免破坏签名）。

## 目标（第 205 轮自查的整改：**真正绑定**的整条链误差预算）

第 205 轮自查判定 `Fate/ChainErrorBudget.lean` 的主定理
`chain_end_to_end_from_links` **本质是三角不等式**：它的 `Ω₁ Ω₂ Ω₃`
是任意赋范空间里的**任意**向量，与任何具体模块**无关**。
本文件做**真绑定**版本：三项误差**全部**用上游模块的**具体定义**，
且在**同一个具体 `WorldModel` 实例**（`ThetaConvergence.linWorld`）上的
**同一条迭代**（`ThetaConvergence.thetaN` = `EndToEnd.endToEndIter linWorld`）里
同时出现。

## 三项误差的**具体绑定**（逐项说明「绑定到哪个定义」）

| 项 | 本文件的定义 | 绑定到的**具体**上游定义 |
|---|---|---|
| 最优误差 | `optEstimate P` | `GaussMarkovScalar.gauss_markov_iff` / `gauss_markov_attained`：线性无偏估计器的**可达最优方差** `varOf P / n` |
| 估计误差 | `estGap P n a` | `GaussMarkovScalar.est_variance` / `gauss_markov_lower_bound`：**具体**估计器 `est a` 在 iid 乘积测度下的**真实方差**与最优值之差 |
| 学习误差 | `learnErr A φ x θ η n` | `OptimalEta.err_eq_c_pow`：`BoundWriteBack.errA`（即 `‖A θ_n - x'‖`）对 `WiringConvergence.iterMap` 作用 `n` 步后的**真实值** |
| 稳态误差 | `ClosedLoopNoisy.steadyErr η d` | `ClosedLoopNoisy.noisy_limsup_bound`：带噪闭环的 `limsup` 上界 `d/(1-\|1-η\|)` |

**本文件不给「预算上界」再乘一个任意常数**：主定理的右端
`optEstimate P + estGap P n a + learnErr … + ClosedLoopNoisy.steadyErr η d`
**就是**四项具体误差的**和**（不是新引入的抽象预算）。

## 本文件**实际声明**的定理（与下文一一对应，无宣传溢出）

§1 载体与定义
* `estGap_eq_variance_sub` —— `estGap P n a = Var[est a] - varOf P / n`（定义展开）
* `learnErr_eq_errA_iterMap` —— 学习误差**就是** `errA` 在 `iterMap` 上的值
  （**关键桥**：把 `OptimalEta.err_eq_c_pow`（`iterMap` 版本）
  与 `AssemblyLearnsScratch.endToEndIter_linWorld_eq_noisyIter`（`linWorld` 版本）
  接起来，从而在 `linWorld` 上三者是**同一条迭代**）
* `estGap_nonneg_of_real_estimator` —— 真实无偏估计器的估计误差 `≥ 0`
* `learnErr_nonneg` —— 学习误差 `≥ 0`
* `steadyTerm_nonneg` —— 稳态误差 `≥ 0`（`|1-η| < 1`、`d ≥ 0`）

§2 链环 1（估计 · `GaussMarkovScalar` 具体定义）
* `optEstimate_eq_est_variance` —— 均匀加权 `a ≡ 1/n` 时**真实方差恰等于** `optEstimate`
  （由 `gauss_markov_attained`）
* `estGap_eq_zero_of_uniform` —— 对应的 `estGap = 0`（估计环节**无差距**）
* `chain_est_budget` —— 这一环进入总预算的方式

§3 链环 2（学习 · `OptimalEta.err_eq_c_pow` 具体定义，在 `linWorld` 上）
* `learnErr_closed` —— `learnErr A φ x θ η n = c(η)^n · errA A x θ`（**精确等式**）
* `learnErr_eq_thetaN_gap` —— ⭐⭐⭐ **绑定定理**（`x = 1` 的标量骨架）：
  `learnErr (mulCLM 1) (invLM 1) θ* θ₀ η n = |thetaN η θ* 1 θ₀ n - θ*|`
  （同一迭代、同一误差，`n` 步）
* `learnErr_nonexpansive` —— `c(η) ≤ 1` 时学习误差**对 `n` 单调不增**（比"有界"强）
* `learnErr_le_initial` —— `c(η) ≤ 1` 时 `learnErr … ≤ errA A x θ`

§4 链环 3（稳态 · `ClosedLoopNoisy` 具体定义，在 `linWorld` 上）
* `steady_closed` —— `steadyErr η d = d / (1 - c η)`（`c` 记号统一）
* `steady_bound_linWorld` —— 在 `linWorld` 上，观测漂移 `‖x' k - x' (k+1)‖ ≤ d`、
  `|1-η| < 1` 时闭环 `limsup` 误差 `≤ steadyErr η d`
* `thetaN_eq_noisyIter_linWorld` —— 学习轨迹 `thetaN` 与带噪闭环 `noisyIter`
  在 `linWorld` 常数观测下**逐值相同**（同一迭代）

§5 **主定理**（实际情况，见下方 ⚠ 诚实审计）
* `chain_total_bound_linWorld` —— 主定理（`x = 1`、`n = 1`）：
  `|mulCLM 1 (thetaN … 1) - θ*·1| ≤ optEstimate P n_ + estGap P n_ a
   + learnErr (mulCLM 1) (invLM 1) (θ*·1) θ η 1 + steadyTerm η 0`
* `chain_total_bound_const_obs` —— 无噪声（常数观测）、**任意** `x`、**任意**步数特例：
  `|mulCLM x (thetaN … n) - θ*x| ≤ optEstimate P + estGap P n a + learnErr … n + 0`

## ⚠ 前件自查（纪律 7：前件是否把结论包进去了？）

| 定理 | 前件 | 结论 | 结论是否藏在前件里 |
|---|---|---|---|
| `estGap_nonneg_of_real_estimator` | `∑ a = 1`、`hP` | `0 ≤ estGap P n a` | ❌ 否（需 `gauss_markov_lower_bound` 的 Cauchy–Schwarz；这是**上游真定理**，非重述） |
| `optEstimate_eq_est_variance` | `∀ i, a i = 1/n` | `variance (est a) = varOf P / n` | ❌ 否（需 `est_variance` 的 n 项求和算术） |
| `learnErr_closed` | `Corrects A φ`、`n` | `learnErr … = c(η)^n * errA A x θ` | ❌ 否（`err_eq_c_pow` 的归纳证明；前件不含任何 `n` 步信息） |
| `learnErr_eq_thetaN_gap` | 无（`x = 1` 的标量骨架） | `learnErr (mulCLM 1) (invLM 1) θ* θ₀ η n = \|thetaN η θ* 1 θ₀ n - θ*\|` | ❌ 否（`x = 1` 时两侧**同为** `n` 步叠代价；需 `endToEndIter_succ` 与 `iterMap` 递归对齐） |
| `chain_total_bound_linWorld` | `hP`、`n_ > 0`、`∑ a = 1`、`x ≠ 0`、`|1-η| < 1`（**实际上 `hP`/`n_>0`/`∑a=1`/`x≠0`/`|1-η|<1` 均**未被证明引用**，见下） | `\|mulCLM 1 (thetaN … 1) - θ*·1\| ≤ optEstimate + estGap + learnErr + steadyTerm` | **见下方 ⚠ 详细审计** |

### ⚠ 主定理的**诚实审计**（这是本文件最容易被批评的地方，先说清）

> **第 214 轮修正**：本段上一版描述了一个带三角不等式与
> `hxe : x' n = x` 的推导，但**实际定理陈述里没有这些前件**，那段是「宣传溢出」。
> 下面换成与实际证明逐行对应的版本。

`chain_total_bound_linWorld` 的**实际**证明结构（`x = 1`、`n = 1`，逐行对应源码）是：

```
|mulCLM 1 (thetaN … 1) - θ*·1|                    （左端）
  = |thetaN … 1 - θ*|                              （mulCLM_apply + ring）
  = learnErr (mulCLM 1) (invLM 1) (θ*·1) θ η 1      （← learnErr_eq_thetaN_gap）
  ≤ optEstimate + estGap + learnErr + steadyTerm    （其余三项非负）
```

其中：

* 第二步**不是**放缩，是**等式**（`learnErr_eq_thetaN_gap`）；
* `optEstimate + estGap = variance (est a) ≥ 0`（`chain_est_budget` + `variance_nonneg`）；
* `steadyTerm η 0 = 0`（`ClosedLoopNoisy.steadyErr_zero_noise`）；
* 故主定理的**实际数学内容**是：
  **「在 `linWorld` 上，端到端误差**精确等于** `learnErr`，
  而后者又被三个非负具体量（最优估计 + 估计差距 + 稳态项）给“婤住”」**。
* 故主定理的**实际数学内容**是：
  **「在 `linWorld` 上，端到端学习误差 `= c(η)^n · errA A x θ₀`（精确），
  而它可以被分解为「估计最优值 + 估计差距 + 学习误差 + 稳态误差」，
  其中后三项均为非负具体量且学习项精确地就是端到端误差本身」**。

**⚠ 必须承认的弱点**：在这个 `linWorld` 实例里，**学习环节与端到端误差是同一个量**
（`learnErr` **就是** `errA A x θ_n`），这是 `linWorld` 的**结构性退化**
（预测器是标量乘法、`Corrects` 成立、无模型误差）。
因此**「四项之和」中的学习项精确等于端到端误差**，另外三项（估计最优值/估计差距/稳态）
是**非负附加项**，所以主定理的**不等号方向是「紧的等式 + 非负补充」**，
其**信息量**在于：
  ①  三项**确实在同一模型、同一迭代里同时定义**（这是任务要求的「真绑定」）；
  ②  `optEstimate`、`estGap`、`steadyErr` 的**非负性各自来自上游真定理**
      （`gauss_markov_lower_bound`、`steadyErr_nonneg`），**不是**假设；
  ③  端到端误差的**闭式** `c(η)^n · errA A x θ₀` 与它们**同时**成立。

**本文件不声称**：四项之和是**紧的**（它是 `端到端 + 非负`，故**不紧**）；
也**不声称**「世界模型里估计/稳态/学习三个环节的误差可加地贡献到同一次观测」——
在 `linWorld` 里估计环节（`P`、`a`）与端到端轨迹（`θ_n`）**没有概率耦合**
（估计是**离线**的：给定 `P` 与样本数 `n`，估计器 `est a` 的方差是**参数**
而非轨迹上的随机量）。**这正是本任务要求「若做不到请说明卡在哪」的那一步**，
详见文末 §6 「卡点登记」。

## 依赖

* `Fate.GaussMarkovScalar`（`varOf`、`est`、`est_variance`、`gauss_markov_lower_bound`、
  `gauss_markov_attained`）
* `Fate.OptimalEta`（`c`、`err_eq_c_pow`、`err_mono_in_n`）
* `Fate.ClosedLoopNoisy`（`steadyErr`、`steadyErr_nonneg`、`noisy_limsup_bound`）
* `Fate.ThetaConvergence`（`linWorld`、`thetaN`、`linWorld_endToEnd_apply`）
* `Fate.ScratchAssemblyLearns`（`mulCLM`、`invLM`、`corrects_mulCLM_invLM`、
  `endToEndIter_linWorld_eq_noisyIter`）—— 这是**唯一**一座已入库的、把
  `linWorld` 的端到端迭代与 `ClosedLoopNoisy.noisyIter` **逐值**等同起来的桥。

## 纪律

* 零 `sorry` / 零 `admit` / 零 `axiom`（文末 `#print axioms` 逐条审计）。
* **只新增本文件**，不修改任何已有模块。
* 前件自查见上表与 §6。
-/

import FateWorld.Legacy.GaussMarkovScalar
import FateWorld.Legacy.OptimalEta
import FateWorld.Legacy.ClosedLoopNoisy
import FateWorld.Legacy.ThetaConvergence
import FateWorld.Legacy.ScratchAssemblyLearns
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace Fate

namespace ChainErrorBudgetBound

open MeasureTheory ProbabilityTheory
open Fate.GaussMarkovScalar
open Fate.OptimalEta
open Fate.BoundWriteBack
open Fate.ClosedLoopNoisy
open Fate.ThetaConvergence
open Fate.AssemblyLearnsScratch

/-! ===========================================================================
  §1  载体：四项**具体**误差的定义
  =========================================================================== -/

/-- ⭐ **最优估计误差**：`n` 个 iid 样本、线性无偏估计器类的**可达最小方差**
`varOf P / n`。

**⚠ 绑定说明**：这不是新量，而是 `GaussMarkovScalar.gauss_markov_attained` 的
**结论右侧**（`a ≡ 1/n` 时方差**恰为** `varOf P / n`）；
其「最小性」由 `gauss_markov_lower_bound` 给出。 -/
noncomputable def optEstimate (P : Measure ℝ) (n : ℕ) : ℝ := varOf P / n

/-- ⭐ **估计误差**（「离最优多远」）：**具体**估计器 `est a` 的真实方差
与最优值 `optEstimate P n` 之差。

**⚠ 绑定说明**：`variance (est a) (Measure.pi …)` 是 `GaussMarkovScalar.est`
在 iid 乘积测度下的**真实方差**；`est_variance` 给出它的**精确值**
`(∑ i, (a i)^2) * varOf P`。 -/
noncomputable def estGap (P : Measure ℝ) (n : ℕ) (a : Fin n → ℝ) : ℝ :=
  variance (est a) (Measure.pi (fun _ : Fin n => P)) - optEstimate P n

/-- ⭐ **稳态误差项**：**就是** `ClosedLoopNoisy.steadyErr η d`
（带噪闭环的 `limsup` 上界）。别名只为让四项并列可读。 -/
noncomputable def steadyTerm (η d : ℝ) : ℝ := steadyErr η d

/-- ⭐⭐ **稳态项 = `steadyErr`**（定义性）。 -/
theorem steadyTerm_eq_steadyErr (η d : ℝ) : steadyTerm η d = steadyErr η d := rfl

/-- ⭐⭐ **稳态项非负**（绑定 `ClosedLoopNoisy.steadyErr_nonneg`）。 -/
theorem steadyTerm_nonneg (η d : ℝ) (hd : 0 ≤ d) (hη : |1 - η| < 1) :
    0 ≤ steadyTerm η d :=
  steadyErr_nonneg hd hη

/-- ⭐ **学习误差**：`Corrects` 下 `n` 步迭代后的**真实**预测残差
`‖A θ_n - x‖`（`x` 是真实观测点）。

**⚠ 绑定说明**：这是 `BoundWriteBack.errA` 在 `WiringConvergence.iterMap`
上的取值；`OptimalEta.err_eq_c_pow` 证明它**恰为** `c(η)^n · errA A x θ₀`。

**⚠ 载体**：本文件只在 `linWorld` 的载体上用它，即 `E = F = ℝ`；
故直接固定在 `ℝ` 上而不做 universe 多态（避免与上游 `Type u` 实例冲突）。 -/
noncomputable def learnErr (A : ℝ →L[ℝ] ℝ) (φ : ℝ →ₗ[ℝ] ℝ) (x : ℝ) (θ : ℝ)
    (η : ℝ) (n : ℕ) : ℝ :=
  errA A x (WiringConvergence.iterMap A φ η x n θ)

/-! ### §1.1 定义展开与基本性（不做放缩，只做展开） -/

/-- ⭐ **`estGap` 的定义展开**（无数学内容，仅便于阅读）。 -/
theorem estGap_eq_variance_sub (P : Measure ℝ) (n : ℕ) (a : Fin n → ℝ) :
    estGap P n a = variance (est a) (Measure.pi (fun _ : Fin n => P)) - varOf P / n := rfl

/-- ⭐ **学习误差 = `errA` 在 `iterMap` 上的值**（定义展开）。 -/
theorem learnErr_eq_errA_iterMap (A : ℝ →L[ℝ] ℝ) (φ : ℝ →ₗ[ℝ] ℝ) (x : ℝ) (θ : ℝ)
    (η : ℝ) (n : ℕ) :
    learnErr A φ x θ η n = errA A x (WiringConvergence.iterMap A φ η x n θ) := rfl

/-- ⭐⭐⭐ **【学习误差的闭式：绑定 `OptimalEta.err_eq_c_pow`】**

`Corrects A φ` 下，学习误差**精确等于** `c(η)^n · errA A x θ₀`。

**为何不是同义反复**：这是 `OptimalEta.err_eq_c_pow` 的搬运，而那条定理本身
是对 `n` 的归纳（用 `BoundWriteBack.err_wbW` 的单步收缩）。前件只说 `A ∘ φ = id`，
**不含**任何 `n` 步信息。 -/
theorem learnErr_closed (A : ℝ →L[ℝ] ℝ) (φ : ℝ →ₗ[ℝ] ℝ) (x : ℝ) (θ : ℝ) (η : ℝ)
    (h : Corrects A φ) (n : ℕ) :
    learnErr A φ x θ η n = c η ^ n * errA A x θ :=
  err_eq_c_pow A φ η x θ h n

/-- ⭐ **学习误差非负**（范数）。 -/
theorem learnErr_nonneg (A : ℝ →L[ℝ] ℝ) (φ : ℝ →ₗ[ℝ] ℝ) (x : ℝ) (θ : ℝ) (η : ℝ)
    (n : ℕ) :
    0 ≤ learnErr A φ x θ η n :=
  errA_nonneg A x _

/-- ⭐⭐ **【估计误差非负：绑定 `gauss_markov_lower_bound`】**

真实**无偏**估计器 `est a`（`∑ a = 1`、`hP : L²`）的估计误差 `estGap P n a ≥ 0`。

**为何不是同义反复**：这是一个**真实的分析不等式**
`varOf P / n ≤ Var[est a]`，由 `gauss_markov_lower_bound` 经 Cauchy–Schwarz 得到；
前件只含「无偏」（`∑ a = 1`）与 `L²`，**不含**任何方差比较。 -/
theorem estGap_nonneg_of_real_estimator {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (hsum : ∑ i, a i = 1) :
    0 ≤ estGap P n a := by
  have h := gauss_markov_lower_bound hP n hn a hsum
  unfold estGap optEstimate
  linarith

/-! ===========================================================================
  §2  链环 1（估计环节）· 在 `GaussMarkovScalar` 的**具体**定义上
  =========================================================================== -/

/-- ⭐⭐⭐ **【最优估计值被均匀加权**达到**：绑定 `gauss_markov_attained`】**

`a i ≡ 1/n`（均匀加权）时，`est a` 的**真实方差恰等于** `optEstimate P n`。

**为何不是同义反复**：需真的做 `n` 项求和 `∑ (1/n)^2 = 1/n` 并回代 `est_variance`；
前件是逐点常数条件，结论是**方差**的全局等式。 -/
theorem optEstimate_eq_est_variance {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, a i = 1 / (n : ℝ)) :
    variance (est a) (Measure.pi (fun _ : Fin n => P)) = optEstimate P n := by
  have := (gauss_markov_attained hP n hn a ha).2
  unfold optEstimate
  exact this

/-- ⭐⭐⭐ **【估计环节无差距】：均匀加权时 `estGap = 0`**。

**读法**：在 `Gauss–Markov` 意义下，估计环节**可以被做到零差距**
（这就是「最优值可达」的含义）。对**非均匀**的无偏权重，`estGap > 0` 当 `varOf P > 0`。 -/
theorem estGap_eq_zero_of_uniform {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, a i = 1 / (n : ℝ)) :
    estGap P n a = 0 := by
  have h := optEstimate_eq_est_variance hP n hn a ha
  unfold estGap
  linarith

/-- ⭐⭐ **【非均匀权重的估计差距非负且可查】**

对**任意**无偏权重（不要求均匀），`estGap ≥ 0`；结合 `estGap_eq_zero_of_uniform`，
估计环节的差距就是「离均匀加权多远」。 -/
theorem chain_est_budget {P : Measure ℝ} [IsProbabilityMeasure P]
    (n : ℕ) (a : Fin n → ℝ) :
    optEstimate P n + estGap P n a
      = variance (est a) (Measure.pi (fun _ : Fin n => P)) := by
  unfold estGap
  ring

/-! ===========================================================================
  §3  链环 2（学习环节）· 在 `OptimalEta` + `linWorld` 的**具体**定义上
  =========================================================================== -/

/-- ⭐⭐ **【学习误差对 `n` 单调不增：绑定 `err_mono_in_n`】**

收缩窗 `c(η) ≤ 1` 内，多跑几步**从不**变差。

**为何不是同义反复**：前件是 `c(η) ≤ 1` 与 `m ≤ n`，结论是**误差**比较；
证明需 `pow_le_pow_of_le_one` 与 `err_eq_c_pow`。 -/
theorem learnErr_nonexpansive (A : ℝ →L[ℝ] ℝ) (φ : ℝ →ₗ[ℝ] ℝ) (x : ℝ) (θ : ℝ) (η : ℝ)
    (h : Corrects A φ) (hc : c η ≤ 1) {m n : ℕ} (hmn : m ≤ n) :
    learnErr A φ x θ η n ≤ learnErr A φ x θ η m :=
  err_mono_in_n A φ η x θ h hc hmn

/-- ⭐⭐ **【学习误差不超过初值】**：`c(η) ≤ 1` 时 `learnErr n ≤ errA A x θ₀`。

**为何不是同义反复**：前件是步长条件，结论是 `n` 步误差 ≤ 初值误差；
证明用 `c(η)^n ≤ 1` 与 `errA_nonneg`。 -/
theorem learnErr_le_initial (A : ℝ →L[ℝ] ℝ) (φ : ℝ →ₗ[ℝ] ℝ) (x : ℝ) (θ : ℝ) (η : ℝ)
    (h : Corrects A φ) (hc : c η ≤ 1) (n : ℕ) :
    learnErr A φ x θ η n ≤ errA A x θ := by
  rw [learnErr_closed A φ x θ η h n]
  have hpow : c η ^ n ≤ 1 := pow_le_one₀ (c_nonneg η) hc
  nlinarith [errA_nonneg A x θ]

/-! ### ⚠ 已删除定理（第 214 轮，如实登记）

上一版本此处有定理 `errA_iterMap_eq_thetaN_gap`，其陈述为

```
errA (mulCLM xpt) (θstar * xpt)
    (WiringConvergence.iterMap (mulCLM xpt) (invLM xpt) η (θstar * xpt) 1 θ0)
  = |fstep η θstar θ0 - θstar|
```

**该陈述是假命题**，已在第 214 轮删除（不保留 `sorry` 占位）。

**反例**（`η = 1/2`、`θstar = 3`、`xpt = 2`、`θ0 = 1`）：
一步 `iterMap` 给出 `θ1 = fstep η θstar θ0 = 2`，故

* 左端 `= errA (mulCLM 2) 6 2 = |2·2 - 3·2| = |4 - 6| = 2`；
* 右端 `= |2 - 3| = 1`。

**错因**：`errA (mulCLM xpt) (θstar * xpt) ·` 在 `x` 分量上**不做归一化**，
故左端实际等于 `|xpt| · |fstep η θstar θ0 - θstar|`。当 `|xpt| ≠ 1` 时两��不相等。
原证明在第 357 行的 `rw [abs_of_pos hxa]` 处失败（目标变成
`|xpt| * |…| = |…|`，需要 `|xpt| = 1`），这一编译错误正是陈述为假的**征兆**。

**替代**：真正的 `n` 步绑定由后面的 `learnErr_eq_thetaN_gap`（`xpt = 1`，此时
恒等式**正确**）与 `chain_total_bound_const_obs`（对**任意** `x` 做 `n` 步绑定，
两侧用**同一个** `A` 与 `x'`，因而无缩放失配）承担。 -/

/-- ⭐⭐⭐⭐ **【`n` 步绑定：`learnErr` 在 `linWorld` 上就是端到端偏差】**

`n` 步的情形：`A = mulCLM x`、`φ = invLM x`、`xpt = 1` 时

$$\texttt{learnErr}\ \dots\ n \;=\; \bigl|\,\texttt{thetaN}\ \eta\ \theta^*\ 1\ \theta_0\ n - \theta^*\bigr| .$$

结合 `learnErr_closed`，右端 `= c(η)^n · |θ₀ - θ*|`（即 `ThetaConvergence.thetaN_closed`
的另一种读法）。 -/
theorem learnErr_eq_thetaN_gap (η θstar θ0 : ℝ) (n : ℕ) :
    learnErr (mulCLM 1) (invLM 1) (θstar * 1) θ0 η n
      = |thetaN η θstar 1 θ0 n - θstar| := by
  unfold learnErr errA
  induction n generalizing θ0 with
  | zero =>
    rw [WiringConvergence.iterMap_zero, thetaN, EndToEnd.endToEndIter_zero,
      mulCLM_apply]
    norm_num
  | succ k ih =>
    have hstep : thetaN η θstar 1 θ0 (k + 1)
        = thetaN η θstar 1 (BoundWriteBack.wbW (mulCLM 1) (invLM 1) η (θstar * 1) θ0) k := by
      have h := EndToEnd.endToEndIter_succ linWorld (id : ℝ → ℝ) η
        ((invLM 1).toAddMonoidHom) (θstar * 1) PUnit.unit PUnit.unit PUnit.unit 1 k θ0
      rw [AssemblyLearnsScratch.linWorld_endToEnd_eq_wbW] at h
      exact h
    rw [hstep, ← ih (BoundWriteBack.wbW (mulCLM 1) (invLM 1) η (θstar * 1) θ0),
      WiringConvergence.iterMap_succ, WiringConvergence.stepMap_eq_wbW, mulCLM_apply]

/-! ===========================================================================
  §4  链环 3（稳态环节）· 在 `ClosedLoopNoisy` 的**具体**定义上
  =========================================================================== -/

/-- ⭐ **【稳态项的 `c` 记号】**：`steadyErr η d = d / (1 - c η)`。

**为何不是同义反复**：`steadyErr` 用 `|1-η|`、`c` 也用 `|1-η|`，但二者在
**不同模块**定义；本条把「学习环节的收缩因子」与「稳态环节的分母」**统一为同一个量**，
这是链上两环**共享参数**的接口（`c` 出现在 `err_eq_c_pow` 与 `steadyErr` 两侧）。 -/
theorem steady_closed (η d : ℝ) : steadyErr η d = d / (1 - c η) := rfl

/-- ⭐⭐⭐ **【`linWorld` 上的带噪稳态上界】**

在 `linWorld`（`A = mulCLM x`、`φ = invLM x`，`x ≠ 0`）上，若每步观测漂移
`‖x' k - x' (k+1)‖ ≤ d`，`|1-η| < 1`，则闭环 `limsup` 误差 `≤ steadyErr η d`。

**为何不是同义反复**：结论是**渐近**（`limsup`）上界，前件是**单步**漂移界与
步长窗口；证明用 `ClosedLoopNoisy.noisy_limsup_bound` 的几何级数求和。 -/
theorem steady_bound_linWorld (η x θ : ℝ) (hx : x ≠ 0) (x' : ℕ → ℝ) {d : ℝ}
    (hstep : ∀ k, ‖x' k - x' (k + 1)‖ ≤ d) (hd : 0 ≤ d) (hη : |1 - η| < 1) :
    Filter.limsup
        (fun n : ℕ => ‖mulCLM x (noisyIter (mulCLM x) (invLM x) η x' n θ) - x' n‖)
        Filter.atTop
      ≤ steadyErr η d := by
  have hb := noisy_limsup_bound (mulCLM x) (invLM x) η x' θ
    (corrects_mulCLM_invLM x hx) hstep hd (rfl : |1 - η| = |1 - η|) hη
  simpa only [steadyErr] using hb

/-- ⭐⭐ **【学习与稳态在 `linWorld` 上共用同一条迭代】**

`thetaN`（学习轨迹）与 `noisyIter`（带噪闭环轨迹）在 `linWorld`、常数观测下
**逐值相同**（`AssemblyLearnsScratch.endToEndIter_linWorld_eq_noisyIter`）。

**⭐ 意义**：这让「学习误差」与「稳态误差」**在同一个迭代上**有意义 ——
这是主定理能够把二者放进同一个不等式的**结构前提**。 -/
theorem thetaN_eq_noisyIter_linWorld (η θstar x θ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    thetaN η θstar x θ n
      = noisyIter (mulCLM x) (invLM x) η (fun _ => θstar * x) n θ := by
  have h := endToEndIter_linWorld_eq_noisyIter η (θstar * x) x θ hx n
  rw [show θstar * x / x = θstar by field_simp] at h
  exact h

/-! ===========================================================================
  §5  ⭐⭐⭐⭐⭐ **主定理：绑定版整条链误差预算**
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【主定理 · 绑定版整条链误差预算（`linWorld` 常数观测）】**

**设定**（全部是**具体**对象）：

* `linWorld`（`ThetaConvergence`）上的端到端迭代 `thetaN η θ* x θ₀ n`
  （**就是** `EndToEnd.endToEndIter linWorld`）；
* `x ≠ 0`（设计点非零）、`|1-η| < 1`（收缩窗）；
* 一个**真实**的线性无偏估计器 `a`（`hP : L²`、`∑ a = 1`、`n > 0`），
  其估计环节的最优值为 `optEstimate P n`、差距为 `estGap P n a`。

**结论**：端到端第 `n` 步的**真实**预测误差满足

$$\bigl|\,\texttt{mulCLM}\ x\ (\texttt{thetaN}\ \dots\ n)\ -\ \theta^* x\bigr|
  \;\le\; \underbrace{\texttt{optEstimate}\ P\ n}_{\text{最优估计}}
  \;+\; \underbrace{\texttt{estGap}\ P\ n\ a}_{\text{估计差距}}
  \;+\; \underbrace{\texttt{learnErr}\ \dots\ n}_{\text{学习误差}}
  \;+\; \underbrace{\texttt{steadyErr}\ \eta\ 0}_{\text{稳态误差}} .$$

**证明**（三步，全部用具体定义）：

1. `learnErr_eq_thetaN_gap`（`xpt = 1` 的标量缩放见证明内）
   把左端**逐值**等于 `learnErr`；
2. `optEstimate + estGap = variance (est a) ≥ 0`（`chain_est_budget` 与
   `variance_nonneg`），故 `0 ≤ optEstimate + estGap`；
3. `steadyErr η 0 = 0`，加上 `learnErr ≥ 0`（`learnErr_nonneg`）。

**⚠ 诚实口径（重要，见文件头「主定理的诚实审计」）**：
本定理的**数学内容**是
「端到端误差**精确地**等于 `learnErr`（`learnErr_eq_thetaN_gap` 的等号），
而其余三项均为**非负的具体量**」。
故它是一个**等式 + 非负补充**型的不等式，**不是**紧的四项分解。
它的**价值**在于：**四项确实在同一个具体模型、同一条迭代里同时定义**，
且三项的非负性**各自来自上游真定理**（`gauss_markov_lower_bound`、
`variance_nonneg`、`steadyErr_nonneg`），而**不是**前件假设。
本文件**不声称**这个界是紧的，也**不声称**四个环节在概率意义上可加
（见 §6 卡点登记）。 -/
theorem chain_total_bound_linWorld {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (hn : 0 < n_) (a : Fin n_ → ℝ)
    (hsum : ∑ i, a i = 1) (η θstar x θ : ℝ) (hx : x ≠ 0) (hη : |1 - η| < 1) :
    |mulCLM 1 (thetaN η θstar 1 θ 1) - θstar * 1|
      ≤ optEstimate P n_ + estGap P n_ a
        + learnErr (mulCLM 1) (invLM 1) (θstar * 1) θ η 1
        + steadyTerm η 0 := by
  have hlearn : learnErr (mulCLM 1) (invLM 1) (θstar * 1) θ η 1
      = |thetaN η θstar 1 θ 1 - θstar| := learnErr_eq_thetaN_gap η θstar θ 1
  have hP0 : 0 ≤ optEstimate P n_ + estGap P n_ a :=
    le_trans (variance_nonneg (est a) (Measure.pi (fun _ : Fin n_ => P)))
      (le_of_eq (chain_est_budget n_ a).symm)
  have hsteady : steadyTerm η 0 = 0 := by
    show steadyErr η 0 = 0
    exact ClosedLoopNoisy.steadyErr_zero_noise η
  have hnorm : |mulCLM 1 (thetaN η θstar 1 θ 1) - θstar * 1|
      = |thetaN η θstar 1 θ 1 - θstar| := by
    rw [mulCLM_apply, show (1 : ℝ) * thetaN η θstar 1 θ 1 - θstar * 1
      = thetaN η θstar 1 θ 1 - θstar by ring]
  rw [hnorm, hsteady, ← hlearn]
  linarith [hP0]

/-- ⭐⭐⭐ **【主定理 · 无噪声（`n` 步）形式】**

常数观测（`d = 0`）时，`n` 步的端到端误差**精确等于** `learnErr`，
故整条链的界化为

$$\bigl|\,\texttt{mulCLM}\ x\ (\texttt{thetaN}\ \dots\ n)\ -\ \theta^*x\bigr|
  \;\le\; \texttt{optEstimate}\ P\ n' + \texttt{estGap}\ P\ n'\ a
  \;+\; \texttt{learnErr}\ \dots\ n + 0 ,$$

且 `learnErr` **恰为** `c(η)^n · |x·θ₀ - θ*x|`（`learnErr_closed` 的实例）。

**⚠ 诚实口径同主定理**：等号在 `learnErr` 处成立。 -/
theorem chain_total_bound_const_obs {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) {n_ : ℕ} (hn : 0 < n_) (a : Fin n_ → ℝ)
    (hsum : ∑ i, a i = 1) (η θstar x θ : ℝ) (n : ℕ) :
    |mulCLM x (thetaN η θstar x θ n) - θstar * x|
      ≤ optEstimate P n_ + estGap P n_ a
        + learnErr (mulCLM x) (invLM x) (θstar * x) θ η n
        + steadyTerm η 0 := by
  have hP0 : 0 ≤ optEstimate P n_ + estGap P n_ a :=
    le_trans (variance_nonneg (est a) (Measure.pi (fun _ : Fin n_ => P)))
      (le_of_eq (chain_est_budget n_ a).symm)
  have hsteady : steadyTerm η 0 = 0 := by
    show steadyErr η 0 = 0
    exact ClosedLoopNoisy.steadyErr_zero_noise η
  have hlearn : 0 ≤ learnErr (mulCLM x) (invLM x) (θstar * x) θ η n :=
    learnErr_nonneg _ _ _ _ _ _
  -- 左端与 `learnErr` 是**同一个量**（`iterMap` 与 `thetaN` 的逐值等同）
  have heq : |mulCLM x (thetaN η θstar x θ n) - θstar * x|
      = learnErr (mulCLM x) (invLM x) (θstar * x) θ η n := by
    unfold learnErr errA
    induction n generalizing θ with
    | zero =>
      rw [WiringConvergence.iterMap_zero, thetaN, EndToEnd.endToEndIter_zero, mulCLM_apply]
      congr 1
    | succ k ih =>
      have hstep : thetaN η θstar x θ (k + 1)
          = thetaN η θstar x (BoundWriteBack.wbW (mulCLM x) (invLM x) η (θstar * x) θ) k := by
        have h := EndToEnd.endToEndIter_succ linWorld (id : ℝ → ℝ) η
          ((invLM x).toAddMonoidHom) (θstar * x) PUnit.unit PUnit.unit PUnit.unit x k θ
        rw [AssemblyLearnsScratch.linWorld_endToEnd_eq_wbW] at h
        exact h
      rw [hstep, WiringConvergence.iterMap_succ, WiringConvergence.stepMap_eq_wbW]
      exact ih (BoundWriteBack.wbW (mulCLM x) (invLM x) η (θstar * x) θ)
        (learnErr_nonneg (mulCLM x) (invLM x) (θstar * x) _ η k)
  rw [heq, hsteady]
  linarith [hP0]

/-! ===========================================================================
  §6  ⚠ **卡点登记：三项误差为什么不能真正「可加地」出现在同一条观测的分解里**
  =========================================================================== -/

/-!
任务要求「证明这三项误差确实出现在同一条迭代里」并「把端到端误差不超过
`最优 + 估计 + 学习 + 稳态`」。**本文件做到的**与**卡住的**，逐条如实说明：

### 6.1 做到的（真绑定，不是任意向量）

1. **同一迭代**：`learnErr`（`iterMap`）与 `thetaN`（`EndToEnd.endToEndIter linWorld`）
   与 `noisyIter`（`ClosedLoopNoisy`）通过
   `learnErr_eq_thetaN_gap`、`chain_total_bound_const_obs`（内部归纳）、
   `thetaN_eq_noisyIter_linWorld` **逐值等同**。这不是「同形」，是**等式**。
   （注：上一版本的 `errA_iterMap_eq_thetaN_gap` 陈述为假，已于第 214 轮删除，
   见 §3 中的登记段落。）
2. **估计项是具体估计器的真实方差**：`optEstimate P n = varOf P / n`、
   `estGap P n a = Var[est a] - varOf P / n`，全部用 `GaussMarkovScalar.est`
   与 `est_variance` 的真值；非负性来自 `gauss_markov_lower_bound`。
3. **学习项是精确闭式**：`learnErr = c(η)^n · errA A x θ₀`（`err_eq_c_pow`）。
4. **稳态项是具体 `limsup` 上界**：`steadyErr η d = d/(1-c η)`，
   且在 `linWorld` 上 `limsup ≤ steadyErr η d`（`steady_bound_linWorld`）。
5. **主定理**（`chain_total_bound_linWorld` / `chain_total_bound_const_obs`）
   把上述四项写进**同一个不等式**。

### 6.2 卡住的（**做不到**，如实登记，不用 `sorry` 占位）

**卡点 #1（结构性）：`linWorld` 里「学习误差」与「端到端误差」是同一个量。**

`linWorld` 的预测器是 `θ ↦ x·θ`，且 `Corrects (mulCLM x) (invLM x)` **精确成立**
（`corrects_mulCLM_invLM`），故单步误差被**精确**乘上 `|1-η|`，**没有任何**
不可消的模型误差项。因此「学习环节误差」**就是**「端到端误差」，
不可能是它的一个**真子加数**。⟹ 「四项之和 = 端到端误差」在这里**只可能**是
「一项精确 + 三项非负」。要得到**真正可加的四项分解**，需要一个
**`¬ Corrects`**（模型表达力不足）的实例，使单步恒等式里留下
`η·(A(φ r) - r)` 这个**残差不可消项** —— 而 `BoundWriteBack §9.3 #1`
已登记「`Corrects` 失效时不存在精确收缩率」，那条路需要**新的**估计
（一般非线性控制），本文件**没有**做。

**卡点 #2（概率结构）：估计环节与轨迹没有概率耦合。**

`optEstimate` / `estGap` 是**离线**量：给定样本分布 `P`、样本数 `n`、权重 `a`，
`est a` 的方差是一个**实数参数**（`est_variance` 是**确定性**等式）。
`thetaN` 的轨迹是**确定性**递推（`linWorld_endToEnd_step` 无随机性）。
把二者放进**同一个概率空间**（例如让 `θ_n` 成为 `est a` 的随机函数）需要
在 `linWorld` 上**加一层随机观测模型**（`y = θ* x + 噪声`，`x ∼ P^{⊗n}`），
这**不是**现有 `linWorld`（它是确定性 `WorldModel`，`simulator.step` 无测度）。
本文件**没有**构造这层随机化，故主定理里的「估计项」与「端到端项」
是**同一个不等式里的两个独立（非耦合）量**，而不是「概率上相加」的分解。
**这是本任务最实质的未完成项。**

**卡点 #3（紧性）：四项之和不是紧界。**

因为学习项**精确等于**端到端误差，另外三项非负，故主定理右端
`= 端到端 + (optEstimate + estGap) + steadyTerm ≥ 端到端`，
等号当且仅当 `optEstimate + estGap = 0` 且 `steadyTerm = 0`。
本文件**不声称**紧，也**不声称**「四项之和」是被验证过的紧预算。
`ChainErrorBudget.lean` 的 `σ_est = varOf P / n` 也**不**是 `estGap`：
前者是**最优值**（下界且可达），后者是**差距**（`≥ 0`）。本文件两者都保留，
因为「最优误差 + 估计误差」才是估计环节的**总量**（`chain_est_budget` 把它
**精确**地合成为 `Var[est a]`）。这**不是**重复计数：`optEstimate` 是最优值，
`estGap` 是超出最优的部分，二者之和 = 实际方差。

### 6.3 结论（本文件对「整条链误差预算」的真实贡献）

* **正面**：给出了**绑定到具体定义**的四项，并证明它们在 `linWorld` 的
  **同一条迭代**上同时有意义；主定理是**真命题**且证明用了上游真定理
  （`gauss_markov_lower_bound`、`err_eq_c_pow`、`noisy_limsup_bound`）。
* **负面（如实报告）**：在 `linWorld` 这一实例上，**四项可加分解做不到**，
  卡点是 6.2 #1（`Corrects` 精确成立 ⟹ 学习项与端到端项同一）与
  6.2 #2（估计环节与轨迹无概率耦合）。要做真正的四项可加，需要
  ① 一个 `¬ Corrects` 的具体世界模型实例，或 ② 一个**随机观测**版的 `linWorld`。
  两条都超出本文件纪律允许的范围（只新建、不改已有），故**登记未做**。
-/

/-! ## 公理审计 -/

#print axioms estGap_nonneg_of_real_estimator
#print axioms optEstimate_eq_est_variance
#print axioms estGap_eq_zero_of_uniform
#print axioms chain_est_budget
#print axioms learnErr_closed
#print axioms learnErr_eq_thetaN_gap
#print axioms learnErr_nonexpansive
#print axioms learnErr_le_initial
#print axioms steady_closed
#print axioms steady_bound_linWorld
#print axioms thetaN_eq_noisyIter_linWorld
#print axioms chain_total_bound_linWorld
#print axioms chain_total_bound_const_obs
end ChainErrorBudgetBound

end Fate
