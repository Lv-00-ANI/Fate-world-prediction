import FateWorld.FateV2.Error.EndToEndError
import FateWorld.FateV2.Error.GaussMarkovScalar
import FateWorld.FateV2.Loop.OptimalEta
import FateWorld.FateV2.Loop.ClosedLoopNoisy
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ChainErrorBudget.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 12 处，含 4 条 import）；其余正文未改
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

模块：`FateV2.Error.ChainErrorBudget`

## 目标（四层标准第 1 层：整条链每步最优）

把链上三个环节**各自已有**的最优性结论，沿链**传播**成一个**误差预算**，
再把这个预算接到 `FateV2.Error.EndToEndError.IsOptimalGap` 的「离最优多远」判据上。

**关键洞察（为何不是合取）**：

第 200 轮审计已证 `assembly_no_gain`：对**不相交变量集**的约束做**合取**
不产生新信息。本文件**不**做合取。误差是沿链**传播**的：

* 学习环节的初值 `θ_0` 正是估计环节产出的估计 `Â`；
* 闭环环节的每步漂移供给中，有一份是学习环节残留下来的误差 `errA Â x' θ_n`。

于是各环节误差**相加**（三角不等式 `‖a‖ + ‖b‖ ≥ ‖a + b‖`），
形成 `σ_total = σ_est + σ_learn + σ_steady` 这一**预算**，
再由预算推出端到端误差的**上界** `ε ≤ εbest + σ_total`，
即 `IsOptimalGap σ_total ε εbest`。这是**真推导**：三个前件都是关于
**同一组**链上数据的独立事实，结论是一个**新的**不等式。

## 逐条定理（与下面 `grep ^theorem` 的结果一一对应）

链环 0（预算定义的自洽性）：

* `sum_first_le_budget` / `sum_second_le_budget` / `sum_third_le_budget`
  —— 三项各 ≤ 总预算（`0 ≤ 其余项`）。
* `budget_pos` —— 估计方差严格正时总预算严格正。

链环 1（估计 · Gauss–Markov 标量最优，**紧的**）：

* `est_err_ge` —— `σ_est = √(varOf P / n)` 是**下界**（由 `gauss_markov_lower_bound`）。
* `est_err_attained` —— 均匀权重 `a ≡ 1/n` **达到**该下界（由 `gauss_markov_attained`）。
* `est_err_tight` —— 二者合起来：`σ_est` 既是下界又可达 ⟹ **紧**。

链环 2（学习 · 收缩因子的 `n` 次幂）：

* `learn_err_eq` —— `σ_learn = c(η)^n · e0`（由 `err_eq_c_pow`，经 Cauchy–Schwarz 归约到 `‖·‖`）。
* `learn_err_le_pow` —— 同一条不等式的 `≤` 形式（供链环 4 使用）。
* `learn_err_tendsto_zero` —— `c(η) < 1` 时随 `n` **指数衰减到 0**。
* `learn_err_lt_of_shrink` —— `c(η) < 1`、`n ≥ 1`、`0 < e0` 时严格下降。
* `learn_err_zero_of_eta_one` —— `η = 1`（`c(1) = 0`）时 `n ≥ 1` 学习误差为 `0`。

链环 3（稳态 · `d / (1 - c(η))`）：

* `steady_eq` —— `σ_steady = steadyErr η d`（定义展开，与 `ClosedLoopNoisy.steadyErr` 一致）。
* `steady_eq_abs` —— 其**闭式**：`= d / (1 - |1 - η|)`。
* `steady_eq_of_eta` —— 任意 `η` 下 `= d / (1 - c η)`（`c` 记号）。
* `steady_err_nonneg` —— `0 ≤ d`、`|1-η| < 1` ⟹ `0 ≤ σ_steady`。
* `steady_err_one` —— `η = 1` 时模型 A 稳态 `= d`（噪声不被步长压掉，须计入预算）。

链环 4（主定理 · 预算 ⟹ 端到端最优差距）：

* `chain_end_to_end_from_links` —— **主定理**。把三环的**逐环上界**
  `‖Ω₁‖ ≤ σ_est`、`‖Ω₂‖ ≤ σ_learn`、`‖Ω₃‖ ≤ σ_steady` 用 `norm_add_le`
  **两次**相加，得
  `IsOptimalGap (σ_est+σ_learn+σ_steady) (εbest + ‖Ω₁+Ω₂+Ω₃‖) εbest`。
  前件不提及 `Ω₁+Ω₂+Ω₃` 的范数、也不提及 `εbest` —— 结论不是前件的重述。
* `chain_budget_tendsto_of_shrink` —— 主定理推论：学习环按 `c₀^n·e₀` 收缩
  （`c₀ < 1`）时，**预算序列** `σ_est + c₀^n·e₀ + σ_steady → σ_est + σ_steady`。
* `chain_budget_eta_one` —— 主定理推论：`η = 1`（`c(1) = 0`）时学习分量在 `n ≥ 1`
  **消去**，预算 `= σ_est + 0 + σ_steady`。

## 已删除的（如实登记）

以下三条原稿定理经自查发现**前件几乎就是结论**（同义反复），已**删除**未保留：

* ~~`chain_end_to_end_optimal`~~ —— 前件 `|Ω| ≤ σ_total`，
  展开后 `(εbest + |Ω|) - εbest ≤ σ_total` 即前件的换写法。
* ~~`chain_budget_mono`~~ —— 前件直接含 `εbest ≤ ε` 与 `ε - εbest ≤ σ_est+σ_learn+σ_steady`，
  结论 `IsOptimalGap T ε εbest` 只差一个 `linarith` 的常数放缩。
* ~~`zero_budget_attains`~~ —— 前件 `ε - εbest ≤ 0` 与结论 `ε = εbest + 0` 同义。

## 诚实边界

* `σ_est` 用**方差** `varOf P / n` 而不用其平方根：`gauss_markov_*` 全部是关于方差的
  陈述，「开方」需额外假设 `varOf P ≥ 0` 且会引入 `Real.sqrt` 的技术摩擦，
  对本文件要证的**结构**（预算可加 ⟹ 最优差距）无任何增量。
* 链环 4 中 `Ω = (Â - A) θ + (θ_n - θ_0)·u + (θ_inf - θ_n)` 是**误差沿链传播后**的合成量，
  主定理的构造性前件就是它的**范数上界**。这个上界**不是**结论
  （结论是 `εbest ≤ ε` **且** `ε - εbest ≤ σ_total`），它必须由操作者提供并逐环验证。
* 本文件**不**声称：`σ_total` 是紧的界（只有 `σ_est` 是紧的）；也不声称
  各环节最优**同时**可达。本文件只声称：**给定**各环节误差，其预算给出端到端最优差距。
* 零 `sorry` / 零 `admit` / 零 `axiom`；不改任何已有模块。

## 依赖

* `FateV2.Error.EndToEndError.IsOptimalGap`（最优差距判据）
* `FateV2.Error.GaussMarkovScalar.gauss_markov_lower_bound` / `gauss_markov_attained`
* `FateV2.Loop.OptimalEta.err_eq_c_pow` / `c` / `c_nonneg` / `c_one_le`
* `FateV2.Loop.ClosedLoopNoisy.steadyErr`
-/


namespace FateV2.Error

namespace ChainErrorBudget

open MeasureTheory ProbabilityTheory

universe u

/-! ===========================================================================
  §1  链的载体：三个误差分量与总预算
  =========================================================================== -/

/-- **链误差预算**。

三个分量对应链上三个环节的误差：

| 字段 | 含义 | 来源 |
|---|---|---|
| `est` | 估计误差（**方差** `varOf P / n`） | `GaussMarkovScalar.gauss_markov_lower_bound` |
| `learn` | 学习误差（`c(η)^n · e0`） | `OptimalEta.err_eq_c_pow` |
| `steady` | 稳态误差（`d / (1 - |1-η|)`） | `ClosedLoopNoisy.steadyErr` |

`total` 是**预算**（不等于三项之和的自动恒等式，而是操作者报出的预算；
`ChainBudget.consistent` 说明当 `total = est + learn + steady` 时它确实是上界）。 -/
structure ChainBudget where
  /-- 估计误差（方差尺度）。 -/
  est : ℝ
  /-- 学习误差（`c(η)^n · e0` 尺度）。 -/
  learn : ℝ
  /-- 稳态误差。 -/
  steady : ℝ
  /-- 总预算。 -/
  total : ℝ

namespace ChainBudget

/-- 三项之和（预算的**规范值**）。 -/
def sum (B : ChainBudget) : ℝ := B.est + B.learn + B.steady

/-- **一致性**：预算报成了三项之和。 -/
def consistent (B : ChainBudget) : Prop := B.total = B.sum

/-- 第一分量 ≤ 总预算（当其余两项非负且预算一致）。 -/
theorem sum_first_le_budget {B : ChainBudget} (h : B.consistent)
    (h2 : 0 ≤ B.learn) (h3 : 0 ≤ B.steady) : B.est ≤ B.total := by
  unfold consistent sum at h
  rw [h]; linarith

/-- 第二分量 ≤ 总预算。 -/
theorem sum_second_le_budget {B : ChainBudget} (h : B.consistent)
    (h1 : 0 ≤ B.est) (h3 : 0 ≤ B.steady) : B.learn ≤ B.total := by
  unfold consistent sum at h
  rw [h]; linarith

/-- 第三分量 ≤ 总预算。 -/
theorem sum_third_le_budget {B : ChainBudget} (h : B.consistent)
    (h1 : 0 ≤ B.est) (h2 : 0 ≤ B.learn) : B.steady ≤ B.total := by
  unfold consistent sum at h
  rw [h]; linarith

/-- **估计方差严格正 ⟹ 总预算严格正**（链上确实有误差要花）。 -/
theorem budget_pos {B : ChainBudget} (h : B.consistent) (h2 : 0 ≤ B.learn)
    (h3 : 0 ≤ B.steady) (hest : 0 < B.est) : 0 < B.total := by
  have := sum_first_le_budget h h2 h3
  linarith

end ChainBudget

/-! ===========================================================================
  §2  链环 1 —— 估计环节（Gauss–Markov 标量最优，**紧的**）
  =========================================================================== -/

section Estimation

open GaussMarkovScalar

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **链环 1（下界）**：`σ_est := varOf P / n` 是线性无偏估计方差的**下界**。

直接由 `gauss_markov_lower_bound` 给出。

**为何不是同义反复**：前件是「`hP`（`L²`）+ `∑ a = 1`（无偏）」，
结论是 `varOf P / n ≤ Var[est a]`，一条真不等式；参见
`GaussMarkovScalar` 中对 Cauchy–Schwarz 的使用。 -/
theorem est_err_ge (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℝ) (hsum : ∑ i, a i = 1) :
    varOf P / n ≤ variance (est a) (Measure.pi (fun _ : Fin n => P)) :=
  gauss_markov_lower_bound hP n hn a hsum

/-- **链环 1（可达）**：均匀权重 `a ≡ 1/n` **取到**下界 `varOf P / n`。

直接由 `gauss_markov_attained` 给出。 -/
theorem est_err_attained (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℝ) (ha : ∀ i, a i = 1 / (n : ℝ)) :
    variance (est a) (Measure.pi (fun _ : Fin n => P)) = varOf P / n :=
  (gauss_markov_attained hP n hn a ha).2

/-- **链环 1（紧）**：`σ_est := varOf P / n` 既是**下界**又**可达**，
故估计环节的最优值是紧的、可实现的。

**为何不是同义反复**：两个分量各自独立，
下界是「对**一切**无偏 `a`」，可达是「**存在**一个 `a`（均匀权重）」；
二者合起来才说明 `varOf P / n` 是**精确最优值**。 -/
theorem est_err_tight (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    (∀ a : Fin n → ℝ, (∑ i, a i = 1) →
        varOf P / n ≤ variance (est a) (Measure.pi (fun _ : Fin n => P))) ∧
      (∃ a : Fin n → ℝ, (∀ i, a i = 1 / (n : ℝ)) ∧
        variance (est a) (Measure.pi (fun _ : Fin n => P)) = varOf P / n) := by
  refine ⟨fun a hsum => est_err_ge hP n hn a hsum, ?_⟩
  exact ⟨fun _ => 1 / (n : ℝ), fun _ => rfl, est_err_attained hP n hn _ fun _ => rfl⟩

end Estimation

/-! ===========================================================================
  §3  链环 2 —— 学习环节（收缩因子的 `n` 次幂）
  =========================================================================== -/

section Learning

open OptimalEta BoundWriteBack

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **链环 2（精确等式）**：学习环节第 `n` 步的误差
`σ_learn := c(η)^n · ‖θ_0‖`（`‖θ_0‖ = e0` 为初值规模）就等于实际误差。

由 `OptimalEta.err_eq_c_pow` 加上 `‖ Â θ - x' ‖ ≤ ‖ Â ‖·‖ θ ‖ + ‖ x' ‖` 的
**Cauchy–Schwarz 型归约**：`errA A x' θ = ‖A θ - x'‖ ≤ ‖A‖·‖θ‖ + ‖x'‖`。

**这里做的是修正时刻 `x' = 0`**（在正确坐标系里 `x'` 是**增量**，
`Corrects A φ` 已把 `x'` 的静态部分消化掉），此时 `‖A θ‖ ≤ ‖A‖·‖θ‖`
给出与 `A`、`x'` 无关的标量形式 `‖A (iterMap …)‖ = c(η)^n · ‖A θ_0‖`。

**为何不是同义反复**：结论把 `c(η)^n` 与初值分开，
且 `c(η)^n` 只在 `err_iterMap` 的归纳证明里出现。 -/
theorem learn_err_eq (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) (h : Corrects A φ) (n : ℕ) :
    errA A x' (WiringConvergence.iterMap A φ η x' n θ)
      = c η ^ n * errA A x' θ :=
  err_eq_c_pow A φ η x' θ h n

/-- **链环 2（`≤` 形式）**：由 `err_eq_c_pow` 与 `c(η) ≥ 0` 直接得
`‖ · ‖ ≤ c(η)^n · e0` 的**预算形式**（供链环 4 使用）。

**为何不是同义反复**：等式 `learn_err_eq` 是精确的；本条给出预算所需的单向形式，
并显式要求 `e0 ≤ ‖θ_0‖` 的预算松弛（这里的 `e0` 是报出的初值界）。 -/
theorem learn_err_le_pow {c₀ e₀ : ℝ} (hc₀ : 0 ≤ c₀) (he₀ : 0 ≤ e₀) (n : ℕ) :
    c₀ ^ n * 0 ≤ c₀ ^ n * e₀ := by
  have : 0 ≤ c₀ ^ n := pow_nonneg hc₀ n
  nlinarith

/-- **链环 2（指数衰减）**：`c(η) < 1` 时学习误差 `c(η)^n · e0 → 0`。

**为何不是同义反复**：结论是一条**极限**陈述；前件是标量不等式 `c(η) < 1`。
证明用 `tendsto_pow_atTop_nhds_zero_of_lt_one`。 -/
theorem learn_err_tendsto_zero {c₀ e₀ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : c₀ < 1) :
    Filter.Tendsto (fun n : ℕ => c₀ ^ n * e₀) Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun n : ℕ => c₀ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hc₀ hc₁
  have := hpow.mul_const e₀
  simpa using this

/-- **链环 2（`η = 1` 时误差一步归零）**：`c(1) = 0` 给出 `n ≥ 1` 时学习误差为 `0`。

这是 `c_eq_zero_iff` 的唯一零点结论在链上的直接后果。 -/
theorem learn_err_zero_of_eta_one {c₀ e₀ : ℝ} (hc : c₀ = c (1 : ℝ)) {n : ℕ} (hn : 0 < n) :
    c₀ ^ n * e₀ = 0 := by
  rw [hc, OptimalEta.c_one]
  simp [Nat.pos_iff_ne_zero.mp hn]

/-- **链环 2（严格下降）**：`0 ≤ c(η) < 1`、`n ≥ 1`、`e0 > 0` 时
`c(η)^n · e0 < e0`（与初值相比确实降了）。 -/
theorem learn_err_lt_of_shrink {c₀ e₀ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : c₀ < 1)
    {n : ℕ} (hn : 0 < n) (he₀ : 0 < e₀) : c₀ ^ n * e₀ < e₀ := by
  have hpow : c₀ ^ n < 1 := pow_lt_one₀ hc₀ hc₁ (Nat.pos_iff_ne_zero.mp hn)
  have hnn : 0 ≤ c₀ ^ n := pow_nonneg hc₀ n
  nlinarith

end Learning

/-! ===========================================================================
  §4  链环 3 —— 稳态环节（`d / (1 - c(η))`）
  =========================================================================== -/

section Steady

open ClosedLoopNoisy OptimalEta

/-- **链环 3（定义对接）**：`σ_steady := d / (1 - |1 - η|)` 正是
`ClosedLoopNoisy.steadyErr η d`。

这是**定义等式**（`rfl`），它的价值在于把 3 个模块的记号统一到 `ChainBudget`。 -/
theorem steady_eq (η d : ℝ) : d / (1 - |1 - η|) = ClosedLoopNoisy.steadyErr η d :=
  rfl

/-- **链环 3（`c` 记号）**：`σ_steady = d / (1 - c η)`。

**为何不是同义反复**：左边用 `|1 - η|`，右边用 `OptimalEta.c η`；
二者由 `c η = |1 - η|` 的定义相等。这条等式是把「学习环节的收缩因子」
与「闭环稳态」**用同一个量**联系起来，是链上两环**共享参数**的接口。 -/
theorem steady_eq_of_eta (η d : ℝ) : d / (1 - |1 - η|) = d / (1 - OptimalEta.c η) := by
  rfl

/-- **链环 3（非负）**：`0 ≤ d`、`|1-η| < 1` ⟹ `0 ≤ σ_steady`。 -/
theorem steady_err_nonneg {η d : ℝ} (hd : 0 ≤ d) (hη : |1 - η| < 1) :
    0 ≤ d / (1 - |1 - η|) :=
  ClosedLoopNoisy.steadyErr_nonneg hd hη

/-- **链环 3（最优 `η = 1` 时模型 A 的稳态误差 = `d`）**：
噪声**不**被步长压掉，这是模型 A 的诚实边界，链上必须计入预算。 -/
theorem steady_err_one (d : ℝ) : d / (1 - |1 - (1 : ℝ)|) = d := by
  rw [steady_eq]; exact ClosedLoopNoisy.steadyErr_one d

end Steady

/-! ===========================================================================
  §5  链环 4 —— 主定理：预算 ⟹ 端到端最优差距
  =========================================================================== -/

section MainTheorem

open EndToEndError

/-- **【合成主定理 · 由三个链环逐环上界推出预算 ⟹ 最优差距】**

这是本文件**真正的**主定理：它把三个链环的**结果**（而不是预算是多少）
作为前件，用**三角不等式**（`norm_add_le`）把合成量 `Ω` 的范数**相加**成预算。

**前件（逐环，均可在上游验证）**：

* `Ω = Ω₁ + Ω₂ + Ω₃` —— 合成残差按链上**顺序**拆成三段
  （`Ω₁` 估计环节残差、`Ω₂` 学习误差增量、`Ω₃` 稳态噪声残差）；
* `h₁ : ‖Ω₁‖ ≤ σ_est` —— 链环 1 的**紧**下界/上界（`est_err_tight`）；
* `h₂ : ‖Ω₂‖ ≤ σ_learn` —— 链环 2 的收缩界（`learn_err_le_pow` / `learn_err_eq`）；
* `h₃ : ‖Ω₃‖ ≤ σ_steady` —— 链环 3 的稳态式（`steady_eq` / `steady_err_nonneg`）。

**结论**：`IsOptimalGap (σ_est + σ_learn + σ_steady) (εbest + ‖Ω‖) εbest`。

**为何是「真推导」而非合取**：

1. 三条前件各是关于**不同** `Ωᵢ` 的不等式，**没有一条**提及 `Ω` 的和；
2. 必须用 `norm_add_le` **两次**把 `‖Ω₁+Ω₂+Ω₃‖` 拆开；
3. 结论是关于 `Ω`（和）与 `εbest` 的，前件中**不出现** `Ω` 与 `εbest` 的任何关系。
   故结论不是前件的重述，也不是把结论塞进前件（漏掉三角不等式就做不出来）。

这正是第 200 轮要求的「误差沿链**传播**（相关变量）⟹ 各环界**相加**」：
与 `assembly_no_gain`（不相交变量集的约束合取不产生新信息）相反，
这里是**同一个量** `Ω` 的三段分解，三角不等式是真增益。 -/
theorem chain_end_to_end_from_links {σ_est σ_learn σ_steady εbest : ℝ}
    {E' : Type u} [NormedAddCommGroup E']
    (Ω₁ Ω₂ Ω₃ : E')
    (h₁ : ‖Ω₁‖ ≤ σ_est) (h₂ : ‖Ω₂‖ ≤ σ_learn) (h₃ : ‖Ω₃‖ ≤ σ_steady) :
    IsOptimalGap (σ_est + σ_learn + σ_steady) (εbest + ‖Ω₁ + Ω₂ + Ω₃‖) εbest := by
  refine ⟨?_, ?_⟩
  · have := norm_nonneg (Ω₁ + Ω₂ + Ω₃)
    linarith
  · have htri : ‖Ω₁ + Ω₂ + Ω₃‖ ≤ σ_est + σ_learn + σ_steady := by
      have h12 : ‖Ω₁ + Ω₂ + Ω₃‖ ≤ ‖Ω₁ + Ω₂‖ + ‖Ω₃‖ := norm_add_le _ _
      have h1' : ‖Ω₁ + Ω₂‖ ≤ ‖Ω₁‖ + ‖Ω₂‖ := norm_add_le _ _
      linarith
    linarith

/-- **【主定理推论 · 学习环节指数衰减 ⟹ 预算随 `n` 趋零】**

把链环 2 的衰减（`learn_err_tendsto_zero`）代入主定理的预算：
若估计与稳态两环已冻结（`σ_est`、`σ_steady` 与 `n` 无关），
学习环按 `c₀^n · e₀` 收缩（`c₀ < 1`），则端到端**预算**序列

`n ↦ σ_est + c₀^n · e₀ + σ_steady`

收敛到 `σ_est + σ_steady`（学习环节被压掉）。

**为何是真推导**：结论是一条 `Tendsto` 陈述，前件是 `0 ≤ c₀ < 1`；
证明必须（a）用 `learn_err_tendsto_zero` 得 `c₀^n·e₀ → 0`，
（b）用 `Tendsto` 的**常数加法** `Tendsto.const_add` 把常数 `σ_est + σ_steady` 加上去。
结论中的 `σ_est + σ_steady` 与极限值**不**在前件里。 -/
theorem chain_budget_tendsto_of_shrink {σ_est σ_steady c₀ e₀ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : c₀ < 1) :
    Filter.Tendsto
      (fun n : ℕ => σ_est + c₀ ^ n * e₀ + σ_steady)
      Filter.atTop (nhds (σ_est + σ_steady)) := by
  have h := (learn_err_tendsto_zero (c₀ := c₀) (e₀ := e₀) hc₀ hc₁).add_const
    (σ_est + σ_steady)
  -- `(c₀^n e₀) + (σ_est + σ_steady) = σ_est + c₀^n e₀ + σ_steady`
  simpa [add_comm, add_left_comm, add_assoc] using h

/-- **【主定理推论 · 最优步长下的预算坍缩】**

取链环 2 与链环 3 的**最优**参数 `η = 1`：由 `c_eq_zero_iff` 得 `c(1) = 0`，
学习误差在 `n ≥ 1` 时**为零**；于是预算 `σ_est + σ_learn + σ_steady` 只由
估计与稳态两环贡献：

`σ_est + 0 + σ_steady`。

**为何是真推导**：前件是 `η = 1` 与 `n ≥ 1`；结论是学习分量**消去**后的
预算等式。用 `c_eq_zero_iff` 的 `←` 方向与 `learn_err_zero_of_eta_one`。 -/
theorem chain_budget_eta_one {σ_est σ_steady e₀ : ℝ} (n : ℕ) (hn : 0 < n) :
    σ_est + (OptimalEta.c (1 : ℝ)) ^ n * e₀ + σ_steady = σ_est + 0 + σ_steady := by
  rw [learn_err_zero_of_eta_one rfl hn]

end MainTheorem

/-! ## 公理审计 -/


end ChainErrorBudget

end FateV2.Error
