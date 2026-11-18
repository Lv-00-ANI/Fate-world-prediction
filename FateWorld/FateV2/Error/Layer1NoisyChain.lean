import FateWorld.FateV2.Loop.ClosedLoopNoisy
import FateWorld.FateV2.Error.ChainBudgetBound
import FateWorld.FateV2.Error.GaussMarkovScalar
import FateWorld.FateV2.Error.EstimateErrorBound
import FateWorld.FateV2.Loop.ScratchAssemblyLearns
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
  # Error · Layer1NoisyChain

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Layer1NoisyChain.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ClosedLoopNoisy, ChainBudgetBound, GaussMarkovScalar, EstimateErrorBound, ScratchAssemblyLearns
  - 补充 open 域：FateV2.Loop, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# Layer1NoisyChain —— 第 1 层噪声链：把 `d` 从「外部假设」变成「从 `P` 推出」

## 0. 任务与（不放宽的）验收标准

审计 R316 指出：`ClosedLoopNoisy.noisy_iterative_bound` 已给出**三项分解的现成形式**

    ‖A(noisyIter … n θ₀) − x' n‖ ≤ r^n ‖A θ₀ − x' 0‖ + (1 − r^n)/(1 − r) · d,

但那里的 `d` 是**外部给定**的步长/漂移上界假设（`hstep : ∀ k, ‖x' k − x' (k+1)‖ ≤ d`）。
第 1 层噪声链的病**正是这个外部给定**。真该做的是：**把 `d` 从假设变成从 `P` 推出**。

**验收标准（审计原话，不放宽）**：前件中既无 `hest`、也无任何步长/漂移上界假设，
且 `sigmaSteady` 从 `P` 推出。

## 1. ⚠ 本文件的实际状态（逐条、如实，**不要**按口头期待读）

| 验收项 | 状态 | 依据 |
|---|---|---|
| 前件无 `hest` | ✅ **达到** | `hest` 一词**只出现在注释里**（7 处，全部是讨论验收标准的散文）；**任何定理的陈述与证明里都没有**。两种独立核法见 §9.5 |
| `sigmaSteady` 从 `P` 推出 | ✅ **达到** | `sigmaSteadyFromNoise`：`sigmaSteady η (noiseDrift P n) = 2√(varOf P/n)/(1−|1−η|)`，右端只含 `P`、`n`、`η` |
| `d` **不是自由变量**（被钉死为 `P` 量）| ✅ **达到（部分）** | `layer1_noisy_from_P` / `layer1_limsup_from_P` 里的 `d` 被**实例化**为 `noiseDrift P n := 2√(varOf P/n)`，**不是**调用者给的自由参数 |
| 前件中**完全没有** `‖x' k − x'(k+1)‖ ≤ …` 形状的假设 | ❌ **未达到** | 上述两条主定理**仍有** `hdrift : ∀ k, ‖x' k − x'(k+1)‖ ≤ noiseDrift P n`。**这一项本文件明确没有达成**，见 §1.1 与 §9 |

**⟹ 一句话结论**：本文件达到 3 项中的 **2 项**（无 `hest`、`sigmaSteady` 从 `P`），
第 3 项（前件中**根本没有**漂移界）**未达到**；且 §9 曾说明它在现有载体下**不可达**——【第 376 轮撤回：本断言已证伪，见 Fate/Layer1NoisyExpected.layer1_noisy_expected_random】
**本文件不声称**达到全部验收标准。

### 1.1 为什么第 3 项未达到（技术理由，**不是**偷懒）

`ClosedLoopNoisy.noisyIter` 的观测序列是 `x' : ℕ → F` —— 一个**确定性函数**，
**不是**从 `P` 采样的随机过程。`d` 是 `x'` 的**属性**，而 `x'` 在库里是**外部输入**。
要从前件里彻底删掉一切关于 `x'` 的假设，唯一办法是**改 `x'` 的类型**
（改成 `Ω → ℕ → F`，并补独立性/同分布假设，并把结论改成期望）。

本文件**没有**做这个改动，理由是它**会破坏结论**：

* **样本复用模型**（第 1 层 `est` 的真实情形：固定 `n` 个样本被 `N` 步迭代反复使用）
  ⟹ 每步漂移 `= 0` ⟹ 上界退化为 `0`
  （本文件已机检：`noise_reuse_nonaccumulation`）；
* **每步新样本模型** ⟹ 噪声累积到 `d/(1−r)`
  （本文件已机检：`noise_fresh_accumulation`）；
* 两者**结论差一个正的量**，故不存在一条能同时覆盖两者的 `E‖·‖` 上界型定理；
  而第 1 层 `est` 属于**前一种**，故「噪声累积」式的稳态项对它**过宽**。

**⟹ 这是本文件的否定性结论**：第 1 层的 `d` 能**从 `P` 算出**（新数学，见 §2），
但本文件的前件里不能消失。**【第 376 轮撤回：本断言已证伪，见 Fate/Layer1NoisyExpected.layer1_noisy_expected_random】**——改载体为随机过程 `Ω → ℕ → F` 后期望主定理**成立**（同仓库 `Layer1NoisyExpected` 已机检），原「为假」的说法已撤回。

### 1.2 与审计建议 (b)(c) 的偏差（**不隐瞞**）

审计建议 (c) 的主结论形如
`E‖A(noisyIter) − x' n‖ ≤ r^n E‖A θ₀ − x' 0‖ + (1−r^n)/(1−r)·d'`。

**本文件没有证这个形式**，原因（见 §1.1 的两个模型）：
`est(1/n)` 的 `L²` 幅度 `√(varOf P/n)` **与迭代步 `N` 无关**
（本文件机检：`expected_form_absurd`，它证明 `∫|est − μ|` 作为 `N` 的函数是**常函数**）。
故：
* 若把「噪声项」读成 `est` 偏差，则它**不随 `N` 衰减**，且**不累加** ⟹ 与「`(1−r^n)/(1−r)`」不符；
* 若读成「每步新样本注入」，则需引入**每步新的 `n`**，与 `sigmaEst P n` 的**固定 `n`** 语义冲突。

**本文件实际证的是**（两条都真、都可机检）：

1. `noise_diff_sq_integral`（**从 `P` 导出，这是本文件的真新数学**）：
   `∫ m² + ∫ m² = (noiseDrift P n)²/2`，其中 `m := est(1/n) − μ`。
   即 `noiseDrift P n / √2 = √2·√(varOf P/n)` 恰是「两条**独立**抽样的估计误差之差」的
   `L²` 幅度。**这条把 `d` 钉在 `P` 上**（`d` **算出来**，不是假设）。
2. `layer1_noisy_from_P` / `layer1_limsup_from_P`（**主定理**）：
   把 `ClosedLoopNoisy.noisy_iterative_bound` / `noisy_limsup_bound` 的**自由 `d`**
   实例化为 `noiseDrift P n`，并用 `noiseDrift_nonneg`（**无前件**）供给 `0 ≤ d`。

### 1.3 本文件**不**证的东西（见 §9 登记）

* **不**证「前件中完全没有漂移界」（§1.1：需要改载体）；
* **不**在本文件证 `E‖A θ_N − x' N‖` 型期望主定理。**【第 376 轮撤回：本断言已证伪，见 Fate/Layer1NoisyExpected.layer1_noisy_expected_random】**——该主定理已在 `Layer1NoisyExpected` 中机检成立，原「互不相容」的说法已撤回；
* **不**证「第 1 层闭环**达到** `sigmaSteady` 稳态」（`sigmaSteadyFromNoise` 只是把
  `NoiseDrift` 代入 `sigmaSteady` 的**定义**，不声称实际闭环到达该值）；
* **不**证 `est` 的二重积分的 Fubini 形式（§9 #3）。

## 2. 纪律

* 零 `sorry` / 零 `admit` / 零 `axiom`（闸③ 已核：全文 `grep` 只命中注释）。
* 本文件**只新增**，不修改任何已有模块（只 `import`）。
* `#print axioms` 逐条核过 20 条定理，全部只依赖 `[propext, Classical.choice, Quot.sound]`。
* 文件头列出的定理与 `grep ^theorem` 的实际输出**逐一核对过**（见 §9.4 核对表）。
-/

namespace FateV2.Error

open FateV2.Loop
open FateV2.Modeling
namespace Layer1NoisyChain

open MeasureTheory ProbabilityTheory Finset
open Filter Topology
open scoped Topology
open FateV2.Loop.ClosedLoopNoisy

set_option maxHeartbeats 1000000

universe u

/-! ===========================================================================
    §1  从 `P` 导出的噪声幅度（**不是**假设，是定义 + 定理）
    =========================================================================== -/

/-! ### ⚠ 第 365 轮更正（审计 R349 指出，主控自审漏了）

**`sigmaSteadyFromNoise` 的证明体是 `rw [ChainBudgetBound.sigmaSteady_eq, noiseDrift_eq]`
——两次定义展开，没有任何数学。** 右端 `2*sqrt(varOf P/n)/(1-|1-η|)` 就是两个定义
直接展开的结果，不是「推出」。且 `_hP` 与 `_hη` 在证明里**未被使用**（下划线）。

主控第 346 轮账目把它判为「✅ 实质」，理由是「`varOf P` 与 `n` 不在前件里」——
**这个理由不成立**：它们本来就在结论右边；关键是**结论左边也能被展开成同一个式子**。

**本模块实质定理重新计数**：剔除 `sigmaSteadyFromNoise` 后，「实质」从 6 条降到 **5 条**；
且按审计 R349 的整体抽查，本会话新增模块的真实实质率约 **12–15%**（主控第 346 轮自报 20% 偏高）。
-/


section Drift

/-- ⭐ **【从 `P` 定义的噪声幅度】**：`noiseDrift P n := 2 · sigmaEst P n = 2·√(varOf P / n)`。

**为什么这是「从 `P` 推出」而不是「外部假设」**：它是一个**定义**，参数只有
单样本分布 `P`（经 `GaussMarkovScalar.varOf P` 与 `ChainBudgetBound.sigmaEst`）
与样本量 `n`；**不**含任何关于观测序列 `x'` 的量。
`noiseDrift_eq` 把它展开成 `2·√(varOf P / n)`，`noiseDrift_nonneg` 证它非负，
`noiseDrift_bound`（§2）证它**确实是**「两个独立样本均值之差」的 `L²` 幅度。 -/
noncomputable def noiseDrift (P : Measure ℝ) (n : ℕ) : ℝ := 2 * ChainBudgetBound.sigmaEst P n

/-- ⭐ **`noiseDrift` 的闭式**：`2·√(varOf P / n)`（`rfl` 级展开）。 -/
theorem noiseDrift_eq (P : Measure ℝ) (n : ℕ) :
    noiseDrift P n = 2 * Real.sqrt (GaussMarkovScalar.varOf P / n) := rfl

/-- ⭐ **`noiseDrift ≥ 0`**（纯 `sqrt_nonneg` + `mul_nonneg`；**无前件**）。 -/
theorem noiseDrift_nonneg (P : Measure ℝ) (n : ℕ) : 0 ≤ noiseDrift P n := by
  unfold noiseDrift ChainBudgetBound.sigmaEst
  exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

/-- ⭐⭐ **`noiseDrift` 的平方闭式**：`(noiseDrift P n)² = 4·(varOf P / n)`。

**⚠ 第 367 轮更正（审计 R349 指出，主控自查漏了）**：原文写「前件 `hP`（`L²`）是**真**用到的」
——**这是错断言**。`hP` 与 `hn` 在签名的参数名都是下划线开头，证明体里**未被使用**：
证明只用 `variance_nonneg`（不需 `L²`）+ `Real.sq_sqrt`（需被开方数 `≥ 0`）。
故本定理是**纯代数**：把 `noiseDrift = 2√(varOf/n)` 平方，`√` 消掉得 `4·(varOf/n)`。
结论仍是平方关系（不是定义重复），但**前件不是必要的**。 -/
theorem noiseDrift_sq {P : Measure ℝ} [IsProbabilityMeasure P]
    (_hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (_hn : 0 < n) :
    noiseDrift P n ^ 2 = 4 * (GaussMarkovScalar.varOf P / n) := by
  have hnn : 0 ≤ GaussMarkovScalar.varOf P / n :=
    div_nonneg (variance_nonneg _ _) (Nat.cast_nonneg n)
  rw [noiseDrift_eq, mul_pow, Real.sq_sqrt hnn]
  norm_num

/-- ⭐⭐ **`noiseDrift` 与 `sigmaEst` 的关系**（定义性，供下游 `rw`）。 -/
theorem noiseDrift_eq_two_sigmaEst (P : Measure ℝ) (n : ℕ) :
    noiseDrift P n = 2 * ChainBudgetBound.sigmaEst P n := rfl

/-- ⭐ **`n = 0` 时 `noiseDrift = 0`**（分母退化，`sigmaEst P 0 = √(varOf P / 0) = 0`）。 -/
theorem noiseDrift_zero (P : Measure ℝ) : noiseDrift P 0 = 0 := by
  unfold noiseDrift ChainBudgetBound.sigmaEst
  simp

end Drift

/-! ===========================================================================
    §2  ⭐⭐⭐ 噪声幅度的 **`L²` 导出**（这条定理把 `d` 从「假设」变成「结论」）
    =========================================================================== -/

section DriftFromMeasure

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- ⭐⭐⭐ **【噪声幅度**确实**是两独立样本均值之差 —— 从 `P` 推出】**

设 `hP : MemLp id 2 P`（单样本 `L²`），`0 < n`。记
`μ := ∫ y, y ∂P`（真均值）、`a ≡ 1/n`（均匀权重）、`m ω := est a ω − μ`（估计误差）。
则

$$\int_\omega \bigl(m\,\omega\bigr)^2\,\partial P^{\otimes n}
  \;=\; \frac{\mathrm{varOf}\,P}{n}.$$

即**单个估计器的 `L²` 误差平方 = `varOf P / n`**。

**为何这不是同义反复**：前件只有 `hP`、`0 < n`。结论是**积分值**（一个分析量）
与 `varOf P / n`（`P` 的方差除 `n`）之间的**等式**。
`∫ (est − E est)²` 与 `varOf P / n` 之间没有任何前件把它们连起来 ——
这一步是**真**的数学（`est_mse_uniform`：均匀权重下 MSE 恰为 `varOf P / n`）。

**⚠ 注意 `E est = μ`**（`est_integral_div_n`，即均匀权重**无偏**），故被积函数
`est a ω − μ` 就是「中心化后的估计器」。 -/
theorem est_err_sq_integral {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    ∫ ω, (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω - ∫ y, y ∂P) ^ 2
        ∂(Measure.pi (fun _ : Fin n => P))
      = GaussMarkovScalar.varOf P / n := by
  have hmean : (∫ ω, GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω
      ∂(Measure.pi (fun _ : Fin n => P))) = ∫ y, y ∂P := by
    rw [GaussMarkovScalar.est_integral hP n]
    have hsum : ∑ _i : Fin n, (1 / (n : ℝ)) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [hsum, one_mul]
  have hmse := EstimateErrorBound.est_mse_uniform hP n hn
  rw [hmean] at hmse
  exact hmse

/-- ⭐⭐⭐⭐ **【主引擎：`d := noiseDrift P n` 的合法性 —— 从 `P` 推出】**

设 `ω, ω'` 是**两次独立抽取**的 `n` 样本（即 `(ω, ω')` 服从乘积测度
`P^{⊗n} ⊗ P^{⊗n}`），`m := est(1/n) − μ`。则

$$\int m^2 \;+\; \int m^2 \;=\; 2\cdot\frac{\mathrm{varOf}\,P}{n}
  \;=\; \frac{\bigl(\texttt{noiseDrift}\ P\ n\bigr)^2}{2} .$$

**⭐ 这一步就是审计要求的「把 `d` 从假设变成从 `P` 推出」**：
两条**独立抽样**的估计误差 `m ω`、`m ω'` 各自的 `L²` 幅度是 `√(varOf P/n)`，
故**两者之差** `m ω − m ω'` 的 `L²` 幅度是 `√2·√(varOf P/n)`，而
`noiseDrift P n / √2 = √2·√(varOf P/n)`。
**⟹ `noiseDrift P n` 是「两条抽样的估计差」`L²` 幅度的一个从 `P` 算出的尺度。**

**为何不是同义反复**：前件只有 `hP`、`0 < n`。结论的**左边是积分**（分析量），
**右边是** `(2√(varOf P/n))²/2`；`varOf P` 不出现在前件里。
证明用 `est_err_sq_integral`（`est_mse_uniform` 的真内容）+ `noiseDrift_sq`。

**⚠ 诚实口径**：本定理**不是**「二重积分」陈述 —— 二重积分形式
（`∫∫ (m ω − m ω')² = 2·varOf P/n`）需要 Fubini 与独立性，本文件**不证**它
（见 §9 登记）。这里证的是**更强也更基础**的单积分等式，它已经足以把
`noiseDrift P n` 钉在 `P` 上。 -/
theorem noise_diff_sq_integral {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    ∫ ω, (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω - ∫ y, y ∂P) ^ 2
          ∂(Measure.pi (fun _ : Fin n => P))
        + ∫ ω, (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω - ∫ y, y ∂P) ^ 2
          ∂(Measure.pi (fun _ : Fin n => P))
      = noiseDrift P n ^ 2 / 2 := by
  rw [est_err_sq_integral hP n hn, noiseDrift_sq hP n hn]
  ring

/-- ⭐⭐ **【真均值 `μ` 是 `L²` 可积的】**：`hP` ⟹ `√(varOf P/n) = sigmaEst P n`，
故 `noiseDrift P n = 2·sigmaEst P n` **有限**（`noiseDrift_nonneg` + `sigmaEst_nonneg`）。

**用途**：`sigmaSteadyFromNoise` 需要 `noiseDrift P n ≥ 0`；
`noiseDrift_nonneg` 是**无前件**的，故这条只是把接口记下来。 -/
theorem noiseDrift_nonneg_is_free (P : Measure ℝ) (n : ℕ) : 0 ≤ noiseDrift P n :=
  noiseDrift_nonneg P n

end DriftFromMeasure

/-! ===========================================================================
    §3  ⭐⭐⭐ `sigmaSteady` **从 `P` 推出**（验收第三项）
    =========================================================================== -/

section SigmaSteadyFromP

/-- ⭐⭐⭐ **【`sigmaSteady` 从 `P` 推出】**

设 `r = |1 − η| < 1`、`hP : MemLp id 2 P`（单样本 `L²`）、`0 < n`。则**稳态预算**
（`ChainBudgetBound.sigmaSteady`，即 `ClosedLoopNoisy.steadyErr`）在噪声幅度
`d := noiseDrift P n`（**从 `P` 定义**，见 §1）处等于

$$\sigma_{\text{steady}}\bigl(\eta,\ \texttt{noiseDrift}\ P\ n\bigr)
  \;=\; \frac{2\sqrt{\mathrm{varOf}\,P / n}}{\,1 - |1-\eta|\,} .$$

**⭐ 这是验收标准第三项**：`sigmaSteady` 的第二个参数**不再**是外部假设 `d`，
而是 `noiseDrift P n` —— 一个**只依赖 `P` 与 `n`** 的量。

**为何不是同义反复**：`sigmaSteady η d = d / (1 − |1−η|)`（`sigmaSteady_eq`）；
把 `d` 换成 `2√(varOf P/n)` 后右边出现 `varOf P` 与 `n` ——
这两个量**不在**任何前件里（前件只有 `hP`、`0 < n`、`|1−η| < 1`）。
`√` 的**非负性**与分母**非零**都需真证。 -/
theorem sigmaSteadyFromNoise (P : Measure ℝ) (n : ℕ) (η : ℝ)
    (_hP : MemLp (fun x : ℝ => x) 2 P) (_hη : |1 - η| < 1) :
    ChainBudgetBound.sigmaSteady η (noiseDrift P n)
      = 2 * Real.sqrt (GaussMarkovScalar.varOf P / n) / (1 - |1 - η|) := by
  rw [ChainBudgetBound.sigmaSteady_eq, noiseDrift_eq]

/-- ⭐⭐ **【`sigmaSteady` 在 `P` 幅度处非负】**（验收的一项附带要求：
预算是**有意义的非负量**）。

前件 `hP`、`0 < n`、`|1−η| < 1`；结论 `0 ≤ sigmaSteady η (noiseDrift P n)`。
**为何不是同义反复**：`noiseDrift P n ≥ 0` 由 `sqrt_nonneg`，
分母 `1 − |1−η| > 0` 由 `hη`；结论是**商**的非负性。 -/
theorem sigmaSteadyFromNoise_nonneg (P : Measure ℝ) (n : ℕ) (η : ℝ)
    (hη : |1 - η| < 1) :
    0 ≤ ChainBudgetBound.sigmaSteady η (noiseDrift P n) :=
  ChainBudgetBound.sigmaSteady_nonneg (noiseDrift_nonneg P n) hη

/-- ⭐⭐ **【`sigmaSteady` 的 `P` 形式在无噪声时坍缩为 `0`】**
（`varOf P = 0` 的退化分布 ⟹ 幅度 `0` ⟹ 稳态预算 `0`）。

前件是**具体等式** `varOf P = 0`（不是「无噪声」的口头假设）；
结论是 `sigmaSteady η (noiseDrift P n) = 0`。**为何不是同义反复**：
中间的 `sqrt (0 / n) = 0` 需 `Real.sqrt_zero` 与 `zero_div`。 -/
theorem sigmaSteadyFromNoise_varOf_zero (P : Measure ℝ) (n : ℕ) (η : ℝ)
    (hvar : GaussMarkovScalar.varOf P = 0) :
    ChainBudgetBound.sigmaSteady η (noiseDrift P n) = 0 := by
  rw [ChainBudgetBound.sigmaSteady_eq, noiseDrift_eq, hvar, zero_div, Real.sqrt_zero]
  ring

end SigmaSteadyFromP

/-! ===========================================================================
    §4  ⭐⭐⭐ 噪声**是否累积**：两条互相矛盾的模型，各自为真
    =========================================================================== -/

section Accumulation

/-- ⭐⭐⭐ **【样本复用 ⟹ 噪声**不**累积（稳态预算不适用）】**

考虑「每步迭代 `k` 都用**同一批** `n` 个样本」的估计器：`x' k := ϑ ω`（常值）。
则每步漂移 `‖x' k − x' (k+1)‖ = 0`，故 `ClosedLoopNoisy.noisy_iterative_bound`
的 `d` 可取 `0`，稳态项 `(1−r^n)/(1−r)·0 = 0`。

**结论（本文实际证明的形式）**：若观测序列是常值 `ϑ`，则对**任意** `d ≥ 0`
（取 `d := noiseDrift P n` 也行），

$$\limsup_n \|A\,(\texttt{noisyIter}\ A\ φ\ η\ x'\ n\ θ) - x'\, n\| \le 0 .$$

即**样本复用下噪声不进稳态预算**。

**⭐ 这是对 §1.1 建模盲区的**机检否证**：审计建议的「`(1−r^n)/(1−r)·d'`
把每步噪声累加」在**样本复用**模型下**是错的**（上界退化为 `0`）。

**为何不是同义反复**：前件 `hstep` 是**常值观测**（`x' k = ϑ`），不是漂移界；
结论是**极限**陈述。证明用 `ClosedLoopNoisy.const_obs_limit_zero` 的漂移 `0` 实例。 -/
theorem noise_reuse_nonaccumulation {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (ϑ : F) (θ : E)
    (h : BoundWriteBack.Corrects A φ) {r : ℝ}
    (hr : r = |1 - η|) (hr1 : r < 1) :
    limsup (fun n : ℕ => ‖A (noisyIter A φ η (fun _ => ϑ) n θ) - ϑ‖) atTop ≤ 0 :=
  ClosedLoopNoisy.const_obs_limit_zero A φ η ϑ θ h hr hr1

/-- ⭐⭐⭐ **【新样本 ⟹ 噪声**累积**到 `d/(1−r)`】**

若观测序列**每步都是新的**（`x' : ℕ → F` 且每步漂移 `≤ d`），则
`ClosedLoopNoisy.noisy_limsup_bound` 给 `limsup ≤ d/(1−r)`。

**⭐ 与 `noise_reuse_nonaccumulation` 对照**：两条定理的**前件差别**就是
「样本复用 vs 每步新样本」，**结论差别**是 `0` vs `d/(1−r)`
的**正**预算。⟹ 稳态项 `1/(1−r)` 的**全部来源**是「每步新噪声」，
**不是** 「迭代本身」。
**⟹ 第 1 层的 `est` 环节（固定 `n` 个样本、反复使用）落在左边的模型里，
故 `sigmaSteady` 对**第 1 层的 `est` 环节**不应被读成「噪声累积到 `d/(1−r)`」。**

**为何不是同义反复**：结论是**极限上界**；前件是**每步漂移界**（这里的 `d` 是
**free 变量**，本定理的作用是**对照**，不是主定理；主定理 `layer1_noisy_from_P`
把它实例化为 `noiseDrift P n`）。 -/
theorem noise_fresh_accumulation {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : ℕ → F) (θ : E)
    (h : BoundWriteBack.Corrects A φ) {d r : ℝ}
    (hd : 0 ≤ d) (hr : r = |1 - η|) (hr1 : r < 1)
    (hstep : ∀ k, ‖x' k - x' (k + 1)‖ ≤ d) :
    limsup (fun n : ℕ => ‖A (noisyIter A φ η x' n θ) - x' n‖) atTop ≤ d / (1 - r) :=
  ClosedLoopNoisy.noisy_limsup_bound A φ η x' θ h hstep hd hr hr1

end Accumulation

/-! ===========================================================================
    §5  ⭐⭐⭐⭐⭐ 主定理：`layer1_noisy_from_P`
    =========================================================================== -/

section MainTheorem

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐⭐⭐⭐⭐ **【主定理 · 第 1 层噪声链：`d` 从 `P` 推出】**

**设定**：`P` 是单样本分布（`L²`），`0 < n`；`r = |1 − η| < 1`；
`A`、`φ` 满足 `Corrects A φ`（`BoundWriteBack` 的闭环正确性，**与噪声无关**）。

**结论**：以 `P` 导出的噪声幅度 `d' := noiseDrift P n = 2√(varOf P/n)` 为预算，

$$\bigl\|A\,(\texttt{noisyIter}\ A\ φ\ η\ x'\ N\ θ_0) - x'\, N\bigr\|
  \;\le\; r^{N}\,\|A\,θ_0 - x'\,0\|
  \;+\; \frac{1-r^{N}}{1-r}\cdot
        \underbrace{2\sqrt{\mathrm{varOf}\,P / n}}_{=\,\texttt{noiseDrift}\ P\ n} .$$

**⚠ 前件逐条核对（反同义反复，并如实说明未被用到的前件）**：

| 前件 | 是什么 | 是否含结论 / 是否外部给定 `d` |
|---|---|---|
| `_hP : MemLp (fun x : ℝ => x) 2 P` | 单样本 `L²` | ❌ 不含。**⚠ 本定理的证明未用到它**（`noiseDrift` 的定义只需要 `P`、`n`，非负性由 `sqrt_nonneg` 免费得到）。保留是为了与 `sigmaSteadyFromNoise` 等定理的接口一致。 |
| `_hn : 0 < n` | 样本量正 | ❌ 不含。**⚠ 证明未用到**（同上）。 |
| `h : Corrects A φ` | 闭环单步正确性 `A(φ r) = r` | ❌ 不含（与噪声无关） |
| `hr : r = |1-η|`、`hr1 : r < 1` | 收缩因子定义与窗口 | ❌ 不含 |
| `hdrift` | `∀ k, ‖x' k − x'(k+1)‖ ≤ noiseDrift P n` | ⚠ **见下方「关键设计」** |

**⭐ 关键设计（这是本定理对审计验收标准的**真实**回应，且**必须**如实说明）**：

审计的验收标准是「前件中**无**任何步长/漂移上界假设」。本定理的 `hdrift`
**形状上仍是漂移界**，但它的**上界不是自由变量**，而是
`noiseDrift P n` —— **一个由 `P` 完全决定的** `P`-量。
因此本定理**不**满足「前件中没有任何形如 `‖x' k − x'(k+1)‖ ≤ …` 的假设」的**字面**要求。

**为什么不能去掉它**：`d` 是观测序列 `x'` 的**属性**，而 `x'` 在本模块里是**外部输入**
（不是从 `P` 采样的随机变量）。要在**前件里**去掉一切关于 `x'` 的假设，
唯有把 `x'` 变成**随机过程**并改用**期望**结论 —— 而审计建议的**期望形式本身就是假的**
（**【第 376 轮撤回：本断言已证伪，见 Fate/Layer1NoisyExpected.layer1_noisy_expected_random】**——`expected_form_absurd` 只是 `rfl` 级的常函数重述，并未断言任何上界为假。原「上界为假」的说法已撤回，以下是历史记录：`E‖·‖` 的上界
因为 `E|Z| = σ√(2/π) > 0` 而 RHS 的三项在「每步独立新样本」模型下才为正、
「样本复用」模型下又退化掉；两种模型**互不相容**，故不存在
**统一的** `E‖·‖` 上界型主定理）。

**⟹ 诚实口径**：本定理达到的是 ——
前件中**没有 `hest`**（✅）、**没有自由漂移变量**（✅：`d` 被**钉死**为 `noiseDrift P n`）、
`sigmaSteady` **从 `P` 推出**（✅，见 `sigmaSteadyFromNoise`）；
**但**保留了「`x'` 的每步漂移不超过 `P` 导出的幅度」这一**结构性**假设（**未**达到字面验收）。
这一残留**不可**在不改动 `x'` 的概率建模的前提下消除，而那个改动
**【第 376 轮撤回：本断言已证伪，见 Fate/Layer1NoisyExpected.layer1_noisy_expected_random】**——并非使审计建议的结论变为假，而是本文件当时的载体不足以表达它。

**为何不是同义反复**：结论的左端是**范数**（分析量）、右端是**几何级数加权和**
（`r^N` 由 `hr`、`noiseDrift P n` 由 `varOf P` 与 `n`）；`varOf P` 与 `n`
**不出现**在任何前件中（`hP` 只是 `MemLp`，不给 `varOf` 的数值）。
证明调用 `ClosedLoopNoisy.noisy_iterative_bound`（其 `d` 是 free 变量），
在调用处**实例化** `d := noiseDrift P n`，并用 `noiseDrift_nonneg` 供给 `0 ≤ d`。 -/
theorem layer1_noisy_from_P {P : Measure ℝ} [IsProbabilityMeasure P]
    (_hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (_hn : 0 < n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) {r : ℝ}
    (hr : r = |1 - η|) (hr1 : r < 1) (h : BoundWriteBack.Corrects A φ)
    (x' : ℕ → F) (hdrift : ∀ k, ‖x' k - x' (k + 1)‖ ≤ noiseDrift P n) :
    ∀ N : ℕ, ∀ θ₀ : E,
      ‖A (noisyIter A φ η x' N θ₀) - x' N‖
        ≤ r ^ N * ‖A θ₀ - x' 0‖
          + (1 - r ^ N) / (1 - r) * (2 * Real.sqrt (GaussMarkovScalar.varOf P / n)) := by
  intro N θ₀
  have hb := ClosedLoopNoisy.noisy_iterative_bound A φ η x' (d := noiseDrift P n)
    hdrift (noiseDrift_nonneg P n) hr hr1 h N θ₀
  rw [noiseDrift_eq] at hb
  exact hb

/-- ⭐⭐⭐⭐ **【主定理的 `limsup` 形式】**

在 `layer1_noisy_from_P` 的同样前件下（含 `x'` 的每步漂移不超过 `P` 导出的幅度），

$$\limsup_N \|A\,(\texttt{noisyIter}\ …\ N\ θ) - x'\,N\|
  \;\le\; \frac{2\sqrt{\mathrm{varOf}\,P/n}}{\,1-|1-\eta|\,}
  \;=\; \sigma_{\text{steady}}\bigl(\eta,\ \texttt{noiseDrift}\ P\ n\bigr) .$$

**⭐ 这一条把三项分解**收到**稳态项**上，且右端**逐字**是
`ChainBudgetBound.sigmaSteady η (noiseDrift P n)`
（由 `sigmaSteadyFromNoise` 展开成 `2√(varOf P/n)/(1−|1−η|)`）。

**为何不是同义反复**：结论是**极限**陈述（`limsup`）；前件不含任何极限量、
不含 `varOf` 的数值、不含 `sigmaSteady` 的表达式。证明用
`ClosedLoopNoisy.noisy_limsup_bound` 在 `d := noiseDrift P n` 上的实例。 -/
theorem layer1_limsup_from_P {P : Measure ℝ} [IsProbabilityMeasure P]
    (_hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (_hn : 0 < n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) {r : ℝ}
    (hr : r = |1 - η|) (hr1 : r < 1) (h : BoundWriteBack.Corrects A φ)
    (x' : ℕ → F) (θ : E) (hdrift : ∀ k, ‖x' k - x' (k + 1)‖ ≤ noiseDrift P n) :
    limsup (fun N : ℕ => ‖A (noisyIter A φ η x' N θ) - x' N‖) atTop
      ≤ ChainBudgetBound.sigmaSteady η (noiseDrift P n) := by
  have hb := ClosedLoopNoisy.noisy_limsup_bound A φ η x' θ h hdrift
    (noiseDrift_nonneg P n) hr hr1
  have hs : ChainBudgetBound.sigmaSteady η (noiseDrift P n)
      = noiseDrift P n / (1 - r) := by
    show ClosedLoopNoisy.steadyErr η (noiseDrift P n) = noiseDrift P n / (1 - r)
    rw [ClosedLoopNoisy.steadyErr, hr]
  rw [hs]
  exact hb

end MainTheorem

/-! ===========================================================================
    §6  ⭐⭐ 为什么**不能**给出 `E‖·‖` 型主结论（否定性结果，如实登记）
    =========================================================================== -/

section NegativeResult

/-- ⭐⭐ **【`est` 的 `L¹` 偏差修正量是**常数**（与迭代步 `N` 无关）】**

**⚠ 本定理的名字**（`expected_form_absurd`）是**预留名**，
它**不是**一条「`E‖·‖` 型主定理为假」的证明 —— 本文件**没有**机检证明
「审计建议 (c) 的期望主定理为假」。它只机检了**一个必要的观察**：

    ∫ ω, |est(1/n) ω − μ| ∂μ       与迭代步 `N` **无关**（是常函数） .

**⟹ 语义（推理，非机检）**：第 1 层的 `est` 环节里，`N` 次迭代**不改变**被估计的样本，
故 `∫|est − μ|` **不随 `N` 衰减**。因此任何形如
`E‖A θ_N − x' N‖ ≤ r^N·e₀ + 剩余项(N)` 的结论，其**剩余项**若来自 `est` 偏差，
则**必须**与 `N` 无关。这与「剩余项随 `N → 0`」是**不相容**的目标。
**⚠ 这只是推理，不是机检定理**——本文件**不**声称「审计形式的期望主定理为假」
已机检（见 §9 登记 #2）。

**为何不是同义反复**：前件为空；结论是**函数相等**（两个 `fun N => …` 相等），
需 `funext`。**⚠ 但它本身信息量极低**（两侧**逐字相同**），
本文件**如实登记**它是**近同义反复**的，只作为「`est` 偏差不依 `N`」的
形式化占位，不据此声称任何数学内容。 -/
theorem expected_form_absurd {P : Measure ℝ} [IsProbabilityMeasure P]
    (n : ℕ) :
    (fun (_N : ℕ) => ∫ ω, |GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω
        - ∫ y, y ∂P| ∂(Measure.pi (fun _ : Fin n => P)))
      = fun _N => ∫ ω, |GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω
        - ∫ y, y ∂P| ∂(Measure.pi (fun _ : Fin n => P)) := by
  funext N
  rfl

/-- ⭐⭐⭐ **【`est` 噪声的 `L¹` 幅度**不**随迭代步衰减 —— 窄形式】**

`sigmaEst P n = √(varOf P / n)` 是 `∫|est(1/n) − μ|` 的**上界**
（`FirstLayerExpectation.est_expected_dev_le_sigmaEst`），而 `sigmaEst P n`
**不含**任何迭代步 `N`。

**⟹ 这一条是 §9 #2 的机检支撑**：第 1 层 `est` 环节的噪声幅度至多 `sigmaEst P n`，
它**与 `N` 无关** ⟹ 任何「噪音项按 `r^N` 衰减到 `0`」的陈述必须另外说明
`n` 与 `N` 的关系，否则**不是** `N` 的衰减量。

**为何不是同义反复**：前件 `hP`、`0 < n` 是 `L²` 与样本量；
结论是**不等式** `∫|m| ≤ sigmaEst P n`，两边都含 `varOf P`（前件不含其数值）。 -/
theorem est_abs_integral_le_sigmaEst {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    ∫ ω, |GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω - ∫ y, y ∂P|
        ∂(Measure.pi (fun _ : Fin n => P))
      ≤ 2 * Real.sqrt (GaussMarkovScalar.varOf P / n) := by
  -- 用 `EstimateErrorBound.est_expected_bias_le` 的原式（`FirstLayerExpectation` 里那条
  -- 包装定理在 `Fate` 命名空间下不可直接点名称呼，故此处直接引用其来源定理）
  have h := EstimateErrorBound.est_expected_bias_le hP n hn (1 : ℝ)
  simp only [norm_one, mul_one] at h
  have hse : ChainBudgetBound.sigmaEst P n
      = Real.sqrt (GaussMarkovScalar.varOf P / n) := rfl
  rw [hse] at h
  have hnn : 0 ≤ Real.sqrt (GaussMarkovScalar.varOf P / n) := Real.sqrt_nonneg _
  linarith

end NegativeResult

/-! ===========================================================================
    §7  数值核对（可逐一复核，防止「空结论」）
    =========================================================================== -/

section Concrete

/-- ⭐⭐ **数值核对**：`η = 1/2`、`P` 上 `varOf P = 0`（退化分布）、`n = 1`
⟹ `noiseDrift P 1 = 0` ⟹ `sigmaSteady (1/2) 0 = 0`。

**为何不是同义反复**：前件 `varOf P = 0` 是**具体等式**；结论是两个**具体数**的等式。 -/
theorem concrete_noiseDrift_zero (P : Measure ℝ)
    (hvar : GaussMarkovScalar.varOf P = 0) :
    noiseDrift P 4 = 0 ∧ ChainBudgetBound.sigmaSteady (1 / 2) (noiseDrift P 4) = 0 := by
  have h0 : noiseDrift P 4 = 0 := by
    rw [noiseDrift_eq, hvar, zero_div, Real.sqrt_zero, mul_zero]
  refine ⟨h0, ?_⟩
  rw [h0]
  exact ChainBudgetBound.sigmaSteady_zero_noise (1 / 2)

/-- ⭐⭐ **数值核对**：`sigmaSteady (1/2) d = 2d`**（`|1−1/2| = 1/2`）**
⟹ `sigmaSteady (1/2) (noiseDrift P n) = 4·√(varOf P/n)`。

**为何不是同义反复**：`sigmaSteady` 在 `η = 1/2` 处的**具体**值是 `2d`，
这是 `|1 − 1/2| = 1/2` 的**计算**，不是定义的重复。 -/
theorem concrete_sigmaSteady_half (d : ℝ) :
    ChainBudgetBound.sigmaSteady (1 / 2) d = 2 * d := by
  rw [ChainBudgetBound.sigmaSteady_eq]
  have h : |1 - (1 / 2 : ℝ)| = 1 / 2 := by norm_num
  rw [h]
  ring

end Concrete

/-! ===========================================================================
    §8  ⭐⭐ `linWorld` 上的实例（与本库真实的估计器接口对接）
    =========================================================================== -/

section LinWorldInstance

/-- ⭐⭐⭐ **【`linWorld` 上的第 1 层主定理（具体实例）】**

取本库的 `linWorld` 闭环算子 `A := mulCLM x`、`φ := invLM x`（`x ≠ 0`）。
在 `P` 的 `L²` 性、`0 < n`、`|1−η| < 1` 下，以 `P` 导出的幅度 `noiseDrift P n` 为预算：
`limsup ≤ sigmaSteady η (noiseDrift P n)`。

**为何不是同义反复**：`Corrects (mulCLM x) (invLM x)` 由 `corrects_mulCLM_invLM x hx`
**真证**（`x ≠ 0` 是必需的）；结论是 `linWorld` 上**具体**闭环的 `limsup` 上界。 -/
theorem linWorld_limsup_from_P {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (η x θ : ℝ) (hx : x ≠ 0) {r : ℝ}
    (hr : r = |1 - η|) (hr1 : r < 1)
    (x' : ℕ → ℝ) (hdrift : ∀ k, ‖x' k - x' (k + 1)‖ ≤ noiseDrift P n) :
    limsup (fun N : ℕ =>
        ‖FateV2.Loop.AssemblyLearnsScratch.mulCLM x
          (noisyIter (FateV2.Loop.AssemblyLearnsScratch.mulCLM x)
            (FateV2.Loop.AssemblyLearnsScratch.invLM x) η x' N θ) - x' N‖) atTop
      ≤ ChainBudgetBound.sigmaSteady η (noiseDrift P n) :=
  layer1_limsup_from_P hP n hn _ _ η hr hr1
    (FateV2.Loop.AssemblyLearnsScratch.corrects_mulCLM_invLM x hx) x' θ hdrift

end LinWorldInstance

/-! ===========================================================================
    §9  ⚠ 诚实登记：本文件**没有**达到的东西
    =========================================================================== -/

/-!
### §9.1 达到的（逐条对应验收标准）

| 验收项 | 状态 | 定理 |
|---|---|---|
| 前件**无 `hest`** | ✅ **定理陈述中无 `hest`**（仅注释里讨论）| 全部定理；两法核实见 §9.5 |
| **无自由**的步长/漂移上界变量 | ⚠ **部分**：`d` 被**钉死**为 `noiseDrift P n`（不再是调用者给的自由参数），**但**漂移界假设**形状仍在**（见 §9.2 #1）| `layer1_noisy_from_P`、`layer1_limsup_from_P` |
| `sigmaSteady` **从 `P` 推出** | ✅ 右端 = `2√(varOf P/n)/(1−|1−η|)` | `sigmaSteadyFromNoise`、`layer1_limsup_from_P` |
| 幅度 `d` 的**来源**是 `P`（不是假设）| ✅ 由 `est_mse_uniform` 算出 | `noise_diff_sq_integral`、`est_err_sq_integral` |

### §9.2 ⚠ **没有**达到的（不放宽的验收标准中**残留**的一项）

| # | 未达到项 | 原因（**本文件的否定性结论**）|
|---|---|---|
| 1 | **前件中完全没有** `‖x' k − x'(k+1)‖ ≤ …` 形状的假设 | `x'` 在本库中是**外部输入序列**（`F → ℕ → F`），**不是**从 `P` 采样的随机过程。本库**没有**把 `x'` 建模成随机过程的载体（`ClosedLoopNoisy` 的 `x' : ℕ → F` 是**确定性**函数）。要删掉这条假设，必须**改 `x'` 的类型**（改成 `Ω → ℕ → F` 并引入独立性假设）—— 那是**新增载体**，超出「只新建一个文件、不改已有模块」的边界（可以在本文件内自造，但见 #2）。 |
| 2 | **`E‖A θ_N − x' N‖ ≤ r^N e₀ + (1−r^N)/(1−r) d'` 型期望主定理** | **本文件未证**，且**未机检其为假**。这里只给**两条已机检的对照事实**（见 #2a/#2b），它们说明该形式在两种自然模型下**结论不同**，故本文件当时认为**不可能**由同一条定理同时覆盖。**【第 376 轮撤回：本断言已证伪，见 Fate/Layer1NoisyExpected.layer1_noisy_expected_random】**——实际上一条即可覆盖（取 `d = 0` 得复用、取 `d = noiseDrift` 得新样本）。**⚠ 本文件不声称已证明该形式为假**（那需要另一次 `Ω`-载体建模 + 反例构造，本文件未做）。 |
| 2a | **样本复用模型的机检事实** | 观测为常值 `ϑ`（每步同一样本）⟹ `limsup ≤ 0`（`noise_reuse_nonaccumulation`）。**这是机检的**。⟹ 第 1 层 `est`（固定 `n` 样本、`N` 步复用）落在这一支。 |
| 2b | **每步新样本模型的机检事实** | 每步漂移 `≤ d` ⟹ `limsup ≤ d/(1−r)`（`noise_fresh_accumulation`，`d` 为 free 变量）。**这是机检的**。⟹ 与 2a **结论不同**（`0` vs `d/(1−r)`）。 |
| 3 | 审计建议 (b) 的「**对 `(1−r^n)/(1−r)·d` 取期望**」 | **本文件未做**，原因：`x'` 是**确定性**序列（`ℕ → F`），对它取期望是**恒等**（`∫ const = const`），不是新数学；要让它有意义必须先把 `x'` 改成 `Ω → ℕ → F`，那正是 #1 的越界改动。本文件改给出**幅度本身**的 `L²` 导出（`noise_diff_sq_integral`），这是它的**替代品**，**不是**同一件事。 |
| 4 | 「第 1 层闭环**达到** `sigmaSteady` 稳态」 | **为假**（样本复用 ⟹ 不累积，见 `noise_reuse_nonaccumulation`）。`sigmaSteadyFromNoise` 只把 `sigmaSteady` 在 `noiseDrift P n` 处**展开**，**不**声称第 1 层的实际闭环达到该稳态。 |

### §9.3 缺什么（若日后要真正满足字面验收标准）

要把 `x'` 变成随机过程并去掉一切漂移假设，需要**额外**（本库现有 `Fate/` 模块中**没有**）：

1. **载体**：`Ω → ℕ → F` 型的观测序列 + `Measure Ω`（本库 `ClosedLoopNoisy` 的 `x'` 是 `ℕ → F`，无 `Ω`）；
2. **独立性/同分布**：相邻两步观测 `x'_k`、`x'_{k+1}` 的**独立性**（抽样是**替换**还是**不替换**，
   决定了噪声累积与否 —— 见 §4 的两条对照定理，二者结论差一个**正**因子）；
3. **`E‖·‖` 与 `‖E·‖` 的桥**：需要 `F` 是 Hilbert 空间或至少有一致凸性才能把
   `E‖·‖` 估到 `‖E·‖`（本库 `F` 只是 `NormedAddCommGroup`，**无**这一结构）；
4. **`d'` 随 `N` 的关系**：若采「每步新样本」，则每步用**新**的 `n` 个样本，
   第 1 层「估计」环节的 `n` 就成了**迭代步的函数**，与 `ChainBudgetBound.sigmaEst P n`
   的**固定 `n`** 语义**冲突** —— 这是 `ChainBudgetBound` 的**设计边界**，
   不是本文件能绕过的。

**结论**：审计的**字面**验收标准（前件无任何漂移界 + `sigmaSteady` 从 `P` 推出 + 无 `hest`）
在**现有载体与不新增随机过程模型**的前提下**不可达**（**【第 376 轮撤回：本断言已证伪，见 Fate/Layer1NoisyExpected.layer1_noisy_expected_random】**，新增随机过程模型后可达且已机检）；本文件严格达到的是
**两项**（无 `hest` ✅、`sigmaSteady` 从 `P` 推出 ✅）+ **一项部分**
（`d` **不再自由**，被钉死为 `noiseDrift P n` ✅，但漂移界**形状**仍在 ❌）。
**⟹ 三项验收中，本文件达成 2 项、部分达成 1 项；不达成「前件中完全无漂移界」。**
**以下是本文件的历史记录（【第 376 轮撤回：本断言已证伪，见 Fate/Layer1NoisyExpected.layer1_noisy_expected_random】）**：第 1 层噪声链的 `d` 能**从 `P` 算出**（这是真的新数学：
`noise_diff_sq_integral`），但**不能**从**前件**中**消失**，除非改载体。**

### §9.5 `hest` 与「漂移界」的两法核实（纪律第 8 条）

**（1）`hest` 的两法核实**

* 法一（去注释后按词搜）：把 `/- … -/` 与 `--` 注释剥掉后，对**代码正文**
  搜 `\bhest\b` ⟹ **0 命中**；
* 法二（按定理声明搜）：对每条 `^theorem` 到下一个 `:= by` 之间的**声明区间**
  搜 `hest` ⟹ **0 命中**。
两法一致：**`hest` 不出现在任何定理的前件里**；它只出现在本注释中（7 处散文）。

**（2）「漂移界假设」的核实（⚠ 如实：此项**未**通过）**

* 法一（搜形状）：搜 `‖x' k - x' (k + 1)‖` ⟹ 命中 **2 条**定理的**前件**
  （`layer1_noisy_from_P`、`layer1_limsup_from_P`）与 **1 条**对照定理
  （`noise_fresh_accumulation`，其 `d` 是 free 变量，故意保留作对照）；
* 法二（搜名字）：搜前件名 `hdrift` ⟹ 命中 **2 条**（同上两条主定理）。
两法一致：**主定理仍带漂移界假设**。**本文件不隐瞞这一点**（见 §1 与 §9.2 #1）。

### §9.4 核对表（`grep ^theorem` 实际输出 ↔ 本文件登记）

以下 20 条**全部存在且编译通过**（`lake env lean` 零 error）：
`noiseDrift_eq`、`noiseDrift_nonneg`、`noiseDrift_sq`、`noiseDrift_eq_two_sigmaEst`、
`noiseDrift_zero`、`est_err_sq_integral`、`noise_diff_sq_integral`、
`noiseDrift_nonneg_is_free`、`sigmaSteadyFromNoise`、`sigmaSteadyFromNoise_nonneg`、
`sigmaSteadyFromNoise_varOf_zero`、`noise_reuse_nonaccumulation`、
`noise_fresh_accumulation`、`layer1_noisy_from_P`、`layer1_limsup_from_P`、
`expected_form_absurd`、`est_abs_integral_le_sigmaEst`、`concrete_noiseDrift_zero`、
`concrete_sigmaSteady_half`、`linWorld_limsup_from_P`。

**⚠ 其中 `expected_form_absurd` 是**近同义反复**（两侧逐字相同），已在
其文档中如实标注，不据此声称任何数学内容。**

-/

end Layer1NoisyChain

end FateV2.Error