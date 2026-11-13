/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.EstimateErrorBound`（**新建**，不修改任何已有模块）

## 0  本文件要回答的问题（审计 R249 第 2 件）

`Fate/FirstLayerBound.lean` 的主定理 `first_layer_bound_real` 已经入库（该文件 21 条
定理），它把第 1 层的 `Ω` 换成了 `linWorld` 上的**具体**端到端残差
`Fate.EndToEnd.e2eResidual`，因此「`Ω` 是自由变量」这一缺陷已经修掉。

但它的前件里还留着一个**未证**的假设：

    hest : ‖θhat − θstar‖ * ‖xhat‖ ≤ ChainBudgetBound.sigmaEst P n

其中 `sigmaEst P n = Real.sqrt (GaussMarkovScalar.varOf P / n)`。
审计的追问是：**`hest` 能否从 Gauss–Markov 推出？**

本文件的回答（定理全部在 §3–§4；**共 10 条**，见 §2 的复核表）：

* **〔均方口径：真定理，但方向要写对〕** 均匀权重 `a ≡ 1/n` 时
  `E(est a − μ)² = varOf P / n`（`est_mse_uniform`，**等式**）；
  任意无偏权重下是 `varOf P / n ≤ E(est a − μ)²`（`est_mse_ge_varOf_div_n`，**下界**）。
  ⚠ 原文件头曾写作「`E‖θ̂ − θ*‖² ≤ varOf P / n`」并引用
  `est_mse_le_varOf_div_n` / `est_bias_sq_le_varOf_div_n` —— **这两个名字不存在**，
  且该不等号方向对非均匀权重**为假**（见 §1.2 与 §2.1）。本段已更正。
* **〔期望口径：真定理〕** `∫|est a − μ|·‖x‖ ≤ √(varOf P/n)·‖x‖`
  （`est_expected_bias_le`，允许 `‖x‖ = 0`）。这是 `hest` 的**期望版**。
  ⚠ 由它**不能**得到 `hest` 原文（逐点版），见下一条。
* **〔逐点口径：数值实例上被反证〕** `n = 1` 时 `est a` 就是那一个观测，
  `single_sample_est_fails` / `hest_not_provable` 给出
  `∀ θ*, ∃ ω, √(1/1) < |est (1) ω − θ*|`。
  ⚠ 该反例的界是**字面常数** `√(1/1) = 1`，**不含** `P` / `varOf`；
  所以它只否定「`varOf = 1, n = 1` 这一个实例上逐点界对所有 `ω` 成立」，
  **不是**「对任意非退化 `P` 逐点界都不成立」的全称定理（§2.2 强度表）。

⚠ **本文件不修改 `Fate/FirstLayerBound.lean`**，
也**不声称** `first_layer_bound_real` 的 `hest` 可被本文件任何定理原文替换。
⚠ **本文件没有**任何「无 `hest` 的第 1 层定理」——原文件头声称的
`first_layer_bound_real_expectation` **不存在**（§2.1）。

## 1  ⚠ 诚实边界（必读，不得含糊）

**1.1 `hest` 的两种读法必须分开，本文件只证其中一种。**

| 读法 | 数学陈述 | 本文件的判定 |
|---|---|---|
| (A) **均方 / 期望** | `varOf P / n ≤ ∫ ω, ‖θ̂ ω − θ*‖² ∂μ`（**下界**，非上界）| **定理**（`est_mse_ge_varOf_div_n`；均匀权重时取等，`est_mse_uniform`）|
| (B) **逐点 / 几乎必然** | `∀ᵐ ω, ‖θ̂ ω − θ*‖ ≤ √(varOf P / n)` | `varOf = 1, n = 1` 实例上**被反证**（`single_sample_est_fails` / `hest_not_provable`）|

`FirstLayerBound.hest` 字面上是**逐点**形式（`‖·‖` 作用在一个具体参数值上），
所以本文件的立场是：**`hest` 原文（逐点读法）没有一般证明，且在 `varOf = 1, n = 1`
的实例上被反例否定**（1.3）。
⚠ 本文件**没有**「以 (A) 为口径的替代第 1 层定理」——
原文件头声称在 §6，但 §6 **不存在**（§2.1）。

**1.2 `varOf P / n` 是`Σ a_i² · varOf P` 的**下确界**，因此 (A) 对**任何**权重 `a` 成立。**

`GaussMarkovScalar.gauss_markov_lower_bound` 说：无偏（`∑ a = 1`）时
`varOf P / n ≤ Var[est a]`。本文件的 `est_mse_ge_varOf_div_n` 与之**同向**
（由 `est_mse_eq_variance` 把均方误差换成方差即得；也即 `Σ a_i² ≥ 1/n`），
而**均方误差** `E(est a − μ)² = Var[est a]`（无偏时等于 `Var` 本身）。⚠ 这两个方向合起来给出的是

    Var[est a] ≥ varOf P / n,

即 `varOf P / n` 是**下界**；而任务描述里写的「`‖θ̂−θ*‖²` 的期望 **≤** `varOf P / n`」
**只在 `a ≡ 1/n`（均匀权重）时成立**（此时取等，`est_mse_uniform`）。
对**非均匀**权重它**反了**：由 `est_variance` 有 `Var[est a] = (Σ aᵢ²)·varOf P`，
取 `n = 2`、`a = (1,0)` 得 `Σ aᵢ² = 1 > 1/2`，故 `Var = varOf P > varOf P/2`
（这是**手算**的说明；本文件**没有**把该数值反例形式化为定理，
原文件头声称的 `concrete_nonuniform_mse` **不存在**）。
故本文件把 (A) 精确地写成**两个**定理：

* `est_mse_uniform`：`a ≡ 1/n` ⟹ `E(est a − μ)² = varOf P / n`（**等式**）；
* `est_mse_ge_varOf_div_n`：无偏 ⟹ `varOf P / n ≤ E(est a − μ)²`（**下界**，任何 `a`）。

**1.3 为什么 `hest` 原文（读法 B）在非退化实例上不成立（本文件只给了 `varOf = 1, n = 1` 的数值见证）。**

在 `n = 1`、`a = 1`（唯一可能的无偏权重）时 `est a = ω 1`，
即估计器**就是那一个观测**。取 `P = N(0,1)`（本文件用 `varOf P = 1` 的参数化），
则 `√(varOf P / 1) = 1`，而 `‖est a ω − θ*‖ = |ω 1 − θ*|` 在 `ω 1` 远离 `θ*` 时 `> 1`。
`single_sample_est_fails` / `hest_not_provable` 把这件事写成**具体数值**定理：
只用到 `Real.sqrt 1 = 1` 与 `est` 在 `n = 1` 上的展开，界是字面常数 `1`。
⚠ **强度边界**：这两条**不**含 `P` / `varOf`，故它们是「`varOf = 1, n = 1` 实例上的反例」，
**不是**「对任意非退化 `P` 逐点界都不成立」的全称定理（见 §2.2 的强度表）。
⚠ **这是本任务「否定结论本身有价值」的那一半**（本件 §1.3 与定理
`single_sample_est_fails` / `hest_not_provable`）。

**1.4 缺什么前提才能把 (A) 升级成 `hest` 原文？**

需要「估计器误差**退化为常数**」，即 `varOf P = 0`（`P` 是点质量）。
⚠ 原文件声称 `mse_zero_imp_varOf_zero` 给出了「逐点为零 ⟹ `varOf P = 0`」，
**但该定理的实际陈述是 `varOf P = 0 → varOf P = 0`（同义反复）**，
**没有**提供任何关于 `varOf P` 的信息（见 §2.2）。
真正的「`∀ᵐ ω, est a ω = μ` ⟹ `varOf P = 0`」本文件**未完成、未声明**，
如实登记在此。

**1.5 本文件不做**：`hest` 的**高概率**版本（Hoeffding/次高斯尾界）。
`Fate/GaussMarkovScalar.lean` 与本地 Mathlib 里只有 Chebyshev
（`ProbabilityTheory.meas_ge_le_variance_div_sq`），它给的是 `1/t²` 型尾界，
不是指数尾界；要 `1 − δ` 型置信界需次高斯性（需要额外假设），
故**未做**，如实登记。本文件**不**声称任何「以概率 `1 − δ`」的界。

**1.6 本文件不做**：估计与学习**共用一个概率模型**。
`hest` 的困难根因是 `FirstLayerBound` §1.2 已登记的「`varOf P` 与 `linWorld` 之间
没有共用的概率模型」。本文件证的是**估计器一侧**（`est a` 在 `Measure.pi` 上）的
均方界；把它接到 `linWorld` 上仍然需要把 `θhat` 认同为 `est a ω`，
这一步是 `FirstLayerBound` §1.2 的外部假设，本文件**未**消除它。

## 2  本文件**实际声明**的定理（写完 `grep ^theorem` 核对过）

§3 均方误差（估计器一侧，`Measure.pi` 上的真定理）—— 7 条
    est_mse_eq_variance           `E(est a − μ)² = Var[est a]`（`variance_eq_integral`）
    est_mse_uniform               ⭐⭐⭐ `a ≡ 1/n` ⟹ `E(est a − μ)² = varOf P / n`（等式）
    est_mse_ge_varOf_div_n        ⭐⭐⭐ 无偏 ⟹ `varOf P / n ≤ E(est a − μ)²`（下界）
    est_bias_abs_le_sqrt_mse      ⚠ **同义反复**（左边为 `|A − A| = 0`），见 §2.2
    est_expected_bias_le          ⭐⭐⭐ 无偏 ⟹ `E‖est a − μ‖·‖x̂‖ ≤ √(varOf P / n)·‖x̂‖`
    est_sigmaEst_eq_sqrt_uniform  ⭐⭐ 均匀权重的标准差**恰是** `sigmaEst P n`
    sigmaEst_zero_varOf           `varOf P = 0` ⟹ `sigmaEst P n = 0`

§4 否定结论（读法 B 为假）—— 3 条
    single_sample_est_fails       ⭐⭐⭐ `n = 1`、`varOf P = 1`：逐点界必在远处失效
    hest_not_provable             ⭐⭐⭐ `∀ θ*, ∃ ω`：误差 > `√(1/1)`（形式化陈述）
    mse_zero_imp_varOf_zero       ⚠ **同义反复**（`v = 0 → v = 0`，恒等映射）

计 **10** 条 `theorem` + 本文件**不新增** `def`（全部复用已有定义）。

### 2.1 【第 269 轮修复登记：原文件头的**虚假声明**已删除】

本文件**接手时编译 7 个 error**（EXIT=1）。修复时发现原文件头声称的
以下内容**在原文件中根本不存在**（属虚假声明，已从本表删除，不再提及）：

* §5「非平凡性」2 条：`concrete_nonuniform_mse`、`concrete_uniform_mse` —— **不存在**；
* §6「无 `hest` 的第 1 层定理」2 条：`e2e_expected_le_of_mse`、
  `first_layer_bound_real_expectation` —— **不存在**；
* 表内引用的 `est_variance_uniform`、`est_mse_le_varOf_div_n` —— **不存在**
  （实际名字是 `est_mse_uniform`、`est_mse_ge_varOf_div_n`）；
* 「计 14 条 theorem」—— 实际是 **10 条**。

⚠ 因此本文件**没有**任何「消除 `hest` 的期望形式第 1 层定理」，
也**没有**任何「非均匀权重的数值反例定理」。下面的 §2.2 是**真实**的复核结果。

### 2.2 【第 269 轮】逐条非平凡性复核（`grep ^theorem` 得 10 条，逐一核对）

真正非平凡（前件不含结论、证明用到实质数学）：

| 定理 | 状态 |
|---|---|
| `est_mse_eq_variance` | ✅ 真：`variance_eq_integral` + `est` 可测性 |
| `est_mse_uniform` | ✅ 真：`est_variance` + `Σ(1/n)² = 1/n` 的算术 |
| `est_mse_ge_varOf_div_n` | ✅ 真：`gauss_markov_lower_bound`（Cauchy–Schwarz）|
| `est_expected_bias_le` | ✅ 真：`est_integral` + `est_mse_uniform` + **Hölder**（本轮修复） |
| `est_sigmaEst_eq_sqrt_uniform` | ✅ 真：`est_variance` + `Σ(1/n)² = 1/n` |
| `sigmaEst_zero_varOf` | ✅ 真（但很浅）：`varOf = 0` 代入定义 |

⚠ **同义反复（前件已把结论包进去），按纪律不改陈述、保留并登记**：

| 定理 | 问题 |
|---|---|
| `est_bias_abs_le_sqrt_mse` | 左边是 `|A − A| = 0`，结论退化为 `0 ≤ √(…)`；`hP` **未被使用** |
| `mse_zero_imp_varOf_zero` | 陈述是 `v = 0 → v = 0`，证明是 `fun h => h`；`hP`、`hμ` **未被使用** |

⚠ **强度受限（成立但比名字暗示的弱）**：

| 定理 | 真实强度 |
|---|---|
| `single_sample_est_fails` | 只比较字面常数 `√(1/1) = 1` 与算出的误差 `2`；**不含任何 `P` / `varOf`** |
| `hest_not_provable` | `∀ θ*, ∃ ω, √(1/1) < |误差|`；是**数值实例**上的否定，**不是**「`hest` 不可由 Gauss–Markov 推出」的全称元数学命题 |

### 2.5 与 `FirstLayerBound.lean` 的关系（如实登记）

* `FirstLayerBound.lean` 的 `first_layer_bound_real` 的 `hest` **未被本文件删除或替换**
  —— 它仍在原文件里、仍是前件（本文件不改已有模块）。
* 本文件**没有**给出任何替代 `hest` 的第 1 层定理（原文件头声称的
  `first_layer_bound_real_expectation` **不存在**，见 §2.1）。
* 本文件对「`hest` 能否由 Gauss–Markov 推出」的贡献**仅限于**：
  `est_mse_uniform` / `est_mse_ge_varOf_div_n`（均方口径）+ Hölder 给
  `est_expected_bias_le`（期望口径），以及 `hest_not_provable`
  在 `varOf = 1, n = 1` 数值实例上的反例。
  **不足以**说「`hest` 被推导出来」或「`hest` 被完全排除」。

## 3  依赖（只 `import`，不改）

`Fate.GaussMarkovScalar`（`varOf`、`est`、`est_variance`、`gauss_markov_lower_bound`、
`variance_coord_pi`、`est_integral`）、
`Fate.ChainBudgetBound`（`sigmaEst`、`sigmaLearn`、`sigmaSteady`、`learnErr_le`、
`e2e_abs_eq`）、
`Fate.ThetaConvergence`（`linWorld`、`thetaN`）、
`Fate.FirstLayerBound`（只用于 `first_layer_bound_real` 的对照，本文件**不**修改它）。

纪律：零 `sorry` / 零 `admit` / 零 `axiom`；只新增本文件，不改任何已有模块。

**【第 269 轮修复记录·7 个 error 全部修好，零 sorry】**

| # | 位置 | 错误 | 修法 |
|---|---|---|---|
| 1 | `est_mse_eq_variance` | `variance_eq_integral` 的参数名不是 `f`（实为 `X`/`hX`） | 改用 `rw [variance_eq_integral]`（唯一参数自动推断）+ 显式给可测性 |
| 2 | 同上 | `est_integral … ▸ AEMeasurable …` 的 `▸` 无效 | 整段删除，改为直接 `rw` + `Finset.aemeasurable_fun_sum` |
| 3 | 同上 | `aemeasurable_finsetSum` **不存在** | 换成 Mathlib 实名 `Finset.aemeasurable_fun_sum` |
| 4 | 同上 | `rw [this]` 找不到模式（`?m` 未实例化） | 先 `have hfun : est a = … := rfl` 再 `rw [hfun]` |
| 5 | `est_mse_uniform` | `field_simp` 后**目标已解**，多出的 tactic 报「No goals」 | 删除多余 tactic |
| 6 | `est_expected_bias_le` | `integral_sq_le_integral_sq_of_memLp` **不存在** | 改用 **Hölder**：`integral_mul_le_Lp_mul_Lq_of_nonneg`（`p=q=2`，`f=|est a − μ|`，`g≡1`），并用 `MemLp`（`memLp_finsetSum` + `coord_memLp`）供给前提 |
| 7 | `est_sigmaEst_eq_sqrt_uniform` | 同 #5（多余 tactic） | 删除多余 tactic |

修复**只动了证明与注释**，10 条定理的**陈述一字未改**；导入的模块也未变。
-/

import FateWorld.Legacy.ChainBudgetBound
import FateWorld.Legacy.ThetaConvergence
import FateWorld.Legacy.GaussMarkovScalar
import FateWorld.Legacy.FirstLayerBound

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Fate
namespace EstimateErrorBound

/-! ===========================================================================
§3  估计器一侧：均方误差 `E(est a − μ)²` 与 `varOf P / n` 的**真**关系
=========================================================================== -/

section MSE

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- ⭐⭐ **【均方误差就是方差】**

$$\int_\omega \bigl(\mathrm{est}\,a\,\omega - \mathbb{E}[\mathrm{est}\,a]\bigr)^2
  \;\partial\mu \;=\; \mathrm{Var}[\mathrm{est}\,a] .$$

这正是 `ProbabilityTheory.variance_eq_integral`（Mathlib 的**定义级**桥），
本文件在此显式引用是为了让 §3 的后续定理都只用「积分形式的均方误差」这一口径。

**为何不是同义反复**：前件是 `hP : MemLp id 2 P`（`n` 只是一个参数，**没有** `0 < n` 前件）；
结论是一条**积分等式**，右边是 `variance`。证明是 `variance_eq_integral`
（`Var[X; μ] = ∫ (X − μ[X])²`）加一步 `est a` 的可测性，
`varOf` / `varOf P / n` / 均方误差的界都**不**出现在前件中。 -/
theorem est_mse_eq_variance (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (a : Fin n → ℝ) :
    ∫ ω, (GaussMarkovScalar.est a ω
        - ∫ ω', GaussMarkovScalar.est a ω' ∂(Measure.pi (fun _ : Fin n => P))) ^ 2
        ∂(Measure.pi (fun _ : Fin n => P))
      = variance (GaussMarkovScalar.est a) (Measure.pi (fun _ : Fin n => P)) := by
  rw [variance_eq_integral]
  have hfun : GaussMarkovScalar.est a = fun ω : Fin n → ℝ => ∑ i, a i * ω i := rfl
  rw [hfun]
  exact Finset.aemeasurable_fun_sum _ fun i _ =>
    (measurable_const.mul (measurable_pi_apply i)).aemeasurable

/-- ⭐⭐⭐ **【均匀权重的均方误差**精确**等于 `varOf P / n`】**

取 `a ≡ 1/n`（即 `est a =` 样本均值），则

$$\int_\omega \bigl(\mathrm{est}\,a\,\omega - \mathbb{E}[\mathrm{est}\,a]\bigr)^2
  \;=\; \frac{\mathrm{varOf}\,P}{n} .$$

这就是本任务要找的「`‖θ̂ − θ*‖²` 的期望 `= varOf P / n`」，
**前提是权重必须均匀**（§1.2 已说明非均匀时 `≥` 而非 `=`）。

**为何不是同义反复**：前件是 `hP`（`L²`）、`0 < n`、`a ≡ 1/n`；
结论是**具体的分式等式**。证明要用 `est_variance`（`Var = (Σ aᵢ²)·v`）
与 `Σᵢ (1/n)² = 1/n` 的算术（`Finset.sum_const` + `field_simp`）。
`varOf P / n` 不出现在任何前件中。 -/
theorem est_mse_uniform (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    ∫ ω, (GaussMarkovScalar.est (fun _ => 1 / (n : ℝ)) ω
        - ∫ ω', GaussMarkovScalar.est (fun _ => 1 / (n : ℝ)) ω'
            ∂(Measure.pi (fun _ : Fin n => P))) ^ 2
        ∂(Measure.pi (fun _ : Fin n => P))
      = GaussMarkovScalar.varOf P / n := by
  rw [est_mse_eq_variance hP n]
  rw [GaussMarkovScalar.est_variance hP n]
  have hsq : ∑ i : Fin n, (1 / (n : ℝ)) ^ 2 = 1 / (n : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hsq]
  field_simp

/-- ⭐⭐⭐ **【无偏估计器的均方误差**不小于** `varOf P / n`】**（任何权重）

$$\frac{\mathrm{varOf}\,P}{n} \;\le\;
  \int_\omega \bigl(\mathrm{est}\,a\,\omega - \mathbb{E}[\mathrm{est}\,a]\bigr)^2 .$$

⚠ **方向说明（本文件最重要的更正）**：任务描述写的是
「`‖θ̂−θ*‖²` 的期望 **≤** `varOf P / n`」。这个方向**对非均匀权重为假**：
`Var[est a] = (Σ aᵢ²)·v`，而 `Σ aᵢ² ≥ 1/n`（Cauchy–Schwarz，无偏时）。
故正确的陈述是 `≥`，本定理给出它；等号只在 `a ≡ 1/n` 时成立（`est_mse_uniform`）。

**为何不是同义反复**：前件是无偏 `∑ a = 1`；结论是「下界」不等式，
证明必须用 Cauchy–Schwarz（`Finset.sum_mul_sq_le_sq_mul_sq`）与
`variance_nonneg`。`Σ aᵢ² ≥ 1/n` 不在前件里。 -/
theorem est_mse_ge_varOf_div_n (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℝ) (hsum : ∑ i, a i = 1) :
    GaussMarkovScalar.varOf P / n
      ≤ ∫ ω, (GaussMarkovScalar.est a ω
          - ∫ ω', GaussMarkovScalar.est a ω' ∂(Measure.pi (fun _ : Fin n => P))) ^ 2
          ∂(Measure.pi (fun _ : Fin n => P)) := by
  rw [est_mse_eq_variance hP n]
  exact GaussMarkovScalar.gauss_markov_lower_bound hP n hn a hsum

/-- ⭐⭐ **【偏差的绝对值 ≤ 均方根误差】**（Jensen / Cauchy–Schwarz）

$$\bigl|\mathbb{E}[\mathrm{est}\,a] - \mu\bigr|
  \;\le\; \sqrt{\int_\omega (\mathrm{est}\,a\,\omega - \mu)^2} .$$

⚠ **【诚实登记·第 269 轮修复时发现】本定理是**同义反复**（前件已把结论包进去）。**
定理陈述写的左边是 `|A − A|`（两处 `∫` 完全相同），因此其值**恒为 `0`**，
结论退化为 `0 ≤ √(…)`，由 `Real.sqrt_nonneg` 一步得证；
前件 `hP`（以及 section 变量 `[IsProbabilityMeasure P]`）**完全没用到**
（编译警告 `Variable name 'hP' is not explicitly referenced` 即为证据）。
按本任务纪律**不改定理陈述**，故保留原样，并在此**明确登记它是同义反复**，
不得据此声称「证出了 Jensen / Cauchy–Schwarz 型的偏差–均方根误差不等式」。
真正的「偏差 ≤ 均方根误差」需要右边是 `√(∫ (est a − μ)²)`、
左边是 `|∫ est a − μ|`（`μ` 为真参数，而**不是** `∫ est a`），
本文件**没有**声明那一条。 -/
theorem est_bias_abs_le_sqrt_mse (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (a : Fin n → ℝ) :
    |∫ ω, GaussMarkovScalar.est a ω ∂(Measure.pi (fun _ : Fin n => P))
        - ∫ ω, GaussMarkovScalar.est a ω ∂(Measure.pi (fun _ : Fin n => P))|
      ≤ Real.sqrt (∫ ω, (GaussMarkovScalar.est a ω
          - ∫ ω', GaussMarkovScalar.est a ω' ∂(Measure.pi (fun _ : Fin n => P))) ^ 2
          ∂(Measure.pi (fun _ : Fin n => P))) := by
  rw [sub_self, abs_zero]
  exact Real.sqrt_nonneg _

/-- ⭐⭐⭐ **【估计器误差的**期望**界：`hest` 的可用替代】**（无偏时）

无偏（`∑ a = 1`）、均匀权重 `a ≡ 1/n` 时

$$\int_\omega \bigl|\mathrm{est}\,a\,\omega - \mu\bigr|\cdot\|x\| \;\le\;
  \sqrt{\frac{\mathrm{varOf}\,P}{n}}\cdot\|x\| ,$$

其中 `μ = ∫ x, x ∂P` 是**真参数**（无偏意味着 `E est a = μ`，
故 `est a ω − μ` 就是**估计误差** `θ̂ − θ*`），
右边正是 `ChainBudgetBound.sigmaEst P n * ‖x‖`。

**⭐ 这就是 `hest` 能立住的那一半**：`hest` 陈述的是**逐点**的
`‖θ̂ − θ*‖‖x‖ ≤ σ_est‖x‖`（§1.3 说它为假），
本定理陈述的是它的**期望**版本 —— 这是**真定理**。

**为何不是同义反复**：前件是 `hP`、`0 < n`、`∑ a = 1`、`a ≡ 1/n`、`0 ≤ ‖x‖`；
结论是**积分不等式**，右端是 `Real.sqrt (varOf P / n) * ‖x‖`。
证明：`est_integral` 给 `E est a = 1 · μ = μ`，
`est_mse_uniform` 给 `E(est a − μ)² = varOf P / n`，
再用 **Hölder**（`integral_mul_le_Lp_mul_Lq_of_nonneg`，`p = q = 2`，
`f = |est a − μ|`、`g ≡ 1`）得
`∫|est a − μ| ≤ (∫1)^{1/2}·(∫(est a−μ)²)^{1/2} = √(varOf P / n)`，
最后乘 `‖x‖ ≥ 0`。`sqrt (varOf P / n) * ‖x‖` 不出现在前件中。

⚠ **注意**：本定理的陈述**没有** `‖x‖ ≠ 0` 的限制，`x = 0` 时两边都是 `0`（真但平凡）；
`‖x‖ > 0` 时才是实质内容。这不是同义反复（左端需要真的用积分估计）。 -/
theorem est_expected_bias_le (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (x : ℝ) :
    ∫ ω, |GaussMarkovScalar.est (fun _ => 1 / (n : ℝ)) ω - ∫ y, y ∂P|
        * ‖x‖ ∂(Measure.pi (fun _ : Fin n => P))
      ≤ ChainBudgetBound.sigmaEst P n * ‖x‖ := by
  -- `E est a = μ`（均匀权重）
  have hsum : ∑ i : Fin n, (1 / (n : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hmean : ∫ ω, GaussMarkovScalar.est (fun _ => 1 / (n : ℝ)) ω
      ∂(Measure.pi (fun _ : Fin n => P)) = ∫ y, y ∂P := by
    rw [GaussMarkovScalar.est_integral hP n, hsum, one_mul]
  -- 均方误差 = `varOf P / n`
  have hmse : ∫ ω, (GaussMarkovScalar.est (fun _ => 1 / (n : ℝ)) ω
      - ∫ y, y ∂P) ^ 2 ∂(Measure.pi (fun _ : Fin n => P))
      = GaussMarkovScalar.varOf P / n := by
    have := est_mse_uniform hP n hn
    rwa [hmean] at this
  -- Cauchy–Schwarz：`∫|f| ≤ √(∫ f²)`
  have hcs : ∫ ω, |GaussMarkovScalar.est (fun _ => 1 / (n : ℝ)) ω - ∫ y, y ∂P|
      ∂(Measure.pi (fun _ : Fin n => P))
      ≤ Real.sqrt (GaussMarkovScalar.varOf P / n) := by
    -- ⚠ 修复记录：原证明引用不存在的 `integral_sq_le_integral_sq_of_memLp`。
    -- 改用 Hölder（`p = q = 2`，`integral_mul_le_Lp_mul_Lq_of_nonneg`）：
    -- 取 `f = |est a − μ|`、`g ≡ 1`，得 `∫|f| ≤ (∫|f|²)^{1/2}·(∫1)^{1/2}`，
    -- 再以 `∫1 = 1`、`|f|² = f²` 整理。
    have hmem : MemLp (fun ω : Fin n → ℝ => GaussMarkovScalar.est (fun _ => 1 / (n : ℝ)) ω
        - ∫ y, y ∂P) 2 (Measure.pi (fun _ : Fin n => P)) := by
      have hE : MemLp (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ))) 2
          (Measure.pi (fun _ : Fin n => P)) := by
        have hfun : GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ))
            = fun ω : Fin n → ℝ => ∑ i, (1 / (n : ℝ)) * ω i := rfl
        rw [hfun]
        exact memLp_finsetSum _ fun i _ =>
          (GaussMarkovScalar.coord_memLp hP n i).const_mul _
      exact hE.sub (memLp_const _)
    have hp : Real.HolderConjugate (2 : ℝ) 2 :=
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have hmem1 : MemLp (fun ω : Fin n → ℝ => |GaussMarkovScalar.est (fun _ => 1 / (n : ℝ)) ω
        - ∫ y, y ∂P|) (ENNReal.ofReal (2 : ℝ)) (Measure.pi (fun _ : Fin n => P)) := by
      simpa using hmem.norm
    have hmem2 : MemLp (fun _ : Fin n → ℝ => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ))
        (Measure.pi (fun _ : Fin n => P)) := memLp_const 1
    have hold := integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := Measure.pi (fun _ : Fin n => P)) hp
      (f := fun ω => |GaussMarkovScalar.est (fun _ => 1 / (n : ℝ)) ω - ∫ y, y ∂P|)
      (g := fun _ => (1 : ℝ))
      (ae_of_all _ fun ω => abs_nonneg _) (ae_of_all _ fun ω => zero_le_one) hmem1 hmem2
    simp only [mul_one] at hold
    have h2 : ∫ ω, |GaussMarkovScalar.est (fun _ => 1 / (n : ℝ)) ω - ∫ y, y ∂P| ^ (2 : ℝ)
        ∂(Measure.pi (fun _ : Fin n => P))
        = ∫ ω, (GaussMarkovScalar.est (fun _ => 1 / (n : ℝ)) ω - ∫ y, y ∂P) ^ 2
            ∂(Measure.pi (fun _ : Fin n => P)) := by
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      show |GaussMarkovScalar.est (fun _ => 1 / (n : ℝ)) ω - ∫ y, y ∂P| ^ (2 : ℝ)
        = (GaussMarkovScalar.est (fun _ => 1 / (n : ℝ)) ω - ∫ y, y ∂P) ^ 2
      rw [Real.rpow_two, sq_abs]
    rw [h2] at hold
    have hone : ∫ _ : Fin n → ℝ, (1 : ℝ) ^ (2 : ℝ) ∂(Measure.pi (fun _ : Fin n => P)) = 1 := by
      simp
    rw [hone, hmse] at hold
    rw [Real.sqrt_eq_rpow]
    simpa using hold
  calc ∫ ω, |GaussMarkovScalar.est (fun _ => 1 / (n : ℝ)) ω - ∫ y, y ∂P| * ‖x‖
        ∂(Measure.pi (fun _ : Fin n => P))
      = (∫ ω, |GaussMarkovScalar.est (fun _ => 1 / (n : ℝ)) ω - ∫ y, y ∂P|
          ∂(Measure.pi (fun _ : Fin n => P))) * ‖x‖ := by
        rw [integral_mul_const]
    _ ≤ Real.sqrt (GaussMarkovScalar.varOf P / n) * ‖x‖ :=
        mul_le_mul_of_nonneg_right hcs (norm_nonneg x)

/-- ⭐⭐ **【均匀权重的标准差**恰是** `sigmaEst`】**

$$\sqrt{\mathrm{Var}\bigl[\mathrm{est}\,(1/n)\bigr]} = \sigma_{est},\qquad
  \sigma_{est} = \sqrt{\mathrm{varOf}\,P / n} .$$

**为何不是同义反复**：前件是 `hP`、`0 < n`、`0 ≤ varOf P`；
结论是**两式合并**的等式：需先 `est_variance` 算出 `Σ(1/n)² = 1/n`，
再 `Real.sqrt` 两边。`sigmaEst` 的**定义体**是 `√(varOf P / n)`，
故最后的 `rfl` 只是名字展开，**前面的方差计算不是**。 -/
theorem est_sigmaEst_eq_sqrt_uniform (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    Real.sqrt (variance (GaussMarkovScalar.est (fun _ => 1 / (n : ℝ)))
        (Measure.pi (fun _ : Fin n => P)))
      = ChainBudgetBound.sigmaEst P n := by
  rw [GaussMarkovScalar.est_variance hP n]
  congr 1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- ⭐ **【零方差时 `sigmaEst` 归零】**：`varOf P = 0` ⟹ `σ_est = 0`。

这是 §1.4 说的**唯一**能让逐点界成立的退化情形。 -/
theorem sigmaEst_zero_varOf (P : Measure ℝ) (n : ℕ)
    (h : GaussMarkovScalar.varOf P = 0) : ChainBudgetBound.sigmaEst P n = 0 := by
  unfold ChainBudgetBound.sigmaEst
  rw [h, zero_div, Real.sqrt_zero]

end MSE

/-! ===========================================================================
§4  否定结论：`hest` 的**逐点**读法（读法 B）**为假**
=========================================================================== -/

section Negative

/-- ⭐⭐⭐ **【单样本估计器的逐点界必然失效】**

取 `n = 1`、`varOf P = 1` 的参数化、以及**任意**真参数 `θ*` 与**任意**候选界 `c`
满足 `c = √(varOf P / 1) = 1`。则存在观测 `ω`（具体地 `ω 0 = θ* + 2`）使

$$\bigl|\mathrm{est}\,(1)\,\omega - \theta^*\bigr| = 2 > 1 = \sqrt{\mathrm{varOf}\,P/1} .$$

也就是说：**在 `n = 1` 时，`est a` 就是那一个观测本身**，它可以任意远离真值；
故「逐点 `‖θ̂ − θ*‖ ≤ σ_est`」**不是** `n = 1` 上的定理。

**为何不是同义反复**：≤ 的一方是字面量 `√(1/1)`，另一边是**真正算出的**估计器误差
`|est (1) (θ*+2) − θ*| = |θ*+2 − θ*| = 2`（`est` 在 `n = 1` 上就是那一个观测），
证明需要展开 `est`（`simp [GaussMarkovScalar.est]`）与绝对值，不是恒等映射。

⚠ **【诚实登记·第 269 轮】本定理的**强度边界**（不得夸大）**：
结论里的界是**字面常数** `√(1/1) = 1`，**不**含任何 `P` 或 `varOf P`。
因此它刻画的是「`varOf P = 1`、`n = 1` 这一个数值实例上，逐点界不可能对**所有**观测成立」，
**不是**「对任意 `P` 的逐点界不成立」。
形式化一条**任意** `P` 的否定需要「存在 `P` 使 `varOf P = 1` 且逐点界被破坏」，
本条只给出了 `varOf = 1` 那一侧的数值见证（`P` 的存在性由 `varOf` 的像覆盖 1 得到，
本文件**未**形式化这一步）。 -/
theorem single_sample_est_fails (θstar : ℝ) :
    Real.sqrt ((1 : ℝ) / 1) < |GaussMarkovScalar.est (fun _ : Fin 1 => (1 : ℝ))
        (fun _ : Fin 1 => θstar + 2) - θstar| := by
  have hest : GaussMarkovScalar.est (fun _ : Fin 1 => (1 : ℝ))
      (fun _ : Fin 1 => θstar + 2) = θstar + 2 := by
    simp [GaussMarkovScalar.est]
  rw [hest]
  have h2 : θstar + 2 - θstar = 2 := by ring
  rw [h2, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  norm_num

/-- ⭐⭐⭐ **【`hest` 原文**没有**关于 `P` 的一般证明】**（形式化否定）

对任意 `θstar : ℝ` 都存在一个具体的观测向量，使**单样本**估计器
`est (fun _ => 1)` 的输出与真值之差的绝对值**严格大于** `√(varOf P / 1)` 的
**下界值尺度** `√(1/1) = 1`。

**这条定理的作用**：它是「`hest` 不能在 `varOf P = 1`、`n = 1` 的实例上被逐点满足」的
**形式化证据**（§1.3）：Gauss–Markov 只约束**方差**（二阶矩），
而 `hest` 要求的是**逐点**（几乎必然）界；后者在该实例上被本定理否定。

**为何不是同义反复**：前件只有 `θstar : ℝ`（真参数可以任意取）；
结论是「存在观测使误差 > 界」。`single_sample_est_fails` 给出**对每个 `θstar`**
的结论，本定理把它打包成 `∃`。

⚠ **【诚实登记·第 269 轮】强度边界（本任务是「否定性定理」，必须报准）**：
本定理是 `∀ θstar, ∃ ω, √(1/1) < |误差|`，即「**该数值实例上**逐点界对所有 `ω` 不成立」。
它**没有**形式化成「`hest` 不可由 Gauss–Markov 推出」的**全称元数学命题**
（那需要把「可推导」形式化编码，超出本文件范围）。
因此引用本定理时只能说：
「在 `varOf P = 1`、`n = 1` 这一族实例上，`hest` 的逐点形式被反例否定」，
**不能**说「本文件证明了 `hest` 在任何意义下都不可证」。
本文件**没有**删除、也没有弱化`FirstLayerBound.hest`，它仍是那条定理的前件。 -/
theorem hest_not_provable :
    ∀ θstar : ℝ, ∃ ω : Fin 1 → ℝ,
      Real.sqrt ((1 : ℝ) / 1)
        < |GaussMarkovScalar.est (fun _ : Fin 1 => (1 : ℝ)) ω - θstar| :=
  fun θstar => ⟨fun _ => θstar + 2, single_sample_est_fails θstar⟩

/-- ⭐⭐ **【逐点为零 ⟹ `varOf P = 0`】**（(A) ⟹ (B) 只差退化情形）

若估计器的偏差**逐点**为零（相对真均值 `μ`），则单样本方差 `varOf P = 0`。

⚠ **【诚实登记·第 269 轮修复时发现】本定理是**同义反复**（前件即结论）。**
定理的结论位写作 `varOf P = 0 → varOf P = 0`，证明是恒等函数 `fun h => h`；
前件 `hP`、`hμ` 以及 `[IsProbabilityMeasure P]` 全部**没用到**
（编译警告 `Variable name 'hP' / 'hμ' is not explicitly referenced` 即为证据）。

上面原来的那段说明（「逐点零 ⟹ `varOf P = 0`」的一般证明）是**思考残留**：
它描述的**不是**本定理的陈述，本文件**没有**声明那条一般结论。

按本任务纪律**不改定理陈述**，故保留原样并在此登记：
本定理**不提供**任何关于 `varOf P` 的信息，**不得**引用它。
真正需要的「`∀ᵐ ω, est a ω = μ` ⟹ `varOf P = 0`」
（需要 `variance_eq_zero_iff` 的 a.e. 常数刻画 + `est_variance` 反解）
本文件**未完成、未声明**，如实登记在此。 -/
theorem mse_zero_imp_varOf_zero {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (hμ : ∫ y, y ∂P = 0) :
    GaussMarkovScalar.varOf P = 0 → GaussMarkovScalar.varOf P = 0 := fun h => h

end Negative

end EstimateErrorBound
end Fate
