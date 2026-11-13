/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.ChainBudgetBound`（**新建**，不修改任何已有模块）

## 0 本文件要解决的问题（承第 205 轮自查）

第 205 轮自查对 `Fate/ChainErrorBudget.lean` 的主定理给出判定：

```lean
theorem chain_end_to_end_from_links {σ_est σ_learn σ_steady εbest : ℝ}
    {E' : Type u} [NormedAddCommGroup E']
    (Ω₁ Ω₂ Ω₃ : E')                                    -- ⚠ 任意向量
    (h₁ : ‖Ω₁‖ ≤ σ_est) (h₂ : ‖Ω₂‖ ≤ σ_learn) (h₃ : ‖Ω₃‖ ≤ σ_steady) :
    IsOptimalGap (σ_est + σ_learn + σ_steady) (εbest + ‖Ω₁ + Ω₂ + Ω₃‖) εbest
```

`Ω₁ Ω₂ Ω₃` 是**任意**向量，与 `GaussMarkovScalar` / `OptimalEta` /
`ClosedLoopNoisy` 的任何具体对象都**没有联系**；证明只是 `norm_add_le` 用两次。
故那条主定理**没有触及世界模型的任何具体环节**，是纯泛函分析。

**本文件做真正绑定的版本**：在**具体 `WorldModel` 实例**
`Fate.ThetaConvergence.linWorld`（机制 `predFrom = θ * x`）上，用三个模块的
**具体定义**构造误差分量，并证明 `linWorld` 的端到端残差不超过其预算之和。

## 0.1 ⚠ 修复记录（本轮：使本文件零 error / 零 sorry）

本文件接手时 **5 error**（另加 1 处 `sigmaSteady_is_noisy_bound` 的参数错位）。
逐条处置如下：

| # | 位置 | 性质 | 处置 |
|---|---|---|---|
| 1 | `learnErr_le` 末 `rfl` | `‖1−η‖ = c(η)` 是定义等号但 `rfl` 在 `norm_pow` 后不闭合 | 补 `have hc : ‖1−η‖ = OptimalEta.c η := by rw [Real.norm_eq_abs]; rfl`，再 `rw [hc]` |
| 2 | `chain_end_to_end_bound` 的 `nlinarith`/`abs` 层收尾 | 战术可用性 | 见下（保持原 `abs` 层写法，已通过） |
| 3 | `sigmaSteady_is_noisy_bound` `rw [sigmaSteady, ← hr]` | `sigmaSteady` 是不可归约 `def`，`rw` 找不到模式 | 改为 `have hs : sigmaSteady η d = d / (1 − r) := by show ClosedLoopNoisy.steadyErr η d = d/(1−r); rw [ClosedLoopNoisy.steadyErr, hr]`，再 `rw [hs]` |
| 4 | `chain_end_to_end_bound_steer` 的 `calc` 末步 | **数学错误（非同义反复的反面：结论比前件弱得不成立）** | **整条删除**（见下） |
| 5 | `chain_end_to_end_bound_full` | 依赖 #4 | **整条删除** |

**关于 #4（诚实登记）**：`chain_end_to_end_bound_steer` 的结论是

    |e2eResidual(·; x)| ≤ σ_est + σ_learn + σ_steer ,

但它的前件 `hsteer` 只给转向项上界 `σ_learn + σ_steer`。与 §5 主定理的
`σ_est + σ_learn` 相加，得到 `σ_est + 2·σ_learn + σ_steer`，**严格大于**结论。
即**该定理在给定前件下不可证**（不是战术问题，是命题为假/不可达）。
按纪律「证不出就删定理并在文件头说明」，本文件**删除** `chain_end_to_end_bound_steer`
与依赖它的 `chain_end_to_end_bound_full`，**不**用 `sorry` 占位，**不**改动其余定理陈述。

## 1 链条的具体形状（**为何三项能进同一条不等式**）

在 `linWorld` 上，参数轨迹 `θ_n := thetaN η θ* x̂ θ̂ n` 是
`EndToEnd.endToEndIter` 的**同一个**对象（`endToEndIter_eq_thetaN`，`rfl`）。
把「真值」拆成三步：

```
θ*  ──①估计──▶  θ̂      （估计环节：θ̂ 是估计器输出，误差 ≤ σ_est）
θ̂   ──②学习──▶  θ_n     （学习环节：θ_n − θ̂ = (1−η)^n(θ̂ − θ̂)，偏差 ≤ σ_learn）
θ_n ──③转向──▶  θ̂ 方向的预测块 → 端到端残差
```

于是**参数空间**里的三角不等式

    ‖θ_n − θ*‖ ≤ ‖θ_n − θ̂‖ + ‖θ̂ − θ*‖

把「学习误差」与「估计误差」**真的**加到一起，再乘上 `‖x̂‖` 就得到
`linWorld` 的**端到端残差** `|e2eResidual|`。**这不是任意向量**：

* `‖θ_n − θ̂‖` 由 `ThetaConvergence.thetaN_closed` + `OptimalEta.c` 给出
  `c(η)^n ‖θ̂ − θ̂₀‖`（`σ_learn`，**精确**值，§4 `learnErr_eq_exact`）；
* `‖θ̂ − θ*‖` 由估计器给出（`σ_est`，§3 `est_bound`，`GaussMarkovScalar` 的真实载体）；
* `‖x̂‖` 是 `linWorld` 的**具体**预测块（§4 `linWorld_errA_thetaN`）。

`σ_steer := |η|·‖θ₀‖·‖x̂ − x‖`（`sigmaSteer`）描述了 `endToEndIter` 的**设计点** `x̂`
与**评估点** `x` 不同时的转向摩擦，本文件**保留该定义**，但其**端到端界的定理已删除**
（§0.1 #4：给定前件下结论不可达）。**本文件不声称**任何含 `σ_steer` 的端到端不等式。

## 2 本文件**实际声明**的定理（与下文逐一对应；无宣传溢出）

§2 记号与定义
    sigmaEst / sigmaLearn / sigmaSteer / sigmaSteady（四个**具体**定义）
    errA_eq_norm              `errA A x' θ = ‖A θ − x'‖`
    idCLM_apply               `idCLM u = u`（`idCLM := ContinuousLinearMap.id ℝ ℝ`）
    linWorld_predFrom'        `predFrom linWorld θ u ε a x = θ * x`（引用，核实例同一）

§3 估计环节（`σ_est` 真的绑定到 `GaussMarkovScalar` 的一个估计器上）
    sigmaEst_nonneg           `0 ≤ σ_est`
    est_ptwise_cauchy         `|∑ aᵢωᵢ| ≤ √(∑aᵢ²)·√(∑ωᵢ²)`（Cauchy–Schwarz）
    est_err_exact             ⭐ 均匀权重 `a ≡ 1/n` 使 `Var[est a] = σ_est²`**精确**成立
    est_bound                 ⭐ `|est a ω| ≤ σ`（`ω = w`）⟹ `‖est a ω‖‖x‖ ≤ σ‖x‖`
    est_zero_obs              `est a (0) = 0`（零观测）
    est_bound_zero_obs        零观测下 `‖est a 0‖·‖x‖ ≤ 0`

§4 学习环节（`errA` / `thetaN` / `c` 三者真的对齐）
    linWorld_errA_thetaN      `errA id (θ̂·x̂) (θ_n·x̂) = ‖θ_n − θ̂‖·‖x̂‖`
    learnErr_eq_exact         ⭐⭐⭐ `θ_n − θ̂ = (1−η)^n(θ̂₀ − θ̂)`（`thetaN_closed` 引用）
    learnErr_le               ⭐⭐⭐ `‖θ_n − θ̂‖‖x̂‖ ≤ σ_learn`

§5 端到端（**主定理**，在 `linWorld` 上）
    e2eResidual_eq            `e2eResidual linWorld (θ̂·x̂) θ_n … x̂ = θ̂·x̂ − θ_n·x̂`
    e2e_abs_eq                `|e2eResidual| = ‖θ_n − θ̂‖·‖x̂‖`（**等式**，不是界）
    chain_end_to_end_bound    ⭐⭐⭐⭐⭐ **主定理**：
                              `|e2eResidual| ≤ σ_est + σ_learn`（`x̂` 为评估点）

§6 稳态环节（`σ_steady` 不是装饰）
    sigmaSteady_eq            `σ_steady = d / (1 − |1−η|)`
    sigmaSteady_nonneg        `0 ≤ d`、`|1−η| < 1` ⟹ `0 ≤ σ_steady`
    sigmaSteady_zero_noise    `σ_steady η 0 = 0`
    sigmaSteady_is_noisy_bound ⭐ `σ_steady` **确实**是 `noisyIter` 的 `limsup` 上界
                              （`ClosedLoopNoisy.noisy_limsup_bound` 的直接应用）

§7 坍缩与非平凡性
    learn_tendsto_zero        `c(η) < 1` ⟹ `σ_learn` 型序列 `→ 0`
    sigmaLearn_eta_one        `η = 1`、`n ≥ 1` ⟹ 学习分量 `= 0`
    chain_end_to_end_bound_eta_one `η = 1`、`n ≥ 1` 时主定理坍缩为 `≤ σ_est + 0`

## 3 ⚠ 诚实边界（必读，不得含糊）

**3.1 `σ_est` 与 `linWorld` 之间**没有**共用的概率模型。**
`σ_est := √(varOf P / n)` 的量纲来自 `GaussMarkovScalar` 的载体
（`P` 上 `n` 个 iid 观测、线性估计器 `est a`；`est_err_exact` 证明它恰是
`est (1/n)` 的标准差）；`linWorld` 是**单**设计点的线性世界，**无**概率结构。
本文件的接法是**外部假设** `hest : ‖θ̂ − θ*‖·‖x̂‖ ≤ σ_est`（§5 主定理前件）：
把估计器输出的误差**当成** `linWorld` 参数的初值误差。**这不是定理。**
本文件**不声称**估计与学习共用一个概率模型。

**3.2 转向项（`σ_steer`）的相关定理已删除（见 §0.1）。**
原 `chain_end_to_end_bound_steer` 用外部前件
`hsteer : ‖θ_n − θ*‖·‖x̂ − x‖ ≤ (σ_learn + σ_steer)/|η|·|η| = σ_learn + σ_steer`
供给转向项，再与 §5 主定理的 `σ_est + σ_learn` 相加。该定理**不可证**：
转向项上界是 `σ_learn + σ_steer`，相加得 `σ_est + 2·σ_learn + σ_steer`，
**严格大于**结论要求的 `σ_est + σ_learn + σ_steer`（当 `σ_learn > 0`）。
本文件**不声称**任何含 `σ_steer` 的端到端界。要证它需要关于 `‖θ_n‖`
（绝对位置，而 `thetaN_closed` 只给偏离）的独立界，本文件未做。

**3.3 稳态项 `σ_steady` 度量的是**另一条**迭代。**
`σ_steady = ClosedLoopNoisy.steadyErr η d` 是 `noisyIter`（每步观测漂移 ≤ d）的
稳态上界；`linWorld` 的 `endToEndIter` 是**自治**的（常数观测）。二者**不是同一条迭代**。
原 `chain_end_to_end_bound_full` 试图把 `σ_steady` 作为**附加的**预算分量加上去，
但它依赖已删除的 `chain_end_to_end_bound_steer`（§0.1），故一并删除。
`sigmaSteady_is_noisy_bound` **保留**：它证明 `σ_steady` 确实是那条噪声闭环的
`limsup` 上界（**不是**装饰），且 `d = 0` 时 `σ_steady = 0`（`sigmaSteady_zero_noise`）。
**本文件不声称** `σ_steady` 是 `linWorld` 误差的必然部分，也不声称含稳态项的全量端到端界。

**3.4 `linWorld` 的机制是线性的**（`θ·x`），不是任意非线性世界。
非线性机制下一步收缩律为假（`ThetaConvergence` §1.1 已登记）。本文件不声称非线性。

**3.5 本文件不做**：`GaussMarkov` 的非线性/对称推广（`GaussMarkovScalar` 登记 1、2）；
`Corrects` 失效时的最优 `η`（`OptimalEta` §9.2）；`σ_learn` 的紧性改善。

## 4 依赖

`Fate.GaussMarkovScalar`、`Fate.OptimalEta`、`Fate.ClosedLoopNoisy`、
`Fate.ThetaConvergence`、`Fate.EndToEndError`、`Fate.EndToEnd`

纪律：零 `sorry` / 零 `admit` / 零 `axiom`；只新增本文件，不改任何已有模块。
-/

import FateWorld.Legacy.GaussMarkovScalar
import FateWorld.Legacy.OptimalEta
import FateWorld.Legacy.ClosedLoopNoisy
import FateWorld.Legacy.ThetaConvergence
import FateWorld.Legacy.EndToEndError

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Fate
namespace ChainBudgetBound

universe u

/-! ===========================================================================
§2  记号：四个分量的**具体**定义
=========================================================================== -/

/-- ⭐ **估计误差** `σ_est := √(varOf P / n)`（Gauss–Markov 标量下界的尺度）。

§3 `est_err_exact` 证明它**恰好**是均匀权重估计器 `est (1/n)` 的标准差。 -/
noncomputable def sigmaEst (P : Measure ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (GaussMarkovScalar.varOf P / n)

/-- ⭐ **学习误差** `σ_learn := c(η)^n · ‖θ̂₀ − θ̂‖ · ‖x̂‖`
（`c = OptimalEta.c`；`θ̂` 是估计器输出，`θ̂₀` 是学习初值）。
§4 `learnErr_le` 证明它就是 `errA id (θ̂·x̂)` 在 `n` 步后的上界。 -/
noncomputable def sigmaLearn (η θhat xhat θ₀ : ℝ) (n : ℕ) : ℝ :=
  OptimalEta.c η ^ n * ‖θ₀ - θhat‖ * ‖xhat‖

/-- ⭐ **转向摩擦** `σ_steer := |η| · ‖θ₀‖ · ‖x̂ − x‖`
（`x̂` 是 `endToEndIter` 实际使用的设计点，`x` 是端到端误差的评估点）。 -/
noncomputable def sigmaSteer (η θ₀ xhat x : ℝ) : ℝ :=
  |η| * ‖θ₀‖ * ‖xhat - x‖

/-- ⭐ **稳态误差** `σ_steady := ClosedLoopNoisy.steadyErr η d = d / (1 − |1−η|)`。 -/
noncomputable def sigmaSteady (η d : ℝ) : ℝ := ClosedLoopNoisy.steadyErr η d

/-- ⭐ `errA A x' θ = ‖A θ − x'‖`（`BoundWriteBack.errA` 的定义展开）。 -/
theorem errA_eq_norm {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F) (x' : F) (θ : E) :
    BoundWriteBack.errA A x' θ = ‖A θ - x'‖ := rfl

/-- ⭐ `id` 作为**连续**线性映射 `ℝ →L[ℝ] ℝ`（本文件 `errA` 的载体）。 -/
noncomputable def idCLM : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

/-- ⭐ `idCLM` 就是恒等函数。 -/
@[simp] theorem idCLM_apply (u : ℝ) : idCLM u = u := rfl

/-- ⭐⭐ **`linWorld` 的预测块就是 `θ * x`**（引用 `ThetaConvergence.linWorld_predFrom`，
确保本文件用的是**同一个**实例，没有另造预测器）。 -/
theorem linWorld_predFrom' (θ : ℝ) (u ε a : PUnit) (x : ℝ) :
    Fate.EndToEnd.predFrom ThetaConvergence.linWorld θ u ε a x = θ * x :=
  ThetaConvergence.linWorld_predFrom θ u ε a x

/-! ===========================================================================
§3  估计环节：`σ_est` 绑定到 `GaussMarkovScalar` 的一个**具体**估计器
=========================================================================== -/

section Estimate

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- ⭐ `0 ≤ σ_est`。 -/
theorem sigmaEst_nonneg (n : ℕ) : 0 ≤ sigmaEst P n := Real.sqrt_nonneg _

/-- ⭐⭐ **Cauchy–Schwarz（有限和）**：`|∑ᵢ aᵢωᵢ| ≤ √(∑ᵢ aᵢ²)·√(∑ᵢ ωᵢ²)`。

**为何不是同义反复**：前件为空；结论是 `Finset.sum_mul_sq_le_sq_mul_sq` 的
平方根形式（`Real.sqrt_le_sqrt` + `Real.sqrt_mul` + `Real.sqrt_sq_eq_abs`）。
本引理是 §3 两条估计引理的桥。 -/
theorem est_ptwise_cauchy (n : ℕ) (a ω : Fin n → ℝ) :
    |∑ i, a i * ω i| ≤ Real.sqrt (∑ i, (a i) ^ 2) * Real.sqrt (∑ i, (ω i) ^ 2) := by
  have hcs : (∑ i, a i * ω i) ^ 2 ≤ (∑ i, (a i) ^ 2) * (∑ i, (ω i) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset (Fin n))) a ω
  have hnn : 0 ≤ ∑ i, (a i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc |∑ i, a i * ω i| = Real.sqrt ((∑ i, a i * ω i) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt ((∑ i, (a i) ^ 2) * (∑ i, (ω i) ^ 2)) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (∑ i, (a i) ^ 2) * Real.sqrt (∑ i, (ω i) ^ 2) := Real.sqrt_mul hnn _

/-- ⭐⭐⭐⭐ **【估计环节核心：`σ_est` 被均匀权重**精确**达到】**

对任意 `n > 0` 存在**具体的**权重 `a : Fin n → ℝ`（即 `a ≡ 1/n`），使得

$$\sum_i a_i = 1 \quad\text{（无偏）}
\qquad\text{且}\qquad
\mathrm{Var}\bigl[\mathrm{est}\,a\bigr] = \sigma_{est}^2 .$$

**这是 `σ_est` 与 `GaussMarkovScalar` 的**唯一**接口**：
`σ_est` 不是自由参数，它是**某个可写下的**线性估计器的标准差。
证明引用 `gauss_markov_attained`（无偏 + 方差取到 `varOf P / n`），
再用 `Real.sq_sqrt` 换成 `σ_est²`。

**为何不是同义反复**：前件只有 `hP`（`L²`）与 `n > 0`；结论是
**存在**一个权重向量并满足两条**等式**。`a ≡ 1/n` 的具体选择与方差闭式都不在前件中。 -/
theorem est_err_exact (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    ∃ a : Fin n → ℝ,
      (∑ i, a i = 1) ∧
      variance (GaussMarkovScalar.est a) (Measure.pi (fun _ : Fin n => P))
        = sigmaEst P n ^ 2 := by
  have hat := GaussMarkovScalar.gauss_markov_attained hP n hn
    (fun _ => 1 / (n : ℝ)) (fun _ => rfl)
  refine ⟨fun _ => 1 / (n : ℝ), hat.1, ?_⟩
  rw [hat.2, sigmaEst, Real.sq_sqrt]
  exact div_nonneg (variance_nonneg _ _) (Nat.cast_nonneg n)

/-- ⭐⭐⭐ **【估计器输出 → 学习初值误差】**

若估计器在观测 `w` 上的输出误差有界 `|est a w| ≤ σ`，则乘上 `‖x‖` 后

$$\bigl|\,\mathrm{est}\,a\,w\,\bigr|\cdot\|x\| \;\le\; \sigma\cdot\|x\| .$$

**这是链条真正接线的一步**：`σ_est` 从「估计标准差」进入「学习初值的参数误差」。

**为何不是同义反复**：前件是 `|est a w| ≤ σ` 与 `0 ≤ ‖x‖`（乘法单调性需要后者）；
结论是同一个界乘 `‖x‖`。`‖x‖ ≥ 0` 不是装饰——去掉它结论为假。 -/
theorem est_bound {n : ℕ} (a w : Fin n → ℝ) (σ x : ℝ)
    (hbound : |GaussMarkovScalar.est a w| ≤ σ) :
    ‖GaussMarkovScalar.est a w‖ * ‖x‖ ≤ σ * ‖x‖ :=
  mul_le_mul_of_nonneg_right (by rwa [Real.norm_eq_abs]) (norm_nonneg x)

/-- ⭐ **估计器在零观测上的输出为零**（供构造性实例使用）。 -/
theorem est_zero_obs {n : ℕ} (a : Fin n → ℝ) :
    GaussMarkovScalar.est a (fun _ => (0 : ℝ)) = 0 := by
  simp [GaussMarkovScalar.est]

/-- ⭐ 零观测下估计器误差为 `0`，故 `σ_est` 型的界自动成立。 -/
theorem est_bound_zero_obs {n : ℕ} (a : Fin n → ℝ) (x : ℝ) :
    ‖GaussMarkovScalar.est a (fun _ => (0 : ℝ))‖ * ‖x‖ ≤ 0 * ‖x‖ := by
  rw [est_zero_obs, norm_zero, zero_mul]

end Estimate

/-! ===========================================================================
§4  学习环节：`errA` / `thetaN` / `c` 三者真的对齐
=========================================================================== -/

open ThetaConvergence

/-- ⭐⭐⭐ **【学习误差的载体就是 `BoundWriteBack.errA`】**

在 `linWorld` 上，参数轨迹 `θ_n := thetaN η θ̂ x̂ θ̂₀ n` 的参数侧误差

$$\mathrm{errA}\;\mathrm{id}\;(\hat\theta\cdot\hat x)\;(\theta_n\cdot\hat x)
  = \|\theta_n - \hat\theta\|\cdot\|\hat x\| .$$

**为何不是同义反复**：左边是 `BoundWriteBack` 的误差泛函 `‖A θ − x'‖`
在 `A = id`、`x' = θ̂·x̂` 上的求值；右边是 `thetaN` 的绝对偏差乘 `‖x̂‖`。
等号把 `BoundWriteBack` 与 `ThetaConvergence` 两个**不同模块**的对象接起来，
是 §5 主定理能把 `thetaN_closed` 用在 `linWorld` 端到端残差上的前提。 -/
theorem linWorld_errA_thetaN (η θhat xhat θ₀ : ℝ) (n : ℕ) :
    BoundWriteBack.errA idCLM (θhat * xhat)
        (thetaN η θhat xhat θ₀ n * xhat)
      = ‖thetaN η θhat xhat θ₀ n - θhat‖ * ‖xhat‖ := by
  rw [errA_eq_norm]
  have h : idCLM (thetaN η θhat xhat θ₀ n * xhat) - θhat * xhat
      = (thetaN η θhat xhat θ₀ n - θhat) * xhat := by
    simp only [idCLM_apply]; ring
  rw [h, norm_mul]

/-- ⭐⭐⭐ **【学习环节的精确闭式：`thetaN_closed` 的引用】**

$$\theta_n - \hat\theta \;=\; (1-\eta)^n\,(\hat\theta_0-\hat\theta).$$

**为何不是同义反复**：前件只有 `x̂ ≠ 0`（`thetaN` 的更新律只在设计点非零时
良定义，见 `ThetaConvergence` §1.3）；结论是**轨迹偏差的闭式**。
`x̂ ≠ 0` 与 `θ_n − θ̂ = (1−η)^n(θ̂₀−θ̂)` 是完全不同的陈述，
后者由 `ThetaConvergence.thetaN_closed` 证得（那里的归纳用了 `linWorld_endToEnd_step`）。 -/
theorem learnErr_eq_exact (η θhat xhat θ₀ : ℝ) (hx : xhat ≠ 0) (n : ℕ) :
    thetaN η θhat xhat θ₀ n - θhat = (1 - η) ^ n * (θ₀ - θhat) :=
  thetaN_closed η θhat xhat θ₀ hx n

/-- ⭐⭐⭐⭐ **【学习误差 ≤ `σ_learn`】**

$$\bigl\|\theta_n-\hat\theta\bigr\|\cdot\|\hat x\|
  \;\le\; c(\eta)^n\cdot\bigl\|\hat\theta_0-\hat\theta\bigr\|\cdot\|\hat x\|
  \;=\; \sigma_{learn} .$$

**（等式成立，故`≤` 是精确的；本文件只声明 `≤` 以便下游替换。）**

**为何不是同义反复**：结论左边是 `linWorld` 的 `errA` 求值（经
`linWorld_errA_thetaN`），右边是 `sigmaLearn` 的定义（含 `OptimalEta.c`）。
证明链：`errA` 展开 → `thetaN_closed` → `‖(1−η)^n‖ = |1−η|^n = c(η)^n`（`c` 的定义）。
`c(η)^n` 与初值都不在前件中。 -/
theorem learnErr_le (η θhat xhat θ₀ : ℝ) (hx : xhat ≠ 0) (n : ℕ) :
    ‖thetaN η θhat xhat θ₀ n - θhat‖ * ‖xhat‖
      ≤ sigmaLearn η θhat xhat θ₀ n := by
  rw [learnErr_eq_exact η θhat xhat θ₀ hx n, sigmaLearn]
  rw [norm_mul, norm_pow]
  have hc : ‖1 - η‖ = OptimalEta.c η := by rw [Real.norm_eq_abs]; rfl
  rw [hc]

/-! ===========================================================================
§5  端到端主定理
=========================================================================== -/

/-- ⭐⭐ **【`e2eResidual` 在 `linWorld` 上的展开】**

$$\mathrm{e2eResidual}\ \mathrm{linWorld}\ (\hat\theta\hat x)\ \theta_n\ \dots\ \hat x
  = \hat\theta\hat x - \theta_n\cdot\hat x .$$

引用 `EndToEnd.e2eResidual_def` 与 `linWorld_predFrom`（**同一实例**的预测块）。 -/
theorem e2eResidual_eq (θhat θn xhat : ℝ) :
    Fate.EndToEnd.e2eResidual ThetaConvergence.linWorld (θhat * xhat) θn
        PUnit.unit PUnit.unit PUnit.unit xhat
      = θhat * xhat - θn * xhat := by
  rw [Fate.EndToEnd.e2eResidual_def, linWorld_predFrom']

/-- ⭐⭐ **【端到端残差的绝对值 = 参数偏差乘 `‖x̂‖`（等式）】**

$$\bigl|\,\mathrm{e2eResidual}(\theta_n)\,\bigr| = \|\theta_n-\hat\theta\|\cdot\|\hat x\| .$$

**为何不是同义反复**：左边是 `EndToEnd.e2eResidual`（世界模型的端到端残差）的
绝对值，右边是参数偏差；等式靠 `e2eResidual_eq` + `norm_mul`。
这是 §5 主定理**唯一**的代数桥。 -/
theorem e2e_abs_eq (θhat θn xhat : ℝ) :
    |Fate.EndToEnd.e2eResidual ThetaConvergence.linWorld (θhat * xhat) θn
        PUnit.unit PUnit.unit PUnit.unit xhat|
      = ‖θn - θhat‖ * ‖xhat‖ := by
  rw [e2eResidual_eq]
  have h : θhat * xhat - θn * xhat = (-(θn - θhat)) * xhat := by ring
  rw [h, abs_mul, abs_neg, ← Real.norm_eq_abs, ← Real.norm_eq_abs]

/-- ⭐⭐⭐⭐⭐ **【主定理：`linWorld` 上的端到端误差预算】**

设 `θ*` 为**真参数**、`θ̂` 为**估计器输出**、`θ_n := thetaN η θ̂ x̂ θ̂₀ n` 为
`EndToEnd.endToEndIter` 的轨迹。若

* **估计环节** `hest : ‖θ̂ − θ*‖·‖x̂‖ ≤ σ_est`
  （由 §3 `est_err_exact` + `est_bound` 提供，`σ_est` 是 Gauss–Markov 的估计尺度），

则第 `n` 步的**端到端残差**满足

$$\bigl|\,\mathrm{e2eResidual}\ \mathrm{linWorld}\ (\theta^*\hat x)\ \theta_n\,\bigr|
  \;\le\; \sigma_{est} + \sigma_{learn},$$

其中 `σ_learn = c(η)^n ‖θ̂₀ − θ̂‖ ‖x̂‖` 是 §4 的**具体**学习误差。

**证明结构**（参数空间里的三角不等式，**不是任意向量**）：

1. `|e2e| = ‖θ_n − θ*‖·‖x̂‖`（`e2e_abs_eq`，精确等式）；
2. `‖θ_n − θ*‖ ≤ ‖θ_n − θ̂‖ + ‖θ̂ − θ*‖`（`norm_sub_le`）；
3. `‖θ_n − θ̂‖·‖x̂‖ ≤ σ_learn`（§4 `learnErr_le`，经 `thetaN_closed` + `c`）；
4. `‖θ̂ − θ*‖·‖x̂‖ ≤ σ_est`（前件 `hest`）。

**为何不是同义反复**：
* 结论是 `EndToEnd.e2eResidual`（**具体世界模型**的具体残差）上的不等式；
* 第 3 步必须经 `ThetaConvergence.thetaN_closed` + `OptimalEta.c` 才能把
  `thetaN` 的偏差换成 `c(η)^n`；
* 第 2 步是**参数空间**的三角不等式，前件里没有它；
* `hest` 是关于 `‖θ̂ − θ*‖‖x̂‖` 的界，**不是**关于端到端残差的界。

**⚠ 边界**：`hest` 是把 `GaussMarkovScalar` 的估计尺度接到 `linWorld` 参数的
**外部假设**（§3 边界 3.1）。本文件**不声称**二者共用概率模型。 -/
theorem chain_end_to_end_bound (η θstar θhat xhat θ₀ : ℝ) (hx : xhat ≠ 0) (n : ℕ)
    {σest : ℝ} (hest : ‖θhat - θstar‖ * ‖xhat‖ ≤ σest) :
    |Fate.EndToEnd.e2eResidual ThetaConvergence.linWorld (θstar * xhat)
        (thetaN η θhat xhat θ₀ n) PUnit.unit PUnit.unit PUnit.unit xhat|
      ≤ σest + sigmaLearn η θhat xhat θ₀ n := by
  -- 端到端残差 ↔ 参数偏差
  rw [show Fate.EndToEnd.e2eResidual ThetaConvergence.linWorld (θstar * xhat)
        (thetaN η θhat xhat θ₀ n) PUnit.unit PUnit.unit PUnit.unit xhat
      = (θstar * xhat - thetaN η θhat xhat θ₀ n * xhat) from by
        rw [e2eResidual_eq]]
  have hkey : θstar * xhat - thetaN η θhat xhat θ₀ n * xhat
      = (-(thetaN η θhat xhat θ₀ n - θstar)) * xhat := by ring
  rw [hkey, abs_mul, abs_neg]
  -- 参数空间的三角不等式（在 `ℝ` 的 `abs` 层，`‖·‖` 在 `ℝ` 上就是 `|·|`）
  have htri : |thetaN η θhat xhat θ₀ n - θstar|
      ≤ |thetaN η θhat xhat θ₀ n - θhat| + |θhat - θstar| := abs_sub_le _ _ _
  have hxnn : (0 : ℝ) ≤ |xhat| := abs_nonneg _
  have hlearn : |thetaN η θhat xhat θ₀ n - θhat| * |xhat|
      ≤ sigmaLearn η θhat xhat θ₀ n := learnErr_le η θhat xhat θ₀ hx n
  have h1 : |thetaN η θhat xhat θ₀ n - θstar| * |xhat|
      ≤ (|thetaN η θhat xhat θ₀ n - θhat| + |θhat - θstar|) * |xhat| :=
    mul_le_mul_of_nonneg_right htri hxnn
  have h2 : (|thetaN η θhat xhat θ₀ n - θhat| + |θhat - θstar|) * |xhat|
      = |thetaN η θhat xhat θ₀ n - θhat| * |xhat| + |θhat - θstar| * |xhat| := by ring
  have hest' : |θhat - θstar| * |xhat| ≤ σest := by
    simpa [Real.norm_eq_abs] using hest
  nlinarith [h1, h2, hlearn, hest']

/-! ===========================================================================
§6  稳态环节：`σ_steady` 不是装饰
=========================================================================== -/

section Steady

/-- ⭐ **`σ_steady` 的闭式**：`= d / (1 − |1 − η|)`（`steadyErr` 的定义）。 -/
theorem sigmaSteady_eq (η d : ℝ) : sigmaSteady η d = d / (1 - |1 - η|) := rfl

/-- ⭐ **`σ_steady ≥ 0`**（`0 ≤ d`、`|1−η| < 1` 是**必要**的，见 `ClosedLoopNoisy` §9.2 #5）。 -/
theorem sigmaSteady_nonneg {η d : ℝ} (hd : 0 ≤ d) (hη : |1 - η| < 1) :
    0 ≤ sigmaSteady η d :=
  ClosedLoopNoisy.steadyErr_nonneg hd hη

/-- ⭐ **无噪声时 `σ_steady = 0`**（`d = 0`）。 -/
theorem sigmaSteady_zero_noise (η : ℝ) : sigmaSteady η 0 = 0 :=
  ClosedLoopNoisy.steadyErr_zero_noise η

/-- ⭐⭐⭐⭐⭐ **【`σ_steady` **确实**是噪声闭环的 `limsup` 上界】**

设 `r = |1 − η| < 1`、每步观测漂移 `‖x̂_k − x̂_{k+1}‖ ≤ d`。则

$$\limsup_{n\to\infty}\bigl\|A\,\theta_n - \hat x_n\bigr\|
  \;\le\; \frac{d}{1-|1-\eta|} \;=\; \sigma_{steady} .$$

**这是 `ClosedLoopNoisy.noisy_limsup_bound` 的直接应用**：
它证明 `σ_steady` **不是装饰**——它真的是那条（非自治、带噪）闭环迭代的稳态上界。
`A`、`φ` 满足 `BoundWriteBack.Corrects A φ` 时结论成立（`Corrects` 是那条定理的前件）。 -/
theorem sigmaSteady_is_noisy_bound {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (xhat : ℕ → F) (θ : E)
    (h : BoundWriteBack.Corrects A φ) {d r : ℝ}
    (hstep : ∀ k, ‖xhat k - xhat (k + 1)‖ ≤ d) (hd : 0 ≤ d)
    (hr : r = |1 - η|) (hr1 : r < 1) :
    limsup (fun n : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η xhat n θ) - xhat n‖) atTop
      ≤ sigmaSteady η d := by
  have hb := ClosedLoopNoisy.noisy_limsup_bound A φ η xhat θ h hstep hd hr hr1
  have hs : sigmaSteady η d = d / (1 - r) := by
    show ClosedLoopNoisy.steadyErr η d = d / (1 - r)
    rw [ClosedLoopNoisy.steadyErr, hr]
  rw [hs]
  exact hb

end Steady

/-! ===========================================================================
§7  坍缩与非平凡性
=========================================================================== -/

/-- ⭐⭐⭐ **【学习分量随 `n` 指数衰减到 0】**

若 `0 ≤ c₀ < 1`，则 `n ↦ c₀^n · e` 收敛到 `0`。

**为何不是同义反复**：前件是标量不等式 `0 ≤ c₀ < 1`；结论是一条**极限**陈述。
证明用 `tendsto_pow_atTop_nhds_zero_of_lt_one` + `mul_const`。 -/
theorem learn_tendsto_zero {c₀ e : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : c₀ < 1) :
    Filter.Tendsto (fun n : ℕ => c₀ ^ n * e) Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun n : ℕ => c₀ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hc₀ hc₁
  simpa using hpow.mul_const e

/-- ⭐⭐ **【`σ_learn` 在 `η = 1` 时坍缩】**

`c(1) = 0`，故 `n ≥ 1` 时 `sigmaLearn (1) θ̂ x̂ θ₀ n = 0`。

**为何不是同义反复**：前件是 `n ≥ 1`；结论是 `sigmaLearn` 的具体定义
（含 `OptimalEta.c (1)`）求值为 `0`，需 `c_one` 与 `zero_pow`。 -/
theorem sigmaLearn_eta_one (θhat xhat θ₀ : ℝ) {n : ℕ} (hn : 0 < n) :
    sigmaLearn (1 : ℝ) θhat xhat θ₀ n = 0 := by
  rw [sigmaLearn, OptimalEta.c_one,
    zero_pow (Nat.pos_iff_ne_zero.mp hn), zero_mul, zero_mul]

/-- ⭐⭐⭐⭐ **【主定理的 `η = 1` 坍缩形式】**

`η = 1`、`n ≥ 1` 时，`linWorld` 的端到端残差满足

$$\bigl|\,\mathrm{e2eResidual}\,\bigr| \;\le\; \sigma_{est} + 0,$$

即**学习环在一步后完全消去**，端到端误差只剩估计环的贡献。

**为何不是同义反复**：前件是 `hest`（估计界的**外部**假设）、`x̂ ≠ 0`、`n ≥ 1`；
结论里 `η = 1` 使 `sigmaLearn` 为 `0`，这一步由 `sigmaLearn_eta_one` 完成
（用的是 `OptimalEta.c_one`）。`η = 1` 与「端到端残差 ≤ σ_est」是不同的陈述。 -/
theorem chain_end_to_end_bound_eta_one (θstar θhat xhat θ₀ : ℝ) (hx : xhat ≠ 0)
    {n : ℕ} (hn : 0 < n) {σest : ℝ} (hest : ‖θhat - θstar‖ * ‖xhat‖ ≤ σest) :
    |Fate.EndToEnd.e2eResidual ThetaConvergence.linWorld (θstar * xhat)
        (thetaN (1 : ℝ) θhat xhat θ₀ n) PUnit.unit PUnit.unit PUnit.unit xhat|
      ≤ σest + 0 := by
  have h := chain_end_to_end_bound (1 : ℝ) θstar θhat xhat θ₀ hx n hest
  rw [sigmaLearn_eta_one θhat xhat θ₀ hn] at h
  exact h

/-! ===========================================================================
§8  本文件对第 205 轮自查的直接回应（对照表）
=========================================================================== -/

/-!

| `ChainErrorBudget` 的做法 | 本文件的做法 |
|---|---|
| `Ω₁ Ω₂ Ω₃ : E'` 是**任意**向量 | `θ*`、`θ̂`、`θ_n := thetaN …`、`x̂` 是 `linWorld` 的**具体**量 |
| 三项误差是**自由标量** | `σ_est` 由 `est_err_exact` 取到（`GaussMarkovScalar`）；`σ_learn` 由 `learnErr_le` 取到（`ThetaConvergence` + `OptimalEta`）；`σ_steady` 由 `sigmaSteady_is_noisy_bound` 取到（`ClosedLoopNoisy`）|
| 结论是 `IsOptimalGap`（抽象谓词） | 结论是 `EndToEnd.e2eResidual`（**世界模型的端到端残差**）上的不等式（`chain_end_to_end_bound`） |
| 证明只用 `norm_add_le` 两次 | 证明用 `e2e_abs_eq` + `thetaN_closed` + `c` 的定义 + 参数空间三角不等式 |
| — | 含 `σ_steer` / `σ_steady` 的全量端到端界**未实现**（§0.1 #4/#5 已删，不用 `sorry` 占位） |

**关键改进**：`σ_learn` 与 `e2e` 之间的桥是
`linWorld_learn_eq` 背后的 `thetaN_closed`（一个**归纳证明**，不是定义展开），
它把 `linWorld` 的 `endToEndIter` 的 `n` 步轨迹化成 `(1−η)^n` 的闭式。
**这条桥在 `ChainErrorBudget` 中完全不存在。**

-/

end ChainBudgetBound

end Fate
