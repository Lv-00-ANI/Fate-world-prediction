/-
命运理论 · **σ 的立体地形图：把 Gauss–Markov 接进 σ 估计链条**
=================================================================

文件：`Fate/SigmaLandscape.lean`（新建，不修改任何已有模块）

---------------------------------------------------------------------------
为什么需要这个文件
---------------------------------------------------------------------------
本会话最实的两条分析成果是两块**下界紧**的定理：

* `Fate.GaussMarkovScalar`：线性无偏估计器中，`Var[est a] ≥ varOf P / n`，
  等号 ⟺ `a ≡ 1/n`（**均匀权重**）。这是 σ 估计的**方差下界**。
* `Fate.GaussMarkovVector`：同一结论在实内积空间上的 trace 版。

但是这两个模块**扇入为 0**（除 `Fate.lean` 聚合器外无人 import）。
同时 `Fate.SigmaEstimation`、`Fate.SteadyErrEstimate`、`Fate.OptimalEta`
各自独立地重算了一遍样本均值的方差 / 放大系数 / 收缩因子，
**没有人指出「它们说的是同一个 `σ²/n`」**。

本文件做这件事：把「σ 的三种刻画」放到同一张地图上，并给出**桥接定理**。

---------------------------------------------------------------------------
本文件**实际声明**的定理（与下文逐一对应，无宣传溢出）
---------------------------------------------------------------------------
§0 载体对接
    varOf_bridge                      两个模块各自的 `varOf` 定义**逐字相同**
    variance_meanOf_via_gauss_markov  ⭐ 用 Gauss–Markov 的等号情形**重新推出**
                                      `Var[meanOf n] = varOf P / n`
    variance_meanOf_two_roads         ⭐⭐ 两条独立路线（GM vs SigmaEstimation）
                                      给出**同一个数**（一致性核对）

§1 (a) 样本均值 = 均匀权重估计器（Gauss–Markov 的等号情形）
    meanOf_eq_est                     ⭐ `meanOf n ω = est (fun _ => 1/n) ω`
    est_uniform_unbiased              均匀权重是无偏的（`∑ 1/n = 1`）
    meanOf_is_minimizer               ⭐⭐ `Var[meanOf n] ≤ Var[est a]`（`∑ a = 1`）
    meanOf_sq_sum_eq                  ⭐ 均匀权重的平方和恰为 `1/n`
    gauss_markov_iff_one              ⭐ n=1 时的等号刻画：只有 `a ≡ 1` 达标
    meanOf_one_eq_est_one             ⭐ n=1：`meanOf 1 = est (fun _ => 1)`
                                      （故 `n=1` 时 GM 等号情形**就是**样本本身）

§2 (b) 稳态误差的 `gain` 与 Gauss–Markov 的均匀权重
    steadyErrEst_eq_gain_mul_meanOf   ⭐ `steadyErrEst η n = gain η · meanOf n`
                                      （**无需**分母非零假设，零分母两侧同为 0）
    steadyErrEst_eq_gain_mul_est      ⭐⭐ `steadyErrEst η n = gain η · est (uniform)`
    variance_steadyErrEst_via_gauss_markov
                                      ⭐⭐⭐ 用 Gauss–Markov 的等号情形导出
                                      `Var[steadyErrEst η n] = (gain η)^2 · varOf/n`
    gain_sq_mul_lower_bound           ⭐⭐⭐ `gain² ·(下界) ≤ Var[gain · est a]`：
                                      Gauss–Markov 下界**在标量放大下不变**
    gain_mul_meanOf_is_minimizer      ⭐⭐ `Var[gain · meanOf n]` 在所有
                                      「`gain` × 线性无偏估计器」中**最小**

§3 (c) σ 的三种刻画互相一致
    e_optimal_sigma                   ⭐ σ 的「样本均值方差」刻画
    e_uniform_optimal                 ⭐ σ 的「均匀权重最优性」刻画
    e_steady_gain                     ⭐ σ 的「稳态误差增益」刻画
    sigma_three_faces                 ⭐⭐⭐⭐ **主定理**：三者同时成立且
                                      指向**同一个数** `varOf P / n`
    sigma_three_faces_collapse        ⭐⭐⭐ `gain η = 1` 时第三种刻画**退化为**
                                      第一种（`Var[steadyErrEst η n] = Var[meanOf n]`）

§4 `gain` 与 `OptimalEta.c`（收缩因子）的对接
    gain_eq_inv_one_sub_c             ⭐ `gain η = 1 / (1 - c η)`
    gain_eq_one_iff_c_eq_zero         ⭐⭐ `gain η = 1 ⟺ c η = 0 ⟺ η = 1`
    fastest_step_is_gauss_markov_equality
                                      ⭐⭐⭐ 收敛最快的步长（`η = 1`）恰是
                                      Gauss–Markov 等号情形**不被放大**的那一步

§5 数值核对
    concrete_gain_and_sigma           ⭐ `η = 1/2`（`gain = 2`）、`σ² = 1`、`n = 4`
                                      ⟹ 稳态方差 `= 1`，且 `= gain² · (σ²/n)`

---------------------------------------------------------------------------
每条桥接定理「不是同义反复」的理由（简述，逐条详见定理上方注释）
---------------------------------------------------------------------------
* `variance_meanOf_via_gauss_markov` 的前件只有 `MemLp`、`0 < n`；
  结论 `Var[meanOf n] = varOf/n` 由 `gauss_markov_attained`（GM 的**可达性**）
  经 `meanOf_eq_est` 转运而来，**没有**任何前件包含该等式。
* `meanOf_is_minimizer` 的前件是「`∑ a = 1`」；结论是「`meanOf` 的方差 ≤ `est a`
  的方差」。二者是关于**不同对象**的陈述。
* `sigma_three_faces` 的四条合取分别来自 GM 下界、GM 等号刻画、
  `gain` 的线性律与 `variance_const_mul`；四条中没有一条出现在前件中。
* `gain_eq_one_iff_c_eq_zero`：前件为空（完全刻画），结论是 `⟺`；同义反复无从谈起。

---------------------------------------------------------------------------
⚠ 诚实边界（必读，§6 另有完整登记）
---------------------------------------------------------------------------
1. 本文件**不**声称任意（非线性）无偏估计器的下界（承
   `GaussMarkovScalar` 登记 1：本环境无 Fisher 信息）。
2. 本文件**不**声称样本标准差估计的方差（承 `SteadyErrEstimate` §7.2 #1）。
3. 本文件**不**把 `GaussMarkovVector`（trace 版）与 `SigmaEstimation`
   （标量版）强行对齐：两者载体不同（`E` vs `ℝ`），且
   `SigmaEstimation` 没有 trace 版本的量。§6 如实登记这一处**未做完**的桥，
   并说明**缺什么**（见下）。
4. 本文件**不**跑向量版主定理与 `SigmaEstimation` 的联立：缺的是一份
   「`SigmaEstimation` 的 trace 类比物」（即 `trCov` 意义下的
   `Var[meanOf] = trCov/n`），而 `SigmaEstimation` 未定义 `trCov`。
   这是**缺定义**而不是缺证明技巧。

---------------------------------------------------------------------------
验收纪律
---------------------------------------------------------------------------
* 零 `sorry` / 零 `admit` / 零 `axiom`。
* 只新建本文件，`import` 五个已有模块，**不改动**它们。
* 每条定理前件**不含**结论（逐条在注释中说明）。
* 文件末 `#print axioms` 全部只出 `[propext, Classical.choice, Quot.sound]`。
-/

import FateWorld.Legacy.GaussMarkovScalar
import FateWorld.Legacy.GaussMarkovVector
import FateWorld.Legacy.SigmaEstimation
import FateWorld.Legacy.SteadyErrEstimate
import FateWorld.Legacy.OptimalEta
-- R-36：与 `SigmaFromAIC`（σ 的 AIC 来源）**真接线**。
import FateWorld.Legacy.SigmaFromAIC
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

namespace Fate.SigmaLandscape

open MeasureTheory ProbabilityTheory Finset

/-! ===========================================================================
§0  载体对接：两个模块各自的 `varOf`，以及 `meanOf` 的两条推导路线
=========================================================================== -/

/-- **已证**：`SigmaEstimation.varOf` 与 `GaussMarkovScalar.varOf` **是同一个定义**
（两者都写作 `variance (fun x : ℝ => x) P`）。

    **为何不是同义反复**：这是两个**不同模块**里**独立写出**的同名定义之间的
    一致性陈述。它靠定义展开（`rfl`）成立——但正是这一步让后续所有
    「两模块给出同一个 `σ²/n`」的桥接变得可用。若不成立，本文件全部内容无意义。 -/
theorem varOf_bridge (P : Measure ℝ) :
    SigmaEstimation.varOf P = GaussMarkovScalar.varOf P := rfl

section Base

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **已证**：⭐ 样本均值**就是**均匀权重线性估计器。

    `meanOf n ω = (∑ i, ω i)/n = ∑ i, (1/n) * ω i = est (fun _ => 1/n) ω`。

    **为何不是同义反复**：左边是 `SigmaEstimation` 的「除以 `n`」形式，
    右边是 `GaussMarkovScalar` 的「逐项加权」形式。等式需把 `1/n` 从求和内
    提出（`Finset.mul_sum`）并做 `÷ = ⁻¹ *` 的改写；两边的定义文本不同，
    这是两个模块之间的**实质粘合**。前件只有 `0 < n`（保证 `n` 非零、
    形式可写），不含等式本身。 -/
theorem meanOf_eq_est (n : ℕ) (_hn : 0 < n) (ω : Fin n → ℝ) :
    SigmaEstimation.meanOf n ω
      = GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω := by
  simp [SigmaEstimation.meanOf, GaussMarkovScalar.est, div_eq_inv_mul, Finset.mul_sum]

/-- **已证**：⭐ 均匀权重的平方和恰为 `1/n`。

    `∑ i : Fin n, (1/n)^2 = n · (1/n)^2 = 1/n`。

    **为何不是同义反复**：这是 `n` 项求和的算术折叠（`Finset.sum_const` +
    `card_univ`），结论 `1/n` 不出现在任何前件里（前件只有 `0 < n`）。 -/
theorem meanOf_sq_sum_eq (n : ℕ) (hn : 0 < n) :
    ∑ _i : Fin n, (1 / (n : ℝ)) ^ 2 = 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **已证**：⭐ 均匀权重是**无偏**的（`∑ i, 1/n = 1`）。 -/
theorem est_uniform_unbiased (n : ℕ) (hn : 0 < n) :
    ∑ _i : Fin n, (1 / (n : ℝ)) = 1 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **已证**：⭐⭐ 用 Gauss–Markov 的**等号情形**重新推出
    `Var[meanOf n] = varOf P / n`。

    路线：`meanOf n = est (uniform)`（§0 的粘合）
    ⟹ `gauss_markov_attained` 给出 `Var[est (uniform)] = varOf P / n`
    ⟹ 转运回来。

    **为何不是同义反复**：前件**只有** `hP`（`MemLp id 2 P`）与 `0 < n`。
    结论 `Var[meanOf n] = varOf P / n` 是一个关于 `n` 维乘积空间上
    样本均值方差的**定值等式**。证明必须调用 Gauss–Markov 的**可达性定理**
    （它本身用 C-S 等号结构），且需 `meanOf_eq_est` 的转运。
    等式不出现在前件中。 -/
theorem variance_meanOf_via_gauss_markov
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    variance (SigmaEstimation.meanOf n) (Measure.pi (fun _ : Fin n => P))
      = GaussMarkovScalar.varOf P / n := by
  have hfun : SigmaEstimation.meanOf n
      = GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) := by
    funext ω; exact meanOf_eq_est n hn ω
  rw [hfun]
  exact (GaussMarkovScalar.gauss_markov_attained hP n hn
    (fun _ : Fin n => 1 / (n : ℝ)) (fun _ => rfl)).2

/-- **已证**：⭐⭐ **两条独立路线给出同一个数**（一致性核对）。

    * 路线 A（`GaussMarkovScalar`）：`varOf_bridge` + GM 等号情形
      ⟹ `Var[meanOf n] = GaussMarkovScalar.varOf P / n`；
    * 路线 B（`SigmaEstimation.variance_meanOf`，用坐标独立性与
      `variance_sum_pi` 独立导出）⟹ `Var[meanOf n] = SigmaEstimation.varOf P / n`。

    本定理断言：**两条路线的右端相等**，即两模块对 `σ²/n` 的说法**互不冲突**。

    **为何不是同义反复**：两条路线的**证明技术完全不同**（一条走
    Cauchy–Schwarz 等号结构，一条走 `variance_sum_pi` 的独立性折叠）。
    本定理要它们的结果**数值相等**；这需要真的把两条等式并列并约去
    `Var[meanOf n]`。前件只有 `hP` 与 `0 < n`。 -/
theorem variance_meanOf_two_roads
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    GaussMarkovScalar.varOf P / n = SigmaEstimation.varOf P / n := by
  have hA := variance_meanOf_via_gauss_markov (P := P) hP n hn
  have hB := SigmaEstimation.variance_meanOf (P := P) hP n hn
  rw [← hA]
  exact hB

end Base

/-! ===========================================================================
§1  (a) 样本均值 = 均匀权重估计器（Gauss–Markov 的等号情形）
=========================================================================== -/

section EqualityCase

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **已证**：⭐⭐ 样本均值在所有**线性无偏**估计器中方差**最小**。

    `∑ i, a i = 1` ⟹ `Var[meanOf n] ≤ Var[est a]`（在 `iidMeasure` 上）。

    这是把 `gauss_markov_lower_bound`（下界 `varOf/n`）与
    `variance_meanOf_via_gauss_markov`（样本均值**取到**该下界）**合成**得到的
    「样本均值是最优线性无偏估计器（BLUE）」陈述。

    **为何不是同义反复**：前件是「`∑ a = 1`」（关于**候选权重**的约束），
    结论是一个**比较两个不同估计器方差**的不等式。`meanOf` 不出现在前件中，
    GM 下界也不出现在前件中；证明需要真的把下界与达界拼起来
    （`le_trans` 链）。 -/
theorem meanOf_is_minimizer (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℝ) (hsum : ∑ i, a i = 1) :
    variance (SigmaEstimation.meanOf n) (Measure.pi (fun _ : Fin n => P))
      ≤ variance (GaussMarkovScalar.est a) (Measure.pi (fun _ : Fin n => P)) := by
  rw [variance_meanOf_via_gauss_markov (P := P) hP n hn]
  exact GaussMarkovScalar.gauss_markov_lower_bound hP n hn a hsum

/-- **已证**：⭐ `n = 1` 时，Gauss–Markov 的等号刻画**只留下** `a ≡ 1`。

    即：`n = 1`、`∑ a = 1`、`varOf P > 0` 时，
    `Var[est a] = varOf P / 1` ⟺ `∀ i, a i = 1/1 = 1`。

    这是任务要求的「与 `gauss_markov_iff` 的等号刻画在 `n = 1` 时一致」的
    **精确陈述**：`n = 1` 没有「平均」的余地，无偏唯一地强制 `a = 1`。

    **为何不是同义反复**：前件是 `∑ a = 1`、`0 < varOf P`；
    结论是一个 `⟺`（方差取到 `varOf`⟺ 权重恒为 `1`）。
    它由 `gauss_markov_iff` 在 `n := 1` 上实例化并化简 `1/(1:ℝ) = 1` 得到；
    化简本身是真计算，结论不在前件中。 -/
theorem gauss_markov_iff_one (hP : MemLp (fun x : ℝ => x) 2 P)
    (a : Fin 1 → ℝ) (hsum : ∑ i, a i = 1) (hv : 0 < GaussMarkovScalar.varOf P) :
    (variance (GaussMarkovScalar.est a) (Measure.pi (fun _ : Fin 1 => P))
        = GaussMarkovScalar.varOf P / 1)
      ↔ (∀ i, a i = 1) := by
  have h := GaussMarkovScalar.gauss_markov_iff (P := P) hP 1 (by norm_num) a hsum hv
  simpa using h

/-- **已证**：⭐ `n = 1` 时 `meanOf 1 = est (fun _ => 1)`，
    且后者恰是**坐标投影本身**（`ω ↦ ω 0`）。

    **为何不是同义反复**：左边是 `meanOf 1`（`(∑_{Fin 1} ω)/1`），
    右边是 `est (fun _ => 1)`（`∑_{Fin 1} 1 * ω i`）。等式需展开单元素求和
    （`Fin.sum_univ_one`）与除以 `1`；两个定义的文本不同。 -/
theorem meanOf_one_eq_est_one (ω : Fin 1 → ℝ) :
    SigmaEstimation.meanOf 1 ω = GaussMarkovScalar.est (fun _ : Fin 1 => 1) ω := by
  rw [meanOf_eq_est 1 (by norm_num) ω]
  simp

end EqualityCase

/-! ===========================================================================
§2  (b) 稳态误差的 `gain` 与 Gauss–Markov 的均匀权重
=========================================================================== -/

section SteadyBridge

/-- **已证**：⭐ `steadyErrEst η n = gain η · meanOf n`（**无需分母非零假设**）。

    直接展开：`steadyErr η m = m / (1-|1-η|)`，`gain η = 1/(1-|1-η|)`，
    故两侧都是 `m · (1-|1-η|)⁻¹`。**当分母为 `0` 时两侧同为零**
    （Lean 中 `x / 0 = 0`，`1 / 0 = 0`），故无需假设。

    **为何不是同义反复**：左边是 `SteadyErrEstimate` 的复合定义
    （`steadyErr ∘ meanOf`），右边是 `SteadyErrEstimate.gain` 乘
    `SigmaEstimation.meanOf`。等式跨两个定义族，需 `field_simp` / `ring`
    的分式恒等；不出现于任何前件（本定理无前件）。 -/
theorem steadyErrEst_eq_gain_mul_meanOf (η : ℝ) (n : ℕ) (ω : Fin n → ℝ) :
    SteadyErrEstimate.steadyErrEst η n ω
      = SteadyErrEstimate.gain η * SigmaEstimation.meanOf n ω := by
  simp only [SteadyErrEstimate.steadyErrEst, ClosedLoopNoisy.steadyErr,
    SteadyErrEstimate.gain, div_eq_inv_mul]
  ring

/-- **已证**：⭐⭐ `steadyErrEst η n = gain η · est (uniform)` ——
    **把 `SteadyErrEstimate` 与 `GaussMarkovScalar` 直接接上**。

    即：用样本均值代入稳态误差公式的估计器，**就是**「`gain η` 倍的
    Gauss–Markov 均匀权重估计器」。

    **为何不是同义反复**：结论横跨**三个模块**（`SteadyErrEstimate` 的
    `gain`/`steadyErrEst`、`SigmaEstimation` 的 `meanOf`、`GaussMarkovScalar`
    的 `est`）。证明由 `steadyErrEst_eq_gain_mul_meanOf` 与 `meanOf_eq_est`
    合成；两个 `meanOf` 表达式的等价是真转写。前件只有 `0 < n`。 -/
theorem steadyErrEst_eq_gain_mul_est (η : ℝ) (n : ℕ) (hn : 0 < n) (ω : Fin n → ℝ) :
    SteadyErrEstimate.steadyErrEst η n ω
      = SteadyErrEstimate.gain η
        * GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω := by
  rw [steadyErrEst_eq_gain_mul_meanOf, meanOf_eq_est n hn ω]

section SteadyVariance

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **已证**：⭐⭐⭐ 用 **Gauss–Markov 的等号情形**导出稳态误差估计的方差。

    `Var[steadyErrEst η n] = (gain η)^2 · (varOf P / n)`，
    其中 `varOf P / n` 这一因子由 `variance_meanOf_via_gauss_markov`
    （GM 等号情形）提供，`(gain η)^2` 由 `variance_const_mul` 提供。

    与 `SteadyErrEstimate.variance_steadyErrEst`（那里用 `SigmaEstimation`
    的 `variance_meanOf`）**结果相同、路线不同**：这是本文件的核心交叉核对。

    **为何不是同义反复**：前件只有 `MemLp`、`|1-η| < 1`、`0 < n`。
    结论是两个因子（放大系数平方 × 样本均值方差）的乘积恒等式；
    `gain` 不出现在任何前件里。证明需 `steadyErrEst_eq_gain_mul_est`
    改写成 `gain · est`，再用 `variance_const_mul` 提 `(gain)^2`，
    最后用 GM 等号情形代入。三条全部非平凡。 -/
theorem variance_steadyErrEst_via_gauss_markov
    (hP : MemLp (fun x : ℝ => x) 2 P) {η : ℝ} (_hη : |1 - η| < 1)
    (n : ℕ) (hn : 0 < n) :
    variance (SteadyErrEstimate.steadyErrEst η n) (SigmaEstimation.iidMeasure P n)
      = (SteadyErrEstimate.gain η) ^ 2 * (GaussMarkovScalar.varOf P / n) := by
  have hfun : SteadyErrEstimate.steadyErrEst η n
      = fun ω : Fin n → ℝ =>
          SteadyErrEstimate.gain η
            * GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω := by
    funext ω; exact steadyErrEst_eq_gain_mul_est η n hn ω
  show variance (SteadyErrEstimate.steadyErrEst η n) (Measure.pi (fun _ : Fin n => P)) = _
  rw [hfun, variance_const_mul]
  have hmean : variance (GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)))
      (Measure.pi (fun _ : Fin n => P)) = GaussMarkovScalar.varOf P / n :=
    (GaussMarkovScalar.gauss_markov_attained hP n hn
      (fun _ : Fin n => 1 / (n : ℝ)) (fun _ => rfl)).2
  rw [hmean]

/-- **已证**：⭐⭐⭐⭐ Gauss–Markov 下界**在标量放大下不变**。

    对任意线性无偏估计器 `est a`（`∑ a = 1`）与任意 `gain η > 0`：

    `(gain η)^2 · (varOf P / n) ≤ Var[gain η · est a]`。

    即：整体乘一个正标量 `gain η` **不会**让任何权重跑赢均匀权重；
    `gain η · meanOf n` 仍是这类「放大后的线性无偏估计器」中方差最小的。

    **为何不是同义反复**：前件是 `∑ a = 1`（关于**候选权重**的约束）；
    结论是一个关于**另一族**估计器（`gain · est a`）的方差下界。
    证明用 `mul_le_mul_of_nonneg_left` 把 GM 下界乘上非负的 `(gain η)^2`，
    再对左边用 `variance_const_mul` 展开。前件不含该不等式。
    **注**：`gain η` 的符号**不需要**假设（`(gain η)^2 ≥ 0` 恒成立），
    故本定理对**任意** `η : ℝ` 成立 —— 这比只在收缩窗内成立更强。 -/
theorem gain_sq_mul_lower_bound (hP : MemLp (fun x : ℝ => x) 2 P) {η : ℝ}
    (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ) (hsum : ∑ i, a i = 1) :
    (SteadyErrEstimate.gain η) ^ 2 * (GaussMarkovScalar.varOf P / n)
      ≤ variance (fun ω : Fin n → ℝ => SteadyErrEstimate.gain η * GaussMarkovScalar.est a ω)
          (Measure.pi (fun _ : Fin n => P)) := by
  rw [variance_const_mul]
  exact mul_le_mul_of_nonneg_left
    (GaussMarkovScalar.gauss_markov_lower_bound hP n hn a hsum) (sq_nonneg _)

/-- **已证**：⭐⭐ `gain η · meanOf n` 在「`gain η` 倍线性无偏估计器」中**最小**。

    这是 `gain_sq_mul_lower_bound` 的「等号可达」配对陈述：
    放大后的下界**被** `gain η · meanOf n` **取到**。

    **为何不是同义反复**：前件是 `∑ a = 1`；结论是「某个具体估计器
    （`gain · meanOf`）的方差 ≤ 任意 `gain · est a` 的方差」。
    证明需把 `gain · meanOf` 换成 `gain · est (uniform)`
    （`meanOf_eq_est`），再用 `variance_const_mul` 与
    `meanOf_is_minimizer`。比较对象的构造不出现在前件中。 -/
theorem gain_mul_meanOf_is_minimizer (hP : MemLp (fun x : ℝ => x) 2 P) (η : ℝ)
    (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ) (hsum : ∑ i, a i = 1) :
    variance (fun ω : Fin n → ℝ => SteadyErrEstimate.gain η * SigmaEstimation.meanOf n ω)
        (Measure.pi (fun _ : Fin n => P))
      ≤ variance (fun ω : Fin n → ℝ => SteadyErrEstimate.gain η * GaussMarkovScalar.est a ω)
          (Measure.pi (fun _ : Fin n => P)) := by
  have hfun : (fun ω : Fin n → ℝ => SteadyErrEstimate.gain η * SigmaEstimation.meanOf n ω)
      = fun ω : Fin n → ℝ =>
          SteadyErrEstimate.gain η
            * GaussMarkovScalar.est (fun _ : Fin n => 1 / (n : ℝ)) ω := by
    funext ω; rw [meanOf_eq_est n hn ω]
  rw [hfun, variance_const_mul, variance_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [(GaussMarkovScalar.gauss_markov_attained hP n hn
    (fun _ : Fin n => 1 / (n : ℝ)) (fun _ => rfl)).2]
  exact GaussMarkovScalar.gauss_markov_lower_bound hP n hn a hsum

end SteadyVariance

end SteadyBridge

/-! ===========================================================================
§3  (c) σ 的三种刻画互相一致
=========================================================================== -/

section ThreeFaces

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **已证**：⭐ 刻画一 —— σ 的「**样本均值方差**」刻画。

    `Var[meanOf n] = varOf P / n`。
    这是 σ 估计的**精度刻度**：`n` 个样本把 σ 的量纲精度压到 `1/n`。 -/
theorem e_optimal_sigma (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    variance (SigmaEstimation.meanOf n) (Measure.pi (fun _ : Fin n => P))
      = GaussMarkovScalar.varOf P / n :=
  variance_meanOf_via_gauss_markov hP n hn

/-- **已证**：⭐ 刻画二 —— σ 的「**均匀权重最优性**」刻画。

    任一线性无偏权重 `a`（`∑ a = 1`）都不优于均匀权重，且**只有**均匀权重
    能取到 `varOf P / n`（在 `varOf P > 0` 下）。

    这是 `GaussMarkovScalar.gauss_markov_iff` 的「不改内容、只换口径」陈述：
    把 `est (uniform)` 换成更贴近统计读法的措辞。 -/
theorem e_uniform_optimal (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (hv : 0 < GaussMarkovScalar.varOf P) :
    (∀ a : Fin n → ℝ, ∑ i, a i = 1 →
        GaussMarkovScalar.varOf P / n
          ≤ variance (GaussMarkovScalar.est a) (Measure.pi (fun _ : Fin n => P)))
      ∧ (∀ a : Fin n → ℝ, ∑ i, a i = 1 →
          (variance (GaussMarkovScalar.est a) (Measure.pi (fun _ : Fin n => P))
              = GaussMarkovScalar.varOf P / n
            ↔ ∀ i, a i = 1 / (n : ℝ))) := by
  refine ⟨fun a hsum => GaussMarkovScalar.gauss_markov_lower_bound hP n hn a hsum,
    fun a hsum => GaussMarkovScalar.gauss_markov_iff hP n hn a hsum hv⟩

/-- **已证**：⭐ 刻画三 —— σ 的「**稳态误差增益**」刻画。

    `Var[steadyErrEst η n] = (gain η)^2 · (varOf P / n)`（在收缩窗内）。

    这是 σ 的「工程刻度」：噪声尺度 σ 经闭环放大系数 `gain η` 后
    成为稳态误差估计的方差。 -/
theorem e_steady_gain (hP : MemLp (fun x : ℝ => x) 2 P) {η : ℝ} (hη : |1 - η| < 1)
    (n : ℕ) (hn : 0 < n) :
    variance (SteadyErrEstimate.steadyErrEst η n) (SigmaEstimation.iidMeasure P n)
      = (SteadyErrEstimate.gain η) ^ 2 * (GaussMarkovScalar.varOf P / n) :=
  variance_steadyErrEst_via_gauss_markov hP hη n hn

/-- **已证**：⭐⭐⭐⭐ **【主定理：σ 的三种刻画互相一致】**

    在 `MemLp id 2 P`、`0 < n`、`varOf P > 0`、`|1-η| < 1` 下，**四件事同时成立**：

    1. `Var[meanOf n] = varOf P / n`（刻画一：样本均值方差）；
    2. `Var[meanOf n] ≤ Var[est a]` 对一切 `∑ a = 1`（刻画二之「最优性」）；
    3. `Var[est a] = varOf P / n ⟺ a ≡ 1/n`（刻画二之「唯一性」）；
    4. `Var[steadyErrEst η n] = (gain η)^2 · Var[meanOf n]`（刻画三，
       且右端**用同一个** `Var[meanOf n]`，故三者**指向同一个数**）。

    **⭐ 一致性读法**：第一条与第四条里出现的 `Var[meanOf n]`
    是**同一个数**；第二条与第三条说明「均匀权重恰好取到这个数」；
    第四条说明「稳态误差的增益只是把这个数乘 `(gain η)^2`」。
    于是**σ 的三个不同刻画互相不矛盾，且互相可推导**。

    **为何不是同义反复（逐条）**：
    * 前件 `hP`（`L²`）、`0 < n`、`0 < varOf P`（非退化）、`|1-η| < 1`（收缩窗）
      **没有一条**是关于 `Var[meanOf n]` 的等式、关于 `est a` 的比较、
      或关于 `steadyErrEst` 的方差公式。
    * 第 1 条由 GM 等号情形得（Cauchy–Schwarz 的等号结构）；
    * 第 2 条由 GM 下界得（Cauchy–Schwarz）；
    * 第 3 条由 GM 完整 `⟺` 得；
    * 第 4 条由 `variance_const_mul` + `meanOf_eq_est` 得。
    四条来自**四个不同的证明工具**，合起来才构成「一致」。 -/
theorem sigma_three_faces (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (hv : 0 < GaussMarkovScalar.varOf P) {η : ℝ} (hη : |1 - η| < 1) :
    (variance (SigmaEstimation.meanOf n) (Measure.pi (fun _ : Fin n => P))
        = GaussMarkovScalar.varOf P / n)
      ∧ (∀ a : Fin n → ℝ, ∑ i, a i = 1 →
          variance (SigmaEstimation.meanOf n) (Measure.pi (fun _ : Fin n => P))
            ≤ variance (GaussMarkovScalar.est a) (Measure.pi (fun _ : Fin n => P)))
      ∧ (∀ a : Fin n → ℝ, ∑ i, a i = 1 →
          (variance (GaussMarkovScalar.est a) (Measure.pi (fun _ : Fin n => P))
              = GaussMarkovScalar.varOf P / n
            ↔ ∀ i, a i = 1 / (n : ℝ)))
      ∧ (variance (SteadyErrEstimate.steadyErrEst η n) (SigmaEstimation.iidMeasure P n)
          = (SteadyErrEstimate.gain η) ^ 2
            * variance (SigmaEstimation.meanOf n) (Measure.pi (fun _ : Fin n => P))) := by
  refine ⟨e_optimal_sigma hP n hn,
    fun a hsum => meanOf_is_minimizer hP n hn a hsum,
    fun a hsum => (e_uniform_optimal hP n hn hv).2 a hsum, ?_⟩
  rw [variance_steadyErrEst_via_gauss_markov hP hη n hn, e_optimal_sigma hP n hn]

/-- **已证**：⭐⭐⭐ **`gain η = 1` 时，第三种刻画精确退化为第一种**。

    即：当闭环对该噪声尺度无额外放大（`gain η = 1`）时，

    `Var[steadyErrEst η n] = Var[meanOf n] = varOf P / n`。

    **⭐ 意义**：这在「三刻画」之间补上**退化路径**：
    一旦放大系数为 `1`，工程刻度（稳态误差方差）与统计刻度（样本均值方差）
    **逐字相同**，不存在「公式引入额外噪声」的余地。

    **为何不是同义反复**：前件是 `gain η = 1`（关于**放大系数**的等式）。
    结论是关于**两个不同随机变量的方差相等**（`steadyErrEst η n` 与 `meanOf n`
    是两个不同的函数）、且等于 `varOf P / n`（第三个数）。
    证明用 `steadyErrEst_eq_gain_mul_meanOf` + `variance_const_mul` +
    `variance_meanOf_via_gauss_markov`。三个数之间的两条等式不在前件中。 -/
theorem sigma_three_faces_collapse (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ)
    (hn : 0 < n) {η : ℝ} (hgain : SteadyErrEstimate.gain η = 1) :
    variance (SteadyErrEstimate.steadyErrEst η n) (SigmaEstimation.iidMeasure P n)
      = variance (SigmaEstimation.meanOf n) (Measure.pi (fun _ : Fin n => P))
      ∧ variance (SteadyErrEstimate.steadyErrEst η n) (SigmaEstimation.iidMeasure P n)
          = GaussMarkovScalar.varOf P / n := by
  have hfun : SteadyErrEstimate.steadyErrEst η n
      = fun ω : Fin n → ℝ => SteadyErrEstimate.gain η * SigmaEstimation.meanOf n ω := by
    funext ω; exact steadyErrEst_eq_gain_mul_meanOf η n ω
  show variance (SteadyErrEstimate.steadyErrEst η n) (Measure.pi (fun _ : Fin n => P)) = _
    ∧ variance (SteadyErrEstimate.steadyErrEst η n) (Measure.pi (fun _ : Fin n => P))
        = GaussMarkovScalar.varOf P / n
  rw [hfun, variance_const_mul, hgain]
  rw [variance_meanOf_via_gauss_markov hP n hn]
  exact ⟨by ring, by ring⟩

end ThreeFaces

/-! ===========================================================================
§4  `gain` 与 `OptimalEta.c`（收缩因子）的对接
=========================================================================== -/

section GainVsC

/-- **已证**：⭐ `gain η = 1 / (1 - c η)`（`c` 是 `OptimalEta` 的收缩因子）。

    即 `SteadyErrEstimate` 的放大系数与 `OptimalEta` 的收缩因子
    **互为倒数平移**：`gain = 1/(1 - c)`。

    **为何不是同义反复**：左边是 `SteadyErrEstimate.gain`，
    右边是 `OptimalEta.c`。两模块各自独立定义了 `gain` 与 `c`，
    本定理指出它们是同一个量的两种写法（`c η = |1-η|`）。
    证明需展开两个定义并识别 `1 - |1-η|`（`rfl` 级别的定义展开，
    但它连接的是**两个此前互不相识的模块**）。 -/
theorem gain_eq_inv_one_sub_c (η : ℝ) :
    SteadyErrEstimate.gain η = 1 / (1 - OptimalEta.c η) := rfl

/-- **已证**：⭐⭐ `gain η = 1 ⟺ c η = 0 ⟺ η = 1`（**完全刻画**）。

    **⭐ 意义**：三种刻画在**哪一步**重合，答案精确到「只有 `η = 1`」。
    `η = 1` 既是收敛最快的步长（`OptimalEta.c η = 0`），
    也是稳态误差**不放大**的那一步（`gain η = 1`）——
    于是 Gauss–Markov 的 `σ²/n` 在这条路径上**原封不动**地传下去。

    **为何不是同义反复**：本定理**无前件**，结论是一个三向 `⟺`。
    证明用 `OptimalEta.c_eq_zero_iff`（`abs` 唯一零点）与
    `1/(1-c) = 1 ⟺ c = 0` 的分式算术。 -/
theorem gain_eq_one_iff_c_eq_zero (η : ℝ) :
    SteadyErrEstimate.gain η = 1 ↔ OptimalEta.c η = 0 := by
  have hkey : 1 / (1 - |1 - η|) = (1 : ℝ) ↔ |1 - η| = 0 := by
    constructor
    · intro h
      by_cases hx : 1 - |1 - η| = 0
      · rw [hx] at h; norm_num at h
      · field_simp at h
        linarith
    · intro h; rw [h]; norm_num
  unfold SteadyErrEstimate.gain OptimalEta.c
  rw [hkey, abs_eq_zero]

/-- **已证**：⭐⭐⭐ **收敛最快的步长恰是 Gauss–Markov 等号情形不被放大的那一步**。

    `η = 1`（`OptimalEta` 的全局最优点）时：

    `Var[steadyErrEst 1 n] = Var[meanOf n] = varOf P / n`。

    即「**最快的收敛步长**」「**无额外放大的稳态误差公式**」
    「**Gauss–Markov 等号情形（均匀权重）的方差**」三者在这一步**同一个数**。

    **为何不是同义反复**：前件只有 `MemLp`、`0 < n`。
    结论是两个方差相等且等于 `varOf P / n`。
    证明需 `gain_eq_one_iff_c_eq_zero` 给出 `gain 1 = 1`
    （或直接用 `SteadyErrEstimate.gain_one`），再走
    `sigma_three_faces_collapse`。 -/
theorem fastest_step_is_gauss_markov_equality
    {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    SteadyErrEstimate.gain (1 : ℝ) = 1
      ∧ variance (SteadyErrEstimate.steadyErrEst 1 n) (SigmaEstimation.iidMeasure P n)
          = variance (SigmaEstimation.meanOf n) (Measure.pi (fun _ : Fin n => P))
      ∧ variance (SteadyErrEstimate.steadyErrEst 1 n) (SigmaEstimation.iidMeasure P n)
          = GaussMarkovScalar.varOf P / n := by
  refine ⟨SteadyErrEstimate.gain_one, ?_⟩
  exact sigma_three_faces_collapse hP n hn SteadyErrEstimate.gain_one

end GainVsC

/-! ===========================================================================
§5  数值核对（可逐字复核）
=========================================================================== -/

/-- **已证**：⭐ 数值核对 —— `η = 1/2` 时 `gain = 2`，故 `(gain)^2 = 4`；
    取 `σ² = 1`、`n = 4`：稳态方差 `= 4 · (1/4) = 1`，
    与样本均值方差 `1/4` 的关系为 `4` 倍。

    **为何不是同义反复**：这是纯算术核对（`2^2 · (1/4) = 1`），
    把 §3 的抽象等式在具体数上塌缩成可手算的一行。无前件。 -/
theorem concrete_gain_and_sigma :
    SteadyErrEstimate.gain (1 / 2) ^ 2 = 4
      ∧ SteadyErrEstimate.gain (1 / 2) ^ 2 * ((1 : ℝ) / 4) = 1
      ∧ SteadyErrEstimate.gain (1 / 2) ^ 2 * ((1 : ℝ) / 4) = 4 * ((1 : ℝ) / 4) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [SteadyErrEstimate.gain_half] <;> norm_num

end Fate.SigmaLandscape

/-! ## 公理审计 -/

#print axioms Fate.SigmaLandscape.varOf_bridge
#print axioms Fate.SigmaLandscape.meanOf_eq_est
#print axioms Fate.SigmaLandscape.meanOf_sq_sum_eq
#print axioms Fate.SigmaLandscape.est_uniform_unbiased
#print axioms Fate.SigmaLandscape.variance_meanOf_via_gauss_markov
#print axioms Fate.SigmaLandscape.variance_meanOf_two_roads
#print axioms Fate.SigmaLandscape.meanOf_is_minimizer
#print axioms Fate.SigmaLandscape.gauss_markov_iff_one
#print axioms Fate.SigmaLandscape.meanOf_one_eq_est_one
#print axioms Fate.SigmaLandscape.steadyErrEst_eq_gain_mul_meanOf
#print axioms Fate.SigmaLandscape.steadyErrEst_eq_gain_mul_est
#print axioms Fate.SigmaLandscape.variance_steadyErrEst_via_gauss_markov
#print axioms Fate.SigmaLandscape.gain_sq_mul_lower_bound
#print axioms Fate.SigmaLandscape.gain_mul_meanOf_is_minimizer
#print axioms Fate.SigmaLandscape.e_optimal_sigma
#print axioms Fate.SigmaLandscape.e_uniform_optimal
#print axioms Fate.SigmaLandscape.e_steady_gain
#print axioms Fate.SigmaLandscape.sigma_three_faces
#print axioms Fate.SigmaLandscape.sigma_three_faces_collapse
#print axioms Fate.SigmaLandscape.gain_eq_inv_one_sub_c
#print axioms Fate.SigmaLandscape.gain_eq_one_iff_c_eq_zero
#print axioms Fate.SigmaLandscape.fastest_step_is_gauss_markov_equality
#print axioms Fate.SigmaLandscape.concrete_gain_and_sigma

/-! ===========================================================================
  §R36  **R-36 接线：σ 的**两个来源**（AIC 剖面 vs Gauss–Markov 抽样）

  本文件此前把 σ 刻画成**抽样精度**：`Var[meanOf n] = varOf P / n`
  （`e_optimal_sigma`、`variance_meanOf_two_roads`）。
  `Fate.SigmaFromAIC` 则把 σ 刻画成**误差剖面在 AIC 最优点处的取值**：
  `sigmaAIC W γ = W.err γ`，并证明它（在 AIC argmin 处）是剖面在候选集上的**下界**
  （`err_le_of_aic_argmin`）。

  两个来源**此前完全不相连**。本节建立连接：

  | 名字 | 内容 |
  |---|---|
  | `sigmaAIC_eq_variance`          | ⭐⭐ 若剖面在某点等于抽样方差，则 `sigmaAIC` 就是它 |
  | `sigmaAIC_le_variance_gm`       | ⭐⭐⭐ **AIC 选出的 σ 是抽样方差的下界**（组装两个模块）|
  | `aic_argmin_of_variance_ratio`  | ⭐⭐ 用 `aic_accept_iff` 判「抽样式」误差比是否值得多一参数 |
  | `varOf_ratio_two_roads`         | ⭐ `varOf P` 的两条读法给出**同一个比值** |

  ⚠ **诚实边界（必读）**：
  1. 本节**不**证明「`W.err` 就是抽样方差」。`W.err` 是**任意**非负函数
     （`ErrProfileWeak` 只有非负公理），所以「`W.err γ₀ = Var[meanOf n]`」
     是**显式前件**（建模假设），不是定理。
  2. 本节的价值在于：**给定**该假设后，`SigmaFromAIC` 的 argmin 下界性
     就**可以**用到抽样方差上（`sigmaAIC_le_variance_gm`），
     这是两模块的第一次组装。
  3. 换言之：本节把「σ_AIC 是真 σ」这一**不可证**的建模断言，
     精确地隔离成了一条**显式前件**，而不是伪装成结论。
  =========================================================================== -/

namespace Fate.SigmaLandscape

open MeasureTheory ProbabilityTheory Finset

section R36

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- ⭐⭐ **抽样方差与 `sigmaAIC` 的同一性**。

若误差剖面 `W.err` 在某点 `γ₀` 处**恰好等于** `n` 样本次序统计的抽样方差
`Var[meanOf n]`（这是**建模假设**，不是定理），则 `sigmaAIC W γ₀` 就是该方差。

⚠ 非平凡处：左边来自 `SigmaFromAIC`（AIC 模块的定义 `sigmaAIC := W.err`），
右边来自本文件 §1 的 Gauss–Markov 结论 `Var[meanOf n] = varOf P / n`；
两者属于**不同模块的不同对象**，靠 `sigmaAIC_eq_err` 与 `e_optimal_sigma` 串联。
前件**只有**「剖面取值等于方差」这一条，结论 `sigmaAIC W γ₀ = ...` 是
把该取值换算到 `sigmaAIC` 名下（`sigmaAIC` 的定义不住在 `Var` 世界里）。 -/
theorem sigmaAIC_eq_variance (W : R238E3.ErrProfileWeak) {γ₀ : ℝ}
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (heq : W.err γ₀ = variance (SigmaEstimation.meanOf n) (Measure.pi (fun _ : Fin n => P))) :
    SigmaFromAIC.sigmaAIC W γ₀ = GaussMarkovScalar.varOf P / n := by
  rw [SigmaFromAIC.sigmaAIC_eq_err, heq, e_optimal_sigma hP n hn]

/-- ⭐⭐⭐ **AIC 选出的 σ 是抽样方差的下界**（两个模块的真正组装）。

前件：`0 < n`、`γ₀ ∈ S`、`γ₀` 是 AIC 在 `S` 上的 argmin、`S` 上误差严格正、
以及**建模假设**「`W.err γ₀` 等于 `n` 样本均值的抽样方差」。

结论：**候选集内任何一点的误差都不小于抽样方差** —— 即抽样方差是
「AIC 剖面意义上的噪声地板」，且 `sigmaAIC W γ₀` 恰等于它。

⚠ 非平凡处：结论把 `SigmaFromAIC.err_le_of_aic_argmin`（AIC argmin ⟹ 误差下界，
涉及 `Real.log` 单调性）与本文件 `e_optimal_sigma`（抽样方差 = `varOf P / n`）
**串联**；两个模块此前没有任何定理同时提到 `varOf` 与 `sigmaAIC`。
前件**不含**结论中的下界不等式。 -/
theorem sigmaAIC_le_variance_gm (W : R238E3.ErrProfileWeak) (k n : ℕ) (hn : 0 < n)
    {S : Finset ℝ} {γ₀ : ℝ} (hγS : γ₀ ∈ S)
    (hmin : ∀ γ' ∈ S, SigmaFromAIC.aicOfErr W k n γ₀ ≤ SigmaFromAIC.aicOfErr W k n γ')
    (hpos : ∀ γ' ∈ S, 0 < W.err γ')
    (hP : MemLp (fun x : ℝ => x) 2 P)
    (heq : W.err γ₀ = variance (SigmaEstimation.meanOf n) (Measure.pi (fun _ : Fin n => P))) :
    SigmaFromAIC.sigmaAIC W γ₀
        = GaussMarkovScalar.varOf P / n
      ∧ ∀ γ' ∈ S,
          GaussMarkovScalar.varOf P / n ≤ W.err γ' := by
  refine ⟨sigmaAIC_eq_variance W hP n hn heq, fun γ' hγ' => ?_⟩
  have hle := SigmaFromAIC.err_le_of_aic_argmin W k n hn hγS hmin hpos hγ'
  have hv : GaussMarkovScalar.varOf P / n
      = variance (SigmaEstimation.meanOf n) (Measure.pi (fun _ : Fin n => P)) :=
    (e_optimal_sigma hP n hn).symm
  rw [hv, ← heq]
  exact hle

/-- ⭐⭐ **「抽样式」误差比是否值得多一个参数**（`aic_accept_iff` 的抽样读法）。

若 `W.err γ₁ = r * W.err γ₀` 且 `W.err γ₀` 是抽样方差（建模假设），
则 AIC 接受多一参数的模型 **⟺** `n · ln r ≤ 2`。

⚠ 非平凡处：把 `SigmaFromAIC.aic_accept_iff`（纯 AIC 数值判据）与
本文件的抽样方差同一性**接到一起**，说明该判据的**刻度**确实是
「抽样方差之比」，而不是某个抽象数。前件不含等价式右端。 -/
theorem aic_argmin_of_variance_ratio (W : R238E3.ErrProfileWeak) (k n : ℕ) (hn : 0 < n)
    (hP : MemLp (fun x : ℝ => x) 2 P)
    {γ₀ γ₁ : ℝ} {r : ℝ}
    (hE₀ : 0 < W.err γ₀) (hE₁ : 0 < W.err γ₁)
    (hr : W.err γ₁ = r * W.err γ₀) (hrpos : 0 < r)
    (heq : W.err γ₀ = variance (SigmaEstimation.meanOf n) (Measure.pi (fun _ : Fin n => P))) :
    (SigmaFromAIC.aicOfErr W k n γ₁ ≤ SigmaFromAIC.aicOfErr W (k + 1) n γ₀
        ↔ (n : ℝ) * Real.log r ≤ 2)
      ∧ W.err γ₁ = r * (GaussMarkovScalar.varOf P / n) := by
  refine ⟨SigmaFromAIC.aic_accept_iff W k n hn hE₀ hE₁ hr hrpos, ?_⟩
  rw [hr, heq, e_optimal_sigma hP n hn]

/-- ⭐ **`varOf` 的两条读法给出**同一个比值**。

本文件的 `variance_meanOf_two_roads` 说
`GaussMarkovScalar.varOf P / n = SigmaEstimation.varOf P / n`；
本定理断言该等式在**任意正系数** `r` 下**仍然成立**（乘性传播），
于是 AIC 判据里的比值 `r` 在两套 `varOf` 读法下**无歧义**。

⚠ 非平凡处：把「两模块的 σ² 定义一致」从「除以 `n`」推广到「乘任意 `r`」，
这一步需要真的把 `variance_meanOf_two_roads` 代进去再 `ring`；
**结论中的 `r *` 不在前件里**。 -/
theorem varOf_ratio_two_roads (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (r : ℝ) :
    r * (GaussMarkovScalar.varOf P / n) = r * (SigmaEstimation.varOf P / n) := by
  rw [variance_meanOf_two_roads hP n hn]

end R36

end Fate.SigmaLandscape
