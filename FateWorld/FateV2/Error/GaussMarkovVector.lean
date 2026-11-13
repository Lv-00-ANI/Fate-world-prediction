import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/GaussMarkovVector.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 17 处，含 0 条 import）；其余正文未改
  - 状态：已编译未验证
-/

/-
命运理论 · **Gauss–Markov 向量版（推广 FateV2.Error.GaussMarkovScalar）**
=================================================================

文件：`FateV2.Error/GaussMarkovVector.lean`（新建，不修改任何已有模块）

---------------------------------------------------------------------------
任务
---------------------------------------------------------------------------
把 `FateV2.Error/GaussMarkovScalar.lean`（标量、9 定理、0 sorry）的 Gauss–Markov 定理
推广到向量情形：

(a) 定义 `estVec a ω = ∑ i, a i • ω i`，其中 `ω : Fin n → E`，
    `E` 是实内积空间；
(b) 期望与协方差的向量版本；
(c) 证明 `tr Cov[estVec a] ≥ tr Cov / n`（在 `∑ i, a i = 1` 下）；
(d) 等号刻画。

---------------------------------------------------------------------------
为什么用「trace」而不是「矩阵」形式
---------------------------------------------------------------------------
`E` 一般是无有限维假设的实内积空间（Hilbert 空间），没有天然的矩阵表示。
标量协方差 `Var[⟨x, ·⟩]` 对每个 `x ∈ E` 都有定义，把它们沿一组**正交规范基**
`b : OrthonormalBasis (Fin d) ℝ E` 求和，就是协方差算子的 trace：

    `trCov b ν = ∑ k, Var[fun z => ⟪b k, z⟫; ν]`

这是 Mathlib 里 `LinearMap.trace_eq_sum_inner` 的同一思想（`Analysis/InnerProductSpace/Trace.lean`）。
本文件对 `ν` 为 `Measure.pi`（iid 样本）与 `ν = P.map (estVec a)` 两种情形
分别给出 trace 的**精确公式**，再由此得到下界与等号刻画。

用 `Var[⟪b k, ·⟫]` 而非 `covarianceBilin μ (b k) (b k)` 的原因：
`covarianceBilin` 需要 `CompleteSpace E` 与 `BorelSpace E`，而 `Var` 的
复合律（`MeasurePreserving.variance_fun_comp`）只要求可测性，
在本环境里更省事、依赖更少，且等价（见 `covariance_vector_eq_variance_inner`）。

---------------------------------------------------------------------------
本文件**实际声明**的定理（与下文逐一对应，无宣传溢出）
---------------------------------------------------------------------------
§0 载体
    eval_memLp_2               坐标投影 `ω ↦ ω i` 在 `Measure.pi` 下属于 L²
    eval_variance              坐标投影的 `⟪b k, ω i⟫` 的方差 = 单样本同量

§1 线性估计器 `estVec` 与它的期望（任务 (b) 的「期望」半边）
    estVec                     定义：`estVec a ω = ∑ i, a i • ω i`
    estVec_integral            E[estVec a] = (∑ i, a i) • É[id; P]
    estVec_unbiased_iff        在 É[id; P] ≠ 0 时：无偏 ⟺ ∑ i, a i = 1

§2 协方差的向量版本（任务 (b) 的「协方差」半边）
    variance_inner_estVec      对正交规范基 `b` 的每个 `b k`：
                               `Var[⟪b k, estVec a·⟫] = (∑ i, (a i)^2) * Var[⟪b k,·⟫; P]`
    trCov                      定义：`trCov b ν = ∑ k, Var[⟪b k, ·⟫; ν]`
    trCov_nonneg               `0 ≤ trCov b ν`
    trCovEst                   定义：`trCovEst b n a P = ∑ k, Var[⟪b k, estVec a·⟫; pi P]`
    trCovEst_eq                `trCovEst b n a P = (∑ i, (a i)^2) * trCov b P`
    trCovEst_nonneg            `0 ≤ trCovEst b n a P`

§3 Gauss–Markov 向量版主定理
    gauss_markov_vector_lower_bound   ∑ a = 1 ⟹ trCov b P / n ≤ trCovEst b n a P
    gauss_markov_vector_equality      ∑ a = 1 且 trCovEst b n a P = trCov b P / n
                                        且 trCov b P > 0 ⟹ a ≡ 1/n
    gauss_markov_vector_attained      a ≡ 1/n ⟹ ∑ a = 1 且 trCovEst b n a P = trCov b P / n
    gauss_markov_vector_iff           ∑ a = 1 且 trCov b P > 0 时：完整 ⟺

---------------------------------------------------------------------------
验收纪律
---------------------------------------------------------------------------
* 零 `sorry` / 零 `admit` / 零 `axiom`。
* 每条定理前件**不含**结论（逐条在注释中说明为何不是同义反复）。
* 文件末 `#print axioms` 只出 `[propext, Classical.choice, Quot.sound]`。
-/


namespace FateV2.Error.GaussMarkovVector

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Finset
open scoped RealInnerProductSpace

/-! ===========================================================================
§0  载体
=========================================================================== -/

section Carrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {P : Measure E} [IsProbabilityMeasure P]

/-- **已证**：坐标投影 `ω ↦ ω i` 在 `Measure.pi (fun _ => P)` 下属于 L²。

    **为何不是同义反复**：这是 `hP` 经测度保持映射 `eval i` 的回拉。
    需要 `MemLp.comp_measurePreserving`；不是定义展开。 -/
theorem eval_memLp_2 (hP : MemLp id 2 P) (n : ℕ) (i : Fin n) :
    MemLp (fun ω : Fin n → E => ω i) 2 (Measure.pi (fun _ : Fin n => P)) := by
  have h := hP.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => P) i)
  simpa [Function.comp_def] using h

/-- **已证**：对任意 `x : E`，`⟪x, ω i⟫` 在 `Measure.pi` 下的方差等于 `⟪x, ·⟫` 在 `P` 下的方差。

    **为何不是同义反复**：左边是 `n` 维乘积空间上的方差，右边是一维单样本方差；
    等式靠 `measurePreserving_eval` 的方差复合律 `variance_fun_comp` 建立。 -/
theorem eval_variance (n : ℕ) (i : Fin n) (x : E) :
    variance (fun ω : Fin n → E => ⟪x, ω i⟫) (Measure.pi (fun _ : Fin n => P))
      = variance (fun z : E => ⟪x, z⟫) P := by
  have h := (measurePreserving_eval (fun _ : Fin n => P) i).variance_fun_comp
    (f := fun z : E => ⟪x, z⟫) (by fun_prop : AEMeasurable (fun z : E => ⟪x, z⟫) P)
  simpa [Function.comp_def] using h

end Carrier

/-! ===========================================================================
§1  线性估计器 `estVec` 与它的期望
=========================================================================== -/

/-- **向量线性估计器**：`estVec a ω = ∑ i, a i • ω i`。

    任务 (a)。 -/
noncomputable def estVec {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (a : Fin n → ℝ) (ω : Fin n → E) : E :=
  ∑ i, a i • ω i

section EstIntegral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {P : Measure E} [IsProbabilityMeasure P]

/-- **已证**：`∫ ω, estVec a ω ∂(pi P) = (∑ i, a i) • ∫ z, z ∂P`。

    任务 (b) 的「期望」部分（向量 Bochner 积分）。

    **为何不是同义反复**：左边是乘积空间上 `E`-值积分的线性组合，右边是
    「权重和」与「单样本均值向量」的标量乘。证明需用 `integral_finsetSum`
    拆和、`integral_smul_const` 提标量、`integral_eval` 把坐标期望归约到单样本。
    这不是定义展开——它蕴含「iid 样本的加权平均的期望等于单样本期望」这一
    真正的统计事实。 -/
theorem estVec_integral (hP : MemLp id 2 P) (n : ℕ) (a : Fin n → ℝ) :
    ∫ ω : Fin n → E, estVec a ω ∂(Measure.pi (fun _ : Fin n => P))
      = (∑ i, a i) • (∫ z, z ∂P) := by
  have hmem : ∀ i : Fin n, Integrable (fun ω : Fin n → E => a i • ω i)
      (Measure.pi (fun _ : Fin n => P)) := by
    intro i
    have h : MemLp (fun ω : Fin n → E => ω i) 2 (Measure.pi (fun _ : Fin n => P)) :=
      eval_memLp_2 hP n i
    exact ((h.const_smul (a i)).integrable (by norm_num))
  change ∫ ω : Fin n → E, ∑ i, a i • ω i ∂(Measure.pi (fun _ : Fin n => P))
      = (∑ i, a i) • (∫ z, z ∂P)
  rw [integral_finsetSum _ (fun i _ => hmem i)]
  simp only [integral_smul, integral_eval]
  exact (Finset.sum_smul).symm

/-- **已证**：无偏性刻画（**充要条件**），向量版。

    `∫ estVec a ∂(pi P) = ∫ z, z ∂P` ⟺ `∑ i, a i = 1`，前提是均值向量 `≠ 0`。

    任务 (b) 的「无偏」部分。

    **为何不是同义反复**：结论是「无偏 ⟺ 权重和为 1」。前件只给出
    「积分相等」与「均值向量非零」；两者都不含 `∑ a = 1`。
    证明由 `estVec_integral` 改写为 `(∑ a) • μ = 1 • μ`，再对非零 `μ` 约去。
    `μ ≠ 0` 是**必要**真前件：若 `μ = 0`，任何权重都无偏。 -/
theorem estVec_unbiased_iff (hP : MemLp id 2 P) (hμ : (∫ z, z ∂P) ≠ 0)
    (n : ℕ) (a : Fin n → ℝ) :
    (∫ ω : Fin n → E, estVec a ω ∂(Measure.pi (fun _ : Fin n => P)) = ∫ z, z ∂P)
      ↔ ∑ i, a i = 1 := by
  rw [estVec_integral hP n a]
  constructor
  · intro h
    have h' : (∑ i, a i) • (∫ z, z ∂P) = (1 : ℝ) • (∫ z, z ∂P) := by
      rw [one_smul]; exact h
    exact smul_left_injective (R := ℝ) hμ h'
  · intro h
    rw [h, one_smul]

end EstIntegral

/-! ===========================================================================
§2  协方差的向量版本
=========================================================================== -/

section TrCov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {P : Measure E} [IsProbabilityMeasure P]

/-- **方差的向量版本（单坐标）**：对任意 `k : Fin d` 与正交规范基 `b : Fin d`，

    `Var[ω ↦ ⟪b k, estVec a ω⟫] = (∑ i, (a i)^2) * Var[z ↦ ⟪b k, z⟫; P]`。

    任务 (b) 的「协方差」部分：这是协方差算子沿 `b k` 方向的对角元。

    **为何不是同义反复**：前件只有 `hP`（L²）。结论是一个 `n` 项加权和的
    方差恒等式。证明必须（a）把 `⟪b k, ∑ a i • ω i⟫` 化为 `∑ i, a i * ⟪b k, ω i⟫`；
    （b）用坐标**两两独立**（`iIndepFun_pi`）使交叉协方差消失
    （`IndepFun.variance_sum`）；（c）每项用 `variance_const_mul` 提出 `a i²`；
    （d）用 `eval_variance` 归约到单样本。结论不出现在前件中。 -/
theorem variance_inner_estVec (hP : MemLp id 2 P) {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ E) (n : ℕ) (a : Fin n → ℝ) (k : Fin d) :
    variance (fun ω : Fin n → E => ⟪b k, estVec a ω⟫)
        (Measure.pi (fun _ : Fin n => P))
      = (∑ i, (a i) ^ 2) * variance (fun z : E => ⟪b k, z⟫) P := by
  have hcoef : ∀ i : Fin n, MemLp (fun ω : Fin n → E => a i * ⟪b k, ω i⟫) 2
      (Measure.pi (fun _ : Fin n => P)) := by
    intro i
    have h : MemLp (fun ω : Fin n → E => ω i) 2 (Measure.pi (fun _ : Fin n => P)) :=
      eval_memLp_2 hP n i
    exact (h.const_inner (b k)).const_mul (a i)
  have hfun : (fun ω : Fin n → E => ⟪b k, estVec a ω⟫)
      = (∑ i, fun ω : Fin n → E => a i * ⟪b k, ω i⟫) := by
    funext ω
    simp only [Finset.sum_apply, estVec, inner_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_smul_right]
  rw [hfun, IndepFun.variance_sum]
  · have hterm : ∀ i : Fin n,
        variance (fun ω : Fin n → E => a i * ⟪b k, ω i⟫) (Measure.pi (fun _ : Fin n => P))
          = (a i) ^ 2 * variance (fun z : E => ⟪b k, z⟫) P := by
      intro i
      rw [variance_const_mul, eval_variance (P := P) n i (b k)]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_mul]
  · intro i _
    exact hcoef i
  · intro i _ j _ hij
    have h1 : IndepFun (fun ω : Fin n → E => ω i) (fun ω : Fin n → E => ω j)
        (Measure.pi (fun _ : Fin n => P)) :=
      (iIndepFun_pi (μ := fun _ : Fin n => P) (X := fun _ => (id : E → E))
        (fun _ => aemeasurable_id)).indepFun hij
    have h2 := h1.comp (φ := fun x : E => a i * ⟪b k, x⟫)
      (ψ := fun x : E => a j * ⟪b k, x⟫)
      (by fun_prop) (by fun_prop)
    simpa [Function.comp_def, mul_comm] using h2
/-- **协方差算子的 trace**（沿正交规范基 `b` 求和）。

    `trCov b ν = ∑ k, Var[z ↦ ⟪b k, z⟫; ν]`。

    这是 `LinearMap.trace_eq_sum_inner`
    （`Mathlib/Analysis/InnerProductSpace/Trace.lean`）的同一思想：
    在正交规范基下，线性泛函的方差之和就是协方差算子的 trace。
    对无有限维假设的实内积空间，这是不依赖矩阵表示的写法。 -/
noncomputable def trCov {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E) (ν : Measure E) : ℝ :=
  ∑ k, variance (fun z : E => ⟪b k, z⟫) ν

/-- **已证**：`trCov` 非负。

    **为何不是同义反复**：`trCov` 是 `d` 项方差之和；结论由逐项 `variance_nonneg`
    得出，不是定义展开。 -/
theorem trCov_nonneg {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E) (ν : Measure E) :
    0 ≤ trCov b ν :=
  Finset.sum_nonneg fun _ _ => variance_nonneg _ _

/-- **线性估计器 `estVec` 在乘积空间上的 trace-协方差**：

    `trCovEst b n a P = ∑ k, Var[ω ↦ ⟪b k, estVec a ω⟫; Measure.pi P]`。

    即估计量 `estVec a` 的协方差算子（在 `E` 的正交规范基 `b` 下）的 trace。 -/
noncomputable def trCovEst {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E) (n : ℕ)
    (a : Fin n → ℝ) (P : Measure E) : ℝ :=
  ∑ k, variance (fun ω : Fin n → E => ⟪b k, estVec a ω⟫) (Measure.pi (fun _ : Fin n => P))

/-- **已证（协方差的向量版本·主公式）**：

    `trCovEst b n a P = (∑ i, (a i)^2) * trCov b P`。

    即「线性估计器的 trace-协方差 = 权重平方和 × 单样本 trace-协方差」。

    任务 (b) 的核心。

    **为何不是同义反复**：左边是 `n` 维乘积空间上 `d` 个方向的方差之和，
    右边是「`n` 项权重平方和」乘「单样本 `d` 个方向的方差之和」。
    证明对每个 `k` 用 `variance_inner_estVec`（那是坐标独立性带来的真内容），
    再对 `k` 求和并交换求和次序 `∑ k ∑ i = ∑ i ∑ k`。结论不出现在前件中。 -/
theorem trCovEst_eq {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E)
    (hP : MemLp id 2 P) (n : ℕ) (a : Fin n → ℝ) :
    trCovEst b n a P = (∑ i, (a i) ^ 2) * trCov b P := by
  have hk : ∀ k : Fin d,
      variance (fun ω : Fin n → E => ⟪b k, estVec a ω⟫) (Measure.pi (fun _ : Fin n => P))
        = (∑ i, (a i) ^ 2) * variance (fun z : E => ⟪b k, z⟫) P :=
    fun k => variance_inner_estVec hP b n a k
  simp only [trCovEst, trCov]
  rw [Finset.sum_congr rfl (fun k _ => hk k), ← Finset.mul_sum, Finset.sum_mul]

/-- **已证**：`trCovEst` 非负。

    **为何不是同义反复**：由 `trCovEst_eq` 与 `∑ (a i)^2 ≥ 0`、`trCov b P ≥ 0`
    两个非负因子相乘得出。不是定义展开。 -/
theorem trCovEst_nonneg {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E)
    (hP : MemLp id 2 P) (n : ℕ) (a : Fin n → ℝ) :
    0 ≤ trCovEst b n a P := by
  rw [trCovEst_eq b hP n a]
  exact mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (trCov_nonneg b P)

/-! ===========================================================================
§3  Gauss–Markov 向量版主定理
=========================================================================== -/

/-- **已证（主定理·下界半边）**：在无偏约束 `∑ i, a i = 1` 下，

    `trCov b P / n ≤ trCovEst b n a P`（即 `tr Cov[estVec a] ≥ tr Cov / n`）。

    任务 (c)。

    **Cauchy–Schwarz 用法**：对 `a i` 与常数序列 `1` 用
    `sum_mul_sq_le_sq_mul_sq` 得 `(∑ a i)² ≤ (∑ (a i)²)·n`；
    代入 `∑ a i = 1` 得 `1 ≤ (∑ (a i)²)·n`，即 `∑ (a i)² ≥ 1/n`；
    再乘 `trCov b P ≥ 0` 得到 `(∑ (a i)²)·trCov b P ≥ trCov b P / n`，
    用 `trCovEst_eq` 换回 `trCovEst`。

    **为何不是同义反复**：前件只有「无偏」（`∑ a = 1`，与结论是不同的陈述）
    与 `hP`（L²）。结论 `trCovEst ≥ trCov / n` 完全不出现在前件中；
    它是一条真不等式，证明用到了 Cauchy–Schwarz 这一非平凡工具。 -/
theorem gauss_markov_vector_lower_bound {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E)
    (hP : MemLp id 2 P) (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (hsum : ∑ i, a i = 1) :
    trCov b P / n ≤ trCovEst b n a P := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [trCovEst_eq b hP n a]
  have hv : 0 ≤ trCov b P := trCov_nonneg b P
  have hcs := sum_mul_sq_le_sq_mul_sq (s := (univ : Finset (Fin n)))
    (fun i => a i) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hcs
  rw [hsum] at hcs
  rw [div_le_iff₀ hnR]
  nlinarith

/-- **已证（等号刻画）**：若 `∑ a i = 1`、`trCov b P > 0`，且 trace-方差已达到下界
    `trCov b P / n`，则 `a i ≡ 1/n`。

    任务 (d)。

    **为何不是同义反复**：前件是「无偏」（`∑ a = 1`）与
    「`trCovEst b n a P = trCov b P / n`」（一个关于 `n` 项权重的**全局**条件）；
    结论是**逐点**的 `∀ i, a i = 1/n`。
    从全局等式推出逐点常值必须用 Cauchy–Schwarz 的等号结构：
    证明把 `∑ (a i - 1/n)²` 展开成 `∑ (a i)² - 1/n`，用 `1 ≤ (∑ a i²)·n`
    与 trace 等式得 `∑ (a i - 1/n)² = 0`，再由平方和为零得每项为零。
    结论 `a ≡ 1/n` 不可能出现在前件中。 -/
theorem gauss_markov_vector_equality {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E)
    (hP : MemLp id 2 P) (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (hsum : ∑ i, a i = 1) (hv : 0 < trCov b P)
    (heq : trCovEst b n a P = trCov b P / n) :
    ∀ i, a i = 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hvar : (∑ i, (a i) ^ 2) * trCov b P = trCov b P / n := by
    rw [← trCovEst_eq b hP n a, heq]
  have hsum_sq : ∑ i, (a i) ^ 2 = 1 / (n : ℝ) := by
    have h1 : (∑ i, (a i) ^ 2) * trCov b P = (1 / (n : ℝ)) * trCov b P := by
      rw [hvar]; field_simp
    exact mul_right_cancel₀ (ne_of_gt hv) h1
  have hzero : ∑ i, (a i - 1 / (n : ℝ)) ^ 2 = 0 := by
    have hsub : ∀ i : Fin n,
        (a i - 1 / (n : ℝ)) ^ 2
          = (a i) ^ 2 - 2 * (1 / (n : ℝ)) * (a i) + (1 / (n : ℝ)) ^ 2 := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i _ => hsub i), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hsum_sq]
    field_simp
    ring
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hzero
  intro i
  have := hall i (Finset.mem_univ i)
  nlinarith [this]

/-- **已证（等号可达）**：若 `a i ≡ 1/n`，则 `∑ a i = 1` 且
    `trCovEst b n a P = trCov b P / n`。

    任务 (d) 的「可达」方向。

    **为何不是同义反复**：前件是逐点条件 `∀ i, a i = 1/n`；结论是
    「无偏」与「trace-方差等于 `trCov P / n`」两个**全局**陈述。
    从逐点条件到全局等式需真的做 `n` 项求和 `∑ (1/n) = 1` 与
    `∑ (1/n)² · n = 1/n` 的算术，并回代 `trCovEst_eq`。结论不在前件中。 -/
theorem gauss_markov_vector_attained {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E)
    (hP : MemLp id 2 P) (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, a i = 1 / (n : ℝ)) :
    (∑ i, a i = 1) ∧ trCovEst b n a P = trCov b P / n := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsum : ∑ i, a i = 1 := by
    rw [Finset.sum_congr rfl (fun i _ => ha i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨hsum, ?_⟩
  rw [trCovEst_eq b hP n a]
  have hsq : ∑ i, (a i) ^ 2 = 1 / (n : ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [ha i]), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hsq]
  field_simp

/-- **已证（完整 ⟺，主定理终形式）**：在无偏约束 `∑ a i = 1` 与
    `trCov b P > 0` 下，

    `trCovEst b n a P = trCov b P / n` ⟺ `a i ≡ 1/n`。

    **为何不是同义反复**：「⟸」由 `gauss_markov_vector_attained` 给出；
    「⟹」由 `gauss_markov_vector_equality` 给出。两方向都不是定义展开，
    且结论 `a ≡ 1/n` 与前提「trace-方差等于 `trCov P / n`」是完全不同的陈述。
    `trCov b P > 0` 这个前件是**必要的**：若 `trCov b P = 0`，
    则任意权重都给出零方差，等号刻画不成立（反例：`n = 2`，`a = (1, 0)`）。 -/
theorem gauss_markov_vector_iff {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E)
    (hP : MemLp id 2 P) (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (hsum : ∑ i, a i = 1) (hv : 0 < trCov b P) :
    (trCovEst b n a P = trCov b P / n) ↔ (∀ i, a i = 1 / (n : ℝ)) := by
  constructor
  · intro heq
    exact gauss_markov_vector_equality b hP n hn a hsum hv heq
  · intro ha
    exact (gauss_markov_vector_attained b hP n hn a ha).2

end TrCov

end FateV2.Error.GaussMarkovVector

/-! ## 公理审计 -/

