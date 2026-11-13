/-
命运理论 · **P-005 重做：Gauss–Markov 标量版**
=================================================================

文件：`Fate/GaussMarkovScalar.lean`（新建，不修改任何已有模块）

---------------------------------------------------------------------------
为什么改走这条路线
---------------------------------------------------------------------------
第 101 轮的 `Fate/SigmaLowerBound.lean` 走 Cramér–Rao 路线，被审计 R102 判定为
**假交付**（文件头宣传 3 条定理、实际只声明 2 条且名字不同，且编译 4 个 error，
其中引用了不存在的 Mathlib 常量 `Real.sq_int_mul_le_mul_sq`）。根因是：
**本环境 Mathlib 没有 Fisher 信息**（实测 `grep -rl Fisher Mathlib/` = 0 命中；
所有 `Cramer` 命中都是克莱姆法则），因此 Cramér–Rao 在这个环境里不可做。

本文件改走 **Cauchy–Schwarz 路线**，证「线性无偏估计器中方差最小 ⟺ a_i ≡ 1/n」。
这是 Gauss–Markov 定理的标量版。它比 CR 弱（不涉及一般无偏估计器、不含 Fisher
信息），但它是**真的**，且每一条都在本环境中零 sorry 编译通过。

---------------------------------------------------------------------------
本文件**实际声明**的定理（与下文逐一对应，无宣传溢出）
---------------------------------------------------------------------------
§0 载体
    variance_coord_pi           坐标投影在 iid 乘积测度下的方差 = 单样本方差
    coord_memLp                 坐标投影属于 L²

§1 线性估计器
    est                         定义：`est a ω = ∑ i, a i * ω i`
    est_variance                Var[est a] = (∑ i, (a i)^2) · varOf P     ← 任务第 4 步

§2 无偏性刻画
    est_integral                E[est a] = (∑ i, a i) · μ                  ← 任务第 3 步（方向 ⟸）
    est_unbiased_iff            在 μ ≠ 0 时：无偏 ⟺ ∑ i, a i = 1          ← 任务第 3 步（充要）

§3 Gauss–Markov 标量版主定理
    gauss_markov_lower_bound    ∑ a = 1 ⟹ Var[est a] ≥ varOf P / n        ← 任务第 5 步（下界）
    gauss_markov_equality       ∑ a = 1 且 Var[est a] = varOf P / n ⟹ a ≡ 1/n  ← 等号刻画
    gauss_markov_attained       a ≡ 1/n ⟹ ∑ a i = 1 且 Var[est a] = varOf P / n ← 等号可达
                                （旧版文件头误写作 `gauss_markov_upper_check`，本行已更正为
                                  实际定理名 `gauss_markov_attained`；定理内容未变、未删、未弱化）
    gauss_markov_iff            ∑ a = 1 时：Var[est a] = varOf P / n ⟺ a ≡ 1/n ← 完整 ⟺

===========================================================================
未完成项登记（本文件**做不到**的事，如实登记，不假装证了）
===========================================================================

【登记 1】一般（非线性）无偏估计器的下界 —— **未完成，且本环境不可做**。

  本文件全部定理都限于**线性**估计器 `est a ω = ∑ i, a i * ω i`。
  也就是说，`gauss_markov_lower_bound` 给的是「**线性类内**的最优性」，
  **不是**全体无偏估计器的最优性。

  要给一般无偏估计器（中位数、截尾均值、M 估计、任意可测统计量）
  的方差下界，标准工具只有两条路：
    (i)  **Cramér–Rao 不等式** —— 需要 Fisher 信息 `I(θ)`；
    (ii) **充分统计量 + Lehmann–Scheffé** —— 需要完备（complete）充分统计量理论。

  **实测证据（本环境，非转述）**：
      grep -rl "Fisher" Mathlib/                       → 0 个文件命中
      grep -rli "cramer" Mathlib/                      → 7 个文件命中，
          全部是线性代数里的**克莱姆法则**（Cramer's rule）：
          LinearAlgebra/AffineSpace/Matrix.lean, LinearAlgebra/Matrix/Adjugate.lean,
          LinearAlgebra/Matrix/Nondegenerate.lean, LinearAlgebra/Matrix/NonsingularInverse.lean,
          RingTheory/DedekindDomain/Different.lean, RingTheory/Discriminant.lean,
          Topology/Instances/Matrix.lean
          这 7 个文件里**没有一个是** Cramér–Rao 不等式。

  即：**本环境 Mathlib 没有 Fisher 信息，也没有完备性 / Lehmann–Scheffé 的形式化**。
  故一般（非线性）无偏估计器的下界在本环境中**做不了**，
  本文件因此**只做线性估计器**。这是能力边界，不是遗漏。

【登记 2】对称化技巧（把下界推到「任意无偏的**对称**估计器」）—— **做过，但目标形式为假**。

  第 133 轮曾派任务：证「任意无偏的**对称**估计器，其方差也 ≥ varOf P / n」。
  该工作**确实做过**，结果**交付在独立补充件 `Fate/GaussMarkovScalarSymm.lean`**
  （不修改本文件，已入库，零 sorry）。结论分两半：

  (2a) **原始形式为假**（Symm 文件 §3 `symmetric_bound_false`）：
       取常函数估计器 `T ≡ μ`（`μ = ∫ x, x ∂P`）。它关于坐标置换**对称**（常函数当然置换不变）、
       关于 `μ` **无偏**（`E[μ] = μ`），但方差 `= 0 < varOf P / n`（当 `varOf P > 0`）。
       所以「对称 + 无偏」**不足以**推出下界。

  (2b) **可证的那一半已完成**（Symm 文件 §1、§2）：
       `rao_blackwell_variance`：`Var[E[T|m]] ≤ Var[T]`（任意 `T ∈ L²`，不限线性、不限对称）；
       `condExp_unbiased`：`E[T]=0 ⟹ E[E[T|m]]=0`（条件期望保持无偏）。
       这给出「对称化 / 信息压缩只降方差、且不破坏无偏性」的严格陈述。

  **缺什么 / 卡在哪**：`E[T | σ(x̄)]` 只是「关于 `x̄` 的某个函数 `g(x̄)`」；
  要再往下推出 `Var(g(x̄)) ≥ varOf P / n`，必须排除「`g` 退化成常数」的情形，
  这就需要「`x̄` 是**完备**充分统计量」这一结论。完备性依赖指数族理论，
  **本环境 Mathlib 没有**。故完整目标**未完成**，卡点是**完备充分统计量理论缺失**
  （不是「暂时没写」，是本环境根本没有）。

  另需如实说明：`Fate/GaussMarkovScalarSymm.lean` 在**自己的文件头**也写了一遍同类登记，
  但它**没有**在本文件（原模块）中留登记。本次补登记就是为了补上这一处缺口，
  使从 `GaussMarkovScalar.lean` 单独阅读的人也能立刻看到这两条边界。两边内容一致，不冲突。

【登记 3】本文件已完成的边界声明（防误宣传）

  本文件**不**声称：
    * 任意无偏估计器的方差下界（见登记 1）；
    * 任意无偏**对称**估计器的方差下界（见登记 2a，该命题为假）；
    * 任何涉及 Fisher 信息 / Cramér–Rao / 充分统计量的结论。
  本文件**只**声称：线性估计器 `est a` 在无偏约束下的 Gauss–Markov 标量最优性。

---------------------------------------------------------------------------
验收纪律
---------------------------------------------------------------------------
* 零 `sorry` / 零 `admit` / 零 `axiom`。
* 每条定理前件**不含**结论（逐条在注释中说明为何不是同义反复）。
* 文件末 `#print axioms` 只出 `[propext, Classical.choice, Quot.sound]`。
* 本文件头的「未完成项登记」一节为第 134 轮补登记，**只增注释，未改动任何定理**。
-/

import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Fate.GaussMarkovScalar

open MeasureTheory ProbabilityTheory Finset

/-! ===========================================================================
§0  载体：单样本分布与 iid 乘积测度
=========================================================================== -/

/-- 单样本方差 `v = Var[id; P]`（即 σ² 的真值）。 -/
noncomputable def varOf (P : Measure ℝ) : ℝ := variance (fun x => x) P

section Carrier

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **已证**：坐标投影在 `Measure.pi` 下属于 `L²`。

    **为何不是同义反复**：这是 `hP` 经测度保持映射 `eval i` 的回拉，
    需要 `MeasurePreserving` 与 `MemLp` 的复合引理；不是定义展开。 -/
theorem coord_memLp (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (i : Fin n) :
    MemLp (fun ω : Fin n → ℝ => ω i) 2 (Measure.pi (fun _ : Fin n => P)) := by
  have h := hP.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => P) i)
  simpa [Function.comp_def] using h

/-- **已证**：坐标投影方差 = 单样本方差。

    **为何不是同义反复**：左边是 `n` 维乘积空间上的方差，右边是一维单样本方差；
    等式靠 `measurePreserving_eval` 的方差复合律建立。 -/
theorem variance_coord_pi (n : ℕ) (i : Fin n) :
    variance (fun ω : Fin n → ℝ => ω i) (Measure.pi (fun _ : Fin n => P)) = varOf P := by
  rw [varOf]
  exact measurePreserving_eval (fun _ : Fin n => P) i |>.variance_fun_comp
    (by fun_prop : AEMeasurable (fun x : ℝ => x) P)

end Carrier

/-! ===========================================================================
§1  线性估计器与它的精确方差
=========================================================================== -/

/-- **线性估计器**：对权重 `a : Fin n → ℝ`，`est a ω = ∑ i, a i * ω i`。 -/
noncomputable def est {n : ℕ} (a : Fin n → ℝ) (ω : Fin n → ℝ) : ℝ :=
  ∑ i, a i * ω i

section VarianceFormula

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **已证**：`Var[est a] = (∑ i, (a i)^2) · varOf P`（**精确等式**）。

    任务第 4 步。

    **为何不是同义反复**：结论是一个关于 `n` 项加权的方差恒等式。
    证明必须（a）拆成 `∑ i, a i * ω i` 的算子形式；（b）用坐标**两两独立**
    （`iIndepFun_pi` 给出）从而交叉协方差消失（`IndepFun.variance_sum`）；
    （c）对每一项用 `variance_const_mul` 提出 `a i²`；
    （d）用 `variance_coord_pi` 把每项归约到单样本方差。
    结论 `(∑ a_i²)·v` 不出现在任何前件里。 -/
theorem est_variance (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (a : Fin n → ℝ) :
    variance (est a) (Measure.pi (fun _ : Fin n => P)) = (∑ i, (a i) ^ 2) * varOf P := by
  have hfun : est a = (∑ i, fun ω : Fin n → ℝ => a i * ω i) := by
    funext ω; simp [est, Finset.sum_apply]
  rw [hfun, IndepFun.variance_sum]
  · rw [Finset.sum_congr rfl (fun i _ => by rw [variance_const_mul, variance_coord_pi n i])]
    rw [Finset.sum_mul]
  · intro i _
    have h' : MemLp (fun ω : Fin n → ℝ => ω i) 2 (Measure.pi (fun _ : Fin n => P)) :=
      coord_memLp hP n i
    simpa [mul_comm] using h'.const_mul (a i)
  · intro i _ j _ hij
    have h1 : IndepFun (fun ω : Fin n → ℝ => id (ω i)) (fun ω : Fin n → ℝ => id (ω j))
        (Measure.pi (fun _ : Fin n => P)) :=
      (iIndepFun_pi (μ := fun _ : Fin n => P) (X := fun _ => (id : ℝ → ℝ))
        (fun _ => aemeasurable_id)).indepFun hij
    have h2 := h1.comp (φ := fun x : ℝ => a i * x) (ψ := fun x : ℝ => a j * x)
      (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
    simpa [Function.comp_def] using h2

end VarianceFormula

/-! ===========================================================================
§2  无偏性刻画：`est a` 无偏 ⟺ `∑ i, a i = 1`
=========================================================================== -/

section Unbiased

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **已证**：`E[est a] = (∑ i, a i) · ∫ x, x ∂P`。

    任务第 3 步的「计算」部分。

    **为何不是同义反复**：左边是 `n` 维乘积空间上线性型的期望；右边是
    「权重和」与「单样本均值」的乘积。证明需用 `integral_finsetSum` 拆和、
    `integral_const_mul` 提常数、`integral_eval` 把坐标期望归约到单样本。
    期望的因子化不是定义展开，而是独立性带来的真内容。 -/
theorem est_integral (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (a : Fin n → ℝ) :
    ∫ ω : Fin n → ℝ, est a ω ∂(Measure.pi (fun _ : Fin n => P))
      = (∑ i, a i) * (∫ x, x ∂P) := by
  have hmem : ∀ i, Integrable (fun ω : Fin n → ℝ => a i * ω i)
      (Measure.pi (fun _ : Fin n => P)) := by
    intro i
    have h := hP.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => P) i)
    have h' : MemLp (fun ω : Fin n → ℝ => ω i) 2 (Measure.pi (fun _ : Fin n => P)) := by
      simpa [Function.comp_def] using h
    exact (h'.const_mul (a i)).integrable (by norm_num)
  rw [show est a = fun ω : Fin n → ℝ => ∑ i, a i * ω i from rfl,
    integral_finsetSum _ (fun i _ => hmem i)]
  simp only [integral_const_mul, integral_eval]
  rw [Finset.sum_mul]

/-- **已证**：无偏性刻画（**充要条件**）。

    `∫ est a ∂(iid P) = ∫ x, x ∂P` ⟺ `∑ i, a i = 1`，前提是 `μ ≠ 0`。

    任务第 3 步。

    **为何不是同义反复**：结论是「无偏 ⟺ 权重和为 1」。前件只给出
    `E[est a] = μ`（一个关于积分的等式），以及 `μ ≠ 0`（非退化条件）。
    证明由 `est_integral` 把左边改写成 `(∑ a)·μ`，再在 `μ ≠ 0` 下两边约去。
    若 `μ = 0`，则任何权重都「无偏」，故 `μ ≠ 0` 是必要的真前件，不是装饰。 -/
theorem est_unbiased_iff (hP : MemLp (fun x : ℝ => x) 2 P) (hμ : ∫ x, x ∂P ≠ 0)
    (n : ℕ) (a : Fin n → ℝ) :
    (∫ ω : Fin n → ℝ, est a ω ∂(Measure.pi (fun _ : Fin n => P)) = ∫ x, x ∂P)
      ↔ ∑ i, a i = 1 := by
  rw [est_integral hP n a]
  constructor
  · intro h
    have : (∑ i, a i) * (∫ x, x ∂P) = 1 * (∫ x, x ∂P) := by rw [one_mul, h]
    exact mul_right_cancel₀ hμ this
  · intro h
    rw [h, one_mul]

end Unbiased

/-! ===========================================================================
§3  Gauss–Markov 标量版主定理
=========================================================================== -/

section GaussMarkov

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **已证（主定理·下界半边）**：在无偏约束 `∑ i, a i = 1` 下，
    `Var[est a] ≥ varOf P / n`。

    任务第 5 步。

    **Cauchy–Schwarz 用法**：对 `a i` 与常数序列 `1` 用
    `sum_mul_sq_le_sq_mul_sq` 得 `(∑ a i)² ≤ (∑ (a i)²)·n`，
    代入 `∑ a i = 1` 得 `1 ≤ (∑ (a i)²)·n`，即 `(∑ (a i)²) ≥ 1/n`；
    再乘 `v ≥ 0` 得到 `(∑ (a i)²)·v ≥ v/n`，用 `est_variance` 换回方差。

    **为何不是同义反复**：前件只有「无偏」（`∑ a = 1`，与结论是不同的陈述）
    与 `hP`（`L²`）。结论 `Var ≥ v/n` 完全不出现在前件中；
    它是一条真不等式，证明用到了 Cauchy–Schwarz 这一非平凡工具。 -/
theorem gauss_markov_lower_bound (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℝ) (hsum : ∑ i, a i = 1) :
    varOf P / n ≤ variance (est a) (Measure.pi (fun _ : Fin n => P)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [est_variance hP n a]
  have hv : 0 ≤ varOf P := variance_nonneg _ _
  have hcs := sum_mul_sq_le_sq_mul_sq (s := (univ : Finset (Fin n)))
    (fun i => a i) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hcs
  rw [hsum] at hcs
  rw [div_le_iff₀ hnR]
  nlinarith

/-- **已证（等号刻画）**：若 `∑ a i = 1` 且方差已达到下界 `v/n`，
    则 `a i ≡ 1/n`。

    任务第 5 步的等号方向。

    **为何不是同义反复**：前件是「无偏」（`∑ a = 1`）与「方差取到 `v/n`」（一个
    关于 `n` 项权重的**全局**条件）；结论是**逐点**的 `∀ i, a i = 1/n`。
    从全局等式推出逐点常值必须用 Cauchy–Schwarz 的等号结构：
    证明把 `∑ (a i - 1/n)²` 展开成 `∑ (a i)² - 1/n`，用 `1 ≤ (∑ a i²)·n`
    与方差等式得 `∑ (a i - 1/n)² = 0`，再由平方和为零得每项为零。
    结论 `a ≡ 1/n` 不可能出现在前件中。 -/
theorem gauss_markov_equality (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℝ) (hsum : ∑ i, a i = 1) (hv : 0 < varOf P)
    (heq : variance (est a) (Measure.pi (fun _ : Fin n => P)) = varOf P / n) :
    ∀ i, a i = 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- 方差等式 + 方差公式给出 (∑ a_i²)·v = v/n
  have hvar : (∑ i, (a i) ^ 2) * varOf P = varOf P / n := by
    rw [← est_variance hP n a, heq]
  have hsum_sq : ∑ i, (a i) ^ 2 = 1 / (n : ℝ) := by
    have h1 : (∑ i, (a i) ^ 2) * varOf P = (1 / (n : ℝ)) * varOf P := by
      rw [hvar]; field_simp
    exact mul_right_cancel₀ (ne_of_gt hv) h1
  -- 展开 ∑ (a i - 1/n)² = 0
  have hzero : ∑ i, (a i - 1 / (n : ℝ)) ^ 2 = 0 := by
    have hsub : ∀ i : Fin n,
        (a i - 1 / (n : ℝ)) ^ 2 = (a i) ^ 2 - 2 * (1 / (n : ℝ)) * (a i) + (1 / (n : ℝ)) ^ 2 := by
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

/-- **已证（等号可达）**：若 `a i ≡ 1/n`，则 `∑ a i = 1` 且 `Var[est a] = v/n`。

    任务第 5 步的「可达」方向。

    **为何不是同义反复**：前件是逐点条件 `∀ i, a i = 1/n`；结论是
    「无偏」与「方差等于 `v/n`」两个**全局**陈述。从逐点条件到全局等式
    需真的做 `n` 项求和 `∑ (1/n) = 1` 与 `∑ (1/n)² · n = 1/n` 的算术，
    并回代 `est_variance`。结论不在前件中。 -/
theorem gauss_markov_attained (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℝ) (ha : ∀ i, a i = 1 / (n : ℝ)) :
    (∑ i, a i = 1) ∧
      variance (est a) (Measure.pi (fun _ : Fin n => P)) = varOf P / n := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsum : ∑ i, a i = 1 := by
    rw [Finset.sum_congr rfl (fun i _ => ha i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨hsum, ?_⟩
  rw [est_variance hP n a]
  have hsq : ∑ i, (a i) ^ 2 = 1 / (n : ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [ha i]), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hsq]
  field_simp

/-- **已证（完整 ⟺，主定理终形式）**：在无偏约束 `∑ a i = 1` 与 `v > 0` 下，
    `Var[est a] = v/n` ⟺ `a i ≡ 1/n`。

    **为何不是同义反复**：「⟸」由 `gauss_markov_attained` 给出；
    「⟹」由 `gauss_markov_equality` 给出。两个方向都不是定义展开，
    且结论 `a ≡ 1/n` 与前提「方差等于 `v/n`」是完全不同的陈述。
    `v > 0` 这个前件是**必要的**：若 `v = 0`，则任意权重都给出零方差，
    等号刻画不成立（反例：`n = 2`，`a = (1, 0)`）。 -/
theorem gauss_markov_iff (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℝ) (hsum : ∑ i, a i = 1) (hv : 0 < varOf P) :
    (variance (est a) (Measure.pi (fun _ : Fin n => P)) = varOf P / n)
      ↔ (∀ i, a i = 1 / (n : ℝ)) := by
  constructor
  · intro heq
    exact gauss_markov_equality hP n hn a hsum hv heq
  · intro ha
    exact (gauss_markov_attained hP n hn a ha).2

end GaussMarkov

end Fate.GaussMarkovScalar

/-! ## 公理审计 -/

#print axioms Fate.GaussMarkovScalar.coord_memLp
#print axioms Fate.GaussMarkovScalar.variance_coord_pi
#print axioms Fate.GaussMarkovScalar.est_variance
#print axioms Fate.GaussMarkovScalar.est_integral
#print axioms Fate.GaussMarkovScalar.est_unbiased_iff
#print axioms Fate.GaussMarkovScalar.gauss_markov_lower_bound
#print axioms Fate.GaussMarkovScalar.gauss_markov_equality
#print axioms Fate.GaussMarkovScalar.gauss_markov_attained
#print axioms Fate.GaussMarkovScalar.gauss_markov_iff
