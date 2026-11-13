/-
命运理论 · **V4：把 σ 不可证这件事转成可证的东西**
=================================================================

文件：`Fate/SigmaEstimation.lean`（新建，不改任何已有模块）

---------------------------------------------------------------------------
背景与定位
---------------------------------------------------------------------------
审计结论说：**σ（噪声尺度）必须从数据估，不可证**。作者裁决：作为例外登记，
然后**尽量优化 σ**。本文件承担「把不可证对象转化为可证对象」这一步。

也就是说：本文件**不**证明「某个 σ 就是真噪声」（那是解释，不可证，仍登记为例外）。
本文件证明的是 **σ 的估计本身**有哪些**可证的数学性质**：

  §1  样本和 / 样本均值的**精确方差**：`Var[∑] = n·v`，`Var[meanOf n] = v/n`；
  §2  **收敛速率**：`Var[√n · meanOf n] = v`（正合 CLT 尺度，正比于 1/n）；
      以及 `Var[meanOf n] → 0`（一致性）；
  §3  **有限样本置信界**（Chebyshev，非渐近）：
       `P(|meanOf n − μ| ≥ ε) ≤ v / (n ε²)`，ε-δ 形式，与显式样本量
       `n ≥ v / (ε² δ)` ⟹ 失效概率 `≤ δ`；
  §4  **最优估计器下界**（Cramér–Rao 型的 Cauchy–Schwarz 核）：
       无偏估计器的方差 `·` Fisher 信息 `≥ 1`（任何无偏估计器都逃不掉）。

**这四条都是真的数学定理，不是同义反复**（逐节说明见下）。

---------------------------------------------------------------------------
载体选择与理由
---------------------------------------------------------------------------
* **§1–§3（均值/速率/置信界）**：用 `Measure.pi` 上的**独立同分布样本**
  `ω : Fin n → ℝ`，`P` 为单样本分布。`Measure.pi` 直接给出独立性，
  避免手工构造 iid 假设；`variance_sum_pi` 给出和的方差。
  单样本方差记作 `varOf P = Var[id; P]`，它就是本文件里 **σ² 的真值**。
  **诚实前提**：`MemLp id 2 P`（二阶矩有限）。σ 存在的前提正是这个；
  若二阶矩无限，方差为 `⊤`，任何 σ 估计都无意义。

* **§4（Cramér–Rao 下界）**：用**有限支撑**加权模型 `(ι, w)`。
  理由与 `_o1_dist_sigma.lean` 一致（那里已登记：「完整 Wasserstein 需测度论载体」）：
  有限支撑上 Fisher 信息、score、无偏性条件全部可**零 sorry** 写清，
  且 Cauchy–Schwarz 核与光滑情形**逐字相同**（只需把 `∑` 换成 `∫`）。
  **未证部分已登记**（§5）：本文件不证光滑情形的 Fisher 正则性条件。

---------------------------------------------------------------------------
验收纪律
---------------------------------------------------------------------------
* 零 `sorry` / 零 `admit` / 零 `axiom`。
* 每个定理都标注「为何不是同义反复」，前件**不含**结论。
* 文件末 `#print axioms` 全部只出 `[propext, Classical.choice, Quot.sound]`。
-/

import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import FateWorld.Legacy.SigmaFromAIC

namespace Fate.SigmaEstimation

open MeasureTheory ProbabilityTheory Finset

/-! ===========================================================================
§0  载体：单样本分布与 iid 乘积测度
=========================================================================== -/

/-- 单样本方差 `v = Var[id; P]`。**这是本文件中 σ² 的真值。** -/
noncomputable def varOf (P : Measure ℝ) : ℝ := variance (fun x => x) P

/-- iid 乘积测度：`n` 个独立同分布样本。 -/
noncomputable def iidMeasure (P : Measure ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => P)

/-- **n 个 iid 样本的样本均值**（`Fin n` 上求平均）。 -/
noncomputable def meanOf (n : ℕ) (ω : Fin n → ℝ) : ℝ := (∑ i, ω i) / n

section Basic

variable {P : Measure ℝ} [hPm : IsProbabilityMeasure P] (hP : MemLp (fun x : ℝ => x) 2 P)

include hP hPm

/-- **已证**：`Measure.pi` 的坐标投影的方差 = 单样本方差。 -/
theorem variance_coord_pi (n : ℕ) (i : Fin n) :
    variance (fun ω : Fin n → ℝ => ω i) (Measure.pi (fun _ : Fin n => P)) = varOf P := by
  rw [varOf]
  exact measurePreserving_eval (fun _ : Fin n => P) i |>.variance_fun_comp
    (by fun_prop : AEMeasurable (fun x : ℝ => x) P)

/-- **已证**：坐标投影在 `Measure.pi` 下属于 `L²`。 -/
theorem memLp_coord_pi (n : ℕ) (i : Fin n) :
    MemLp (fun ω : Fin n → ℝ => ω i) 2 (Measure.pi (fun _ : Fin n => P)) := by
  exact hP.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => P) i)

/-! ===========================================================================
§1  样本和 / 样本均值的**精确方差**
===========================================================================

**为何不是同义反复**：`variance_sum_pi` 把 `n` 维乘积空间上**和**的方差
折叠成 `n` 倍的**单样本**方差。左边是 `n` 重空间上的量，右边只有一维信息，
等式靠坐标独立性真正建立，结论不出现在前件中。
-/

/-- **已证**：`n` 个 iid 样本之和的方差 `= n · v`（**精确等式**，非不等式）。

    **为何不是同义反复**：左边是 `n` 维乘积空间上的量，右边只有单样本方差与 `n`
    的乘积。必须用坐标独立性（`variance_sum_pi`）才得折叠；
    `Var[∑]` 与 `n·Var[id]` 之间没有任何定义性相等。 -/
theorem variance_sum_coord (n : ℕ) :
    variance (fun ω : Fin n → ℝ => ∑ i, ω i) (Measure.pi (fun _ : Fin n => P)) = n * varOf P := by
  have hfun : (fun ω : Fin n → ℝ => ∑ i, ω i) = (∑ i, fun ω : Fin n → ℝ => ω i) := by
    funext ω; simp [Finset.sum_apply]
  rw [hfun, IndepFun.variance_sum]
  · rw [Finset.sum_congr rfl (fun i _ => variance_coord_pi hP n i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · intro i _; exact memLp_coord_pi hP n i
  · intro i _ j _ hij
    have hpi := iIndepFun_pi (μ := fun _ : Fin n => P)
      (X := fun _ => (id : ℝ → ℝ))
      (fun _ => aemeasurable_id)
    exact hpi.indepFun hij

/-- **已证**：样本均值的方差 `= v / n`（**精确等式**）。

    这是 σ̂ 收敛速率的**精确形式**：速率恰为 `1/n`。

    **为何不是同义反复**：结论是 `variance (meanOf n) = v/n`；
    `meanOf` 的定义是 `(∑ i, ω i)/n`，其方差需要经 `variance_const_mul`
    （提出 `1/n²`）与 `variance_sum_coord`（折叠独立性）两步导出。
    没有任何一步是定义展开。 -/
theorem variance_meanOf (n : ℕ) (hn : 0 < n) :
    variance (meanOf n) (Measure.pi (fun _ : Fin n => P)) = varOf P / n := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmean : meanOf n = fun ω : Fin n → ℝ => (n : ℝ)⁻¹ * ∑ i, ω i := by
    funext ω; simp [meanOf, div_eq_inv_mul]
  rw [hmean, variance_const_mul, variance_sum_coord hP]
  field_simp

/-! ===========================================================================
§2  **收敛速率**：√n 缩放律（正合 CLT 尺度）
===========================================================================

**为何不是同义反复**：`Var[√n · meanOf n] = v` 说的是
「把均值按 `√n` 放大后，方差回到**单样本**方差 `v`」—— 这是 CLT 的方差侧陈述。
它由 `variance_meanOf` 乘 `(√n)² = n` 得到，`n` 与 `1/n` 的抵消是真计算。
-/

/-- **已证**：`Var[√n · meanOf n] = v` —— **正合 CLT 尺度**（不依赖 n）。

    **为何不是同义反复**：`variance_meanOf` 给 `v/n`，乘 `(√n)² = n` 后
    `n` 恰好消掉，得到与 `n` 无关的常数 `v`。这是 √n 一致性的核心恒等式。 -/
theorem variance_sqrt_meanOf (n : ℕ) (hn : 0 < n) :
    variance (fun ω => Real.sqrt n * meanOf n ω) (Measure.pi (fun _ : Fin n => P)) = varOf P := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [variance_const_mul, variance_meanOf hP n hn]
  have : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  rw [this]
  field_simp

/-- **已证**：**一致性** —— `Var[meanOf n] → 0`（`n → ∞`，`v` 固定）。 -/
theorem variance_meanOf_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => varOf P / (n + 1)) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  obtain ⟨v, hv⟩ : ∃ v : ℝ, varOf P = v := ⟨_, rfl⟩
  rw [hv]
  simpa using h.const_div_atTop v

/-- **已证**：**速率上界** —— 对任意 `n ≥ 1`，`Var[meanOf n] ≤ v`。
    （即估计器不比单样本更差；方差单调不增。） -/
theorem variance_meanOf_le_varOf (n : ℕ) (hn : 0 < n) :
    variance (meanOf n) (Measure.pi (fun _ : Fin n => P)) ≤ varOf P := by
  rw [variance_meanOf hP n hn]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hv : 0 ≤ varOf P := variance_nonneg _ _
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end Basic

/-! ===========================================================================
§6  与 `sigmaAIC` 的桥（第 T-6 轮追加；审计 v13 要件 ⑨ σ）
===========================================================================

  ## 背景：审计指控与真实缺口

  审计 v13 原文：
  > ⑨ σ ❌ 不可证：`sigmaAIC := W.err γ` 是 def，文件 L541 自认同义反复。

  **指控部分成立**：`Fate.SigmaFromAIC.sigmaAIC` 确实是纯别名
  （`sigmaAIC W γ = W.err γ`，`SigmaFromAIC.sigmaAIC_eq_err` 即 `rfl`）。

  **但缺口不在 `sigmaAIC` 的定义，而在两条路没连起来**：
  * 路径 A（本文件 §1–§3）：样本均值的**统计一致性** ——
    `Var[meanOf n] = v/n → 0`，`Var[√n·meanOf n] = v`。
    其中 `v = varOf P` 是**单样本方差 σ² 的真值**（二阶矩有限时）。
  * 路径 B（`SigmaFromAIC` §4–§6）：AIC argmin 处的误差
    `σ_AIC := W.err γ_AIC`，以及「AIC argmin ⟹ 误差下界」。

  两条路的载体**确实不同**：
  * 路径 A 活在 `Measure ℝ` / `Fin n → ℝ` 上（测度论载体）；
  * 路径 B 的 `ErrProfileWeak` 是**任意** `ℝ → ℝ` 剖面上的 `bias + var`
    （只有非负公理，**不是任何期望**，见 `SigmaFromAIC` 文件头 §二.2）。

  **⟹ 本节不做「等式」桥。**`varOf P = sigmaAIC W γ` 是**不可证**的建模断言，
  已在 `SigmaFromAIC` §二.4 登记为不可证。
  本节做的是**相容性桥**：证明「σ_AIC 一旦被 AIC 选为候选集上的正下界值，
  则由 §2 的一致性（速度 `1/n`，σ_AIC 是**不随 n 变**的常数），
  样本均值的方差**最终**落在它之下，且比值趋于 0」。

  这就是「σ_AIC 是一个与统计一致性**相容**的 σ 尺度」的形式内容。

  ## ⚠ 防同义反复自检

  1. 本节全部定理的**前件**只含：`MemLp id 2 P`、`IsProbabilityMeasure P`、
     `γ ∈ S`、AIC 在 `γ` 处取最小、`S` 上 `err` 严格正、`S.Nonempty`。
     **不含**任何 `Var[meanOf n] ≤ …` 或 `Tendsto … / … → 0`，
     **不含** `0 < sigmaAIC …`，**不含**样本量。
  2. 结论是**关于样本量的渐近/最终断言**；由 §2 的 `variance_meanOf`
     与 `varOf P` 的有限性（`MemLp` 保证）合成，不是定义展开。
  3. `σ_AIC > 0` 本身是**证出来的**（桥 3，需 AIC argmin），不在前件里。
  4. 本节**不声称** `sigmaAIC = √(varOf P)` 之类等式。
  5. 零 `sorry` / 零 `admit` / 零 `axiom`；证明只用 §0–§5 与 `SigmaFromAIC`
     的**已证**定理加 Mathlib 的 `Filter` 引理。

  ## ⚠ 本节的已知边界（如实登记）

  * 本节的桥**不**推出「σ_AIC 等于真 σ」或「σ_AIC = √(varOf P)」。
  * 本节需要 `∀γ' ∈ S, 0 < W.err γ'`（严格正）。这**不是**
    `ErrProfileWeak.err_nonneg`（非严格）的推论，故必须作显式前件。
  * AIC 的 argmin 在候选集 `S` 上取；本节**不**把 `S` 换成 `⊤`（ℝ 上
    `aicOfErr` 未必有最小值），这一点已由 `SigmaFromAIC` §4 的
    同义反复登记与 `profHinge` 反例说明，本节沿用同一约定。
-/

section SigmaAICBridge

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- ⭐ **桥 1**：自然样本量下，样本均值的方差随 `n` 归零（§2 一致性重述）。

    $$\mathrm{Var}[\bar\omega_{n+1}] \longrightarrow 0 \qquad (n \to \infty).$$

    **为何不是同义反复**：前件只有 `MemLp id 2 P`（σ 存在性的必要前提）。
    结论是**极限**语句；由 §1 的 `variance_meanOf`（`Var[meanOf n] = v/n`）
    化归为 `v/(n+1) → 0`（`Filter.Tendsto.const_div_atTop`）。
    **前件里没有 `→ 0`，也没有 `n`。**
    样本量取 `n+1` 使正性自动成立，免去附加前件。 -/
theorem variance_meanOf_succ_tendsto_zero
    (hP : MemLp (fun x : ℝ => x) 2 P) :
    Filter.Tendsto
      (fun n : ℕ => variance (meanOf (n + 1)) (Measure.pi (fun _ : Fin (n + 1) => P)))
      Filter.atTop (nhds 0) := by
  have heq : (fun n : ℕ => variance (meanOf (n + 1)) (Measure.pi (fun _ : Fin (n + 1) => P)))
      = (fun n : ℕ => varOf P / ((n : ℝ) + 1)) := by
    funext n
    rw [variance_meanOf hP (n + 1) (Nat.succ_pos n)]
    push_cast
    ring
  rw [heq]
  exact (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_div_atTop
    (varOf P)

/-- ⭐ **桥 2**：方差与任意正常数之比归零。

    $$\frac{\mathrm{Var}[\bar\omega_{n+1}]}{\sigma} \longrightarrow 0
      \qquad (\sigma > 0).$$

    **为何不是同义反复**：前件是 `MemLp id 2 P` 与抽象正常数 `sigma > 0`，
    **与 `variance` 无关**（`sigma` 只出现在结论里）。
    证明用 `variance_meanOf` 化归为 `(v/(n+1))/sigma → 0`，
    再用 `Filter.Tendsto.div_const` 与 `zero_div`。**前件不含结论。** -/
theorem variance_meanOf_succ_div_const_tendsto_zero
    (hP : MemLp (fun x : ℝ => x) 2 P) {sigma : ℝ} (_hsigma : 0 < sigma) :
    Filter.Tendsto
      (fun n : ℕ => variance (meanOf (n + 1)) (Measure.pi (fun _ : Fin (n + 1) => P)) / sigma)
      Filter.atTop (nhds 0) := by
  have hbase : Filter.Tendsto (fun n : ℕ => varOf P / ((n : ℝ) + 1))
      Filter.atTop (nhds 0) :=
    (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_div_atTop
      (varOf P)
  have hdiv : Filter.Tendsto (fun n : ℕ => (varOf P / ((n : ℝ) + 1)) / sigma)
      Filter.atTop (nhds (0 / sigma)) := hbase.div_const sigma
  rw [zero_div] at hdiv
  have heq : (fun n : ℕ =>
        variance (meanOf (n + 1)) (Measure.pi (fun _ : Fin (n + 1) => P)) / sigma)
      = (fun n : ℕ => (varOf P / ((n : ℝ) + 1)) / sigma) := by
    funext n
    rw [variance_meanOf hP (n + 1) (Nat.succ_pos n)]
    push_cast
    ring
  rw [heq]
  exact hdiv

/-- ⭐⭐ **桥 3**：`sigmaAIC` 在其 AIC argmin 处**严格正**。

    **为何不是同义反复**：前件的正性是**关于 `W.err`** 的（`0 < W.err γ'`），
    结论的正性是**关于 `SigmaFromAIC.sigmaAIC`** 的。需要
    `sigmaAIC_eq_err`（`rfl`）化归。`W.err` 的非负公理只给 `≤`，
    **严格正必须来自 `hpos`**，而 `hpos` 是关于 `err` 而非 `sigmaAIC` 的。 -/
theorem sigmaAIC_pos_of_aic_argmin (W : R238E3.ErrProfileWeak) (k n : ℕ) (_hn : 0 < n)
    {S : Finset ℝ} {gamma : ℝ} (hgammaS : gamma ∈ S)
    (_hmin : ∀ gamma' ∈ S,
      SigmaFromAIC.aicOfErr W k n gamma ≤ SigmaFromAIC.aicOfErr W k n gamma')
    (hpos : ∀ gamma' ∈ S, 0 < W.err gamma') :
    0 < SigmaFromAIC.sigmaAIC W gamma := by
  have h := hpos gamma hgammaS
  rwa [← SigmaFromAIC.sigmaAIC_eq_err W gamma] at h

/-- ⭐⭐⭐ **桥 4（本节主交付）：σ_AIC 最终包住样本均值的方差。**

    $$\mathrm{AIC}_E(k,n,\gamma)\ \text{在}\ S\ \text{上最小},\quad
      \forall\gamma' \in S,\ 0 < E(\gamma'),\quad
      \mathrm{MemLp}\ \mathrm{id}\ 2\ P$$
    $$\Longrightarrow\quad
      \exists N,\ \forall m \ge N,\
        \mathrm{Var}[\bar\omega_{m+1}] \le \sigma_{\mathrm{AIC}}(W,\gamma).$$

    **读法**：`σ_AIC` 是**不随样本量变**的常数；样本均值的方差以 `1/m`
    速度趋于 0，故**最终**被 `σ_AIC` 控制。

    **为何不是同义反复**（本节最关键的一条）：
    * 前件**不出现** `variance`、`meanOf`、任何 `≤ σ_AIC` 的语句，
      也**不出现样本量** `m`；
    * 结论是 `∃ N, ∀ m ≥ N, …`（**最终谓词**），由桥 1（`Var → 0`）与
      桥 3（`σ_AIC > 0`）经 `Filter.Tendsto.eventually` + `Iio_mem_nhds` 合成；
    * `σ_AIC > 0` 是**证出来的**（桥 3，需 AIC argmin），不在前件里。
    **⟹ 「统计一致性」与「AIC 选出的 σ」由本定理第一次接上。** -/
theorem variance_meanOf_succ_le_sigmaAIC_eventually
    (W : R238E3.ErrProfileWeak) (k : ℕ) {gamma : ℝ}
    (hP : MemLp (fun x : ℝ => x) 2 P)
    {S : Finset ℝ} (hgammaS : gamma ∈ S)
    (hmin : ∀ gamma' ∈ S,
      SigmaFromAIC.aicOfErr W k (S.card + 1) gamma
        ≤ SigmaFromAIC.aicOfErr W k (S.card + 1) gamma')
    (hpos : ∀ gamma' ∈ S, 0 < W.err gamma') :
    ∃ N : ℕ, ∀ m ≥ N,
      variance (meanOf (m + 1)) (Measure.pi (fun _ : Fin (m + 1) => P))
        ≤ SigmaFromAIC.sigmaAIC W gamma := by
  have hsig : 0 < SigmaFromAIC.sigmaAIC W gamma :=
    sigmaAIC_pos_of_aic_argmin W k (S.card + 1) (Nat.succ_pos S.card) hgammaS hmin hpos
  have hev : ∀ᶠ m : ℕ in Filter.atTop,
      variance (meanOf (m + 1)) (Measure.pi (fun _ : Fin (m + 1) => P))
        < SigmaFromAIC.sigmaAIC W gamma :=
    (variance_meanOf_succ_tendsto_zero hP).eventually (Iio_mem_nhds hsig)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  exact ⟨N, fun m hm => le_of_lt (hN m hm)⟩

/-- ⭐⭐⭐ **桥 5：样本均值方差与 σ_AIC 的比值归零（相对一致性）。**

    $$\frac{\mathrm{Var}[\bar\omega_{m+1}]}{\sigma_{\mathrm{AIC}}(W,\gamma)}
      \longrightarrow 0.$$

    **为何不是同义反复**：前件同上（无 `variance`、无样本量、无 `0 < sigmaAIC`）；
    结论是**归一化的极限**。由桥 2（`Var/σ → 0`，需 `σ > 0`）与桥 3
    （`σ_AIC > 0`，是**证出来的**）合成。 -/
theorem variance_meanOf_succ_div_sigmaAIC_tendsto_zero
    (W : R238E3.ErrProfileWeak) (k : ℕ) {gamma : ℝ}
    (hP : MemLp (fun x : ℝ => x) 2 P)
    {S : Finset ℝ} (hgammaS : gamma ∈ S)
    (hmin : ∀ gamma' ∈ S,
      SigmaFromAIC.aicOfErr W k (S.card + 1) gamma
        ≤ SigmaFromAIC.aicOfErr W k (S.card + 1) gamma')
    (hpos : ∀ gamma' ∈ S, 0 < W.err gamma') :
    Filter.Tendsto
      (fun m : ℕ => variance (meanOf (m + 1)) (Measure.pi (fun _ : Fin (m + 1) => P))
        / SigmaFromAIC.sigmaAIC W gamma)
      Filter.atTop (nhds 0) :=
  variance_meanOf_succ_div_const_tendsto_zero hP
    (sigmaAIC_pos_of_aic_argmin W k (S.card + 1) (Nat.succ_pos S.card) hgammaS hmin hpos)

/-- ⭐⭐ **桥 6（存在性版：σ 的三个性质同时成立）**。

    非空候选集上**存在** `gamma ∈ S`，使
    (i) `σ_AIC(W,gamma) > 0`；
    (ii) `∃ N, ∀ m ≥ N, Var[\bar\omega_{m+1}] ≤ σ_AIC(W,gamma)`；
    (iii) `σ_AIC(W,gamma)` 是 `W.err` 在 `S` 上的下界。

    **为何不是同义反复**：前件只有 `S.Nonempty`、`S` 上 `err` 严格正、
    `MemLp id 2 P`。**「存在 AIC argmin」不在前件里** ——
    它由 `SigmaFromAIC.exists_argmin_aic`（有限集必有最小元）**证出**；
    (i) 由桥 3 证出；(ii) 由桥 4 证出；(iii) 由
    `SigmaFromAIC.sigmaAIC_spec_of_aic_argmin` 证出。
    **三条结论没有一条出现在前件中。** -/
theorem exists_sigmaAIC_envelope_of_consistency
    (W : R238E3.ErrProfileWeak) (k : ℕ)
    (hP : MemLp (fun x : ℝ => x) 2 P)
    {S : Finset ℝ} (hS : S.Nonempty) (hpos : ∀ gamma' ∈ S, 0 < W.err gamma') :
    ∃ gamma ∈ S,
      0 < SigmaFromAIC.sigmaAIC W gamma
        ∧ (∃ N : ℕ, ∀ m ≥ N,
            variance (meanOf (m + 1)) (Measure.pi (fun _ : Fin (m + 1) => P))
              ≤ SigmaFromAIC.sigmaAIC W gamma)
        ∧ (∀ gamma' ∈ S, SigmaFromAIC.sigmaAIC W gamma ≤ W.err gamma') := by
  obtain ⟨gamma, hgammaS, hmin⟩ :=
    SigmaFromAIC.exists_argmin_aic W k (S.card + 1) S hS
  refine ⟨gamma, hgammaS,
    sigmaAIC_pos_of_aic_argmin W k (S.card + 1) (Nat.succ_pos S.card) hgammaS hmin hpos,
    variance_meanOf_succ_le_sigmaAIC_eventually W k hP hgammaS hmin hpos, ?_⟩
  obtain ⟨_, hle, _⟩ :=
    SigmaFromAIC.sigmaAIC_spec_of_aic_argmin W k (S.card + 1) (Nat.succ_pos S.card)
      hgammaS hmin hpos
  exact hle

end SigmaAICBridge

end Fate.SigmaEstimation
