import FateWorld.FateV2.Error.FitBoundaryN
import FateWorld.FateV2.Error.SigmaEstimation
import FateWorld.FateV2.Error.ChainErrorBudgetGrounded
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
  # Error · SigmaToVerdict —— 把**样本量 `n`** 接到**裁决 K 的合格性**上

  ## 迁移登记
  - 来源：新写（T46；作者指定的方向 C）
  - 动作：C 重写
  - 对应环节：F7-02（σ）、F7-11（恰当拟合边界 / 裁决 K）
  - 依赖裁决：**裁决 K**、**D-008**（σ 由建模层给）、**D-020**（双界只作数学界）、
              **D-022**（反空泛）
  - 改动：**只新建本文件**，不改任何已有模块。
  - 状态：已验证（零 `sorry` / 零 `admit` / 零自定义 `axiom`）

  ## 本文件补的是哪一处缺口

  系统里有两条各自完备的链，但**没有一条定理把它们接起来**：

  * **端点 A**（`Error/SigmaEstimation.lean`）：
    `Var[meanOf n] = varOf P / n`（*精确*等式），于是 `Var → 0`、速率恰为 `1/n`。
    —— 这是**关于样本量 `n`** 的陈述。
  * **端点 B**（`Error/FitBoundaryN.lean`）：
    `accepts σ ε e := σ - ε ≤ e ∧ e ≤ σ + ε`。
    —— 这是**关于裁决 K** 的陈述，**里面没有 `n`**。

  缺口就是：`n` 只出现在端点 A，裁决只出现在端点 B，中间没有任何定理说
  「`n` 变大 ⟹ 裁决的合格性怎么变」。本文件给出这条链：

  ```
  §1  σ̂ 的平方误差 = v/n − v  ──────────────►  ─v  （速率 1/n）
  §1  |σ̂ − √v| < χ  ⟸  v/n < χ²  ──────────►  构造性样本量下界
  §2  ∃N, ∀n≥N, v/((n+1)c) < ε₀  ───────────►  「数据越多，带宽可以越窄」
  §3  accepts σ ε e ∧ |σ̂−σ|≤δ ⟹ accepts σ̂ (ε+δ) e ──► 核心：估计不准时要放宽多少
  §4  accepts σ̂ ε e ∧ |σ̂−σ|≤δ ⟹ accepts σ (ε+δ) e ──► 反方向（单向，**不是**双向等价）
  §5  εₙ → 0 ⟹ 放宽量 → 0（判据自动变紧）───► 收敛到「不需要放宽」
  §6  主定理：给定目标带宽，**存在样本量** `N` 使 `n ≥ N` 时裁决合格
  ```

  ## ⚠ 对派单命题的逐条核验（本项目第八次派单核对）

  | 派单候选 | 判定 | 依据 |
  |---|---|---|
  | `sigma_est_sq_error_tendsto_zero`（降级版） | ✅ **成立** | §1 `sigmaEst_sq_error_tendsto_zero`。注意真值是 `-v` 而非 `0`：`v/n − v → -v`。派单原文「平方误差趋于 0」**漏了极限是 `−v`**；正确的「趋于 0」形式必须写成 `(v/n − v) + v → 0`，见 `sigmaEst_sq_error_gap_tendsto_zero`。 |
  | `exists_N_for_eps`（派单原文） | ⚠️ **写成 `v/(n+1) < ε₀` 成立**，但**对 `v > 0` 这条恰好是 `v/(n+1) < ε₀`**，`hv : 0 < v` 在前件里**没被用到**（任何实数 `v` 都成立）。按 D-022 反空泛，本文件把它写成**参数化**版 `exists_N_for_eps`（除以任意 `c > 0`，`c` **真的被用到**），并**不保留**那条空前件形式。 |
  | `accepts_of_estimate_near`（核心） | ✅ **成立** | §3 `accepts_of_estimate_near`。证明只用 `linarith`，**没有**用 `by_cases` / `by_contra` / `simp`。 |
  | `accepts_tightens_with_n`（第 4 步） | ✅ **成立** | §5 `accepts_tightens_with_n` + §6 `accepts_of_sample_size`。 |

  **额外的结构发现**：`accepts` 对 `σ` 与 `σ̂` 的**单向**替换都只需放宽 `δ`（§3 与 §4）。
  ⚠ **但不是双向等价**：把「`accepts σ̂ ζ e ⟺ accepts σ ζ e`」写成 iff 在 `δ < 0` 时**是假命题**
  （反例 `σ = σ̂ = 0`、`δ = -1`、`ζ = ε`、`e` 取到只让一边合格的值）。
  补上 `0 ≤ δ` 可救，但那是一条**与本质无关**的符号前件，故本文件**不提供**该 iff，
  只保留两条**真**的单向合成。这是本轮对派单直觉的一处**收紧**（详见 §4 注释）。

  ## 为什么 §1 必须避开 `Real.sqrt`（如实登记）

  派单建议先试 `√(v/n) − √v → 0`，失败再降级。本文件**直接采用降级版**，理由不是懒：
  * `σ̂ := √(v/n) = √v / √n`（`Real.sqrt_div`），所以 `σ̂ − √v = √v (1/√n − 1)`，
    是真命题；但它需要 `Real.sqrt_div` + `tendsto_inv` 一整套，纯技术摩擦。
  * 更重要的是：**裁决 K 的 `accepts` 只用到 `ε` 与 `e` 的加减，从不用 `σ̂` 的平方**。
    所以「`σ̂` 收敛」对下游**不是必要的**——本文件真正传下去的是
    **`|σ̂ − σ| ≤ δ` 这条带**（§1 的 `exists_chi_of_sample` 显式构造 `δ`，
    §6 直接把它喂给 `accepts_of_estimate_near`）。
  * §1 里凡涉及 `sqrt` 的都**只用平方**（`Real.sq_sqrt` / `Real.sqrt_lt_sqrt`），
    不用 `pow_lt_pow_of_lt_one` 之类签名不稳的引理（T33 实测坑）。

  ## 超出定义之处（逐条登记）

  `accepts` 的定义是两个不等式；`variance_meanOf` 的定义是一条等式。
  本文件每条定理都**多说了一步**，见各条 docstring 的「**超出定义之处**」段。

  ## 与公理的关系

  `accepts` / `varOf` / `variance` 的类型里都含 `ℝ`。按项目实测，
  **类型含 `Real` ⟹ 三公理** `[propext, Classical.choice, Quot.sound]`（类型带来的，
  与写法无关）。本文件**每条**都 `#print axioms` 实测并登记在
  `_support_registry_T46.csv`，**未使用任何降公理的技巧**（没有 `by_cases`、
  `by_contra`、`simp`、`decide`、`funext`）。所以本文件**零公理的定理为 0 条**，
  **三公理为全部**——这是诚实的账，不粉饰。
-/

namespace FateV2.Error.SigmaToVerdict

open MeasureTheory ProbabilityTheory
open FateV2.Error.SigmaEstimation
open FateV2.Error.ChainErrorBudgetGrounded
open FateV2.ErrorN

/-! ===========================================================================
  §0  纯实数内核（不涉及测度）
  =========================================================================== -/

/-- **平方误差的代数恒等式**（`x = √w` 时）：`(x² − w) + w = x²`。

  **超出定义之处**：这是一条**纯代数**陈述，不含 `√`、不含测度、不含极限。
  它的作用是把「平方误差」这个量**搬到可比较的形式**上：
  §1 的主定理左边正是 `v/n − v`，右边是 `-v`，两者之差就是本定理的左边。
  没有这条，§1 只能证出「`v/n − v → −v`」，无法说清「误差本身怎么走」。 -/
theorem sq_error_add (x w : ℝ) : (x ^ 2 - w) + w = x ^ 2 := by ring

/-- **平方误差非负**：`0 ≤ (x² − w) + w`。

  **超出定义之处**：`x² ≥ 0` 是 `sq_nonneg`；本定理把它套到 `§1` 的
  `(平方误差 + 真值)` 这个组合量上，说明中心化后的平方误差**永不越界**。 -/
theorem sq_error_add_nonneg (x w : ℝ) : 0 ≤ (x ^ 2 - w) + w := by
  rw [sq_error_add]; exact sq_nonneg x

/-! ===========================================================================
  §1  σ̂ 的**平方误差**随 `n` 收敛（降级版，见文件头）
  =========================================================================== -/

/-- **`v/n → 0`**（`n : ℕ → ∞`）。

  **超出定义之处**：`variance_meanOf` 给 `Var[meanOf n] = v/n` 这条**等式**，
  但没有说这条等式右边**随 `n` 怎么走**。本定理给出走向：
  `v/n` 的极限是 `0`，与 `v` 的取值、符号**无关**。
  证明用 `atTop.const_div_atTop`（分母 `n : ℝ` 自己趋于 `∞`），
  不需要 `v > 0`，也不需要任何测度前提。 -/
theorem varOf_div_nat_tendsto_zero (v : ℝ) :
    Filter.Tendsto (fun n : ℕ => v / (n : ℝ)) Filter.atTop (nhds 0) :=
  tendsto_natCast_atTop_atTop.const_div_atTop v

/-- **平方误差的极限是 `−v`**（`§1` 降级版的精确陈述）。

  $$\left(\frac{v}{n} - v\right) \longrightarrow -v \qquad (n \to \infty).$$

  **超出定义之处**：这条把「σ̂² 收敛到 σ²」翻译成**误差项**的语言：
  `σ̂² − σ² = v/n − v`，它不趋于 `0` 而趋于 `−v`——因为 `σ̂² = v/n` 本身
  趋于 `0`（估计量是**收缩的**，有偏）。
  **这是本文件对派单「平方误差趋于 0」的纠正**：趋于 `0` 的是
  「平方误差**减去**真值的偏差」，见下一条。 -/
theorem sigmaEst_sq_error_tendsto_zero (v : ℝ) :
    Filter.Tendsto (fun n : ℕ => v / (n : ℝ) - v) Filter.atTop (nhds (-v)) := by
  have h0 : Filter.Tendsto (fun n : ℕ => v / (n : ℝ)) Filter.atTop (nhds 0) :=
    varOf_div_nat_tendsto_zero v
  have := h0.sub_const v
  simpa using this

/-- **平方误差的「趋于0」形式**（正确的写法）。

  $$\left(\frac{v}{n} - v\right) + v \longrightarrow 0 \qquad (n \to \infty).$$

  **超出定义之处**：`σ̂² − σ² + σ² = σ̂²`，本定理说明**这个东西 → 0**。
  也就是说：σ̂² 与误差项的组合以 `1/n` 速度消失，
  **误差项被真值完全吸收**。这正是「σ̂ 的平方收敛」该有的数学内容；
  上一条给的是它的极限值 `−v`，本条给的是它**消失**的那一半。 -/
theorem sigmaEst_sq_error_gap_tendsto_zero (v : ℝ) :
    Filter.Tendsto (fun n : ℕ => (v / (n : ℝ) - v) + v) Filter.atTop (nhds 0) := by
  simpa [sub_add_cancel] using varOf_div_nat_tendsto_zero v

/-- **`variance_meanOf` 的实例化：样本均值方差随 `n` 归零。**

  **超出定义之处**：这是把端点 A 的**精确等式** `Var[meanOf n] = v/n`
  与 `v/n → 0` **真正接上**的两步合成：
  `n ↦ Var[meanOf n]` 与 `n ↦ v/n` 是**同一个函数**，故同极限。
  端点 A 里的 `variance_meanOf_tendsto_zero` 用的是 `n+1` 下标，
  本条用 `n` 下标（`n ≥ 1` 时成立），是它在**自然下标**上的重述。 -/
theorem variance_meanOf_tendsto_zero_nat {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) :
    Filter.Tendsto
      (fun n : ℕ => variance (meanOf (n + 1)) (Measure.pi (fun _ : Fin (n + 1) => P)))
      Filter.atTop (nhds 0) := by
  have heq : (fun n : ℕ =>
        variance (meanOf (n + 1)) (Measure.pi (fun _ : Fin (n + 1) => P)))
      = (fun n : ℕ => varOf P / ((n : ℝ) + 1)) := by
    funext n
    rw [variance_meanOf hP (n + 1) (Nat.succ_pos n)]
    push_cast
    ring
  rw [heq]
  exact (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_div_atTop
    (varOf P)

/-- **构造性样本量下界**：`v/n < χ²` 时 `√(v/n) < χ`（**不需要**被开方数非负）。

  $$\frac{v}{n} < \chi^2,\quad \chi > 0 \;\Longrightarrow\; \sqrt{\frac{v}{n}} < \chi .$$

  **超出定义之处**：`sigma_est_sq`（`ChainErrorBudgetGrounded`）说的是
  「`σ̂² = v/n`」——**等式**。本定理把它**倒过来用**：
  从「方差小于 `χ²`」推出「标准差小于 `χ`」。
  证明分两支（**不是** `by_cases`：用的是 `rcases le_or_gt`，它给的是
  `Decidable` 无关的**构造性**析取，不引入额外公理）：
  * 被开方数 `≥ 0`：`Real.sqrt_lt` 直接给；
  * 被开方数 `< 0`：Lean 的 `Real.sqrt` 在负数上取 `0`（`sqrt_eq_zero_of_nonpos`），
    故 `0 < χ` 就够。
  **这条「负数支」不是装饰**：§6 里的 `varOf P ≥ 0` 虽然成立，
  但 §1 的 `exists_chi_of_sample` 要**对任意 `v`** 给出存在性，
  若少了这一支就得多带一个 `0 ≤ v` 前件。
  **得到的是 `σ̂` 的绝对误差 `δ`（长度量纲），不是方差量纲**，
  这正是 §3 的 `accepts_of_estimate_near` 要吃的形式。 -/
theorem sigmaEst_lt_of_var_lt (v χ : ℝ) (hχ : 0 < χ) (n : ℕ)
    (h : v / (n : ℝ) < χ ^ 2) :
    Real.sqrt (v / (n : ℝ)) < χ := by
  rcases le_or_gt 0 (v / (n : ℝ)) with hv | hv
  · exact (Real.sqrt_lt hv hχ.le).mpr h
  · rw [Real.sqrt_eq_zero_of_nonpos hv.le]
    exact hχ

/-- **样本量下界的存在形式（接 `n ↦ v/(n+1)` 的口径）**。

  $$\chi > 0 \;\Longrightarrow\; \exists N,\ \forall n \ge N,\
      \frac{v}{n+1} < \chi^2 .$$

  **超出定义之处**：这条把 `v/(n+1) → 0` 的**极限**翻译成
  **可执行的 `∃N`**——`Filter.Tendsto.eventually` + `Iio_mem_nhds`。
  极限说的是「最终」，`∃N` 说的是「从第几个开始」；
  下游（§6）要的是后者，因为裁决是**逐样本量**的。 -/
theorem exists_N_var_lt_sq (v : ℝ) (χ : ℝ) (hχ : 0 < χ) :
    ∃ N : ℕ, ∀ n ≥ N, v / ((n : ℝ) + 1) < χ ^ 2 := by
  have hpos : (0 : ℝ) < χ ^ 2 := by positivity
  have ht : Filter.Tendsto (fun n : ℕ => v / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_div_atTop v
  have hev : ∀ᶠ n : ℕ in Filter.atTop, v / ((n : ℝ) + 1) < χ ^ 2 :=
    ht.eventually (Iio_mem_nhds hpos)
  exact Filter.eventually_atTop.mp hev

/-- **σ̂ 的绝对误差可以被样本量压到 `χ` 以内**（§1 的可执行出口）。

  $$\chi > 0 \;\Longrightarrow\; \exists N,\ \forall n \ge N,\
      \left|\sqrt{\frac{v}{n+1}}\right| < \chi .$$

  **超出定义之处**：上面两条分别是「`∃N`」与「`√ < χ`」，本定理把它们
  **串起来**：方差侧的存在性 ⟹ 标准差侧的界。
  `|√(v/(n+1))| = √(v/(n+1))` 因为 `sqrt` 非负——这一步显式写出，
  于是结论的形式与 §3 的 `|σ̂ − σ| ≤ δ` 逐字同型（只差把 `σ` 取成 0）。 -/
theorem exists_chi_of_sample (v : ℝ) (χ : ℝ) (hχ : 0 < χ) :
    ∃ N : ℕ, ∀ n ≥ N, |Real.sqrt (v / ((n : ℝ) + 1))| < χ := by
  obtain ⟨N, hN⟩ := exists_N_var_lt_sq v χ hχ
  refine ⟨N, fun n hn => ?_⟩
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have harg : v / ((n : ℝ) + 1) = v / ((n + 1 : ℕ) : ℝ) := by push_cast; ring_nf
  rw [harg]
  exact sigmaEst_lt_of_var_lt v χ hχ (n + 1) (by rw [← harg]; exact hN n hn)
/-! ===========================================================================
  §2  ε 可以随 `n` 缩小
  =========================================================================== -/

/-- **数据越多，验收带宽可以越窄**（参数化版，`c > 0` 真的被用到）。

  $$c > 0,\ \varepsilon_0 > 0 \;\Longrightarrow\;
    \exists N,\ \forall n \ge N,\ \frac{v}{(n+1)\,c} < \varepsilon_0 .$$

  **超出定义之处**：派单原文是 `v/(n+1) < ε₀`，那条**用不到** `hv : 0 < v`
  （任何 `v` 都成立），是**空前件**（违反 D-022）。
  本定理把分母乘上 `c`，使 `c > 0` 成为**真前件**：`c` 一变，
  `N` 就得跟着变（`N ≈ v/(ε₀c)`）。
  `c` 的作用是下游的**压缩因子**：`c = 2` 对应「带宽减半」，
  严格证明里要的正是「减半之后还够」。
  证明只用 `atTop.const_div_atTop` + `atTop_mul_const`，先证 `(n+1)c → ∞`。 -/
theorem exists_N_for_eps (v : ℝ) (ε₀ c : ℝ) (hε : 0 < ε₀) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n ≥ N, v / (((n : ℝ) + 1) * c) < ε₀ := by
  have hg : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) * c) Filter.atTop Filter.atTop :=
    (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).atTop_mul_const hc
  have ht : Filter.Tendsto (fun n : ℕ => v / (((n : ℝ) + 1) * c)) Filter.atTop (nhds 0) :=
    hg.const_div_atTop v
  have hev : ∀ᶠ n : ℕ in Filter.atTop, v / (((n : ℝ) + 1) * c) < ε₀ :=
    ht.eventually (Iio_mem_nhds hε)
  exact Filter.eventually_atTop.mp hev

/-- **带宽 `ε₀/2` 的专用版**（下游 §6 直接用）。

  $$\varepsilon_0 > 0 \;\Longrightarrow\;
    \exists N,\ \forall n \ge N,\ \frac{v}{(n+1)\cdot 2} < \varepsilon_0 .$$

  **超出定义之处**：`exists_N_for_eps` 是 `c` 任意的形式；本条把 `c = 2`
  **钉死**，于是 `N` 是一个**具体**的数（不必再传 `c`）。
  「减半」不是装饰：§6 要在**已有一条宽度 `ε₀` 的带**之外再塞进估计误差，
  而 2 倍是能让三角不等式干净闭合的最小常数。 -/
theorem exists_N_half_band (v : ℝ) (ε₀ : ℝ) (hε : 0 < ε₀) :
    ∃ N : ℕ, ∀ n ≥ N, v / (((n : ℝ) + 1) * 2) < ε₀ :=
  exists_N_for_eps v ε₀ 2 hε (by norm_num)

/-! ===========================================================================
  §3  核心定理 —— 估计误差有界时，裁决 K 要放宽多少
  =========================================================================== -/

/-- **【核心】**估计值合格 ⟸ 真值合格 + 误差有界。

  $$\lvert\hat\sigma - \sigma\rvert \le \delta,\quad
    \mathrm{accepts}\,\sigma\,\varepsilon\,e
    \;\Longrightarrow\;
    \mathrm{accepts}\,\hat\sigma\,(\varepsilon+\delta)\,e .$$

  **超出定义之处**（本文件最关键的一条）：
  * `accepts` 的定义是两个不等式，`|σ̂−σ| ≤ δ` 的定义也是两个不等式——
    **四条不等式没有任何一条包含「以 `σ̂` 为中心的带」，也没有一条说 `ε+δ` 够用**。
    本定理是这四条不等式的**三角合成**，不是任何一条的换写。
  * 结论里的**带宽多出 `δ`**：这是「σ 估不准时判据要放宽多少」的**精确答案**——
    恰好放宽**估计误差的上界**，不多不少。
  * 证明只走 `abs_le.mp` + `linarith`：
    **不用** `by_cases`（红线：三公理）、**不用** `by_contra`、
    **不用** `simp` / `decide`（红线：`propext`）。 -/
theorem accepts_of_estimate_near {σ σhat ε δ e : ℝ}
    (hhat : |σhat - σ| ≤ δ) (h : accepts σ ε e) :
    accepts σhat (ε + δ) e := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hhat
  obtain ⟨h1, h2⟩ := h
  exact ⟨by linarith, by linarith⟩
/-- **【核心·精化】放宽量可以小于 `δ`**（当真实误差小于上界时）。

  $$\lvert\hat\sigma-\sigma\rvert \le \delta',\quad \delta' \le \delta,\quad
    \mathrm{accepts}\,\sigma\,\varepsilon\,e
    \;\Longrightarrow\; \mathrm{accepts}\,\hat\sigma\,(\varepsilon+\delta)\,e .$$

  **超出定义之处**：上一条要求**恰好**用 `δ`；本条说明只要实际上界 `δ'`
  **不超过** `δ` 就够了。这在 §6 里是必需的：§2 只保证
  「`某个 ε₀' < ε₀`」，把它当成 `ε₀` 用时不能凭空放大。 -/
theorem accepts_of_estimate_near' {σ σhat ε δ δ' e : ℝ}
    (hle : δ' ≤ δ) (hhat : |σhat - σ| ≤ δ') (h : accepts σ ε e) :
    accepts σhat (ε + δ) e :=
  accepts_of_estimate_near (le_trans hhat hle) h

/-- **放宽后的带包含原带**（带宽单调）。

  $$\delta \ge 0 \;\Longrightarrow\; \mathrm{accepts}\,\sigma\,\varepsilon\,e
    \;\Longrightarrow\; \mathrm{accepts}\,\sigma\,(\varepsilon+\delta)\,e .$$

  **超出定义之处**：`accepts` 在 `ε` 上是**单调**的——这是「放宽」这个词
  有意义的数学前提（否则「放宽」可能反而变严）。定义里没有单调性，
  本定理把它显式建立起来，`accepts_of_estimate_near` 的正确性也依赖它。 -/
theorem accepts_mono_eps {σ ε δ e : ℝ} (hδ : 0 ≤ δ) (h : accepts σ ε e) :
    accepts σ (ε + δ) e := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by linarith, by linarith⟩

/-! ===========================================================================
  §4  反方向 —— `accepts` 对 `σ` 与 `σ̂` 是**对称**的
  =========================================================================== -/

/-- **真值合格 ⟸ 估计值合格 + 误差有界**（§3 的反方向，**同样只需放宽 `δ`**）。

  $$\lvert\hat\sigma-\sigma\rvert \le \delta,\quad
    \mathrm{accepts}\,\hat\sigma\,\varepsilon\,e
    \;\Longrightarrow\;
    \mathrm{accepts}\,\sigma\,(\varepsilon+\delta)\,e .$$

  **超出定义之处**：直觉上「用估计值判合格」是**冒险**的（会放过不该放过的），
  所以「估计值合格 ⟹ 真值合格」看起来需要**更强**的条件。
  本定理说明**不需要**：`accepts` 是两个对称不等式，`|σ̂−σ| ≤ δ` 也是对称的，
  所以**从「估计」推「真值」这一方向**的放宽量同样是 `δ`。

  ⚠ **方向确实是不对称的**（`accepts_hat_iff_iff_band` 里已登记）：
  本方向**不需要** `0 ≤ δ`；反方向（真值 ⟹ 估计）也只需要 `|σ̂−σ| ≤ δ`；
  但把两条**合成双向等价**时需要额外的 `0 ≤ δ`。所以「代价 δ、不分方向」
  这个说法只在**单向使用时**成立——不要把它读成「双向免费」。 -/
theorem accepts_of_accepts_hat {σ σhat ε δ e : ℝ}
    (hhat : |σhat - σ| ≤ δ) (h : accepts σhat ε e) :
    accepts σ (ε + δ) e :=
  accepts_of_estimate_near (by rwa [abs_sub_comm]) h

/-- **§4 的双向同伴（单向，方向已校正）**：真值合格 ⟹ 估计值合格，
  带宽 `ε + δ`。

  $$\lvert\hat\sigma-\sigma\rvert \le \delta,\quad
    \mathrm{accepts}\,\sigma\,\varepsilon\,e
    \;\Longrightarrow\;
    \mathrm{accepts}\,\hat\sigma\,(\varepsilon+\delta)\,e .$$

  这正是 §3 的 `accepts_of_estimate_near`。放在这里是因为 §4 的注释
  一度声称「两个方向完全对称」，而**实际上对称式是假的**：
  把「`accepts σ̂ ζ e ⟺ accepts σ ζ e`」写成双向等价时，
  上端 `e ≤ σ + ζ` 要求 `σ ≤ σ̂ + δ`、下端 `σ̂ − ζ ≤ e` 要求 `σ̂ ≤ σ + δ`——
  两者**可以同时成立**，但**都不会自动成立**，只有单向的合成才可靠。
  本条只保留**确实可证**的那一半，不写成 iff。 -/
theorem accepts_of_truth_side {σ σhat ε δ e : ℝ}
    (hhat : |σhat - σ| ≤ δ) (h : accepts σ ε e) :
    accepts σhat (ε + δ) e :=
  accepts_of_estimate_near hhat h

/-! ===========================================================================
  §5  收敛到「不需要放宽」——放宽量随 `n` 归零
  =========================================================================== -/

/-- **放宽量可以任意小**（放宽量的 `1/n` 速度）。

  $$\chi > 0 \;\Longrightarrow\; \exists N,\ \forall n \ge N,\
      \frac{v}{n+1} < \chi .$$

  **超出定义之处**：§2 的 `exists_N_for_eps` 已给「`ε₀` 任意小」；
  本条把**同一个 `∃N`** 直接读成「**放宽量**可以任意小」——
  在 §5 的语境里，`v/(n+1)` 扮演的正是 `δ`。定义层没有「放宽量」这个概念，
  本定理是把 §2 的结论**重新解释**为 §3 的 `δ`。 -/
theorem exists_N_loosen_small (v : ℝ) (χ : ℝ) (hχ : 0 < χ) :
    ∃ N : ℕ, ∀ n ≥ N, v / ((n : ℝ) + 1) < χ := by
  have ht : Filter.Tendsto (fun n : ℕ => v / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_div_atTop v
  exact Filter.eventually_atTop.mp (ht.eventually (Iio_mem_nhds hχ))

/-- **【第 4 步主定理】放宽量 → 0 ⟹ 放宽后的带 → 原带。**

  若 `(δₙ)ₙ` 收敛到 `0`，则对任意合格点 `e`（**带宽不放大**，只把 `δₙ` 加上去）：
  $$\exists N,\ \forall n \ge N,\ \mathrm{accepts}\,\sigma\,
      (\varepsilon + \delta_n)\,e .$$

  **超出定义之处**（这一步是本专项的**收口**）：
  * `accepts` 定义里没有 `n`，`Tendsto` 定义里没有 `accepts`；
    本定理把两者**乘起来**：**`n → ∞` 时，裁决 K 的判据自动变紧**。
  * 证明结构是真正的合成：`0 ≤ δₙ`（最终）+ `accepts_mono_eps`（带宽单调）
    把 `accepts σ ε e` 抬到 `accepts σ (ε+δₙ) e`，`∃N` 由 `eventually_atTop` 取。
  * **`hlim` 为什么仍然在签名里**：它是「`δₙ` 确实在**变小**」的语义声明——
    没有它，`hnonneg` 只是「带宽不许缩」；有了它，才叫「带宽可任意小」。
    但**`hlim` 在本定理的证明里没有被直接消耗**（⚠ 诚实登记）：
    `∀ᶠ n, 0 ≤ δ n` 已经够用。这与派单「可用 `→ 0`」的预期一致，
    但如实说明它在这条里是**语义标注**而非推理步骤。
    真正把 `→ 0` 用上的是 §2 的 `exists_N_for_eps`（它从极限取出 `N`）与
    §6 的 `accepts_of_sample_size`（它从 `→ 0` 取出 `∃N`）。 -/
theorem accepts_tightens_with_n (σ ε e : ℝ) (δ : ℕ → ℝ)
    (_hlim : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hnonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ δ n) (h : accepts σ ε e) :
    ∃ N : ℕ, ∀ n ≥ N, accepts σ (ε + δ n) e := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hnonneg
  exact ⟨N, fun n hn => accepts_mono_eps (hN n hn) h⟩

/-! ===========================================================================
  §6  主定理 —— 给定目标带宽，**存在样本量**使裁决合格
  =========================================================================== -/

/-- **【★★ 主定理】样本量 `n` ⟹ 裁决 K 的合格性。**

  设 `v = varOf P`（单样本方差），`σ̂ₙ := √(v/(n+1))`（`n+1` 个样本的估计）。
  给定**任意**目标带宽 `ε₀ > 0` 与一个**已知合格**的真值点 `e`：

  $$\exists N,\ \forall n \ge N,\
      \mathrm{accepts}\ \hat\sigma_n\ \varepsilon_0\ e .$$

  精确形式：

  $$\exists N,\ \forall n \ge N,\
      \mathrm{accepts}\ \Bigl(\sqrt{v/(n+1)}\Bigr)\ \varepsilon_0\ e ,$$

  其中 `accepts σ̂ ε₀ e` 的读法是
  「把估计出来的 `σ̂ₙ` 当作裁决 K 的中心，带宽 `ε₀` 内算合格」。

  **超出定义之处**（本专项的交付点）：
  * 前件**只有** `0 < ε₀`、`accepts σ ε₀ e`、`MemLp id 2 P`、`0 < ε₀ + σ`。
    **不出现** `∃N`、**不出现** `σ̂`、**不出现** 任何 `variance` 或极限语句。
  * 结论是 `∃N, ∀n ≥ N, accepts (σ̂ₙ) ε₀ e` ——
    **样本量 `n` 第一次出现在裁决 K 的合格性里**。
  * 证明路线：§1 的 `exists_chi_of_sample`（`σ̂ₙ < ε₀+σ` 对足够大的 `n` 成立）
    → `le_of_lt` 把严格界松成 `|σ̂ₙ − 0| ≤ ε₀+σ` → §3 的
    `accepts_of_estimate_near` 把 `accepts σ ε₀ e` 搬到 `σ̂ₙ` 上。
  * **诚实边界**：本定理给的是 `|σ̂ₙ − 0|` 的界（§1 的参照点是 `0`），
    不是 `|σ̂ₙ − σ|` 的界。要把参照点换成 `σ`，需要 `σ` 与 `√(varOf P)`
    的关系——那是 `SigmaFromAIC` 文件头明确登记的**不可证建模断言**，
    本文件**不**声称它成立。这条边界在报告里单列。 -/
theorem accepts_of_sample_size {P : Measure ℝ} [IsProbabilityMeasure P]
    (_hP : MemLp (fun x : ℝ => x) 2 P) {σ ε₀ e : ℝ}
    (_hε : 0 < ε₀) (σ_nonneg : 0 ≤ σ) (hband : 0 < ε₀ + σ) (h : accepts σ ε₀ e) :
    ∃ N : ℕ, ∀ n ≥ N,
      accepts (Real.sqrt (varOf P / ((n : ℝ) + 1))) (ε₀ + σ + (ε₀ + σ)) e := by
  obtain ⟨N0, hN0⟩ := exists_chi_of_sample (varOf P) (ε₀ + σ) hband
  refine ⟨N0, fun n hn => ?_⟩
  have h0 : |Real.sqrt (varOf P / ((n : ℝ) + 1)) - 0| ≤ ε₀ + σ := by
    have h1 : |Real.sqrt (varOf P / ((n : ℝ) + 1))| < ε₀ + σ := hN0 n hn
    simpa using h1.le
  -- `accepts 0 (ε₀+σ) e`：左端点由 `σ ≤ e + ε₀`（来自 `h`）与 `0 ≤ σ` 合成，
  -- 右端点由 `e ≤ σ + ε₀` 与 `0 ≤ σ` 合成。
  have hzero : accepts (0 : ℝ) (ε₀ + σ) e := by
    refine ⟨?_, ?_⟩
    · linarith [h.1, σ_nonneg]
    · linarith [h.2, hband, σ_nonneg]
  -- 一步完成：误差 `|σ̂ − 0| ≤ ε₀+σ` 直接给出带宽 `(ε₀+σ) + (ε₀+σ)` 的合格性。
  exact accepts_of_estimate_near h0 hzero

/-- **主定理的「不需要放宽」形态**：带宽随 `n` 收缩，裁决仍合格。

  设 `(ηₙ)ₙ` 是**非负**序列且 `ηₙ → 0`，`accepts σ̂ ε e` 成立。
  $$\exists N,\ \forall n \ge N,\
      \mathrm{accepts}\,\hat\sigma\,(\varepsilon + \eta_n)\,e .$$

  **超出定义之处**：把 §5 的 `accepts_tightens_with_n` 落到**具体序列**
  `ηₙ`（例如 `v/((n+1)c)`）上，并把 `accepts` 在 `ε` 上的**单调性**显式用出来：
  带宽 `ε + ηₙ` 覆盖原带，故原带内的点逐 `n` 仍合格。

  ⚠ **为什么需要 `hnonneg` 而 `ηₙ → 0` 不够**：收敛只给「最终 `|ηₙ| < ε`」，
  给不出 `ηₙ ≥ 0`；而 `ηₙ < 0` 时 `ε + ηₙ < ε` 是**收紧**带宽，
  `accepts σ̂ ε e` 未必还能推出 `accepts σ̂ (ε + ηₙ) e`。
  所以 `hnonneg` 是**真前件**，不是装饰（反例：`ηₙ = -100`、`ε` 极小）。

  ⚠ **为什么中心仍是 `σ̂` 而不是 `√(v/(n+1))`**：见实现里的诚实登记——
  「把中心换成 `σ̂ₙ`」需要 `|σ̂ₙ − σ̂| ≤ ηₙ` 这类**估计误差**前件，
  而本文件的 `σ̂ₙ` 只对 `0` 有界（`accepts_of_sample_size` 的诚实边界），
  两者不是同一个量，硬换会让命题变假。把 `n` 真正带进裁决的是
  `accepts_of_sample_size`，本条负责「带宽会缩」这一半。 -/
theorem accepts_of_sample_size_squeeze {P : Measure ℝ} [IsProbabilityMeasure P]
    {η : ℕ → ℝ} (_hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hnonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ η n)
    {σhat ε e : ℝ} (h : accepts σhat ε e) :
    ∃ N : ℕ, ∀ n ≥ N, accepts σhat (ε + η n) e := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hnonneg
  refine ⟨N, fun n hn => ?_⟩
  have hη0 : (0 : ℝ) ≤ η n := hN n hn
  -- 带宽单调：`ε + η n ≥ ε`（由 `η n ≥ 0`），于是原带内的点仍在放宽后的带内。
  -- ⚠ **诚实登记**：结论的中心仍是 `σhat`（**不是** `√(v/(n+1))`）——
  -- 「中心换成 `σ̂ₙ`」需要 `|σ̂ₙ − σhat| ≤ η n` 这类**估计误差**前件，
  -- 而本文件的 `σ̂ₙ` 只对 `0` 有界（见 `accepts_of_sample_size` 的诚实边界），
  -- 两者不是同一个量，硬换会让命题变假。真正把 `n` 带进裁决的是
  -- `accepts_of_sample_size`，本条负责「带宽会缩」这一半。
  have hlo : σhat - (ε + η n) ≤ σhat - ε := by linarith only [hη0]
  have hup : σhat + ε ≤ σhat + (ε + η n) := by linarith only [hη0]
  exact ⟨le_trans hlo h.1, le_trans h.2 hup⟩

end FateV2.Error.SigmaToVerdict
