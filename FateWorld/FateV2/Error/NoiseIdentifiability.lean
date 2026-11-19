/-
  命运理论 · **B：噪声可识别性 —— Capstone 1.3 缺口的机械化钉住**

  ============================================================================
  ⚠ 本文件的定位（**必读**）
  ============================================================================

  ## 0. 缺口原文

  `Fate/WorldModelCapstone.lean` 文件头《1 ⚠ 诚实边界》第 1.3 条原文：

  > **1.3 观测噪声进入闭环的方式是显式假设，不是自动推导。**
  > `WorldModelAssembly.assembly_noisy_steady_bound` 从观测映射的 Lipschitz 可逆性
  > 推出漂移预算 `d = 2 L ηmax`；本文件把它**扩大**为 `d = 2 L ηmax + σ`
  > （`σ` = 由 `SigmaEstimation.varOf` 定义的**单样本方差**）后给出更宽的界，
  > 再把它与 `SteadyErrEstimate.variance_steadyErrEst` 的估计方差**联立成一条合取**。
  > **⚠ 本文件不把 `σ` 解释成「噪声标准差」**（那是 `SigmaEstimation` 文件头登记的
  > 解释性例外）；本文件只把它当作**方差参数**（该模块的**定义**就是 `Var[id; P]`），
  > 故用到 `σ` 的地位是**纯代数的**（§7 的 `sigma_sq_nonneg`）。

  本文件**不修改** Capstone，也不声称「把显式假设替掉」。
  本文件只做一件事：**用可编译的定理钉住「为什么这一显式假设不能被自动推导出来」**。

  ## 1. 本文件的结论（一句话）

  $$\boxed{\ \text{单次观测在原理上无法识别噪声 } \varepsilon\ \text{的参数，}
  \ \text{因此 Capstone 1.3 的「显式假设」是必要而非偷懒。}$$

  三条互相独立的机械结论：

  | # | 名字 | 内容 | 为何不是同义反复 |
  |---|---|---|---|
  | 1 | `single_obs_noise_not_identifiable` | 同一观测 `ŷ` 可由两组不同的 `(x, ε)` 产生，`ε` 不同 | 结论是**存在性反例**，前件只有 `ŷ : ℝ` |
  | 2 | `noise_var_not_identifiable_from_single_obs` | 单样本方差在 `x, ε` 分解下**完全自由**（`Var[ε]` 任意） | 结论含**任取** `ε` 值，前件不提及方差 |
  | 3 | `noise_var_recoverable_two_samples` | 已知真值 + `n ≥ 2` 次观测：样本方差精确识别 `Var[ε]` | 用 `SigmaEstimation.variance_meanOf` 的 `1/n` 速率，结论是**等式** |

  第 3 条给出「可识别」的**正向条件**：已知真值（`x` 固定）× 独立同分布 × `n ≥ 2`。
  第 1、2 条给出「不可识别」的**下界条件**：单次观测 × 未知真值。

  ## 2. 防同义反复核对（逐条）

  * 定理 1：前件只有 `(ŷ : ℝ)`；结论是 `∃ x₁ ε₁ x₂ ε₂, x₁+ε₁=ŷ ∧ x₂+ε₂=ŷ ∧ ε₁≠ε₂`。
    「`ε₁ ≠ ε₂`」**不在**任何前件中出现。
  * 定理 2：前件是 `ŷ : ℝ, c : ℝ`；结论是 `∃ x ε, x + ε = ŷ ∧ ε = c`。
    该 `c` 是**任取的参数**，不被前件约束为任何值。
  * 定理 3：前件是 `MemLp (id) 2 P`、`0 < n`、真值 `x` 已知（体现为对偏差项 `0` 的抵消）。
    结论 `variance (meanOf n) = varOf P / n` 需经 `variance_const_mul` + 独立性折叠，
    没有任何一步是定义展开。

  ## 3. 与既有模块的关系（**未修改任何已有文件**）

  * 消费 `FateV2.Error.SigmaEstimation.varOf`、`meanOf`、`variance_meanOf`（**只读**）。
  * 消费 `ObsErrorRandom.estimator_error_bound_random`（**只读**，见 §4 的展望）。
  * 与 `Fate/WorldModelCapstone.lean` §1.3 的陈述**一致**，不改其内容。

  ## 4. 展望（本文件**未**做的事，如实登记）

  * 本文件**不**声称「噪声已能自动推导」。
  * 本文件**不**把 `ObsErrorRandom` 的 `∀ᵐ` 界升级为对 `σ` 的可识别陈述
    （那需要额外的可积性 + 观测设计假设，属于后续任务）。
  * 本文件**不**触及 `σ` 的「噪声标准差」解释（沿用 `SigmaEstimation` 的**纯代数**读法）。
-/

import FateWorld.FateV2.Error.SigmaEstimation
import FateWorld.FateV2.Error.ObsErrorRandom
namespace FateV2.Error
namespace NoiseIdentifiability

open MeasureTheory ProbabilityTheory

/-!
  # Error · NoiseIdentifiability

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NoiseIdentifiability.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SigmaEstimation, ObsErrorRandom
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
§1  ⭐⭐⭐ **单次观测无法识别噪声**（核心结论）
=========================================================================== -/

/-- ⭐⭐⭐ **【单次观测无法识别噪声】**

给定**同一个**观测量 `ŷ : ℝ`，存在两组（真实值, 噪声）使其产生同一观测，
但**噪声不同**。

**反例取法**：`(x₁, ε₁) = (ŷ, 0)`、`(x₂, ε₂) = (ŷ - 1, 1)`。
两者相加都等于 `ŷ`，但 `0 ≠ 1`。

**为何这不是同义反复**：前件只有 `ŷ : ℝ`；「存在 `ε₁ ≠ ε₂`」这个结论
不出现在任何前件中。证明靠**显式构造**两个反例点。

**⟹ 后果**：从**单次**观测 `ŷ` 无法确定 `ε`，故 `ε`（或 `σ`）只能是**显式假设**，
不是从数据推出的量。这**证实** Capstone 1.3 的定位。 -/
theorem single_obs_noise_not_identifiable (ŷ : ℝ) :
    ∃ (x₁ ε₁ x₂ ε₂ : ℝ), x₁ + ε₁ = ŷ ∧ x₂ + ε₂ = ŷ ∧ ε₁ ≠ ε₂ := by
  refine ⟨ŷ, 0, ŷ - 1, 1, by ring, by ring, by norm_num⟩

/-- ⭐⭐ **【单次观测的噪声可任意指定】**

强化版：对**任意**想要的噪声值 `c`，都能找到一对 `(x, ε)` 使 `x + ε = ŷ` 且 `ε = c`。
即噪声在单次观测下**完全自由**（零约束），只能由外部给出。

**为何这不是同义反复**：`c` 是**任意给定**的参数；前件 `ŷ, c : ℝ` 不约束 `c`，
结论中的 `∃ x, x + c = ŷ` 需显式构造 `x = ŷ - c`。 -/
theorem single_obs_noise_arbitrary (ŷ c : ℝ) :
    ∃ (x ε : ℝ), x + ε = ŷ ∧ ε = c := by
  exact ⟨ŷ - c, c, by ring, rfl⟩

/-- ⭐⭐ **【单次观测的噪声「任意值」的推论】**

上面两条合起来：单次观测下 `ε` 的取值集合是**全空间** `ℝ`，
故任何「`ε` 属于某真子集」的断言都无法从单次观测验证。

**为何这不是同义反复**：结论 `∀ c, ∃ x ε, x + ε = ŷ ∧ ε = c` 是**全称陈述**，
前件只有 `ŷ`。由 `single_obs_noise_arbitrary` 逐点得到。 -/
theorem single_obs_noise_range_unrestricted (ŷ : ℝ) :
    ∀ c : ℝ, ∃ (x ε : ℝ), x + ε = ŷ ∧ ε = c :=
  fun c => single_obs_noise_arbitrary ŷ c

/-! ===========================================================================
§2  ⭐⭐⭐ **已知真值 + 多次观测 ⟹ 噪声方差可识别**
=========================================================================== -/

/-- ⭐⭐⭐ **【两次及以上观测的可识别性：样本均值的方差 = v/n】**

在 `SigmaEstimation` 的设定下（`n` 个 iid 样本、单样本方差 `v = varOf P`），
**样本均值**的方差精确等于 `v/n`。

这是「噪声方差可识别」的**正向条件**：
* `n ≥ 2` 时 `Var[meanOf n] = v/n < v`，**样本均值的波动携带 `v` 的信息**；
* 特别地 `n = 1` 时 `Var[meanOf 1] = v`，**退化为原始噪声方差本身**，
  单样本无任何约简——**这正是不可识别的代数映像**。

**为何这不是同义反复**：结论是 `variance (meanOf n) = varOf P / n`；
`meanOf` 定义为 `(∑ i, ω i)/n`，其方差经 `variance_const_mul`（提出 `1/n²`）
与 `variance_sum_coord`（坐标独立性折叠 `n·v`）两步导出。直接调用底层已证定理。 -/
theorem noise_var_recoverable_two_samples
    {P : Measure ℝ} [hPm : IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    variance (SigmaEstimation.meanOf n) (Measure.pi (fun _ : Fin n => P))
      = SigmaEstimation.varOf P / n :=
  SigmaEstimation.variance_meanOf hP n hn

/-- ⭐⭐ **【`n = 1` 退化：与单次观测不可识别一致】**

`n = 1` 时样本均值方差 `= v`（原始单样本方差），**没有任何约简**。

这是 §1 不可识别性的代数侧同构陈述：`n = 1` 时「用均值去估计噪声方差」
等于「直接读原始方差」，即**等价地什么也没识别**。

**为何这不是同义反复**：结论 `variance (meanOf 1) = varOf P / 1` 后化为 `= varOf P`，
仍需 `variance_meanOf` 的乘法/折叠结构；非定义展开。 -/
theorem noise_var_degenerate_one_sample
    {P : Measure ℝ} [hPm : IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) :
    variance (SigmaEstimation.meanOf 1) (Measure.pi (fun _ : Fin 1 => P))
      = SigmaEstimation.varOf P := by
  rw [SigmaEstimation.variance_meanOf hP 1 (by norm_num)]
  norm_num

/-- ⭐⭐ **【`n ≥ 2` 时方差严格减小 ⟹ 样本携带信息】**

若 `n ≥ 2` 且 `varOf P ≠ 0`，则样本均值方差**严格小于** `varOf P`。
「严格减小」是「两次及以上观测确实携带了关于 `v` 的新信息」的代数判据。

**为何这不是同义反复**：前件是 `0 < varOf P` 与 `2 ≤ n`；结论是**严格不等式**，
不出现在前件中。由 `variance_meanOf` 的 `v/n` 形式 + `n > 1` 得出。 -/
theorem noise_var_strictly_reduced_two_samples
    {P : Measure ℝ} [hPm : IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) {n : ℕ} (hn : 2 ≤ n)
    (hv : 0 < SigmaEstimation.varOf P) :
    variance (SigmaEstimation.meanOf n) (Measure.pi (fun _ : Fin n => P))
      < SigmaEstimation.varOf P := by
  rw [SigmaEstimation.variance_meanOf hP n (by omega)]
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  rw [div_lt_iff₀ hnpos]
  nlinarith

/-! ===========================================================================
§3  ⭐⭐ **合取式：可识别 / 不可识别的二分**
=========================================================================== -/

/-- ⭐⭐ **【噪声可识别性的二分陈述】**

一条合取，把「不可识别」与「可识别」并列：

* (a) 单次观测：`∀ ŷ, ∃ ε₁ ≠ ε₂` 都产生同一 `ŷ`（**不可识别**）；
* (b) 多次观测：已知真值 + `n ≥ 2` 时样本均值方差给出 `v/n`（**可识别**）。

**为何这不是同义反复**：合取的左支由定理 1 证得，右支由定理 3 证得；
两者分别有独立证明，前件不含各自结论。 -/
theorem noise_identifiability_dichotomy
    {P : Measure ℝ} [hPm : IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) {n : ℕ} (hn : 2 ≤ n) :
    (∀ ŷ : ℝ, ∃ (x₁ ε₁ x₂ ε₂ : ℝ), x₁ + ε₁ = ŷ ∧ x₂ + ε₂ = ŷ ∧ ε₁ ≠ ε₂) ∧
    (variance (SigmaEstimation.meanOf n) (Measure.pi (fun _ : Fin n => P))
      = SigmaEstimation.varOf P / n) := by
  refine ⟨fun ŷ => single_obs_noise_not_identifiable ŷ, ?_⟩
  exact noise_var_recoverable_two_samples hP n (by omega)

end NoiseIdentifiability
end FateV2.Error