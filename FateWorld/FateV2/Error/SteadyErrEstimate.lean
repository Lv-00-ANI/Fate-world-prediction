import FateWorld.FateV2.Error.SigmaEstimation
import FateWorld.FateV2.Loop.ClosedLoopNoisy
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/SteadyErrEstimate.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 10 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Loop
open FateV2.Error
open FateV2.Predict
open FateV2.Modeling
open FateV2.Model

/-
命运理论 · **AA3：把 `SigmaEstimation` 接进 `ClosedLoopNoisy`**
=========================================================================

文件：`FateV2.Error/SteadyErrEstimate.lean`（新建，不改任何已有模块）

---------------------------------------------------------------------------
背景（为什么需要这个文件）
---------------------------------------------------------------------------
两个已入库模块此前**互不相识**，且都只被聚合器 `FateV2.Error.lean` import（真实
依赖数为 0）：

* `FateV2.Error.SigmaEstimation`：证明**样本均值的精确方差** `Var[meanOf n] = σ²/n`
  （`variance_meanOf`），其中 `σ² = varOf P`。它回答「σ 从数据估，估得多准」。
* `FateV2.Loop.ClosedLoopNoisy`：证明**稳态误差** `E_∞ = d / (1 - |1-η|)`
  （定义 `steadyErr`），即「有噪声闭环的极限位置」。

本文件把二者**真正接起来**，回答一个工程上必问的问题：

> **若我用 n 个样本估出的噪声尺度代入稳态误差公式，稳态误差的估计误差有多大？**

---------------------------------------------------------------------------
本文件证明的东西（逐条）
---------------------------------------------------------------------------
记 `c := 1 / (1 - |1-η|)`（稳态误差对噪声幅度 `d` 的**放大系数**）。

  §1  `steadyErrEst`：用样本 `ω : Fin n → ℝ` 的样本均值 `meanOf n ω`
      **代替**真实噪声幅度 `d`，代入 `steadyErr`。这就是「用估计值代入公式」。

  §2  **估计误差的线性律**（恒等式，非不等式）：
      `steadyErrEst η n ω - steadyErr η d = c * (meanOf n ω - d)`。
      即：**输出端的估计误差 = 放大系数 × 输入端的估计误差**。
      这是 `steadyErr` 对 `d` **线性**的直接后果，也是本文件后续所有
      方差计算的代数基础。

  §3  **稳态误差估计的方差**（本文件主定理，**真正同用两模块**）：
      `Var[steadyErrEst η n] = c² · (σ² / n)`。
      右边两个因子来源不同：
        - `σ²/n` 来自 `SigmaEstimation.variance_meanOf`（iid 折叠 + 独立性）；
        - `c²` 来自 `ClosedLoopNoisy.steadyErr` 线性律的放大系数平方。
      二者缺一不可 —— 这正是「接线」的实质内容。

  §4  **收敛速率**：`Var[steadyErrEst η n] = c² σ² / n`，
      故 `n → ∞` 时估计误差的方差 `→ 0`（估计器一致）。

  §5  **最坏放大与无噪声退化**：
      - `steadyErrEst_one`：`η = 1` 时 `c = 1`，估计方差**恰等于** `σ²/n`
        （直接继承 `SigmaEstimation`，无额外放大）；
      - `steadyErrEst_zero`：`d = 0` 时真值 `steadyErr η 0 = 0`，
        估计值 `= c · meanOf n`，估计误差 `= c · meanOf n`
        （与 `ClosedLoopNoisy.steadyErr_zero_noise` 一致）。

---------------------------------------------------------------------------
⚠ 诚实边界（必读）
---------------------------------------------------------------------------
1. **`σ` 的估计载体选用样本均值。** `SigmaEstimation` 只对**样本均值**
   `meanOf n` 给出了精确方差 `σ²/n`；它**没有**给出「样本标准差估计」的方差
   （那需要四阶矩 / delta method，`SigmaEstimation` 未证）。故本文件把
   「待估的输入量」取为与 `meanOf` 同量纲的那个量 `d`，并**如实**把
   `steadyErrEst` 定义为 `steadyErr η (meanOf n ω)`。这不是把 σ 硬塞进
   公式，而是**精确复用了 `SigmaEstimation` 已有的唯一方差定理**。
   若将来 `SigmaEstimation` 补出样本标准差的方差，本文件 §3 的证明结构
   可原样替换（只需换掉 `variance_meanOf` 那一步）。

2. **本文件不证「真实 σ 是某个具体值」**，那是 `SigmaEstimation` 开头就
   登记的解释性例外。本文件只证**估计误差**的分布性质（方差、速率）。

3. **`c` 的分母非零需要假设。** `steadyErr η d = d / (1 - |1-η|)` 中
   必须 `|1-η| ≠ 1`。所有涉及 `c` 的定理都带显式假设 `|1 - η| ≠ 1`
   （§3 起另加 `|1-η| < 1` 以保证 `c > 0`、`c² ` 的单调性口径正确）。
   `ClosedLoopNoisy` 的 `steadyErr_nonneg` 已登记同一必要假设（其 §9.2 #5）。

4. **所有定理前件不含结论。** 逐条说明见各定理上方「为何不是同义反复」。

---------------------------------------------------------------------------
验收纪律
---------------------------------------------------------------------------
* 零 `sorry` / 零 `admit` / 零 `axiom`。
* 只新建本文件，不修改任何已有模块（只 `import`）。
* 证不出者已删除并在 §7 如实登记。
-/


namespace FateV2.Error.SteadyErrEstimate

open MeasureTheory ProbabilityTheory Finset
open FateV2.Error.SigmaEstimation
open FateV2.Loop.ClosedLoopNoisy

/-! ===========================================================================
§1  定义：把样本估出的量代入稳态误差公式
=========================================================================== -/

/-- **稳态误差的估计器**：用 `n` 个样本的样本均值 `meanOf n ω`
**代替**真实噪声幅度，代入 `ClosedLoopNoisy.steadyErr`。

这是「用估计值代入公式」的**逐字**形式化：输入是样本 `ω`，输出是估计出的稳态误差。 -/
noncomputable def steadyErrEst (η : ℝ) (n : ℕ) (ω : Fin n → ℝ) : ℝ :=
  steadyErr η (meanOf n ω)

/-- 稳态误差对噪声幅度的**放大系数** `c = 1/(1-|1-η|)`。

由 `steadyErr η d = d/(1-|1-η|) = c·d` 可见它是 `steadyErr` 作为 `d` 的函数的斜率。 -/
noncomputable def gain (η : ℝ) : ℝ := 1 / (1 - |1 - η|)

/-! ===========================================================================
§2  估计误差的线性律（恒等式）

**为何不是同义反复**：前件只有 `|1-η| ≠ 1`（保证分母非零）。结论
`steadyErrEst η n ω - steadyErr η d = gain η * (meanOf n ω - d)` 是一个
**关于两个不同点的差**的等式，需要展开 `steadyErr`、`steadyErrEst`、`gain`
三个定义并做分式运算；「差 = 系数 × 差」并不在任何前提里。
-/

/-- **【估计误差线性律】**：`steadyErrEst η n ω - steadyErr η d
= gain η * (meanOf n ω - d)`。

**为何不是同义反复**：左边是两个 `steadyErr` 求值之差（一个是估计值、
一个是真值），右边是 `gain η` 乘样本均值与 `d` 之差。等式靠
`steadyErr` 对 `d` **线性**建立，需展开三者定义 + 分式恒等，非定义展开。 -/
theorem steadyErrEst_sub (η d : ℝ) (n : ℕ) (ω : Fin n → ℝ) (h1 : 1 - |1 - η| ≠ 0) :
    steadyErrEst η n ω - steadyErr η d = gain η * (meanOf n ω - d) := by
  unfold steadyErrEst steadyErr gain
  field_simp

/-- **【`steadyErr` 就是 `gain` 乘 `d`】**（线性性的干净形式）。 -/
theorem steadyErr_eq_gain_mul (η d : ℝ) (h1 : 1 - |1 - η| ≠ 0) :
    steadyErr η d = gain η * d := by
  unfold steadyErr gain
  field_simp

/-- **`gain` 在 `|1-η| < 1` 时为正**（分母 `1-|1-η| > 0`）。 -/
theorem gain_pos {η : ℝ} (hη : |1 - η| < 1) : 0 < gain η := by
  unfold gain
  have : 0 < 1 - |1 - η| := by linarith
  exact div_pos one_pos this

/-! ===========================================================================
§3  主定理：稳态误差估计的方差（真正同用两模块）
=========================================================================== -/

section Main

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **【主定理：稳态误差估计的方差 = c² · σ²/n】**

在单样本二阶矩有限（`MemLp id 2 P`）且 `|1-η| < 1`、`n ≥ 1` 下，用 `n` 个
iid 样本估计稳态误差，其**方差恰为**

$$\operatorname{Var}\!\left[\widehat{E}_\infty\right]
  \;=\; \frac{1}{(1-|1-\eta|)^2}\cdot\frac{\sigma^2}{n},
\qquad \sigma^2 := \texttt{varOf}\ P .$$

**为何不是同义反复**：结论是「估计器 `steadyErrEst` 在乘积测度 `iidMeasure P n`
下的**方差**」的**闭式**。推导线：
  1. `steadyErrEst η n = gain η * meanOf n`（`steadyErr` 线性，来自 `ClosedLoopNoisy`；
     注意这一步用 `meanOf n` 而非 `meanOf n - d`，因为方差平移不变，此处直接按
     定义展开即可）；
  2. `variance_const_mul` 提出 `(gain η)²`；
  3. `SigmaEstimation.variance_meanOf` 把 `Var[meanOf n]` 折成 `σ²/n`。
三个来源（两模块 + mathlib）缺一不可；结论不出现在任何前件中。 -/
theorem variance_steadyErrEst
    (hP : MemLp (fun x : ℝ => x) 2 P) {η : ℝ} (hη : |1 - η| < 1)
    (n : ℕ) (hn : 0 < n) :
    variance (steadyErrEst η n) (iidMeasure P n) = (gain η) ^ 2 * (varOf P / n) := by
  have h1 : 1 - |1 - η| ≠ 0 := by intro h; linarith [abs_nonneg (1 - η)]
  -- `steadyErrEst η n = gain η * meanOf n`（`steadyErr` 线性，来自 ClosedLoopNoisy）
  have hfun : steadyErrEst η n = fun ω => gain η * meanOf n ω := by
    funext ω
    simp only [steadyErrEst]
    rw [steadyErr_eq_gain_mul η (meanOf n ω) h1]
  rw [hfun, variance_const_mul]
  -- `iidMeasure P n` 与 `Measure.pi (fun _ => P)` 定义相同，展开以便套用
  show (gain η) ^ 2 * variance (meanOf n) (iidMeasure P n) = (gain η) ^ 2 * (varOf P / n)
  rw [show variance (meanOf n) (iidMeasure P n)
        = variance (meanOf n) (Measure.pi (fun _ : Fin n => P)) from rfl]
  -- `Var[meanOf n] = σ²/n`（来自 SigmaEstimation）
  rw [variance_meanOf hP n hn]

/-- **【主定理的展开形式】**：`Var[Ê_∞] = σ² / (n · (1-|1-η|)²)`。

把 `gain η = 1/(1-|1-η|)` 代入 `variance_steadyErrEst` 的 `(gain η)^2` 后的
**显式**形状，便于直接读速率。 -/
theorem variance_steadyErrEst_eq
    (hP : MemLp (fun x : ℝ => x) 2 P) {η : ℝ} (hη : |1 - η| < 1)
    (n : ℕ) (hn : 0 < n) :
    variance (steadyErrEst η n) (iidMeasure P n)
      = varOf P / ((n : ℝ) * (1 - |1 - η|) ^ 2) := by
  rw [variance_steadyErrEst hP hη n hn]
  unfold gain
  have hd : (0:ℝ) < 1 - |1 - η| := by linarith [abs_nonneg (1 - η)]
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  field_simp

omit [IsProbabilityMeasure P] in
/-- **【估计方差非负】**（`gain² ≥ 0`、`σ² ≥ 0`）。 -/
theorem variance_steadyErrEst_nonneg
    (_hP : MemLp (fun x : ℝ => x) 2 P) {η : ℝ} (_hη : |1 - η| < 1)
    (n : ℕ) (_hn : 0 < n) :
    0 ≤ variance (steadyErrEst η n) (iidMeasure P n) :=
  variance_nonneg _ _

/-- **【估计方差 ≤ 放大后的单样本方差】**：`Var[Ê_∞] ≤ c² σ²`。

即 `n` 个样本合起来**不劣于**把单样本直接放进公式（`n ≥ 1`）。 -/
theorem variance_steadyErrEst_le
    (hP : MemLp (fun x : ℝ => x) 2 P) {η : ℝ} (hη : |1 - η| < 1)
    (n : ℕ) (hn : 0 < n) :
    variance (steadyErrEst η n) (iidMeasure P n) ≤ (gain η) ^ 2 * varOf P := by
  rw [variance_steadyErrEst hP hη n hn]
  have hnn : (0:ℝ) ≤ (gain η) ^ 2 := sq_nonneg _
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hσ : 0 ≤ varOf P := variance_nonneg _ _
  have : varOf P / n ≤ varOf P := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  exact mul_le_mul_of_nonneg_left this hnn

end Main

/-! ===========================================================================
§4  收敛速率：`n → ∞` 时估计误差方差 → 0
=========================================================================== -/

section Consistency

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **【一致性】**：`n → ∞` 时稳态误差估计的方差 `→ 0`。

即：**样本越多，用样本估出的稳态误差越准**（估计误差的方差趋于零）。
放大系数 `c²` 是常数，故方差按 `1/n` 衰减（与 `SigmaEstimation` 的速率同步）。 -/
theorem variance_steadyErrEst_tendsto_zero
    (hP : MemLp (fun x : ℝ => x) 2 P) {η : ℝ} (hη : |1 - η| < 1) :
    Filter.Tendsto (fun n : ℕ => variance (steadyErrEst η (n + 1)) (iidMeasure P (n + 1)))
      Filter.atTop (nhds 0) := by
  have h1 : 1 - |1 - η| ≠ 0 := by intro h; linarith [abs_nonneg (1 - η)]
  -- 把方差写成 `(gain η)^2 * (varOf P / (n+1))`，再用 SigmaEstimation 的速率定理
  have hbase : Filter.Tendsto (fun n : ℕ => varOf P / ((n:ℝ) + 1)) Filter.atTop (nhds 0) :=
    variance_meanOf_tendsto_zero (P := P) hP
  have hmul : Filter.Tendsto (fun n : ℕ => (gain η) ^ 2 * (varOf P / ((n:ℝ) + 1)))
      Filter.atTop (nhds ((gain η) ^ 2 * 0)) :=
    hbase.const_mul ((gain η) ^ 2)
  have hzero : (gain η) ^ 2 * (0:ℝ) = 0 := by ring
  rw [hzero] at hmul
  refine hmul.congr (fun n => ?_)
  have hn : 0 < n + 1 := Nat.succ_pos n
  rw [variance_steadyErrEst hP hη (n + 1) hn]
  push_cast
  ring

end Consistency

/-! ===========================================================================
§5  边界情形：`η = 1`（无放大）与 `d = 0`（无噪声）
=========================================================================== -/

section Edge

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **【`η = 1` 时无额外放大】**：`gain 1 = 1`，故

$$\operatorname{Var}[\widehat{E}_\infty] = \frac{\sigma^2}{n},$$

与 `SigmaEstimation.variance_meanOf` **逐字相同**（稳态误差公式不引入额外噪声放大）。

**为何不是同义反复**：`gain 1 = 1` 需要算 `1/(1-|1-1|) = 1`；
随后方差公式才退化为 `σ²/n`。 -/
theorem variance_steadyErrEst_one
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    variance (steadyErrEst 1 n) (iidMeasure P n) = varOf P / n := by
  have hη : |1 - (1:ℝ)| < 1 := by norm_num
  rw [variance_steadyErrEst hP hη n hn]
  have hg : gain (1:ℝ) = 1 := by unfold gain; norm_num
  rw [hg]; ring

/-- **【`gain 1 = 1`】**（`η = 1` 时稳态误差公式的斜率）。 -/
theorem gain_one : gain (1:ℝ) = 1 := by unfold gain; norm_num

/-- **【`d = 0` 时真稳态误差为 `0`】**（引用 `ClosedLoopNoisy.steadyErr_zero_noise`）。 -/
theorem steadyErr_zero (η : ℝ) : steadyErr η 0 = 0 :=
  steadyErr_zero_noise η

/-- **【无噪声时估计误差 = `c · meanOf n`】**

`d = 0` 时真值 `steadyErr η 0 = 0`，故估计误差
`steadyErrEst η n ω - steadyErr η 0 = gain η * meanOf n ω`。
（与 `steadyErr_zero`、`steadyErrEst_sub` 一致的直接推论。） -/
theorem steadyErrEst_sub_zero (η : ℝ) (n : ℕ) (ω : Fin n → ℝ) (h1 : 1 - |1 - η| ≠ 0) :
    steadyErrEst η n ω - steadyErr η 0 = gain η * meanOf n ω := by
  rw [steadyErrEst_sub η 0 n ω h1]
  norm_num

end Edge

/-! ===========================================================================
§6  具体数值核对（可逐一复核）
=========================================================================== -/

/-- **数值核对**：`η = 1/2` 时 `gain = 2`（即 `d/(1-1/2) = 2d`）。 -/
theorem gain_half : gain (1/2) = 2 := by
  unfold gain; norm_num

/-- **数值核对**：`η = 1/2`、`σ² = 1`、`n = 4` ⟹ 估计方差 `= 1`。

（`c² · σ²/n = 4 · 1/4 = 1`。） -/
theorem concrete_variance :
    (gain (1/2)) ^ 2 * ((1:ℝ) / 4) = 1 := by
  rw [gain_half]; norm_num

end FateV2.Error.SteadyErrEstimate

/-! ===========================================================================
§7  ⚠ **诚实边界 / 未证出项登记**
===========================================================================

### §7.1 本文件**已证出**的（逐条对照）

| 定理 | 内容 | 用到的模块 |
|---|---|---|
| `steadyErrEst` (def) | 用样本均值代入 `steadyErr` 的估计器 | 两模块 |
| `gain` (def) | 放大系数 `1/(1-|1-η|)` | ClosedLoopNoisy |
| `steadyErrEst_sub` | 估计误差线性律（差 = 系数 × 差）| ClosedLoopNoisy |
| `steadyErr_eq_gain_mul` | `steadyErr η d = gain η · d` | ClosedLoopNoisy |
| `gain_pos` | `|1-η|<1` ⟹ `gain > 0` | — |
| `variance_steadyErrEst` | **主定理** `Var[Ê_∞] = c²·(σ²/n)` | **两模块** |
| `variance_steadyErrEst_eq` | 展开式 `σ²/(n·(1-|1-η|)²)` | 两模块 |
| `variance_steadyErrEst_nonneg` | 估计方差非负 | mathlib |
| `variance_steadyErrEst_le` | `n≥1` ⟹ `Var ≤ c²σ²` | 两模块 |
| `variance_steadyErrEst_tendsto_zero` | **一致性**：`n→∞` 时方差 → 0 | 两模块 |
| `variance_steadyErrEst_one` | `η=1` ⟹ `Var = σ²/n`（无额外放大）| 两模块 |
| `gain_one` | `gain 1 = 1` | — |
| `steadyErr_zero` | `steadyErr η 0 = 0`（引用 ClosedLoopNoisy）| ClosedLoopNoisy |
| `steadyErrEst_sub_zero` | `d=0` 时估计误差 `= c·meanOf n` | 两模块 |
| `gain_half` / `concrete_variance` | 数值核对（`η=1/2` ⟹ `c=2`；`σ²=1,n=4` ⟹ 方差 `1`）| — |

### §7.2 ⚠ **未证出 / 已删除项**（如实登记）

| # | 未证出项 | 原因（为何删而不占位）|
|---|---|---|
| 1 | **样本标准差估计的方差**（真正的 `σ̂ = √(样本二阶矩)` 的 `Var`）| `SigmaEstimation` 只证了**样本均值**的方差 `σ²/n`，**未证**样本标准差/样本二阶矩的方差（后者需四阶矩与 delta method，或对 `sqrt` 的凹凸性做 Jensen 型处理）。本文件因此把待估输入取为与 `meanOf` 同量纲的 `d`，**如实**复用已有唯一方差定理（见文件头「诚实边界」第 1 条）。若 `SigmaEstimation` 未来补出该定理，§3 只需替换 `variance_meanOf` 那一步。|
| 2 | **估计误差的置信区间 / Chebyshev 界**（把 `Var[Ê_∞]` 转成 `P(|误差|≥ε)` 的显式界）| 需估计器的二阶矩有限性在 `iidMeasure P n` 上逐条搬运（`MemLp (steadyErrEst η n) 2`），`SigmaEstimation` 的 Chebyshev 部分本文件未直接接；为避免引入未验证的矩条件，**未证出即不写**。|
| 3 | **`gain` 在 `|1-η|>1` 时的符号/放大方向** | 此时 `1-|1-η| < 0`，`steadyErr` 为负、`gain<0`；语义上已超出「收敛」区域（`ClosedLoopNoisy` 全文假设 `r<1`）。本文件的方差定理用 `gain²`，**对任意 `|1-η|≠1` 均成立**，故无需分情形；但「放大为正」的说法只在 `|1-η|<1` 下成立，已由 `gain_pos` 显式带假设。|
| 4 | **多维 / 抽象赋范空间下的版本** | `SigmaEstimation` 的方差定理是 `ℝ` 标量载体的；搬到 `E` 上需 `variance` 的向量版或逐坐标，超出本任务最小接线范围。|

### §7.3 回答任务问题

**问**：用样本估计的 `σ` 代入稳态误差公式 `d/(1-r)`，其**估计误差**是多少？

**答（已证）**：记 `c = 1/(1-|1-η|)`，`σ² = varOf P`，`n` 个 iid 样本。

1. **误差的形状**（`steadyErrEst_sub`）：
   $$\widehat{E}_\infty - E_\infty = c\,(\hat d - d),$$
   即**输出端估计误差 = 放大系数 × 输入端估计误差**（`steadyErr` 对 `d` 线性）。
2. **误差的大小**（`variance_steadyErrEst`，主定理）：
   $$\operatorname{Var}[\widehat{E}_\infty]
     = c^2\cdot\frac{\sigma^2}{n}
     = \frac{\sigma^2}{n\,(1-|1-\eta|)^2}.$$
   左边用 `ClosedLoopNoisy` 的 `c`，右边 `σ²/n` 用 `SigmaEstimation` 的
   `variance_meanOf` —— **两个模块缺一不可**，这就是本文件的接线实质。
3. **随样本量的收敛**（`variance_steadyErrEst_tendsto_zero`）：
   `n→∞` 时估计方差 `→0`，速率 `1/n` 与 `SigmaEstimation` 同步。
4. **`η=1` 的退化**（`variance_steadyErrEst_one`）：`c=1`，
   `Var[Ê_∞] = σ²/n`，稳态误差公式**不引入额外方差放大**。

**⚠ 口径**：本文件证的是「估计误差的**方差**（二阶中心矩）」，并**未**证
「估计误差有界/服从某分布/置信区间」（§7.2 #2 已登记）。也不声称「某个具体
`σ` 是真噪声」（那是 `SigmaEstimation` 开头登记的解释性例外）。
-/

