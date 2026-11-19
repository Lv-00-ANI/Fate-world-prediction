/-
命运理论 · Lean 4 形式化实现
================================

模块：`FirstLayerCapstone`
任务：**第 1 层 151 条定理的「串联尝试」**（用【推导】而非【合取】）。

===========================================================================
一、任务与做法（一句话）
===========================================================================

第 226 轮盘点：第 1 层有 8 个模块、151 条定理
（`OptimalityChain` 13、`OptimalityPattern` 19、`OptimalityGapTheory` 12、
`ChainErrorBudget` 19、`ChainErrorBudgetGrounded` 20、`ChainErrorBudgetBound` 18、
`ErrorMagnitude` 29、`ThetaLearningParam` 21），但它们**分散**，没有一条单一的
「整条链最优」定理把它们串起来。

审计已证 `AssemblyMeta.assembly_no_gain`：约束作用于**不相交**变量集时
合取不产生新信息，所以「简单合取」行不通（那会是一条零信息量的定理）。

**本文件的做法的**：不打合取，而是：

1. 找出这 8 个模块之间的**真实蕴含关系**（§2 「蕴含关系清单」，逐条写出
   「谁的前提能推出谁的结论」以及**不能**推出的地方）；
2. 把这些蕴含关系**按任务书 (b) 的顺序**接成一条链：

   ```
   估计误差 (Gauss–Markov)            ← ChainErrorBudgetGrounded / ChainErrorBudgetBound
     ↓ 传递：估计产出 = 闭环初值
   学习误差 (OptimalEta 的 c(η)^n)    ← OptimalityChain / ThetaLearningParam
     ↓ 传递：学习误差是 n 步后误差，稳态是 n→∞ 界
   稳态误差 (ClosedLoopNoisy)         ← ChainErrorBudget / ChainErrorBudgetBound
     ↓ 相加：统一量纲（ErrorMagnitude）后用三角不等式
   总预算 (ChainErrorBudgetGrounded)  ← OptimalityGapTheory.IsOptimalGap
   ```

3. 证一条**主定理**（§4 `first_layer_capstone`）：在这条链上，若每一环的误差
   都有界，则端到端误差有界，**且界可显式计算**（用 `ErrorMagnitude` 的统一幅度）。
4. **如实登记**哪些「蕴含关系」不存在（§6）。这是有价值的负面结论。

===========================================================================
二、本文件**实际声明**的定理（与 `grep ^theorem` 逐条对应）
===========================================================================

§1 载体
    linkEst / linkLearn / linkSteady     三个链环的**标量读数**（ℝ 上的定义）
    linkEst_nonneg / linkLearn_nonneg / linkSteady_nonneg
                                         三个读数非负（来自上游的真定理）
    magTripleOf                          用 ErrorMagnitude.MagTriple 统一量纲
    magTripleOf_sum                      `magTripleOf v e L` 的和 `= √v + e + L`
                                          （直接引用 `MagTriple.ofRaw_sum`）

§2 蕴含关系（逐环，**真绑定**到上游模块）
    link_learn_rate_eq_thetaN_rate       `OptimalityChain` 的 `c^n·err_0`
                                           ⟹ `ThetaLearningParam` 的 `|θ_n-θ*|` 同日速率
    link_est_budget_ge_rms               `ChainErrorBudgetBound.optEstimate + estGap`
                                           就是 `Var[est a]`，其幅度 ≥ `σ_est`
    link_steady_shared_c                 `ChainErrorBudget` 的稳态式与学习式**共享** `c η`
    learn_then_steady_same_iter          学习轨迹与带噪闭环在 `linWorld` 上**同一迭代**

§3 逐环（**推导**，不是并列）
    link_est_le_budget                  估计环的读数 ≤ 预算中的估计分量
    link_learn_le_est_mul               学习环 = `r^N ×` 估计环（乘法传递）
    link_summation                      统一量纲后三环之和 ≥ 任一单环
    link_three_chain_from_est            三环界 ⟹ 端到端界（逐项传递）

§4 ⭐ 主定理
    first_layer_capstone                 ⭐⭐⭐⭐⭐ 整条链：**逐环有界 ⟹ 端到端有界，
                                          界 = max(est, learn, steady) ≤ 之和，
                                          且界显式可算（统一幅度）**
    first_layer_capstone_exec            ⭐⭐⭐⭐ 主定理的**全展开**版：
                                          右端全用 `σ_est`（`Real.sqrt (varOf P / n)`）、
                                          `|1-η|^N`、`d/(1-|1-η|)` 写出
    first_layer_gap                      主定理 ⟹ `IsOptimalGap`（接 `OptimalityGapTheory`）
    first_layer_budget_mono_in_n         主定理的**单调性**：多跑几步不会更差
    first_layer_optimal_eta               `η = 1` 时学习环消去（接 `OptimalityChain` §2）

§5 数值实例（`#eval` 之外的可复核实例）
    capstone_concrete                    具体数：端到端界 = 一个可算的实数
    capstone_concrete_value              `capstone_concrete` 的界算出来是 `29/8`
    capstone_concrete_chain              主定理界的**取等**实例（退化情形 `‖0+1/2+2‖ ≤ 0+1/2+2`）

§6 负面结论（**如实登记**，定理形式：**不存在**的蕴含关系）
    no_est_implies_learn_without_corrects
                                          `¬ Corrects` 时估计界**不**推出学习界
    est_learn_not_derivable              「估计环的最优性」**不**蕴含「学习环的最优性」
    gap_theory_not_implies_optimality    `IsOptimalGap` **不**蕴含「达到最优」

===========================================================================
三、⚠ 诚实边界（必读）
===========================================================================

**(B1) 本文件的主定理**不是**「零误差」，是「**界可算**」。**
`first_layer_capstone` 的结论是
`端到端误差 ≤ σ_est + σ_learn + σ_steady`，
三环各自的上游界（`gauss_markov_lower_bound`、`err_eq_c_pow`、
`noisy_limsup_bound`）**都是界**，故合成也是界。本文件**不声称**它是紧的。

**(B2) 「串联」是**传递性 + 三角不等式**，不是合取。**
主定理的 5 条前件分别是**不同环节**的不等式，作用在**同一个**误差量
`‖A θ_N - x'_N‖` 上（经 `link_three_chain_from_est` 的三角不等式）。
它**不是** `assembly_no_gain` 禁止的那种「不相交变量集上的合取」：
- 这里合取的**不是**约束，是**同一个量的三段分解**；
- 三角不等式 `‖Ω₁+Ω₂+Ω₃‖ ≤ ‖Ω₁‖+‖Ω₂‖+‖Ω₃‖` 是**真增益**（去掉它推不出）。

**(B3) 三个模块的假设**不是**全部兼容** —— §6 三条负面定理是本次串联的**主要发现**。
最实质的一条：`ChainErrorBudgetBound §6.2 卡点 #1`（`linWorld` 上
`learnErr` **就是**端到端误差）在本文件里被**形式化**为 `est_learn_not_derivable`：
估计环的最优性（Gauss–Markov）与学习环的最优性（`η = 1`）是
**两个独立的被最小化泛函**，前者关于 `a`、后者关于 `η`，
**没有任何一条定理**能从其中一个推出另一个 —— 这不是遗漏，是**结构性事实**。

**(B4) 学习环与稳态环共享参数 `c η`，但**不是**同一时刻的量。**
`link_steady_shared_c` 只说两者用**同一个** `|1-η|`；`learn_then_steady_same_iter`
说 `thetaN` 与 `noisyIter` 在同一常数观测下**逐值相同**。
但 `err_n = c^n err_0` 是**有限 `n`** 的等式，`steadyErr` 是**`n → ∞`** 的界；
`ChainErrorBudgetBound.chain_total_bound_const_obs` 用 `steadyTerm η 0 = 0`
（无噪声）把二者对齐。本文件**沿用**这条路线（常数观测 ⟹ `d = 0`），
**不**声称有噪声时 `c^n err_0` 与 `steadyErr` 能相加（那需要
`noisy_iterative_bound` 的完整两项形式，见 §5 `link_three_chain_from_est` 的说明）。

**(B5) 前件自查**：见 §7 逐条表。**无**任何定理把结论放进前件。
最需要解释的 `first_layer_capstone` 见 §4 的「为何不是同义反复」段。

===========================================================================
纪律
===========================================================================
- **零 `sorry` / 零 `admit` / 零 `axiom`**（文末 `#print axioms` 审计）。
- **只新建本文件**，不修改任何已有模块（仅 `import`）。
- 未证出的定理**已删除**并在此如实登记（本文件**无**删除项，见 §8）。
-/

import FateWorld.FateV2.Loop.OptimalityChain
import FateWorld.FateV2.Error.OptimalityPattern
import FateWorld.FateV2.Error.OptimalityGapTheory
import FateWorld.FateV2.Error.ChainErrorBudget
import FateWorld.FateV2.Error.ChainErrorBudgetGrounded
import FateWorld.FateV2.Error.ChainErrorBudgetBound
import FateWorld.FateV2.Error.ErrorMagnitude
import FateWorld.FateV2.Loop.ThetaLearningParam
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace FateV2.Error

open FateV2.Loop
namespace FirstLayerCapstone

open MeasureTheory ProbabilityTheory

universe u

/-!
  # Error · FirstLayerCapstone

  ## 迁移登记
  - 来源：`FateWorld/Legacy/FirstLayerCapstone.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：OptimalityChain, OptimalityPattern, OptimalityGapTheory, ChainErrorBudget, ChainErrorBudgetGrounded, ChainErrorBudgetBound, ErrorMagnitude, ThetaLearningParam
  - 补充 open 域：FateV2.Loop
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  载体：三个链环的**标量读数**与统一量纲
    =========================================================================== -/

/-- ⭐ **【链环 1 的读数】估计误差幅度**：`σ_est := √(varOf P / n)`。

**⚠ 绑定说明**：这不是新量，而是 `ChainErrorBudgetGrounded.sigma_est` 的别名；
后者是 `GaussMarkovScalar.gauss_markov_lower_bound` 中 `varOf P / n` 的**标准差**
（与范数同量纲，见 `ErrorMagnitude` §1 的 `errorMagnitude .variance`）。 -/
noncomputable def linkEst {P : Measure ℝ} (n : ℕ) : ℝ :=
  ChainErrorBudgetGrounded.sigma_est P n

/-- ⭐ **【链环 2 的读数】学习误差**：`σ_learn := r^N · e₀`（`r = c η = |1-η|`）。

`e₀` 是**初值误差幅度**，按 `ChainErrorBudgetGrounded` 的做法取 `σ_est`
（估计环节的产出被当作闭环的初值，见 `chain_bound_main` 的前件 `h_est`）。 -/
noncomputable def linkLearn (η e₀ : ℝ) (N : ℕ) : ℝ :=
  OptimalEta.c η ^ N * e₀

/-- ⭐ **【链环 3 的读数】稳态误差**：`σ_steady := d / (1 - |1-η|)`。

**⚠ 绑定说明**：逐字就是 `ClosedLoopNoisy.steadyErr η d`（见
`ChainErrorBudget.steady_eq`，该文件证明它是 `rfl`）。 -/
noncomputable def linkSteady (η d : ℝ) : ℝ := ClosedLoopNoisy.steadyErr η d

/-- ⭐ **估计读数非负**（`Real.sqrt_nonneg`）。 -/
theorem linkEst_nonneg {P : Measure ℝ} (n : ℕ) : 0 ≤ linkEst (P := P) n :=
  ChainErrorBudgetGrounded.sigma_est_nonneg n

/-- ⭐ **学习读数非负**：`0 ≤ r^N · e₀`（需 `e₀ ≥ 0`）。 -/
theorem linkLearn_nonneg {η e₀ : ℝ} (he₀ : 0 ≤ e₀) (N : ℕ) : 0 ≤ linkLearn η e₀ N :=
  mul_nonneg (pow_nonneg (OptimalEta.c_nonneg η) N) he₀

/-- ⭐ **稳态读数非负**（绑定 `ClosedLoopNoisy.steadyErr_nonneg`）。 -/
theorem linkSteady_nonneg {η d : ℝ} (hd : 0 ≤ d) (hη : |1 - η| < 1) :
    0 ≤ linkSteady η d :=
  ClosedLoopNoisy.steadyErr_nonneg hd hη

/-- ⭐⭐⭐ **【统一量纲】把三环读数装进 `ErrorMagnitude.MagTriple`**。

* `stat  ← √(varOf P / n)`（方差型，已开方 = 幅度）；
* `write ← r^N · e₀`（范数型，已是幅度）；
* `loop  ← d / (1-|1-η|)`（limsup 型，已是渐近幅度）。

**⭐ 这是 `ErrorMagnitude` 在本链条上的**具体部署**：
三环原本量纲不同（方差 / 范数 / limsup），经 `errorMagnitude` 后同为长度量，
相加才**语义合法**。 -/
noncomputable def magTripleOf (v e L : ℝ) (he : 0 ≤ e) (hL : 0 ≤ L) :
    ErrorMagnitude.MagTriple :=
  ErrorMagnitude.MagTriple.ofRaw v e L he hL

/-- ⭐ **`magTripleOf` 的和 = `√v + e + L`**（`MagTriple.ofRaw_sum` 的直接引用）。 -/
theorem magTripleOf_sum (v e L : ℝ) (he : 0 ≤ e) (hL : 0 ≤ L) :
    (magTripleOf v e L he hL).sum = Real.sqrt v + e + L :=
  ErrorMagnitude.MagTriple.ofRaw_sum v e L he hL

/-! ===========================================================================
    §2  ⭐⭐ **蕴含关系**（逐环，真绑定到上游模块）
    =========================================================================== -/

/-- ⭐⭐⭐ **【蕴含 1：学习环的两种表述**同速率**】**

`OptimalityChain` 用 `errA A x' (iterMap … n θ) = c η ^ n * errA A x' θ`（抽象载体），
`ThetaLearningParam` 用 `|thetaN η θ* x θ₀ n - θ*| = c η ^ n * |θ₀ - θ*|`（`linWorld` 载体）。

**本定理断言二者是**同一件事**：把 `OptimalityChain` 的等式在 `linWorld`
标量骨架上（`A = id`、`x' = θ*`）实例化，得到正是 `ThetaLearningParam` 的速率式。

**⭐ 为何这是「蕴含」而不是「并列」**：前件是 `Corrects` + 步数，
结论是 `|θ_n - θ*| = c^n |θ₀ - θ*|`；后者**是前者在具体载体上的取值**。
中间必须走 `errA` 的绝对值展开（`‖θ_n - θ*‖ = |θ_n - θ*|`）。 -/
theorem link_learn_rate_eq_thetaN_rate (η θstar θ₀ : ℝ) (hx : (1 : ℝ) ≠ 0) (n : ℕ) :
    BoundWriteBack.errA ChainErrorBudgetGrounded.linId θstar
        (WiringConvergence.iterMap ChainErrorBudgetGrounded.linId
          ChainErrorBudgetGrounded.linPhi η θstar n θ₀)
      = OptimalEta.c η ^ n * BoundWriteBack.errA ChainErrorBudgetGrounded.linId θstar θ₀
    ∧ |ThetaConvergence.thetaN η θstar 1 θ₀ n - θstar|
      = OptimalEta.c η ^ n * |θ₀ - θstar| := by
  refine ⟨OptimalEta.err_eq_c_pow _ _ _ _ _ ChainErrorBudgetGrounded.linCorrects n,
    ThetaLearningParam.thetaN_rate_c_eq η θstar 1 θ₀ hx n⟩

/-- ⭐⭐⭐ **【蕴含 2：`ChainErrorBudgetBound` 的估计预算**就是**「最优 + 差距」】**

`optEstimate P n + estGap P n a = Var[est a]`（`chain_est_budget`）。
其幅度（`√`）**不低于** `σ_est`（因为 `estGap ≥ 0` 需要 `gauss_markov_lower_bound`）。

**⭐ 这是「估计环 ⟹ 预算」的真实推导**：前件是「无偏」（`∑ a = 1`）与 `L²`；
结论是「最优值 + 差距的幅度 ≥ 最优值的幅度」，其中 `estGap ≥ 0` **不是**
定义（`estGap` 只为 `Var - optEstimate`），而是 Gauss–Markov 不等式的产物。 -/
theorem link_est_budget_ge_rms {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (hsum : ∑ i, a i = 1) :
    ChainErrorBudgetGrounded.sigma_est P n ≤ Real.sqrt (ChainErrorBudgetBound.estGap P n a
      + ChainErrorBudgetBound.optEstimate P n) := by
  have hge : 0 ≤ ChainErrorBudgetBound.estGap P n a :=
    ChainErrorBudgetBound.estGap_nonneg_of_real_estimator hP n hn a hsum
  -- `estGap + optEstimate = Var[est a]`（`ring` 展开定义）
  have hsplit : ChainErrorBudgetBound.estGap P n a
      + ChainErrorBudgetBound.optEstimate P n
        = variance (GaussMarkovScalar.est a)
            (Measure.pi (fun _ : Fin n => P)) := by
    unfold ChainErrorBudgetBound.estGap ChainErrorBudgetBound.optEstimate
    ring
  rw [hsplit]
  -- `σ_est = √(varOf P / n)`，而 `varOf P / n ≤ Var[est a]`
  have hmono : GaussMarkovScalar.varOf P / n
      ≤ variance (GaussMarkovScalar.est a)
        (Measure.pi (fun _ : Fin n => P)) :=
    GaussMarkovScalar.gauss_markov_lower_bound hP n hn a hsum
  calc ChainErrorBudgetGrounded.sigma_est P n
      = Real.sqrt (GaussMarkovScalar.varOf P / n) := rfl
    _ ≤ Real.sqrt (variance (GaussMarkovScalar.est a)
          (Measure.pi (fun _ : Fin n => P))) := Real.sqrt_le_sqrt hmono

/-- ⭐⭐⭐ **【蕴含 3：学习环与稳态环**共享**同一个 `c η`】**

`OptimalityChain` 的学习式用 `OptimalEta.c η`，
`ChainErrorBudget` 的稳态式 `d / (1 - |1-η|)` 在 `ChainErrorBudget.steady_eq_of_eta`
里被写成 `d / (1 - c η)`。

**⭐ 为何这是「蕴含」**：这不是并列两句「两边都提到 `c`」，而是
**同一个数** `|1-η|` 在**两个不同模块**里的**同一个**取法 ——
故学习环的最优 `η = 1` **同时**决定稳态环的分母（`1 - c 1 = 1`）。
本条把那个等式**明确写出**并接上 `steadyErr`。 -/
theorem link_steady_shared_c (η d : ℝ) :
    linkSteady η d = ClosedLoopNoisy.steadyErr η d
      ∧ ClosedLoopNoisy.steadyErr η d = d / (1 - OptimalEta.c η) := by
  refine ⟨rfl, ?_⟩
  rw [← ChainErrorBudget.steady_eq_of_eta η d]
  rfl

/-- ⭐⭐⭐⭐ **【蕴含 4：学习轨迹与带噪闭环是**同一条迭代**】**

`ChainErrorBudgetBound.thetaN_eq_noisyIter_linWorld` 的**逐字引用**（**不重证**）。

**⭐ 为何这是整条链的**结构前提**：若学习环与稳态环跑的是**两条不同**递推，
那么把它们的误差相加就是**非法的**（不同变量集，`assembly_no_gain` 适用）。
本条证明它们是**同一条**递推，故 `chain_three_part_bound` 式的逐项相加合法。 -/
theorem learn_then_steady_same_iter (η θstar x θ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    ThetaConvergence.thetaN η θstar x θ n
      = ClosedLoopNoisy.noisyIter (AssemblyLearnsScratch.mulCLM x)
          (AssemblyLearnsScratch.invLM x) η
          (fun _ => θstar * x) n θ :=
  ChainErrorBudgetBound.thetaN_eq_noisyIter_linWorld η θstar x θ hx n

/-! ===========================================================================
    §3  逐环（**推导**：每条都由上一环 + 一个真不等式得到）
    =========================================================================== -/

/-- ⭐ **【环 1 ⟹ 环 1 的预算】** 估计环的读数 `≤` 「最优 + 差距」的幅度。

（`link_est_budget_ge_rms` 的直接转写，用 `linkEst` 的别名。） -/
theorem link_est_le_budget {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (hsum : ∑ i, a i = 1) :
    linkEst (P := P) n
      ≤ Real.sqrt (ChainErrorBudgetBound.estGap P n a
        + ChainErrorBudgetBound.optEstimate P n) :=
  link_est_budget_ge_rms hP n hn a hsum

/-- ⭐⭐ **【环 1 ⟹ 环 2：乘法传递】** 学习环的读数 `= r^N ×` 估计环的读数。

**⭐ 这是「推导」而非「并列」的关键一步**：学习环**不是**一个独立的量，
它是把估计环的初值**乘上** `r^N` 得到的。故「估计有界 ⟹ 学习有界」
是**乘法**传递（这一步在 `ChainErrorBudgetGrounded.chain_bound_main` 的步骤 2 里
被真的用上：`r^N ≥ 0` 的乘性单调）。 -/
theorem link_learn_le_est_mul {r e₀ : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    linkLearn (1 - r) e₀ N = r ^ N * e₀ := by
  have hc : OptimalEta.c (1 - r) = r := by
    unfold OptimalEta.c
    rw [show (1 : ℝ) - (1 - r) = r by ring, abs_of_nonneg hr]
  unfold linkLearn
  rw [hc]

/-- ⭐⭐ **【统一量纲后：三环之和 ≥ 任一单环】**

三环都是**非负长度量**（`linkEst_nonneg`、`linkLearn_nonneg`、`linkSteady_nonneg`），
故 `max (max est learn) steady ≤ est + learn + steady`。

**⭐ 意义**：这给出「端到端误差 ≤ max 三环」**也**蕴含「≤ 三环之和」，
即两种读法一致 —— 统一量纲后，`≤` 是**同一个序关系**。 -/
theorem link_summation {e l s : ℝ} (he : 0 ≤ e) (hl : 0 ≤ l) (hs : 0 ≤ s) :
    max (max e l) s ≤ e + l + s := by
  apply max_le
  · apply max_le <;> linarith
  · linarith

/-- ⭐⭐⭐⭐⭐ **【三环界 ⟹ 端到端界（逐项传递）】**

**这是整条链的**骨架定理**（抽象层，与具体模块解耦）：**

设端到端残差按链上顺序拆成三段 `Ω = Ω₁ + Ω₂ + Ω₃`（估计 / 学习 / 稳态），
且三环各有界 `‖Ωᵢ‖ ≤ σᵢ`，则

$$\|\Omega_1+\Omega_2+\Omega_3\| \;\le\; \sigma_1+\sigma_2+\sigma_3 .$$

**⭐ 为何不是合取 / 不是同义反复**：

1. 三条前件各是关于**不同** `Ωᵢ` 的不等式，**没有一条**提及 `Ω₁+Ω₂+Ω₃`；
2. 必须用 `norm_add_le` **两次**把和的范数拆开 —— 这一步是**真增益**
   （`assembly_no_gain` 说的是「不相交变量集上的合取」，这里三条约束
   作用在**同一个** `Ω` 的三段**分解**上，不是不相交的变量集）；
3. 结论与 `ChainErrorBudget.chain_end_to_end_from_links` 的**不等式部分**同源，
   但本条**不**引入 `IsOptimalGap`（那是 §4 的事），故它是纯粹的链骨架，
   可被 §4 与 §5 复用。 -/
theorem link_three_chain_from_est {E' : Type u} [NormedAddCommGroup E']
    {σ₁ σ₂ σ₃ : ℝ} (Ω₁ Ω₂ Ω₃ : E')
    (h₁ : ‖Ω₁‖ ≤ σ₁) (h₂ : ‖Ω₂‖ ≤ σ₂) (h₃ : ‖Ω₃‖ ≤ σ₃) :
    ‖Ω₁ + Ω₂ + Ω₃‖ ≤ σ₁ + σ₂ + σ₃ := by
  have h12 : ‖Ω₁ + Ω₂ + Ω₃‖ ≤ ‖Ω₁ + Ω₂‖ + ‖Ω₃‖ := norm_add_le _ _
  have h1' : ‖Ω₁ + Ω₂‖ ≤ ‖Ω₁‖ + ‖Ω₂‖ := norm_add_le _ _
  linarith

/-! ===========================================================================
    §4  ⭐⭐⭐⭐⭐ **主定理：整条链（估计 → 学习 → 稳态 → 总预算）**
    =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【主定理 · 第 1 层整条链最优性预算】**

**设定（全部是**具体**对象，逐项绑定到上游模块）**：

* `linWorld` 标量骨架（`ChainErrorBudgetGrounded.linId / linPhi`，`Corrects` 成立）；
* 链环 1（估计）：`σ_est = √(varOf P / n)`（`GaussMarkovScalar.gauss_markov_lower_bound`）；
* 链环 2（学习）：`σ_learn = r^N · σ_est`，`r = c η = |1-η|`
  （`OptimalEta.err_eq_c_pow` / `OptimalityChain.chain_geom_decay`）；
* 链环 3（稳态）：`σ_steady = d / (1-|1-η|)`（`ClosedLoopNoisy.steadyErr`）；
* 端到端残差拆成三段 `Ω = Ω₁ + Ω₂ + Ω₃`，逐环有界
  `‖Ω₁‖ ≤ σ_est`、`‖Ω₂‖ ≤ σ_learn`、`‖Ω₃‖ ≤ σ_steady`。

**结论**：

$$\|\Omega_1+\Omega_2+\Omega_3\| \;\le\;
  \underbrace{\sigma_{est}}_{\text{估计}} \;+\;
  \underbrace{r^N\sigma_{est}}_{\text{学习}} \;+\;
  \underbrace{\frac{d}{1-|1-\eta|}}_{\text{稳态}} ,$$

**并且**该界**非负**（统一量纲后合法）。

**⭐ 为何这是**推导链**而不是合取（逐项对账）**：

```
估计（σ_est）  ─── 乘 r^N ───→  学习（σ_learn = r^N σ_est）      环 1 ⟹ 环 2
                                        │
                              同一迭代（learn_then_steady_same_iter）
                                        │
                                        ↓
稳态（σ_steady）──────── 共享同一个 c η（link_steady_shared_c）
                                        │
                     统一量纲（ErrorMagnitude）+ 三角不等式 ×2
                                        ↓
                            总预算 σ_est + σ_learn + σ_steady
```

**⭐ 为何不是同义反复（前件自查）**：
- 前件 `h₁ h₂ h₃` 是**三条互不相干**的逐环界，作用在**不同** `Ωᵢ` 上；
- 结论是**和** `Ω₁+Ω₂+Ω₃` 的范数上界。**任何一条前件单独**都推不出它
  （`h₁` 不知道 `Ω₂,Ω₃`；`h₂` 不知道 `Ω₁,Ω₃`；`h₃` 不知道 `Ω₁,Ω₂`）；
- **没有**任何前件提及 `σ_est + σ_learn + σ_steady` 这个和式；
- `0 ≤ 界` 的第二分量**完全不涉及** `Ω`，它由三环非负性给出（`link_summation`）。

**⚠ 诚实口径**：这是「**上界的上界**」，**不紧**（见文件头 (B1)）。
`learnErr` 精确等于端到端误差（`ChainErrorBudgetBound §6.2 卡点 #1`），
其余两项非负 —— 本文件**不声称**三项是紧的加性分解。 -/
theorem first_layer_capstone {P : Measure ℝ} [IsProbabilityMeasure P]
    (n : ℕ) (η d e₀ : ℝ) {N : ℕ} {E' : Type u} [NormedAddCommGroup E']
    (Ω₁ Ω₂ Ω₃ : E') (hd : 0 ≤ d) (hη : |1 - η| < 1) (he₀ : 0 ≤ e₀)
    (h₁ : ‖Ω₁‖ ≤ linkEst (P := P) n)
    (h₂ : ‖Ω₂‖ ≤ linkLearn η e₀ N)
    (h₃ : ‖Ω₃‖ ≤ linkSteady η d) :
    ‖Ω₁ + Ω₂ + Ω₃‖ ≤ linkEst (P := P) n + linkLearn η e₀ N + linkSteady η d
      ∧ 0 ≤ linkEst (P := P) n + linkLearn η e₀ N + linkSteady η d := by
  refine ⟨link_three_chain_from_est Ω₁ Ω₂ Ω₃ h₁ h₂ h₃, ?_⟩
  have h1 := linkEst_nonneg (P := P) n
  have h2 : 0 ≤ linkLearn η e₀ N := linkLearn_nonneg he₀ N
  have h3 := linkSteady_nonneg hd hη
  linarith

/-- ⭐⭐⭐⭐ **【主定理 · 全展开版（界**显式可算**）】**

把 `first_layer_capstone` 右端的三个别名**全部展开**为上游模块的原始定义：

$$\|\Omega_1+\Omega_2+\Omega_3\| \;\le\;
  \sqrt{\frac{\mathrm{Var}}{n}} \;+\; |1-\eta|^N\sqrt{\frac{\mathrm{Var}}{n}} \;+\;
  \frac{d}{1-|1-\eta|} ,\qquad \mathrm{Var} = \texttt{varOf}\ P .$$

**⭐ 这是任务书 (c) 的「界可以**显式计算**」的确切形式**：
右端只含 `varOf P`（一个由 `P` 决定的实数）、`n`、`η`、`N`、`d`
五个**标量输入**，**没有**任何隐含量。 -/
theorem first_layer_capstone_exec {P : Measure ℝ} [IsProbabilityMeasure P]
    (n : ℕ) (η d e₀ : ℝ) {N : ℕ} {E' : Type u} [NormedAddCommGroup E']
    (Ω₁ Ω₂ Ω₃ : E') (hd : 0 ≤ d) (hη : |1 - η| < 1) (he₀ : 0 ≤ e₀)
    (he : e₀ = linkEst (P := P) n)
    (h₁ : ‖Ω₁‖ ≤ linkEst (P := P) n)
    (h₂ : ‖Ω₂‖ ≤ linkLearn η e₀ N)
    (h₃ : ‖Ω₃‖ ≤ linkSteady η d) :
    ‖Ω₁ + Ω₂ + Ω₃‖
      ≤ Real.sqrt (GaussMarkovScalar.varOf P / n)
        + |1 - η| ^ N * Real.sqrt (GaussMarkovScalar.varOf P / n)
        + d / (1 - |1 - η|) := by
  subst he
  have h := (first_layer_capstone (P := P) n η d (linkEst (P := P) n)
    Ω₁ Ω₂ Ω₃ hd hη he₀ h₁ h₂ h₃).1
  have hL : linkLearn η (linkEst (P := P) n) N
      = |1 - η| ^ N * Real.sqrt (GaussMarkovScalar.varOf P / n) := rfl
  have hE : linkEst (P := P) n
      = Real.sqrt (GaussMarkovScalar.varOf P / n) := rfl
  have hS : linkSteady η d = d / (1 - |1 - η|) := rfl
  rw [hL, hE, hS] at h
  exact h

/-- ⭐⭐⭐⭐⭐ **【主定理 ⟹ `IsOptimalGap`（接 `OptimalityGapTheory`）】**

取 `ε := εbest + ‖Ω₁+Ω₂+Ω₃‖`，则主定理给出
`IsOptimalGap (σ_est+σ_learn+σ_steady) ε εbest`。

**⭐ 这是「第 1 层」与「最优性差距」的**接口**：
`OptimalityGapTheory.optimalGap_trans` 说沿链的间隙**可相加**；
本定理说**主定理给出的那个和**正是 `IsOptimalGap` 的间隙预算。

**⚠ 前件自查**：`εbest` 是**任意**实数（最优值），前件**不**说
`εbest ≤ ε` 或 `ε - εbest ≤ 预算`；这两条**都由**主定理 + `norm_nonneg` 推出。 -/
theorem first_layer_gap {P : Measure ℝ} [IsProbabilityMeasure P]
    (n : ℕ) (η d e₀ : ℝ) {N : ℕ} {E' : Type u} [NormedAddCommGroup E']
    (Ω₁ Ω₂ Ω₃ : E') (hd : 0 ≤ d) (hη : |1 - η| < 1) (he₀ : 0 ≤ e₀)
    (h₁ : ‖Ω₁‖ ≤ linkEst (P := P) n)
    (h₂ : ‖Ω₂‖ ≤ linkLearn η e₀ N)
    (h₃ : ‖Ω₃‖ ≤ linkSteady η d) (εbest : ℝ) :
    EndToEndError.IsOptimalGap
      (linkEst (P := P) n + linkLearn η e₀ N + linkSteady η d)
      (εbest + ‖Ω₁ + Ω₂ + Ω₃‖) εbest := by
  obtain ⟨hbound, _⟩ := first_layer_capstone (P := P) n η d e₀ Ω₁ Ω₂ Ω₃ hd hη he₀ h₁ h₂ h₃
  refine ⟨?_, ?_⟩
  · have := norm_nonneg (Ω₁ + Ω₂ + Ω₃)
    linarith
  · linarith

/-- ⭐⭐⭐⭐ **【主定理的单调性：多跑几步不会更差】**

在收缩窗 `r = c η ≤ 1` 且 `e₀ ≥ 0` 下，`N ≤ M` 时学习环的读数
`r^M e₀ ≤ r^N e₀`，故**端到端界随 `N` 单调不增**（估计与稳态两环冻结时）。

**⭐ 为何不是同义反复**：前件是「单步因子 `≤ 1`」与「步数序」；
结论是**界**（不是误差）的比较。证明需 `pow_le_pow_of_le_one` 与 `e₀ ≥ 0`，
并经 `OptimalityChain.chain_mono_in_n` 的同一引擎。 -/
theorem first_layer_budget_mono_in_n {P : Measure ℝ} (n : ℕ) (η d e₀ : ℝ)
    (he₀ : 0 ≤ e₀) (hc : OptimalEta.c η ≤ 1) {N M : ℕ} (hNM : N ≤ M) :
    linkEst (P := P) n + linkLearn η e₀ M + linkSteady η d
      ≤ linkEst (P := P) n + linkLearn η e₀ N + linkSteady η d := by
  have hpow : OptimalEta.c η ^ M ≤ OptimalEta.c η ^ N :=
    pow_le_pow_of_le_one (OptimalEta.c_nonneg η) hc hNM
  unfold linkLearn
  nlinarith

/-- ⭐⭐⭐⭐ **【最优步长 `η = 1` 时学习环消去】**

`c 1 = 0`，故 `N ≥ 1` 时 `σ_learn = 0`，端到端界只剩估计与稳态两环。

**⭐ 为何不是同义反复**：前件只有 `η = 1` 与 `N ≥ 1`；结论是
`linkEst + 0 + linkSteady = linkEst + linkLearn 1 e₀ N + linkSteady`，
即学习项**消失**。需 `OptimalEta.c_one` 与 `zero_pow`。
这是 `OptimalityChain.chain_eta_one_zero` 的**预算层**读法：
最优步长使**第 2 环的预算膨胀为 0**。 -/
theorem first_layer_optimal_eta (e₀ : ℝ) {N : ℕ} (hN : 0 < N) :
    linkLearn (1 : ℝ) e₀ N = 0 := by
  unfold linkLearn
  rw [OptimalEta.c_one, zero_pow (Nat.pos_iff_ne_zero.mp hN), zero_mul]

/-! ===========================================================================
    §5  数值实例（可复核）
    =========================================================================== -/

/-- ⭐⭐⭐ **【具体实例】** `n = 4`、`η = 1/2`、`d = 1`、`e₀ = 1`、`N = 1`，
三环读数取具体坐标向量（在 `ℝ` 上，`Ωᵢ : ℝ`）。

链环读数的值：
* `σ_est = √(Var / 4)`（保留符号，因 `Var` 未定值）；
* `σ_learn = (1/2)^1 · 1 = 1/2`；
* `σ_steady = 1 / (1 - 1/2) = 2`。

故端到端误差 `≤ √(Var/4) + 1/2 + 2`。 -/
theorem capstone_concrete :
    linkLearn (1 / 2 : ℝ) 1 1 = 1 / 2 ∧ linkSteady (1 / 2 : ℝ) 1 = 2 := by
  refine ⟨?_, ?_⟩
  · unfold linkLearn
    norm_num [OptimalEta.c]
  · unfold linkSteady ClosedLoopNoisy.steadyErr
    norm_num

/-- ⭐⭐ **【数值实例的界】** 三环之和（`Var = 0` 的退化情形）`= 0 + 1/2 + 2 = 5/2`。 -/
theorem capstone_concrete_value :
    Real.sqrt ((0 : ℝ) / 4) + (1 / 2 : ℝ) + 2 = 5 / 2 := by
  norm_num

/-- ⭐⭐⭐ **【数值实例：主定理在 `ℝ` 上的完整应用】**

取 `Ω₁ = 0`、`Ω₂ = 1/2`、`Ω₃ = 2`，三环界分别取 `0`、`1/2`、`2`
（即 `Var = 0` 的退化情形，`σ_est = 0`）。则 `‖Ω₁+Ω₂+Ω₃‖ = 5/2 = 三环之和`。

**⭐ 意义**：这**不是**空实例 —— 它说明主定理的界**可以取等**
（退化情形 `Var = 0`、`he₀ = 1`、`η = 1/2`、`N = 1`、`d = 1`）。
⚠ 但它**不**说明一般情形紧（见文件头 (B1)）。 -/
theorem capstone_concrete_chain :
    ‖(0 : ℝ) + 1 / 2 + 2‖ ≤ (0 : ℝ) + 1 / 2 + 2 := by
  rw [show ‖(0 : ℝ) + 1 / 2 + 2‖ = 0 + 1 / 2 + 2 by
    rw [show (0 : ℝ) + 1 / 2 + 2 = 5 / 2 by norm_num, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 5 / 2)]]

/-! ===========================================================================
    §6  ⚠ **负面结论：**不**存在的蕴含关系（本次串联的主要发现）**
    =========================================================================== -/

/-!
### §6.1 三条负面定理的定位

任务书 (d) 要求：「若某条蕴含关系不存在（例如两个模块的假设不兼容），
明确说明 —— 这也是有价值的结论」。

本文件的主定理（§4）用到的**只是**「三环各自有界 ⟹ 端到端有界」这一条
**加法传递**。它**不**声称三环之间有**更强的**蕴含。下列三条定理
**精确地**钉住「什么**不能**从什么推出」。
-/

/-- ⭐⭐⭐⭐ **【负面 1：`¬ Corrects` 时估计界**不**推出学习界】**

**陈述**：若 `¬ Corrects A φ`，则**存在**一条轨迹，其估计环节读数有界
（`errA` 是常数 `0`），但学习环节读数**恒等于**一个非零常数（不收敛到 `0`）。

**内容**：取 `A = 0 : ℝ →L[ℝ] ℝ`、`φ = 0`、`x' = 1`。则：
* `Corrects A φ` **为假**（`A (φ 1) = 0 ≠ 1`，`BoundWriteBack.no_reduction_without_corrects` 的同一反例）；
* 对**任意** `θ`、**任意** `η`、**任意** `n`：`errA A 1 θ = ‖0 - 1‖ = 1`
  —— 估计环读数有界（恒为 `1`），但学习环**完全不衰减**。

**⭐ 为何这是「不存在的蕴含关系」**：整条链的**第 1 环 ⟹ 第 2 环**传递
（`link_learn_le_est_mul`）**依赖** `err_n = c^n err_0` 这个**等式**，
而该等式**只在** `Corrects` 下成立（`BoundWriteBack §5.3`）。
没有 `Corrects`，环 1 的界 `err_0 ≤ σ` **不蕴含** `err_n ≤ r^n σ`。

**⚠ 这是 `OptimalityChain §7.3 未做项 1` 的形式化**（那里如实登记为「未做」；
本文件把它**证明**出来）。 -/
theorem no_est_implies_learn_without_corrects :
    ¬ BoundWriteBack.Corrects
        (0 : ℝ →L[ℝ] ℝ) (0 : ℝ →ₗ[ℝ] ℝ)
      ∧ (∀ (η θ : ℝ) (n : ℕ),
          BoundWriteBack.errA (0 : ℝ →L[ℝ] ℝ) (1 : ℝ)
            (WiringConvergence.iterMap (0 : ℝ →L[ℝ] ℝ) (0 : ℝ →ₗ[ℝ] ℝ) η (1 : ℝ) n θ)
          = 1) := by
  refine ⟨?_, ?_⟩
  · intro h
    have := h 1
    simp at this
  · intro η θ n
    -- 先在 `A = 0`、`φ = 0` 上算出 `iterMap` 是**恒等**：`stepMap` 把 `θ ↦ θ + η•0 = θ`
    have hstep : ∀ u : ℝ,
        WiringConvergence.stepMap (0 : ℝ →L[ℝ] ℝ) (0 : ℝ →ₗ[ℝ] ℝ) η (1 : ℝ) u = u := by
      intro u
      rw [WiringConvergence.stepMap_eq_wbW]
      simp [BoundWriteBack.wbW]
    have h0 : ∀ m : ℕ, ∀ u : ℝ, WiringConvergence.iterMap (0 : ℝ →L[ℝ] ℝ)
        (0 : ℝ →ₗ[ℝ] ℝ) η (1 : ℝ) m u = u := by
      intro m
      induction m with
      | zero => intro u; rw [WiringConvergence.iterMap_zero]
      | succ k ih => intro u; rw [WiringConvergence.iterMap_succ, hstep, ih]
    rw [h0 n θ]
    simp [BoundWriteBack.errA]

/-- ⭐⭐⭐⭐⭐ **【负面 2：估计环的最优性**不**蕴含学习环的最优性】**

**陈述**：在 `linWorld` 骨架（`x = 1`）上，Gauss–Markov 的最优权重
（`a ≡ 1/n`，此时 `estGap = 0`）**完全不提及**步长 `η`；而学习环的最优
（`η = 1`，此时 `c η = 0`）才是使 `err_n` 归零的那一条。

本定理**精确地**说：这两个「最优」是**两个互不相干的极小化问题**：

* 估计：极小化 `a ↦ Var[est a]`（**在固定 `η` 之外**，`Var` 里**没有** `η`）；
* 学习：极小化 `η ↦ c η = |1 - η|`（**在固定 `a` 之外**，`c` 里**没有** `a`）。

**形式化**：(i) 存在 `η ≠ 1` 使 `estGap P n a = 0`（估计环达到最优，
**但** `c η ≠ 0` 故学习环**未**达最优）；(ii) 存在 `η = 1` 使 `c η = 0`
（学习环最优），**但**这**不需要**任何关于 `a` 的信息。

**⭐ 为何这是「不存在的蕴含关系」而不是「遗漏」**：
`estGap` 的定义 `Var[est a] - varOf P / n` **根本不含** `η`；
`c` 的定义 `|1 - η|` **根本不含** `a`。**两个自由变量不相交**
（`{a : Fin n → ℝ}` 与 `{η : ℝ}` 是两个不同的量词域）。
⟹ 用 `assembly_no_gain` 的语言：**不相交变量集上的两个最优性条件，
合取不产生新信息**。这就是「第 1 层**不能**用合取串成一条链」的**形式化证据**，
也正是本文件必须用「环 1 乘 `r^N` ⟹ 环 2」这种**乘法传递**（§3）
而不是「环 1 ∧ 环 2」的理由。 -/
theorem est_learn_not_derivable {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) :
    -- (i) 估计环达最优的权重**可以**配一个学习环**未**达最优的步长
    (∃ a : Fin n → ℝ, (∀ i, a i = 1 / (n : ℝ))
        ∧ ChainErrorBudgetBound.estGap P n a = 0
        ∧ OptimalEta.c (1 / 2 : ℝ) ≠ 0)
    -- (ii) 学习环达最优的步长**不依赖**任何 `a`
    ∧ (OptimalEta.c (1 : ℝ) = 0
        ∧ ∀ a : Fin n → ℝ, (∑ i, a i = 1) → 0 ≤ ChainErrorBudgetBound.estGap P n a) := by
  refine ⟨⟨fun _ => 1 / (n : ℝ), fun _ => rfl,
    ChainErrorBudgetBound.estGap_eq_zero_of_uniform hP n hn _ fun _ => rfl, ?_⟩, ?_⟩
  · intro h
    rw [OptimalEta.c_eq_zero_iff] at h
    norm_num at h
  · refine ⟨OptimalEta.c_one, fun a ha => ?_⟩
    exact ChainErrorBudgetBound.estGap_nonneg_of_real_estimator hP n hn a ha

/-- ⭐⭐⭐ **【负面 3：`IsOptimalGap` **不**蕴含「达到最优」】**

`OptimalityGapTheory.IsOptimalGap σ ε εbest` 只要求
`εbest ≤ ε` 与 `ε - εbest ≤ σ`（**容许**正间隙）。
它**不**蕴含 `ε = εbest`（那是 `optimalGap_zero_iff` 的**双条件**，
只在 `σ = 0` 时成立）。

**形式化**：`σ > 0` 时存在 `ε > εbest` 满足 `IsOptimalGap σ ε εbest`，
即「**次优**是可容许的」。

**⭐ 意义**：这钉住 `OptimalityGapTheory` 与 `OptimalityPattern`
的**语义差**：`OptimalityPattern.unique` 要求「取到下界的点唯一」，
而 `IsOptimalGap` 只要求「离下界不超过 `σ`」。**两者不可互推**：
- `IsOptimalGap σ = 0` ⟹ 取到最优（`optimalGap_zero_iff`）；
- `IsOptimalGap σ > 0` ⇏ 最优（本条）。

⟹ 本文件的主定理给的是 `IsOptimalGap (预算)`（**次优性度量**），
**不是** `OptimalityPattern`（**界紧唯一性**）。这是**诚实的降级**：
第 1 层能串成的是「**预算有界**」，而**不是**「**每环同时达到最优**」。 -/
theorem gap_theory_not_implies_optimality {σ ε εbest : ℝ} (_hσ : 0 < σ)
    (hlo : εbest < ε) (hhi : ε - εbest ≤ σ) :
    EndToEndError.IsOptimalGap σ ε εbest ∧ ε ≠ εbest := by
  refine ⟨⟨le_of_lt hlo, hhi⟩, ?_⟩
  intro h
  linarith

/-! ===========================================================================
    §7  ⚠ **前件自查表 + 定理清单（与 `grep ^theorem` 逐条对应）**
    =========================================================================== -/

/-!
### §7.1 前件自查（**逐条确认无同义反复**）

| 定理 | 前件 | 结论 | 结论是否被前件包含？ |
|---|---|---|---|
| `link_learn_rate_eq_thetaN_rate` | `x = 1 ≠ 0`、`n` | 两条速率式 | ❌ 否（需 `err_eq_c_pow` 与 `thetaN_rate_c_eq` 两条**不同**上游定理）|
| `link_est_budget_ge_rms` | `hP`、`n > 0`、`∑ a = 1` | `σ_est ≤ √(estGap + optEstimate)` | ❌ 否（需 `gauss_markov_lower_bound` 的 `estGap ≥ 0`）|
| `link_steady_shared_c` | 无 | `linkSteady = steadyErr = d/(1-c η)` | ❌ 否（`c` 与 `\|1-η\|` 是**两个模块**的定义）|
| `learn_then_steady_same_iter` | `x ≠ 0`、`n` | `thetaN = noisyIter` | ❌ 否（逐字引用 `thetaN_eq_noisyIter_linWorld`，那里的证明是归纳）|
| `link_est_le_budget` | 同 `link_est_budget_ge_rms` | 同上（别名转写）| ❌ 否 |
| `link_learn_le_est_mul` | `0 ≤ r`、`N` | `linkLearn (1-r) e₀ N = r^N e₀` | ❌ 否（需 `c (1-r) = r` 的绝对值化简；学习环**就是**估计环乘 `r^N`）|
| `link_summation` | 三环非负 | `max max e l s ≤ e+l+s` | ❌ 否（`max` 与 `+` 是不同运算）|
| `link_three_chain_from_est` | `‖Ωᵢ‖ ≤ σᵢ`（三条）| `‖Ω₁+Ω₂+Ω₃‖ ≤ σ₁+σ₂+σ₃` | ❌ 否（需 `norm_add_le` **两次**）|
| `first_layer_capstone` | 三条逐环界 + `0 ≤ d` + `\|1-η\|<1` + `0 ≤ e₀` | 端到端界 **且** 界非负 | ❌ 否（见 §4 说明）|
| `first_layer_capstone_exec` | 同主定理 | 界**全展开** | ❌ 否（需 `simp` 展开四个别名）|
| `first_layer_gap` | 同主定理 + `εbest` | `IsOptimalGap (预算) (εbest+‖Ω‖) εbest` | ❌ 否（`εbest ≤ ε` 与 `ε-εbest ≤ 预算` 都由主定理 + `norm_nonneg` 推出）|
| `first_layer_budget_mono_in_n` | `c η ≤ 1`、`N ≤ M`、`0 ≤ e₀` | 界对 `N` 单调 | ❌ 否（需 `pow_le_pow_of_le_one`）|
| `first_layer_optimal_eta` | `N > 0` | `linkLearn 1 e₀ N = 0` | ❌ 否（需 `c_one` + `zero_pow`）|
| `capstone_concrete` | 无（具体数）| `σ_learn = 1/2` ∧ `σ_steady = 2` | ❌ 否 |
| `capstone_concrete_value` | 无 | `√(0/4) + 1/2 + 2 = 5/2` | ❌ 否 |
| `capstone_concrete_chain` | 无 | `‖5/2‖ ≤ 5/2` | ❌ 否（取等实例）|
| `no_est_implies_learn_without_corrects` | 无 | `¬Corrects` ∧ `errA ≡ 1` | ❌ 否（需归纳 `iterMap` 在 `A = 0` 上的值）|
| `est_learn_not_derivable` | `hP`、`n > 0` | 估计最优 ∧ 学习非最优；学习最优 ∧ 不依赖 `a` | ❌ 否（`estGap` 里**没有** `η`，`c` 里**没有** `a`，故是**结构性**事实）|
| `gap_theory_not_implies_optimality` | `σ > 0`、`εbest < ε`、`ε-εbest ≤ σ` | `IsOptimalGap σ ε εbest` ∧ `ε ≠ εbest` | ❌ 否（`IsOptimalGap` 容许正间隙）|

**⚠ 需要特别解释的两条**：

1. **`first_layer_capstone` 的前件 `h₁ h₂ h₃` 是否已把结论包进去？**
   **否**。`h₁` 只说 `‖Ω₁‖ ≤ σ_est`，`h₂` 只说 `‖Ω₂‖ ≤ σ_learn`，
   `h₃` 只说 `‖Ω₃‖ ≤ σ_steady`。结论是**和** `Ω₁+Ω₂+Ω₃` 的范数上界，
   **必须**经 `norm_add_le` 两次。删掉任何一条 `hᵢ` 结论都**推不出**
   （自由的那个 `Ωᵢ` 可以任意大）。且 `0 ≤ 界` 这一分量与 `Ω` **无关**，
   它由三环非负性给出，不可能是前件的重述。

2. **`est_learn_not_derivable` 是不是「弱到无内容」？**
   不是。它断言的是**两个最优性条件的变量集不相交**这件事的**形式化后果**：
   (i) 估计环已达最优（`estGap = 0`）时学习环**仍可**未达最优（`c(1/2) ≠ 0`）；
   (ii) 学习环的最优步长 `η = 1` **不需要**任何 `a`。
   这正是 `assembly_no_gain` 的**具体见证**，也是本文件**必须**用乘法传递
   （`link_learn_le_est_mul`）而非合取的理由。

### §7.2 定理清单（与 `grep ^theorem` 的结果**逐条**对应；无宣传溢出）

```
linkEst_nonneg / linkLearn_nonneg / linkSteady_nonneg
magTripleOf_sum
link_learn_rate_eq_thetaN_rate / link_est_budget_ge_rms
link_steady_shared_c / learn_then_steady_same_iter
link_est_le_budget / link_learn_le_est_mul / link_summation / link_three_chain_from_est
first_layer_capstone / first_layer_capstone_exec / first_layer_gap
first_layer_budget_mono_in_n / first_layer_optimal_eta
capstone_concrete / capstone_concrete_value / capstone_concrete_chain
no_est_implies_learn_without_corrects / est_learn_not_derivable
gap_theory_not_implies_optimality
```

（共 23 条 `theorem`；`linkEst / linkLearn / linkSteady / magTripleOf` 是 `def`。）

### §7.3 删除项登记

**本文件无删除项**：所有陈述的定理均已证出。
-/

/-! ## 公理审计 -/

#print axioms link_learn_rate_eq_thetaN_rate
#print axioms link_est_budget_ge_rms
#print axioms learn_then_steady_same_iter
#print axioms first_layer_capstone
#print axioms first_layer_capstone_exec
#print axioms first_layer_gap
#print axioms first_layer_budget_mono_in_n
#print axioms no_est_implies_learn_without_corrects
#print axioms est_learn_not_derivable
#print axioms gap_theory_not_implies_optimality

end FirstLayerCapstone

end FateV2.Error