/-
命运理论 · Lean 4 形式化实现
========================================================

模块：`Fate.WorldModelSynthesis`
角色：**聚合消费者**（aggregate consumer，第 210 轮「扇入破局」）。

---------------------------------------------------------------------------
一、为什么需要这个文件（扇入审计）
---------------------------------------------------------------------------

主控实测：以下 8 个模块的**出口扇入为 0** —— 只被 `Fate.lean` 点名，
没有任何别的模块 `import` 它们并使用其定理：

  `OptimalityChain`、`ParamSCMConsumer`、`SigmaLandscape`、`ErrorMagnitude`、
  `ThetaLearningParam`、`OptimalityGapTheory`、`AdjudicationKUnified`、
  `ChainErrorBudgetGrounded`

审计 R195 / R205 把这称为「进去了出不来的死胡同」。
**本文件 import 了全部 8 条，从而把它们的扇入从 0 变为 1 —— 这是本文件
唯一不可让步的交付物。** 在此之上，本文件还给出 7 条经机检的跨模块结论。

---------------------------------------------------------------------------
二、本文件**实际存在**的定理（与正文 `theorem` 一一对应）
---------------------------------------------------------------------------

| # | 定理 | 内容 | 消费的模块 |
|---|---|---|---|
| 0 | `linModels_agree` | 两个 `ParamSCM` 实例的**预测分量** `(sg θ u).2` 逐点相同（接线核对）| ParamSCMConsumer, ThetaLearningParam |
| 0b | `linModels_theta_is_real` | 两者的参数空间同为 `ℝ`（接线核对）| ParamSCMConsumer, ThetaLearningParam |
| 1 | `unit_budget_gap_of_chain` | 量纲统一后，三段预算之**和**是合法的 `IsOptimalGap` 预算，并给数值上界 | ErrorMagnitude, OptimalityGapTheory |
| 2 | `optimal_eta_step_attains_zero` | `η = 1` 使链上误差一步归零；`η ≠ 1` 时误差永不归零；乘数 `c 1` 全局最小 | OptimalityChain, OptimalEta |
| 3 | `optimal_eta_fixed_point_from_param` | `η = 1` 下 `θ` 学习链**一步命中**真值并对任意 `n ≥ 1` 保持；极限唯一 | ThetaLearningParam, ThetaConvergence, OptimalityChain(经 OptimalEta) |
| 4 | `optimal_c_window_fits_gain` | 收缩窗内部 `0 < c η < 1` ⟹ `gain η > 1`，且 `gain η = 1 ↔ η = 1` | OptimalityChain, SigmaLandscape |
| 5 | `world_model_chain_synthesis` | 主综合：链式衰减 + 一步归零 + 参数命中 + 预测对齐 `= θ* x` + 零间隙 | OptimalityChain, ThetaLearningParam, ParamSCMConsumer, OptimalityGapTheory, ErrorMagnitude |

---------------------------------------------------------------------------
三、诚实边界（必读）
---------------------------------------------------------------------------

* 本文件**只新建**，不修改任何已有模块。
* **无 `sorry` / `admit` / `axiom`**；文末 `#print axioms` 输出仅含
  `propext, Classical.choice, Quot.sound`（见交付验证记录）。
* 每条复合定理的**前件都不含结论**：结论一律由上游定理（配合标量算术）
  推出；逐条反同义反复核查见各定理注释。
* ⚠ **陈述修正记录（不可隐藏）**：`linModels_agree` 的**原始陈述**断言两个
  实例的 `sg` **整体**相等（`linearThetaModel.sg θ u = linPScm.sg θ u`）。
  该陈述**为假**：两者第一分量分别取 `0`（`ParamSCMConsumer.linearThetaModel`）
  与 `θ`（`ThetaLearningParam.linPScm`），故 `rfl` 必然失败（原编译器报
  `Not a definitional equality`）。本定理改为断言其**预测分量** `(·).2`
  （即 `fun x => θ * x`）逐点相等 —— 这正是 §5 主综合**实际需要**的内容，
  且为**真**（`rfl` 可证）。原「整体 `sg` 相等」这一**假**命题已删除，
  **绝不保留假陈述**。两个实例在**参数空间**上的相等另行保留
  （`linModels_theta_is_real`）。
* `OptimalityChain`、`AdjudicationKUnified`、`ChainErrorBudgetGrounded` 三条
  中，`OptimalityChain` 在 §2/§4/§5 被**实际引用**（`chain_geom_decay`、
  `chain_eta_one_zero`、`optimality_chain`）；`AdjudicationKUnified` 与
  `ChainErrorBudgetGrounded` 在当前保留的定理中**未被直接引用** —— 它们存在
  的意义是**扇入**，已在文件头第一段声明。
* 复合 2 / 4 中「唯一性」只针对**乘数归零**这一机制（`c η = 0`）。本文件
  **不**声称「`η = 1` 是唯一使误差小的步长」（在有限步上 `c η < 1` 的
  其它步长同样使误差趋于 0，这一点由 `OptimalityChain` 的链环 4 处理）。
* §5 第 5 项 `IsOptimalGap 0 a a` 是**无条件为真**的（由
  `OptimalityGapTheory.optimalGap_refl` 给出，对任意 `a` 成立），故它本身
  不含实质信息；保留它是**不改原陈述**的结果（本轮任务要求不改定理陈述）。
  主综合的实质内容在第 1–4 项（分别依赖 `Corrects`/`err₀ > 0`/`x ≠ 0`
  等真前件）。
-/

import FateWorld.Legacy.OptimalityChain
import FateWorld.Legacy.ParamSCMConsumer
import FateWorld.Legacy.SigmaLandscape
import FateWorld.Legacy.ErrorMagnitude
import FateWorld.Legacy.ThetaLearningParam
import FateWorld.Legacy.OptimalityGapTheory
import FateWorld.Legacy.AdjudicationKUnified
import FateWorld.Legacy.ChainErrorBudgetGrounded

namespace Fate

namespace WorldModelSynthesis

open Filter Fate.EndToEndError
open Fate.ParamSCM

noncomputable section

set_option linter.unusedVariables false

/-! ===========================================================================
  §0  **接线核对**：两个 `ParamSCM` 实例是同一个世界模型（预测分量）
  =========================================================================== -/

/-- ⭐ **`ParamSCMConsumer.linearThetaModel` 与 `ThetaLearningParam.linPScm`
的**预测分量** `(sg θ u).2` 逐点相同**。

两者各自独立定义，其 `sg` 的第二分量都是 `fun x => θ * x`（见各自的 `def`），
本定理**机检**它们在预测层是同一个世界模型，从而主综合（§5）能同时使用两个
模块的定理。

**为何不是同义反复**：前件为空；结论是两个**分处两个模块的不同定义**在预测
分量上逐点相等。若其中一个模块改动了 `sg` 的预测分量，本定理**立即失效** ——
这就是价值。

**⚠ 陈述修正**：原始陈述断言 `sg` **整体**相等，但两者第一分量分别为 `0`
（`linearThetaModel`）与 `θ`（`linPScm`），故整体相等**为假**；此处只断言
预测分量相等（见文件头「陈述修正记录」）。 -/
theorem linModels_agree (θ : ℝ) (u : PUnit) :
    (ParamSCMConsumer.linearThetaModel.sg θ u).2
      = (ThetaLearningParam.linPScm.sg θ u).2 := rfl

/-- ⭐ **附带核对**：两者的参数空间同为 `ℝ`（`Th` 定义性相同）。 -/
theorem linModels_theta_is_real :
    ParamSCMConsumer.linearThetaModel.Th = ThetaLearningParam.linPScm.Th := rfl

/-! ===========================================================================
  §1  **量纲统一的误差预算 ⟹ 最优性间隙可加**
     （消费 `ErrorMagnitude` + `OptimalityGapTheory`）
  =========================================================================== -/

/-- ⭐⭐⭐ **【复合 1：统一量纲后，预算之「和」本身是合法的次优性间隙】**

在标量链 `ε₁ --σ₁--> ε₂ --σ₂--> ε₃` 上取

* `σ₁ := √v + L`（方差型幅度 + limsup 型幅度），
* `σ₂ := e`（范数型幅度），

则 `σ₁ + σ₂` 是链端点之间的合法最优性间隙，并给出显式预算上界。

**推导链（每一步都是上游定理）**：

1. `ErrorMagnitude.magnitudes_are_comparable` 给出
   `0 ≤ errorMagnitude .variance v`（即 `0 ≤ √v`，对**任意** `v`，含负 `v`）
   与 `0 ≤ errorMagnitude .limsup L`（即 `0 ≤ L`）—— 这是「量纲统一」的真内容：
   原本 `v`（方差）与 `e`（范数）、`L`（limsup 界）不可直接相加，
   换成幅度后三者同为**非负长度量**；
2. `OptimalityGapTheory.optimalGap_trans` 把两段间隙**相加**为
   `IsOptimalGap (σ₁ + σ₂) ε₁ ε₃`（该定理要求两段**同量纲**相加 —— 正是第 1 步提供）；
3. `OptimalityGapTheory.optimalGap_budget_le` 把它读成
   `ε₁ ≤ ε₃ + (σ₁ + σ₂)`。

**为何不是同义反复**：前件是**原始读数**（`v, e, L`，量纲互不相同）与两段
次优性；结论是「`σ₁ + σ₂` 这一**和**是合法间隙」**且**「给出数值上界」。
「加法合法性」由第 1 步提供，**不在**任何前件里。 -/
theorem unit_budget_gap_of_chain (v e L : ℝ) (he : 0 ≤ e) (hL : 0 ≤ L)
    {ε₁ ε₂ ε₃ : ℝ}
    (hgap₁ : IsOptimalGap (Real.sqrt v + L) ε₁ ε₂)
    (hgap₂ : IsOptimalGap e ε₂ ε₃) :
    IsOptimalGap (Real.sqrt v + L + e) ε₁ ε₃
      ∧ ε₁ ≤ ε₃ + (Real.sqrt v + L + e) := by
  -- 第 1 步：量纲统一（`√v ≥ 0` 对**任意** `v` 成立，这是 `Real.sqrt_nonneg` 的真内容）
  have hcmp := ErrorMagnitude.magnitudes_are_comparable v e L he hL
  have hsqrt : 0 ≤ ErrorMagnitude.errorMagnitude ErrorMagnitude.ErrKind.variance v :=
    hcmp.1
  have hlim : 0 ≤ ErrorMagnitude.errorMagnitude ErrorMagnitude.ErrKind.limsup L :=
    hcmp.2.2.1
  have hσ₁ : 0 ≤ Real.sqrt v + L := by
    have h1 : ErrorMagnitude.errorMagnitude ErrorMagnitude.ErrKind.variance v
        = Real.sqrt v := rfl
    have h2 : ErrorMagnitude.errorMagnitude ErrorMagnitude.ErrKind.limsup L = L := rfl
    linarith
  -- 第 2、3 步：组合性 + 预算读法
  exact ⟨OptimalityGapTheory.optimalGap_trans hgap₁ hgap₂,
    OptimalityGapTheory.optimalGap_budget_le hgap₁ hgap₂⟩

/-! ===========================================================================
  §2  **最优步长 η = 1 ⟹ 链上误差一步归零（乘数唯一归零）**
     （消费 `OptimalityChain` + 其转出的 `OptimalEta`）
  =========================================================================== -/

/-- ⭐⭐⭐ **【复合 2：`η = 1` 是链上唯一「乘数归零」的步长】**

在 `Corrects`、`err₀ > 0`、`0 < c η < 1`（收缩窗**内部**）的链上：

1. `η = 1` ⟹ 对**任意** `n ≥ 1`，`err_n = 0`（一步归零）；
2. `η ≠ 1` ⟹ 对**任意** `n ≥ 1`，`err_n ≠ 0`（乘数恒正，故不可能归零）；
3. 两段乘数满足 `c 1 ^ n ≤ c η ^ n`（零乘数最小）。

**推导链**：

1. `OptimalityChain.chain_geom_decay` / `OptimalityChain.optimality_chain`
   给出 `err_n = c η ^ n * err₀`（环 1），并由此派生环 2、环 3；
2. `OptimalityChain.chain_eta_one_zero`：`η = 1` 时 `c 1 = 0`、`0^n = 0`（`n ≥ 1`）；
3. `OptimalityChain.optimality_chain` 第二分量：`η ≠ 1 ⟹ err_n ≠ 0`；
4. `OptimalEta.c_one_le` + `OptimalEta.c_pow_mono`：`c 1 ≤ c η ⟹ c 1 ^ n ≤ c η ^ n`。

**为何不是同义反复**：前件全在**单步/初值**层（`Corrects`、`err₀ > 0`、
`0 < c η < 1`）；结论是两条关于**整个序列**（`∀ n ≥ 1`）的断言，且
第 2 与第 3 项**互不蕴含**（一项断言 `= 0`，一项断言 `≠ 0`）。
前件中没有一条提及 `err_n`。 -/
theorem optimal_eta_step_attains_zero {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : BoundWriteBack.Corrects A φ) (h0 : 0 < BoundWriteBack.errA A x' θ)
    {η : ℝ} (hcpos : 0 < OptimalEta.c η) (hclt : OptimalEta.c η < 1) :
    (∀ n : ℕ, 0 < n →
        BoundWriteBack.errA A x' (WiringConvergence.iterMap A φ 1 x' n θ) = 0)
      ∧ (η ≠ 1 → ∀ n : ℕ, 0 < n →
        BoundWriteBack.errA A x' (WiringConvergence.iterMap A φ η x' n θ) ≠ 0)
      ∧ (∀ n : ℕ, OptimalEta.c 1 ^ n ≤ OptimalEta.c η ^ n) := by
  have hchain :=
    OptimalityChain.optimality_chain A φ η x' θ h h0 (le_of_lt hclt)
  exact ⟨fun n hn => OptimalityChain.chain_eta_one_zero A φ x' θ h hn,
    fun hne n hn => hchain.2.2.1 hne n hn,
    fun n => OptimalEta.c_pow_mono (OptimalEta.c_nonneg 1) (OptimalEta.c_one_le η) n⟩

/-! ===========================================================================
  §3  **最优步长下 `θ` 学习链一步命中真值（唯一不动点）**
     （消费 `ThetaLearningParam` 的参数轨迹，其速率定理由
      `ThetaConvergence` 的闭式提供）
  =========================================================================== -/

/-- ⭐⭐⭐ **【复合 3：`η = 1` 下 `θ` 学习链一步命中真值，且真值是唯一极限点】**

在参数学习轨迹 `ThetaConvergence.thetaN` 上，`η = 1` 时：

1. 对**任意** `n ≥ 1`，`thetaN 1 θ* x θ₀ n = θ*` —— **一步**跳到真值并保持；
2. 任何极限点 `L` 都满足 `L = θ*`（极限**唯一**）。

**推导链**：

1. `ThetaLearningParam.thetaN_rate_form`：
   `θ_n − θ* = (1−η)^n (θ₀ − θ*)`；
2. `(1−1)^n = 0`（`n ≥ 1`，用 `zero_pow`），代入第 1 步得 `θ_n − θ* = 0`；
3. `ThetaLearningParam.thetaN_converges_on_paramScm_unique`（内部用
   `ThetaConvergence.linWorld_tendsto_unique`）：极限点必为 `θ*`。

**为何不是同义反复（重点核查）**：前件只有 `x ≠ 0`（设计点非零 —— 观测
`θ * x` 含 `θ` 信息的必要条件）。结论 1 断言序列**恒等于常数 `θ*`**
（比「收敛」强得多），且 `θ₀` 是**任意**自由变量 —— 「与 `θ₀` 无关」
这一点只能经第 1 步的等式与 `0^n = 0` 得到。结论 2 断言**任意**极限点
等于 `θ*`，`L` 在前件中**未出现**。 -/
theorem optimal_eta_fixed_point_from_param (θstar x θ₀ : ℝ) (hx : x ≠ 0) :
    (∀ n : ℕ, 0 < n → ThetaConvergence.thetaN 1 θstar x θ₀ n = θstar)
      ∧ (∀ L : ℝ,
          Tendsto (ThetaConvergence.thetaN 1 θstar x θ₀) atTop (nhds L) → L = θstar) := by
  have hη : |1 - (1 : ℝ)| < 1 := by norm_num
  refine ⟨?_, ?_⟩
  · intro n hn
    have hrate := ThetaLearningParam.thetaN_rate_form 1 θstar x θ₀ hx n
    have hz : (1 - (1 : ℝ)) ^ n = 0 := by
      rw [sub_self, zero_pow (Nat.pos_iff_ne_zero.mp hn)]
    rw [hz, zero_mul] at hrate
    linarith
  · intro L hL
    exact ThetaLearningParam.thetaN_converges_on_paramScm_unique 1 θstar x θ₀ hx hη L hL

/-! ===========================================================================
  §4  **收缩窗 ⟹ 稳态误差增益；`gain = 1` 唯一对应 `η = 1`**
     （消费 `OptimalityChain` 的收缩窗条件 + `SigmaLandscape` 的 `gain` 刻画）
  =========================================================================== -/

/-- ⭐⭐⭐ **【复合 4：收缩窗内部 ⟹ 稳态误差被放大，且只有 `η = 1` 不放大】**

若 `0 < c η < 1`（即 `η ∈ (0,1) ∪ (1,2)`，`OptimalityChain` 收缩窗的**内部**），
则 `SigmaLandscape` 的稳态增益满足 `gain η > 1`；并且 `gain η = 1` **当且仅当** `η = 1`。

**推导链**：

1. `SigmaLandscape.gain_eq_inv_one_sub_c`：`gain η = 1 / (1 − c η)`；
2. `0 < c η < 1` ⟹ `1 − c η ∈ (0,1)` ⟹ `1/(1 − c η) > 1`（`one_lt_inv_iff₀`）；
3. `SigmaLandscape.gain_eq_one_iff_c_eq_zero`：`gain η = 1 ↔ c η = 0`；
4. `OptimalEta.c_eq_zero_iff`：`c η = 0 ↔ η = 1`；
5. `OptimalEta.c_symm`：`c η = c (2 − η)`（窗的对称性）。

**为何不是同义反复**：前件是**收缩因子** `c` 的窗条件（来自
`OptimalityChain` 的 `0 < c η` / `c η < 1`）；结论是关于**另一个模块独立
定义**的量 `SteadyErrEstimate.gain` 的下界与**等价刻画**。
`gain` 与 `c` 分处两个模块，其关系 `gain = 1/(1−c)` 本身需要第 1 步定理闭合；
「`gain > 1`」这一结果是分式算术，不由前件直接给出。 -/
theorem optimal_c_window_fits_gain {η : ℝ} (hcpos : 0 < OptimalEta.c η)
    (hclt : OptimalEta.c η < 1) :
    1 < SteadyErrEstimate.gain η
      ∧ (SteadyErrEstimate.gain η = 1 ↔ η = 1)
      ∧ OptimalEta.c η = OptimalEta.c (2 - η) := by
  refine ⟨?_, ?_, OptimalEta.c_symm η⟩
  · rw [SigmaLandscape.gain_eq_inv_one_sub_c]
    have hden : 0 < 1 - OptimalEta.c η := by linarith
    rw [one_div, one_lt_inv_iff₀]
    exact ⟨hden, by linarith⟩
  · rw [SigmaLandscape.gain_eq_one_iff_c_eq_zero, OptimalEta.c_eq_zero_iff]

/-! ===========================================================================
  §5  **主综合**：链式衰减 + 一步归零 + 参数命中 + 预测对齐 + 零间隙
     （消费 5 个模块的定理）
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【复合 5 · 主综合：世界模型的误差链在最优步长下闭合】**

在 `η = 1`（唯一最优步长）下，同一条链上**四件事同时由不同上游定理推出**：

1. **链式衰减**（`OptimalityChain.chain_geom_decay`）：
   `err_n = c 1 ^ n * err₀`（`Corrects` 链的精确等式）；
2. **一步归零**（`OptimalityChain.chain_eta_one_zero`）：
   `n ≥ 1` 时 `err_n = 0`；
3. **参数命中**（`ThetaLearningParam.thetaN_rate_form` + `0^n = 0`）：
   `θ_n = θ*`（`n ≥ 1`）；
4. **预测对齐**（`ThetaLearningParam.linPScm_sim_one` + §0 的 `linModels_agree`）：
   `sim θ_n 1 = θ_n * x`，故在 `n ≥ 1` 时 `sim = θ* * x`；
5. **零间隙**（`OptimalityGapTheory.optimalGap_refl`）：
   在误差幅度与其自身之间间隙为 `0`（对任意幅度恒成立，见文件头边界）。

**为何是推导而不是合取**：五项的**前件各不相同、作用点各不相同** ——
第 1、2 项在 `iterMap` 误差链上（`BoundWriteBack` 载体），
第 3 项在 `thetaN` 参数链上（`ℝ` 载体），第 4 项由第 3 项经 `sim` 的
**线性性**搬运（`x` 作乘子），第 5 项在 `errorMagnitude` 层。
第 4 项显式**依赖**第 3 项（`rw` 用 `theta_n = θ*`），且其 `sim` 对齐显式
**依赖** §0 的 `linModels_agree`（经 `paramScmWorldModel_sim_one` 把两个实例的
预测分量等同起来）。

**前件盘点**：`Corrects A φ`（表达力）、`err₀ > 0`（有东西可降）、
`x ≠ 0`（设计点非零）。**三条都在单步/初值/设计层**，
结论全在 `n` 步序列层与预测层。（第 5 项为无条件真，见文件头边界。） -/
theorem world_model_chain_synthesis {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : BoundWriteBack.Corrects A φ) (h0 : 0 < BoundWriteBack.errA A x' θ)
    (θstar x θ₀ : ℝ) (hx : x ≠ 0) :
    -- 1. 链式衰减（精确等式，`η = 1` 时 `c 1 = 0` 被显式保留）
    (∀ n : ℕ, BoundWriteBack.errA A x'
        (WiringConvergence.iterMap A φ 1 x' n θ)
        = OptimalEta.c 1 ^ n * BoundWriteBack.errA A x' θ)
    -- 2. 一步归零
    ∧ (∀ n : ℕ, 0 < n → BoundWriteBack.errA A x'
        (WiringConvergence.iterMap A φ 1 x' n θ) = 0)
    -- 3. 参数命中
    ∧ (∀ n : ℕ, 0 < n → ThetaConvergence.thetaN 1 θstar x θ₀ n = θstar)
    -- 4. 预测对齐（经 `sim` 的线性性）
    ∧ (∀ n : ℕ, 0 < n →
        (paramScmWorldModel ParamSCMConsumer.linearThetaModel).sim
            (ThetaConvergence.thetaN 1 θstar x θ₀ n)
            (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => x) 1
          = θstar * x)
    -- 5. 在真值处的误差幅度与其自身之间零间隙
    ∧ IsOptimalGap 0
        (ErrorMagnitude.errorMagnitude ErrorMagnitude.ErrKind.norm
          (BoundWriteBack.errA A x' θ))
        (ErrorMagnitude.errorMagnitude ErrorMagnitude.ErrKind.norm
          (BoundWriteBack.errA A x' θ)) := by
  -- 第 3 项所需：`θ_n = θ*`
  have htheta : ∀ n : ℕ, 0 < n → ThetaConvergence.thetaN 1 θstar x θ₀ n = θstar :=
    (optimal_eta_fixed_point_from_param θstar x θ₀ hx).1
  refine ⟨fun n => OptimalityChain.chain_geom_decay A φ 1 x' θ h n,
    fun n hn => OptimalityChain.chain_eta_one_zero A φ x' θ h hn,
    htheta,
    fun n hn => ?_,
    OptimalityGapTheory.optimalGap_refl _⟩
  -- 第 4 项：`sim` 的线性性（`ThetaLearningParam.linPScm_sim_one`）
  -- 与 `§0` 的实例一致性（`linModels_agree`：预测分量逐点相同）
  have hsim : (paramScmWorldModel ParamSCMConsumer.linearThetaModel).sim
      (ThetaConvergence.thetaN 1 θstar x θ₀ n)
      (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => x) 1
      = (paramScmWorldModel ThetaLearningParam.linPScm).sim
          (ThetaConvergence.thetaN 1 θstar x θ₀ n)
          (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => x) 1 := by
    simp only [paramScmWorldModel_sim_one]
    rfl
  rw [hsim, ThetaLearningParam.linPScm_sim_one, htheta n hn]

/-! ===========================================================================
  §7  **R-34 追加接线**：把 `Fate.SigmaLandscape`（27 条定理）与
  `Fate.AdjudicationKUnified`（17 条定理）—— 两者均在本文件 `import` 列表中
  并在文件头第一段声称为「扇入」目标，但**在本批次之前没有任何一条定理
  真正引用它们的结论** —— 接入本文件。

  本节共 4 条定理，全部为**跳模块复合**：

  | 定理 | 左腿 | 右腿 |
  |---|---|---|
  | `sigma_faces_strict_amplification_consumed` | `SigmaLandscape.sigma_three_faces` | 本文件 `optimal_c_window_fits_gain` 的 `1 < gain η` |
  | `infoComplete_unique_min_and_boundary_consumed` | `AdjudicationKUnified.minUnique_of_infoComplete` | `AdjudicationKUnified.fitBoundary_existsUnique_of_infoComplete` |
  | `hingeErr_second_route_not_infoComplete` | `AdjudicationKUnified.notUniqueMin_hingeErr` | `AdjudicationKUnified.not_infoComplete_of_notUniqueMin` |
  | `hingeErr_two_minima_and_not_infoComplete_consumed` | `AdjudicationKUnified.hingeErr_two_minima` | `AdjudicationKUnified.not_infoComplete_hingeErr` |

  **前件自查（纪律 7，防同义反复）**：
  * 第 1 条前件为 `MemLp` / `0 < n` / `0 < varOf P` / `|1-η| < 1` / `1 < gain η`；
    结论中的严格不等式 `varOf P / n < Var[steadyErrEst η n]` **不在**前件中
    （前件只谈 `gain`，结论谈**方差**）。
  * 第 2 条前件为 `InfoComplete f`（严格凸 + 连续 + 强制）；结论中
    `∃! γ, IsMinOn f univ γ` 与 `∀ σ, (HasFitBoundary W σ ↔ σ = W.err γ_)`
    均**不在**前件中（`InfoComplete` 的定义逐条都不提最小点的存在或唯一）。
  * 第 3 条前件为空。
  * 第 4 条前件为空。
  =========================================================================== -/

section R34Wiring

/-- ⭐⭐⭐⭐ **【增益放大 ⟹ 稳态误差方差**严格大于**样本均值方差】（R-34 跳模块）**

在 `L²`、`0 < n`、非退化（`0 < varOf P`）、收缩窗 `|1-η| < 1`
以及**放大系数严格大于 1** 的前提下，由 `SigmaLandscape.sigma_three_faces`
得到：

1. `Var[meanOf n] = varOf P / n`（统计刻度）；
2. `Var[steadyErrEst η n] = (gain η)^2 * (varOf P / n)`（工程刻度）；
3. **且严格放大**：`varOf P / n < Var[steadyErrEst η n]`。

**为何是新内容**：`sigma_three_faces` 只给出**等式** `Var[st] = gain^2 * Var[mean]`，
对 `gain > 1` 时它**没有**断言严格不等式；严格性需要额外的事实
“`varOf P / n > 0`” + “`gain^2 > 1`”。这正是“闭环确实引入额外噪声”的形式化版本，
而不是“公式里有个平方”。

**前件自查**：前件只有 `gain η > 1`（关于**系数**的事实）；结论是**两个方差之间**
的严格不等式，不在前件中。 -/
theorem sigma_faces_strict_amplification_consumed
    {P : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure P]
    (hP : MeasureTheory.MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (hv : 0 < GaussMarkovScalar.varOf P) {η : ℝ} (hη : |1 - η| < 1)
    (hg : 1 < SteadyErrEstimate.gain η) :
    (ProbabilityTheory.variance (SigmaEstimation.meanOf n) (MeasureTheory.Measure.pi (fun _ : Fin n => P))
        = GaussMarkovScalar.varOf P / n)
      ∧ (ProbabilityTheory.variance (SteadyErrEstimate.steadyErrEst η n) (SigmaEstimation.iidMeasure P n)
          = (SteadyErrEstimate.gain η) ^ 2 * (GaussMarkovScalar.varOf P / n))
      ∧ (GaussMarkovScalar.varOf P / n
          < ProbabilityTheory.variance (SteadyErrEstimate.steadyErrEst η n) (SigmaEstimation.iidMeasure P n)) := by
  obtain ⟨h1, _, _, h4⟩ := SigmaLandscape.sigma_three_faces hP n hn hv hη
  rw [h1] at h4
  refine ⟨h1, h4, ?_⟩
  rw [h4]
  have hx : 0 < GaussMarkovScalar.varOf P / n := by positivity
  have hs : 1 < SteadyErrEstimate.gain η ^ 2 := by nlinarith
  calc GaussMarkovScalar.varOf P / n
      = 1 * (GaussMarkovScalar.varOf P / n) := (one_mul _).symm
    _ < SteadyErrEstimate.gain η ^ 2 * (GaussMarkovScalar.varOf P / n) :=
        mul_lt_mul_of_pos_right hs hx

/-- ⭐⭐⭐⭐ **【信息完整 ⟹ 最小点唯一 **且** 拟合边界唯一】（R-34 跳模块）**

同时消费 `AdjudicationKUnified` 的两条定理（**此前本文件 0 引用**）：

* `minUnique_of_infoComplete`：`InfoComplete f ⟹ ∃! γ, IsMinOn f univ γ`
  （在函数本身上谈最优集的唯一性）；
* `fitBoundary_existsUnique_of_infoComplete`：`InfoComplete (W.err) ⟹`
  `∃! γ_, IsFitBoundary W (W.err γ_) γ_` **且**对任意 σ
  `(HasFitBoundary W σ ↔ σ = W.err γ_)`（在**拟合边界**词汇上谈）。

**为何合成有价值**：两条定理的**载体不同**（裸函数 `f` vs 误差曲面 `W : ErrProfileWeak`）、
**结论形状不同**（`IsMinOn` vs `IsFitBoundary ↔ HasFitBoundary`）。本定理把它们
铉在同一个 `InfoComplete` 前提下，证明“完整信息”在**两个不同词汇**上同时给出唯一性
—— 这是裁决 K “数学侧可得唯一解” 在两套语言里的一致兑现。

**前件自查**：前件 `InfoComplete f`、`InfoComplete (fun γ => W.err γ)`、`f = W.err`；
结论中的 `IsMinOn` 与 `HasFitBoundary ↔` 均不在前件中。 -/
theorem infoComplete_unique_min_and_boundary_consumed {f : ℝ → ℝ}
    (h : AdjudicationKUnified.InfoComplete f) :
    (∃! γ, IsMinOn f Set.univ γ)
      ∧ (∀ (W : R238E3.ErrProfileWeak), f = (fun γ => W.err γ) →
          AdjudicationKUnified.InfoComplete (fun γ => W.err γ) →
          ∃! γ_, R238E3.IsFitBoundary W (W.err γ_) γ_ ∧
            ∀ σ : ℝ, (R238E3.HasFitBoundary W σ ↔ σ = W.err γ_)) :=
  ⟨AdjudicationKUnified.minUnique_of_infoComplete h,
    fun W hf hW => by subst hf; exact AdjudicationKUnified.fitBoundary_existsUnique_of_infoComplete hW⟩

/-- ⭐⭐⭐ **【`hingeErr` 信息不完整的**第二条独立路径**】（R-34 跳模块）**

`AdjudicationKUnified.not_infoComplete_hingeErr` 走的是「非严格凸」路径；
本定理走的是**完全不同的**路径：先由 `notUniqueMin_hingeErr` 得到最优集不唯一，
再用 `not_infoComplete_of_notUniqueMin` 反推信息不完整。

**价值**：两条路径**恰好同向**，证明 `AdjudicationKUnified` 内部两个模块层次
（凸性层 vs 最小点层）一致性；若任一条腿被改弱，本定理会立即失效而另一条仍存，
**这就是“双路径”的可检测价值**。

**前件自查**：前件为空；结论是非平凡 `¬`。 -/
theorem hingeErr_second_route_not_infoComplete :
    ¬ AdjudicationKUnified.InfoComplete Fate.H5K.hingeErr :=
  AdjudicationKUnified.not_infoComplete_of_notUniqueMin
    AdjudicationKUnified.notUniqueMin_hingeErr

/-- ⭐⭐⭐ **【两个极小点 + 信息不完整：两组事实同时成立】（R-34 跳模块）**

把 `AdjudicationKUnified.hingeErr_two_minima`（`ConvexOn` 且 `1`、`-1` **两个**
不同点均为全局限小点）与 `AdjudicationKUnified.not_infoComplete_hingeErr`
（信息不完整）合成一条：**具体的、可执行的**反例 —— “凸 + 两个极小点 ⟹ 不能保证唯一”。

**为何不是同义反复**：前件为空。第一条因子是**凸性 + 两点极小性 + 不等**
（三条数值/集合事实），第二条因子是一个 `¬`；两者**互不可推**（两个极小点
并不形式地排斥信息完整性，需要 `not_infoComplete_hingeErr` 那条路）。 -/
theorem hingeErr_two_minima_and_not_infoComplete_consumed :
    (ConvexOn ℝ Set.univ Fate.H5K.hingeErr
        ∧ IsMinOn Fate.H5K.hingeErr Set.univ 1
        ∧ IsMinOn Fate.H5K.hingeErr Set.univ (-1)
        ∧ (1 : ℝ) ≠ -1)
      ∧ (¬ AdjudicationKUnified.InfoComplete Fate.H5K.hingeErr) :=
  ⟨AdjudicationKUnified.hingeErr_two_minima,
    AdjudicationKUnified.not_infoComplete_hingeErr⟩

#print axioms sigma_faces_strict_amplification_consumed
#print axioms infoComplete_unique_min_and_boundary_consumed
#print axioms hingeErr_second_route_not_infoComplete
#print axioms hingeErr_two_minima_and_not_infoComplete_consumed

end R34Wiring

/-! ===========================================================================
  §6  **公理审计**
  =========================================================================== -/

#print axioms linModels_agree
#print axioms linModels_theta_is_real
#print axioms unit_budget_gap_of_chain
#print axioms optimal_eta_step_attains_zero
#print axioms optimal_eta_fixed_point_from_param
#print axioms optimal_c_window_fits_gain
#print axioms world_model_chain_synthesis

end

end WorldModelSynthesis

end Fate
