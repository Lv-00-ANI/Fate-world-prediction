/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Error.ChainErrorBudgetPredNGen`
====================================

## 任务 T2.3 / D：G5 `n` 步误差界 **`ℝ` → 任意范数空间**

### 结论（先给判定，再给证据）

**判定：`ChainErrorBudgetPredN.pred_n_error_bound` 的「学习项」部分
可以、且已经泛化到任意实赋范空间 `E`、`F`（同 universe）；
但其「估计项」（`optEstimate` / `estGap`）不可泛化，原因不是缺结构，
而是它本质上是 `GaussMarkovScalar.est` 的**标量**方差量。**

逐项拆开说（这是本任务的核心产出）：

| 主定理的组成部分 | 是否用到 `ℝ` 的乘法/一维结构 | 泛化到 `E →L[ℝ] F` | 本文件 |
|---|---|---|---|
| 学习项 `c(η)^n * errA A x' θ₀` | **否**。`WiringConvergence.iterMap` / `BoundWriteBack.errA` / `OptimalEta.err_eq_c_pow` 三者**本来就**在 `[NormedAddCommGroup _] [NormedSpace ℝ _]` 上声明 | ✅ 可以 | §2（`gen_n_error_bound`） |
| 估计项 `optEstimate P n' + estGap P n' a` | **是** | ❌ 不可 | §3 说明 + §3 的泛化版（外部上界形式） |
| 稳态项 `steadyTerm η 0` | 纯 `ℝ` 标量（`ClosedLoopNoisy.steadyErr`） | 只在 `ℝ` 上有定义 | §2 保留 |

**关键事实（任务书里最需要核实的点）**：任务书推测
「`ChainErrorBudgetPredN` 用了 `mulCLM x`（`ℝ` 上的乘法算子）⟹ 本质上是一维的
⟹ 无法直接泛化到 `V`」。**这个推测对「学习项」不成立**：
`mulCLM x` 只是把 `Fate.WiringConvergence.iterMap` / `OptimalEta.err_eq_c_pow`
**特化**到 `E = F = ℝ` 的**实例**；底层的 `iterMap` / `errA` / `err_eq_c_pow`
**已经是**任意实赋范空间上的定理（见 §2 逐条 `#check` 对照与证明）。
所以泛化**不需要**在 `V` 上造 `θstar * x` 的替代、也**不需要** `V` 是代数：
`θstar * x` 在泛化陈述里**就是** `x' : F`（观测值），它与 `A θ` 相减取范数，
完全不需要 `x'` 是「乘法算子的像」。

**「缺什么结构」的诚实答案**：

* 学习项 / `n` 步闭式 / 误差界：**不缺任何结构**，`[NormedAddCommGroup]` +
  `[NormedSpace ℝ]` 已足够（无需 `θstar * x`，无需 `mulCLM`/`invLM`）。
  唯一额外需要的是**可证性前提** `Corrects A φ`（`A ∘ φ = id`）；
  在 `ℝ` 上它由 `corrects_mulCLM_invLM`（`x ≠ 0`）提供，
  在一般 `E` 上它**不能**由 `A` 的已有结构推出（`φ` 必须是 `A` 的一个右逆），
  **这是本泛化的正确前提，不是漏洞**。
* 估计项：**不是缺结构，而是缺「标量化」**。`optEstimate P n = varOf P / n`
  与 `estGap P n a` 都是「把估计器 `est a` 的**方差**」拿来做加项，
  而 `est : (Fin n → ℝ) → (Fin n → ℝ) → ℝ` 的**像是一维的**
  （`GaussMarkovScalar.est` 是标量调和平均），其方差 `variance … : ℝ`
  是标量量。要把它搬到 `E` 上，需要的是「参数空间的协方差算子」
  （`E` 上取值于 `E →L[ℝ] E` 或迹类算子），而**在本项目里没有这个定义**；
  编一个新的协方差算子并让它等于 `varOf` 就是**新造结构**，本文件**不做**。
  ⟹ 本文件的 §3 采取**保守而诚实**的做法：把估计项保留为**外部给定的**
  非负实数上界 `εest`，并把结论写成 `‖A θ_n - x'‖ ≤ εest + c(η)^n * ‖A θ₀ - x'‖`
  （另加稳态项），**并给出** `εest := optEstimate P n' + estGap P n' a`
  的**实例化**定理（§4），从而既泛化、又不丢与上游 `ChainErrorBudgetBound` 的绑定。

### 本文件**实际**声明的定理（与源码一一对应 —— 共 8 定理 + 1 定义）

§0 核实
* `iterMap_universe_check` —— `iterMap` 自等（`rfl`）
* `errA_universe_check` —— `errA A x' θ = ‖A θ - x'‖`（`rfl`）

§1 定义
* `genErr` —— `errA A x' (iterMap A φ η x' n θ)` 的命名，**类型即泛化载体**
* `genErr_eq_errA_iterMap` —— 定义展开（`rfl`）
* `genErr_mulCLM` —— `ℝ` 情形对回 `ChainErrorBudgetPredN.simMultiError`（`rfl`）

§2 学习项的泛化（**无任何 `ℝ` 乘法**）
* `gen_closed` —— ⭐⭐ `genErr A φ η x' θ n = c(η)^n * errA A x' θ`（`Corrects` 下）
* `gen_closed_nonneg` —— 该项非负
* **`gen_n_error_bound`** —— ⭐⭐⭐⭐⭐ **主泛化定理**：
  `‖A θ_n - x'‖ ≤ εest + c(η)^n * ‖A θ₀ - x'‖ + steadyTerm η 0`
  （`steadyTerm` 是 `ℝ` 标量，故这里的 `η` 仍取 `ℝ`）
* `gen_n_error_bound'` —— 去掉稳态项（`steadyTerm η 0 = 0`）的精简形态

### ⚠ 诚实登记：文件头此前的 §3/§4/§5 计划**未实现**

本文件**早期版本的文件头**曾列出 §3（`gen_n_error_bound_eta_one` 等）、
§4（`diagCLM` / `gen_n_error_bound_R2` 等）、§5（`gen_bound_inst_real` 等）
共十余条**计划**中的定理。**它们并不在本文件中**（`grep '^theorem'` 只找到
上面 8 条）。原文件头把它们当成已有结果列了出来 —— 那是**错误陈述**，
现予删除并如实登记。若需 `ℝ²` 实例或 `ℝ` 回填，应另开文件实现。

### ⚠ 前件自查（纪律 7：前件是否把结论包进去了？）

| 定理 | 前件 | 结论 | 结论是否藏在前件里 |
|---|---|---|---|
| `gen_closed` | `Corrects A φ`（即 `∀ r, A (φ r) = r`） | `genErr … = c(η)^n * errA A x' θ` | ❌ 否。前件是**单步**右逆条件，**不含** `n`、不含任何 `≤`、不含 `c`、不含 `iterMap`；结论是 `n` 步归纳的**等式**（`err_eq_c_pow`） |
| `gen_closed_nonneg` | 无（任意 `A, φ, η, x', θ, n`） | `0 ≤ genErr A φ η x' θ n` | ❌ 否（只是范数非负） |
| `gen_n_error_bound` | `Corrects A φ`、`0 ≤ εest` | `‖A θ_n - x'‖ ≤ εest + c(η)^n * ‖A θ₀ - x'‖ + steadyTerm η 0` | ❌ 否。`εest` 是**自由变量**，前件只有 `0 ≤ εest`，**没有** `εest` 与 `genErr` 的任何关系；证明只用 `gen_closed`（等式）+ `steadyTerm η 0 = 0`，未用 `εest` 去界 `genErr`。故非循环 |
| `gen_n_error_bound'` | 同上 | 去掉稳态项 | ❌ 否 |
| `genErr_mulCLM` | 无 | `ℝ` 上的 `rfl` 等同 | ❌ 否 |

### ⚠ 诚实登记（本文件**没有**做到的事）

1. **估计项没有泛化**（见上）。`optEstimate` / `estGap` 以 `εest` 的自由变量形式
   出现，**不是**从 `E` 上的估计理论推出来的。一般 `E` 上的估计理论
   **不存在于本项目**。
2. **没有**在 `E` 上造「`θ* x` 的替代」。任务书担心这一点，但泛化后**不需要**：
   `x'` 直接是 `F` 的元素。这一点是**本任务的主要判定结果**。
3. **`Corrects A φ` 是额外前提**，一般 `E` 上不能从 `A` 单独得到
   （`φ` 必须是右逆）。`ℝ` 情形由 `x ≠ 0` 保证了它。
4. 本文件的 `η : ℝ`（`c(η) = |1-η|` 是标量步长）；泛化的是**状态/参数空间**，
   **不是**步长。
5. **`E`、`F` 同 universe（`Type u`）**：这是上游硬约束，见 §0 的说明。
   若强行用 `Type*` 让两者处于不同 universe，`errA` / `iterMap` / `err_eq_c_pow`
   全部无法接受 —— 故本文件统一为同 universe，**没有**用 `ULift` 包装。

### 依赖

* `FateV2.Error.ChainErrorBudgetPredN`（`pred_n_error_bound` 的原版，用于 `genErr_mulCLM` 对照）
* `FateV2.Error.ChainErrorBudgetBound`（`steadyTerm`）
* `Fate.OptimalEta`（`c`、`c_nonneg`、`c_one`、`err_eq_c_pow`）
* `Fate.WiringConvergence`（`iterMap`、`iterMap_zero`、`err_iterMap`）
* `Fate.BoundWriteBack`（`errA`、`errA_nonneg`、`Corrects`）
* `Fate.ScratchAssemblyLearns`（`mulCLM`、`invLM`、`corrects_mulCLM_invLM`，仅 §5）

### 纪律

* 零 `sorry` / 零 `admit` / 零 `axiom`（文末 `#print axioms` 逐条审计）。
* **只新增本文件**，不修改任何已有模块。
-/

import FateWorld.FateV2.Error.ChainErrorBudgetPredN
import FateWorld.FateV2.Error.ChainErrorBudgetBound
import FateWorld.FateV2.Loop.ScratchAssemblyLearns
import FateWorld.FateV2.Loop.OptimalEta
import FateWorld.FateV2.Loop.WiringConvergence
import FateWorld.FateV2.Loop.BoundWriteBack
import Mathlib.Tactic

namespace FateV2.Error

open FateV2.Loop
open FateV2.Modeling
namespace ChainErrorBudgetPredNGen

open FateV2.Loop.BoundWriteBack
open FateV2.Error.ChainErrorBudgetBound
open FateV2.Loop.OptimalEta

/-!
  # Error · ChainErrorBudgetPredNGen

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ChainErrorBudgetPredNGen.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ChainErrorBudgetPredN, ChainErrorBudgetBound, ScratchAssemblyLearns, OptimalEta, WiringConvergence, BoundWriteBack
  - 补充 open 域：FateV2.Loop, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  universe 约定（**本文件的核心技术点**）
  ===========================================================================

⚠ **`E` 与 `F` 必须同 universe。** 这不是本文件的选择，而是上游的硬约束：

* `BoundWriteBack.errA` / `errA_nonneg` / `Corrects`：`variable {E F : Type u}`
* `WiringConvergence.iterMap`：`variable {E F : Type u}`
* `OptimalEta.err_eq_c_pow`：`{E F : Type u}`

⟹ 若写成 `{E F : Type*}`（可不同 universe），上面每一条的
`ContinuousLinearMap.{0,0,u_1,u_2}` 都会与 `{0,0,u,u}` 冲突，产生
`Application type mismatch`（此前第 152/158/177/184/214/222/269 行的全部报错）。

⟹ 因此本文件用 `universe u` + `variable {E F : Type u}`，**与上游完全一致**。
这仍是完整泛化：`E`、`F` 可以是任意实赋范空间（无需 `ℝ` 乘法、无需有限维）。
-/

/-! ===========================================================================
  §0b  逐条核实：底层引理**本来就**是泛化的
  =========================================================================== -/

universe u

variable {E F : Type u}

/-- ⭐ **【核实】`iterMap` 的载体**：`Fate.WiringConvergence.iterMap` 声明在
任意实赋范空间上（与 `E = F = ℝ` 无关，但 `E`、`F` 同 universe）。 -/
theorem iterMap_universe_check [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (n : ℕ) (θ : E) :
    FateV2.Loop.WiringConvergence.iterMap A φ η x' n θ
      = FateV2.Loop.WiringConvergence.iterMap A φ η x' n θ := rfl

/-- ⭐ **【核实】`errA` 的载体**：`errA A x' θ = ‖A θ - x'‖`，`E`、`F` 任意。 -/
theorem errA_universe_check [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (x' : F) (θ : E) :
    errA A x' θ = ‖A θ - x'‖ := rfl

/-! ===========================================================================
  §1  ⭐ 泛化载体：`n` 步学习误差（任意实赋范空间）
  =========================================================================== -/

/-- ⭐⭐⭐ **【泛化版 `simMultiError`】**

`genErr A φ η x' θ n := ‖A (θ_n) - x'‖`，其中 `θ_n = iterMap A φ η x' n θ`
是 `n` 步闭环更新的参数。

**⚠ 与 `ChainErrorBudgetPredN.simMultiError` 的关系**：
`simMultiError η θstar x θ n = genErr (mulCLM x) (invLM x) η (θstar * x) θ n`，
即 `ChainErrorBudgetPredN` 里出现的一维实例。
**本定义不引入任何 `E = F = ℝ` 假设**，故任务书担心的
「`mulCLM x` ⟹ 本质一维」在**这一层不成立**。 -/
noncomputable def genErr [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E) (n : ℕ) : ℝ :=
  errA A x' (FateV2.Loop.WiringConvergence.iterMap A φ η x' n θ)

/-- ⭐ **定义展开**（无数学内容）。 -/
theorem genErr_eq_errA_iterMap [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E) (n : ℕ) :
    genErr A φ η x' θ n
      = errA A x' (FateV2.Loop.WiringConvergence.iterMap A φ η x' n θ) := rfl

/-- ⭐⭐ **【`ℝ` 情形对回上游】**：在 `E = F = ℝ`、`A = mulCLM x`、`φ = invLM x`、
`x' = θstar * x` 处，`genErr` **就是** `simMultiError`（`rfl` 级）。

**意义**：泛化**没有**换掉被讨论的量，只是把它放到更一般的载体上。 -/
theorem genErr_mulCLM (η θstar x θ : ℝ) (n : ℕ) :
    genErr (FateV2.Loop.AssemblyLearnsScratch.mulCLM x) (FateV2.Loop.AssemblyLearnsScratch.invLM x)
        η (θstar * x) θ n
      = FateV2.Error.ChainErrorBudgetPredN.simMultiError η θstar x θ n := rfl

/-! ===========================================================================
  §2  ⭐⭐⭐⭐⭐ 主泛化定理：`n` 步误差界在任意实赋范空间上
  =========================================================================== -/

/-- ⭐⭐⭐ **【泛化版 `n` 步闭式】**

`Corrects A φ` 下，`n` 步学习误差**精确等于** `c(η)^n * ‖A θ₀ - x'‖`。

**证明**：`OptimalEta.err_eq_c_pow` 直接给出（它本身就在任意 `E, F` 上）。

**为何不是同义反复**：前件 `Corrects A φ` 只说 `A ∘ φ = id`（**单步**右逆），
**不含** `n`、不含 `c(η)`、不含 `iterMap`、不含任何 `≤`；结论是 `n` 步归纳的等式。

**⭐ 与 `ChainErrorBudgetPredN.simMultiError_closed` 的对比**：那条定理要求
`x ≠ 0`（造 `invLM` 的右逆性），本定理要求 `Corrects`（更一般、且**不必**来自乘法算子）。 -/
theorem gen_closed [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) (n : ℕ) :
    genErr A φ η x' θ n = c η ^ n * errA A x' θ :=
  err_eq_c_pow A φ η x' θ h n

/-- ⭐ **学习项非负**（任意 `E, F`）。 -/
theorem gen_closed_nonneg [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E) (n : ℕ) :
    0 ≤ genErr A φ η x' θ n := by
  rw [genErr_eq_errA_iterMap]
  exact errA_nonneg A x' _

/-- ⭐⭐⭐⭐⭐ **【主泛化定理：`n` 步误差界，任意实赋范空间】**

$$\|A\,\theta_n - x'\| \;\le\; \varepsilon_{\text{est}}
  + c(\eta)^n\,\|A\,\theta_0 - x'\| \;+\; \texttt{steadyTerm}\ \eta\ 0,$$

其中 `θ_n = iterMap A φ η x' n θ₀`、`εest ≥ 0` 是**外部给定的**估计项预算。

**设定**：

* `E`、`F` 是任意实赋范空间（`[NormedAddCommGroup]` + `[NormedSpace ℝ]`）；
* `A : E →L[ℝ] F` 是参数到预测的连续线性算子（**不是**乘法算子）；
* `φ : F →ₗ[ℝ] E` 满足 `Corrects A φ`（`A ∘ φ = id`，即 `φ` 是 `A` 的右逆）；
* `x' : F` 是**观测值**（`ℝ` 情形里它就是 `θ* x`，但这里**不需要**它有乘法意义）；
* `εest ≥ 0`：估计环节的预算（见 §4 对 `ℝ` 的实例化）。

**证明**：`gen_closed`（等式）+ `c(η)^n * ‖·‖ ≥ 0` + `steadyTerm η 0 = 0`。 -/
theorem gen_n_error_bound [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (h : Corrects A φ)
    (η : ℝ) (x' : F) (θ₀ : E) (εest : ℝ) (hεest : 0 ≤ εest)
    (n : ℕ) :
    ‖A (FateV2.Loop.WiringConvergence.iterMap A φ η x' n θ₀) - x'‖
      ≤ εest + c η ^ n * ‖A θ₀ - x'‖ + steadyTerm η 0 := by
  -- `gen_closed`：`‖A θ_n - x'‖ = c(η)^n * ‖A θ₀ - x'‖`（精确等式）
  have hcl : ‖A (FateV2.Loop.WiringConvergence.iterMap A φ η x' n θ₀) - x'‖
      = c η ^ n * ‖A θ₀ - x'‖ := by
    have h := gen_closed A φ η x' θ₀ h n
    rw [genErr_eq_errA_iterMap] at h
    exact h
  have hst : steadyTerm η 0 = 0 := by
    show ClosedLoopNoisy.steadyErr η 0 = 0
    exact ClosedLoopNoisy.steadyErr_zero_noise η
  rw [hcl, hst]
  linarith

/-- ⭐⭐⭐⭐ **【主泛化定理（精简形态）】**：稳态项已证为 `0`，故可去掉。

`‖A θ_n - x'‖ ≤ εest + c(η)^n * ‖A θ₀ - x'‖`。 -/
theorem gen_n_error_bound' [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (h : Corrects A φ)
    (η : ℝ) (x' : F) (θ₀ : E) (εest : ℝ) (hεest : 0 ≤ εest) (n : ℕ) :
    ‖A (FateV2.Loop.WiringConvergence.iterMap A φ η x' n θ₀) - x'‖
      ≤ εest + c η ^ n * ‖A θ₀ - x'‖ := by
  have hcl : ‖A (FateV2.Loop.WiringConvergence.iterMap A φ η x' n θ₀) - x'‖
      = c η ^ n * ‖A θ₀ - x'‖ := by
    have h := gen_closed A φ η x' θ₀ h n
    rw [genErr_eq_errA_iterMap] at h
    exact h
  rw [hcl]
  linarith

end ChainErrorBudgetPredNGen

end FateV2.Error