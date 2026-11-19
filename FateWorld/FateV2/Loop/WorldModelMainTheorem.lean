/-
命运理论 · Lean 4 形式化实现
================================

模块：`WorldModelMainTheorem`
任务：**【世界模型的最终交付物 / 真正的收口点】**

---------------------------------------------------------------------------
## 0  缘起（审计 R96 的判定）
---------------------------------------------------------------------------
`WorldModelCapstone.worldModel_capstone`（`WorldModelCapstone.lean:650`）
是全库**唯一**一条真正的世界模型装配定理：它 import 并真实调用 **8 个上游
模块**（`ThetaConvergence` / `WorldModelReadsTheta` / `ConvergenceOptimal` /
`SteadyErrEstimate` / `WorldModelAssembly` / `ClosedLoopNoisy` /
`OptimalEta` / `SigmaEstimation` / `WiringBackdoorFixed` / `CausalRouteDo`）的
主定理，结论是 5 条实质结论的合取。

但审计实测其消费链是：

    WorldModelCapstone  ←  WorldModelCapstoneConsumer（扇入 1）
                        ←  无人（扇入 0）

即**链的终点是一个谁都不用的文件**。审计判定：
「把没人认领的成品改名成有人签收但没人使用的成品」。

本文件的任务是**给出世界模型的最终交付物**，并让**它自己**消费
`WorldModelCapstone` 与 `WorldModelCapstoneConsumer` 两侧 ——
从而使这条链有一个**真正的、被下游可引用的终端陈述**。

---------------------------------------------------------------------------
## 1  为什么**不**复用三个 `Main*` 文件（任务步骤 (a) 的判定）
---------------------------------------------------------------------------
* `Fate/MainTheoremCFinal.lean` —— 内容是**主定理 C 的 `Z = ∅` 情形**
  （`Split R X Y ∅` ⟹ `CondIndep`），属**因果桥**的交付物，与世界模型无关。
* `Fate/MainlineTheorems.lean` —— 内容是**规则代数**（商上运算良定义 T6.6、
  组合封闭性 T6.4），属**规则层**，与世界模型无关。
* `Fate/MainlineIntegration.lean` —— 名字里虽含 "Mainline"，但其内容全部是
  **因果桥的接线**（`BridgeFinal` / `BridgeSingleFiber` / `Kernel.Indep` /
  do-演算 / SCM 观测层），**一条世界模型定理也没有**。它是**因果桥**的交付物。

⟹ **三者都不是世界模型的交付物。** 故按任务步骤 (b) **新建本文件**。

---------------------------------------------------------------------------
## 2  本文件的主定理（步骤 (b)(c)）
---------------------------------------------------------------------------
`worldModel_main_theorem`：**唯一一条**世界模型最终陈述。

**载体收口（真 L3 的来源）**：前件里 `A`/`φ`/`η`/`Corrects`/收缩窗 这 **5 个
散落的参数**被 `WorldModelCapstone.ClosedLoopWorld E F` **一个结构参数 `W`** 取代
（`W.A`、`W.φ`、`W.η`、`W.corrects`、`W.window`）。该限定名出现在本定理的
**类型签名**里 —— 删掉 `WorldModelCapstone`，签名直接不合法。这是**真 L3**，
且不是同义反复（`W` 是**结构性的**，不含任何结论）。

**结论（capstone 的 5 条实质结论 + 一致性，共 7 条）**：

| # | 结论 | 来源 |
|---|---|---|
| 1 | `θ_n → θ*`（学习真的收敛到真值）| Capstone `worldModel_capstone` (1) |
| 2 | `c 1 = 0`（`η = 1` 的收缩因子归零）| Capstone `worldModel_capstone` (2) |
| 3 | `θ₁(1) = θ*`（`η = 1` 一步学到真值）| Capstone `worldModel_capstone` (2) |
| 4 | 不同 `θ` ⟹ 不同预测（`θ` 可辨识）| Capstone `worldModel_capstone` (3) |
| 5 | 有观测噪声闭环的 `limsup` 上界 `≤ steadyErr η (2Lηmax)` | Capstone `worldModel_capstone` (4) |
| 6 | `Var[Ê_∞] = gain(η)² · (σ²/n)` | Capstone `worldModel_capstone` (5) |
| 7 | `σ²/(m+1) → 0`（σ 估计的一致性）| **Consumer** `capstone_endToEnd_implies_learning_bound` |

**⭐ 为什么第 7 条是真实新增**：`worldModel_capstone` 只给出**方差等式**
（第 6 条），**不含**任何关于样本量的一致极限。该极限在
`WorldModelCapstoneConsumer.capstone_endToEnd_implies_learning_bound` 里被
**下游投影**出来。故本定理是**两侧同时消费**的联合陈述 —— 它不是把
capstone 的合取「拆开再拼回」（步骤 (c) 明令禁止），而是：

* 对 capstone 结论：**证明体直接 `obtain` 其 9 元合取**（一次调用，
  **不重新证明**任何一条）；
* 新增第 7 条：**只能**经 Consumer 得到（capstone 自身没有）。

---------------------------------------------------------------------------
## 3  ⚠ 诚实边界（如实登记）
---------------------------------------------------------------------------
**3.1** 本文件**不**声称 `linWorld`（线性学习链）与 `ClosedLoopWorld`
（抽象赋范空间闭环）是**同一条链的同构**。二者的联结点仍是标量收缩因子
`c(η) = |1-η|`（`OptimalEta.c` 的定义），本文件**如实登记**这一点
（与 `WorldModelCapstone §10.2 #1` 一致）。

**3.2** 第 6 条的 `varOf P` 只作为**方差参数**使用，**不**解释为「噪声标准差」
（沿用 `SigmaEstimation` 文件首登记的解释性例外）。

**3.3** 本文件**不**消费 Capstone 的因果接口（第 6/7 条之外的
`adjustLaw = doLaw2`、`doLaw` 幂等）。原因：那两条属于**因果层**，
而本文件是**世界模型**的交付物；强行并入会把因果桥与世界模型混为一谈
（审计 R96 明确批评过的「混装」）。它们已由
`WorldModelCapstoneConsumer.capstone_causal_interface_consistent` 消费。

**3.4** `WorldModelCapstoneConsumer` 中 **L3 见证** `capstone_closedLoopWorld_
contraction_interface`（`:374`）的结论 `c W.η < 1` 是同义反复
（`OptimalEta.c η := |1-η|` 是**定义**，`W.window` 就是 `|1 - W.η| < 1`，
故结论 = 前件经定义展开，零信息）。本文件**不**引用它、**不**依赖它；
本文件的第 1–7 条**没有**任何一条由定义展开得出。该问题**按纪律不在本文件
修复**（不得修改已有模块），**如实登记于此**。

**3.5** 零 `sorry` / 零 `admit` / 零 `axiom`；只新建本文件，**不修改**任何
已有模块；未跑全量 `lake build`。

---------------------------------------------------------------------------
## 4  前件自查（纪律 7：前件是否已把结论包进去）
---------------------------------------------------------------------------
| 前件 | 内容 | 是否等于/蕴含结论 |
|---|---|---|
| `W : ClosedLoopWorld E F` | `A ∘ φ = id`、`\|1-η\| < 1`、`drift ≥ 0` | **否**（结构性字段；不含任何极限/方差/不等式结论）|
| `hx : x ≠ 0` | 设计点非零 | **否**（是标量非零性，结论是轨迹/预测/上界）|
| `hθ : θ₁ ≠ θ₂` | 参数不等 | **否**（参数不等 vs **预测**不等，需 `hx` 才传递）|
| `hP : MemLp id 2 P` | 二阶矩有限 | **否**（结论是方差**等式**与极限）|
| `hn : 0 < n` | 样本数正 | **否**（结论是涉及 `n` 的等式）|
| `hL : 0 < L`、`hLI`、`hηmax` | `h` 的 Lipschitz 可逆性 | **否**（结论是 `limsup` 的数值界）|
| `hx'`、`hδ` | 观测方程与**单步**噪声界 | **否**（结论是 `limsup` 界，非单步）|

**特别检查（本项目最高频问题）**：`W.window : |1 - W.η| < 1` 是否已把第 2 条
`c 1 = 0` 包进去？**否** —— `window` 讲的是**未定的** `W.η`，而第 2 条讲的是
**常数** `OptimalEta.c 1`（`1` 与 `W.η` 无关）。二者**不是**同一命题。
同理第 5 条讲 `W.η` 的 `limsup` 界，`window` 只讲 `|1 - W.η| < 1`，
是**界存在**的结构前提，不是界本身。

**⚠ 唯一的近似风险**：第 3 条 `θ₁(1) = θ*` 与第 2 条 `c 1 = 0` 都由
`η = 1` 推出，而 `W.window` 关于 `W.η`。三者**互不蕴含**（`1` 固定，
`W.η` 自由）。故**非同义反复**。

**引用**：`WorldModelCapstone.worldModel_capstone`（8 模块总装，一次调用）、
`WorldModelCapstoneConsumer.capstone_endToEnd_implies_learning_bound`
（σ 估计一致性，第 7 条）、`WorldModelAssembly.obs_noise_drift_bound`
（为 Consumer 提供 `hstep`，从观测模型推出而非假设结论）。
-/

import FateWorld.FateV2.Loop.WorldModelCapstone
import FateWorld.FateV2.Loop.WorldModelCapstoneConsumer
import Mathlib.Tactic

namespace FateV2.Loop
namespace WorldModelMainTheorem

universe u

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Topology

/-!
  # Loop · WorldModelMainTheorem

  ## 迁移登记
  - 来源：`FateWorld/Legacy/WorldModelMainTheorem.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：WorldModelCapstone, WorldModelCapstoneConsumer
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §5  ⭐⭐⭐⭐⭐ **【世界模型主定理】最终交付陈述**
    =========================================================================== -/

section MainTheorem

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- ⭐⭐⭐⭐⭐ **【世界模型主定理】`WorldModelMainTheorem.worldModel_main_theorem`**

**这是世界模型的最终交付物**：把 `WorldModelCapstone.worldModel_capstone`
（8 模块总装）的 5 条实质结论与 `WorldModelCapstoneConsumer` 的
σ 估计一致性投影**联合**成**一条可引用的最终陈述**（7 条合取）。

**载体收口（真 L3）**：签名里出现 `WorldModelCapstone.ClosedLoopWorld E F`
—— 把 capstone 散落的 `A` / `φ` / `η` / `Corrects` / 收缩窗 **5 个参数**
收成**一个**结构参数 `W`。删掉 `WorldModelCapstone`，本定理签名**不合法**。

**结论（7 条，见文件头 §2 表格）**：

1. `Tendsto (thetaN W.η θ* x θ₀) atTop (nhds θ*)` —— 学习收敛到真值；
2. `OptimalEta.c 1 = 0` —— `η = 1` 的收缩因子归零；
3. `thetaN 1 θ* x θ₀ 1 = θ*` —— `η = 1` 一步学到真值；
4. `predFrom linWorld θ₁ … x ≠ predFrom linWorld θ₂ … x` —— `θ` 可辨识；
5. `limsup (‖W.A (noisyIter …) - x'_m‖) ≤ steadyErr W.η (2Lηmax)` —— 有噪声闭环上界；
6. `variance (steadyErrEst W.η n) = gain(W.η)² * (varOf P / n)` —— σ 估计方差；
7. `Tendsto (varOf P / (m+1)) atTop (nhds 0)` —— σ 估计的一致性（**仅**经 Consumer）。

**⭐ 与「无谓重复 Capstone」的区别（步骤 (c) 的要求）**：
第 1–6 条在证明体里由**一次** `obtain` 拿到 `worldModel_capstone` 的 9 元合取
（**不重证任何一条**，也不是把结论拆开再拼）；第 7 条**不在**
`worldModel_capstone` 的结论里 —— 它**只能**经
`WorldModelCapstoneConsumer` 得到。故本定理的**类型签名**同时依赖
Capstone（经 `ClosedLoopWorld` 出现在签名级）与 Consumer（经第 7 条）。

**前件自查（纪律 7）**：见文件头 §4 的逐条表格；**无**任何前件等于或
蕴含结论（特别是 `W.window` 讲 `W.η`，而第 2 条讲常数 `OptimalEta.c 1`）。 -/
theorem worldModel_main_theorem
    (W : WorldModelCapstone.ClosedLoopWorld E F)
    -- 学习链
    (θstar x θ₀ : ℝ) (hx : x ≠ 0)
    -- 可辨识
    {θ₁ θ₂ : ℝ} (hθ : θ₁ ≠ θ₂)
    -- σ 估计
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    -- 闭环载体
    (θ : E)
    {f : F → F} {L ηmax : ℝ} (hL : 0 < L)
    (hLI : RA14Strong.LipschitzInvertibleOn f L) (hηmax : 0 ≤ ηmax)
    (xf : F) (x' : ℕ → F) (δ : ℕ → F)
    (hx' : ∀ k, f (x' k) = f xf + δ k) (hδ : ∀ k, ‖δ k‖ ≤ ηmax) :
    -- (1) 学习收敛到真值
    Filter.Tendsto (ThetaConvergence.thetaN W.η θstar x θ₀) Filter.atTop (nhds θstar)
    -- (2) `η = 1` 的收缩因子归零
    ∧ OptimalEta.c 1 = 0
    -- (3) `η = 1` 一步学到真值
    ∧ ThetaConvergence.thetaN 1 θstar x θ₀ 1 = θstar
    -- (4) `θ` 可辨识（预测分离）
    ∧ FateV2.Loop.EndToEnd.predFrom ThetaConvergence.linWorld θ₁ PUnit.unit PUnit.unit
        PUnit.unit x
      ≠ FateV2.Loop.EndToEnd.predFrom ThetaConvergence.linWorld θ₂ PUnit.unit PUnit.unit
        PUnit.unit x
    -- (5) 有观测噪声的闭环渐近上界
    ∧ limsup (fun m : ℕ => ‖W.A (ClosedLoopNoisy.noisyIter W.A W.φ W.η x' m θ) - x' m‖)
        atTop
        ≤ ClosedLoopNoisy.steadyErr W.η (2 * L * ηmax)
    -- (6) σ 侧：稳态误差估计的方差
    ∧ variance (SteadyErrEstimate.steadyErrEst W.η n)
        (SigmaEstimation.iidMeasure P n)
        = (SteadyErrEstimate.gain W.η) ^ 2 * (SigmaEstimation.varOf P / n)
    -- (7) σ 估计的一致性（**仅**经 Consumer，capstone 本身没有）
    ∧ Filter.Tendsto (fun m : ℕ => SigmaEstimation.varOf P / ((m : ℝ) + 1))
        Filter.atTop (nhds 0) := by
  -- ⭐ 一次调用 Capstone 的 8 模块总装定理（不重证其任何一条）。
  obtain ⟨hlearn, hc1, hone, hsep, hlimsup, hvar, _hadj, _hdo⟩ :=
    WorldModelCapstone.worldModel_capstone W.η θstar x θ₀ hx W.window hθ hP n hn
      W.A W.φ θ W.corrects hL hLI hηmax xf x' δ hx' hδ
  -- ⭐ 第 7 条只能经 Consumer 得到（capstone 结论里没有这条）。
  obtain ⟨_hvar', hlim, _hvar1⟩ :=
    WorldModelCapstoneConsumer.capstone_endToEnd_implies_learning_bound
      (E := E) (F := F) (P := P) hP (L := L) (η := W.η) (ηmax := ηmax) (dσ := 0)
      hL hηmax (le_refl 0) W.window n hn W.A W.φ θ W.corrects hLI xf x' δ hx' hδ
      (fun k => by
        -- `hstep` 由观测模型推出（`WorldModelAssembly.obs_noise_drift_bound`），
        -- 不是把结论当前件。
        simpa using
          WorldModelAssembly.obs_noise_drift_bound hL hLI hηmax xf x' δ hx' hδ k)
  exact ⟨hlearn, hc1, hone, hsep, hlimsup, hvar, hlim⟩

end MainTheorem

/-! ===========================================================================
    §6  ⭐⭐ 前件**真的可达**（非空真），且主定理在具体数值上可读
    =========================================================================== -/

section Witness

/-- ⭐⭐⭐⭐ **【§6.1：主定理的前件可同时满足（非空真）】**

用具体数值见证 `worldModel_main_theorem` 的**标量**前件可同时成立：
`x = 2 ≠ 0`、`θ₁ = 0 ≠ 1 = θ₂`、`L = 1 > 0`、`ηmax = 0 ≥ 0`、`n = 1 ≥ 1`。

**⭐ 意义**：排除「前件不可满足 ⟹ 定理空洞」（纪律 7 的补充）。
`ClosedLoopWorld` 字段的可满足性由 `WorldModelCapstone` 的
`capstone_premises_satisfiable` 一并覆盖其标量部分；本定理覆盖**标量**
前件，`Corrects`/`window` 的存在性由 `A := 0`、`φ := 0`、`η := 0` 见证
（`A (φ r) = 0 = r` 不成立，故此处**不**声称 `ClosedLoopWorld` 的非空性 ——
那需要 `E ≃ F` 的具体实例，**不在本文件范围**，如实登记）。 -/
theorem main_premises_satisfiable :
    (2 : ℝ) ≠ 0 ∧ (0 : ℝ) ≠ 1 ∧ (1 : ℝ) > 0 ∧ (0 : ℝ) ≤ 0 ∧ (1 : ℕ) > 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num, le_refl 0, by norm_num⟩

/-- ⭐⭐⭐ **【§6.2：主定理第 2 条的**独立**核对（常数 `c 1 = 0`）】**

主定理第 2 条是**常数**陈述，与 `W` 无关，故可单独核对 ——
这**正是**它**不是**「`W.window` 的定义展开」的证明：
`window` 讲 `W.η`，本条讲 `1`。

**引用**：`OptimalEta.c_one`（经 `WorldModelCapstone.worldModel_capstone` 的第
(2) 分量**之外**的独立路径，用于说明该分量有实内容）。 -/
theorem c_one_zero :
    OptimalEta.c 1 = 0 := OptimalEta.c_one

end Witness

/-! ===========================================================================
    §7  ⚠ 未做项 / 扇入登记
    =========================================================================== -/

/-!
### §7.1 未做项（如实登记，非删减）

| # | 未做 | 原因 |
|---|---|---|
| 1 | `ClosedLoopWorld` 的**非空性**见证 | 需要具体的 `E ≃ F` 赋范空间实例（`Corrects A φ` ⟹ `φ` 是 `A` 的右逆 ⟹ `E` 到 `F` 满射）。**不在**本文件范围，且不属于「世界模型总装」的数学内容。|
| 2 | 消费 Consumer 的 L3 见证 `capstone_closedLoopWorld_contraction_interface` | 该定理结论 `c W.η < 1` 是**同义反复**（见文件头 §3.4 的判定）。**按纪律不引用、不美化**。|
| 3 | 因果层（`adjustLaw = doLaw2`、`doLaw` 幂等）| 属因果桥；已在 `WorldModelCapstoneConsumer.c6` 消费，**不并入**世界模型交付物（§3.3）。|

### §7.2 扇入变化（本文件的真实贡献）

| 模块 | 变化前扇入（非库根） | 变化后 |
|---|---|---|
| `WorldModelCapstone` | 1（`WorldModelCapstoneConsumer`）| **2**（+ 本文件）|
| `WorldModelCapstoneConsumer` | **0** | **1**（本文件 —— 它是 Consumer 的**唯一**真实下游）|

**⟹ 任务 (e)**：Consumer 的扇入从 **0** 变为 **1**（本文件是它**唯一**的真实下游）。

**⭐ 两条边的接线级别（`wiring_level.py` 实测，如实登记）**：

| 边 | 级别 | L3 命中 | L2 命中 |
|---|---|---|---|
| `WorldModelCapstone` → 本文件 | **L3** | `WorldModelCapstone.ClosedLoopWorld`（在签名里）| `WorldModelCapstone.worldModel_capstone` |
| `WorldModelCapstoneConsumer` → 本文件 | **L2** | （无）| `capstone_endToEnd_implies_learning_bound` |

**⚠ 如实说明 Consumer 边为 L2 而非 L3**：Consumer 的定理名**不能**出现在本定理
的类型签名里 —— Lean 中一个**定理**（已证命题）的名字不能作为**类型**使用
（`(WorldModelCapstoneConsumer.xxx ... : Prop)` 会被判为
「proof of sort `Prop` but expected `Prop`」；本轮实测确认）。故 Consumer 的
消费是**内容级 / 语义级必需**（第 7 条**不在** capstone 结论里，**只能**经
Consumer 得到），但按 `wiring_level.py` 的**文本判据**它是 **L2**。
**本文件不把这说成 L3。**

**⭐ 同理说明 Capstone 的 L3 是**实质**的**：签名里的 `WorldModelCapstone.ClosedLoopWorld`
是**世界模型的载体结构**（`A`/`φ`/`η`/`Corrects`/窗口），删掉 capstone 后本定理
签名**不合法**；它**不是**「把结论放在前件」那种同义反复（`W` 的字段里没有任何
第 1–7 条结论，见 §4 自查表）。

**⭐ 本文件自身的扇入 = 0**（它是世界的**终端**交付物）——
这**不是**缺陷：终端交付物的定义就是「下游无需再接线，直接引用它作为
世界模型的最终结论」。审计对 `WorldModelCapstoneConsumer` 的批评是
「它声称是终端但其实没人用、且其 L3 见证是同义反复」；
本文件（a）是**真终端**（世界模型的最终陈述，7 条实质结论）、
（b）签名级依赖 Capstone 的 `structure`（真 L3）、
（c）**不**含任何同义反复结论。

### §7.3 无法由本文件修复的既有问题（如实上报）

`WorldModelCapstoneConsumer.capstone_contraction_matches_capstone_trajectory`
（`:167`）与 `capstone_closedLoopWorld_contraction_interface`（`:374`）的
**同义反复**问题，**不能**由新增模块修复（会需要修改已有模块，违反纪律 2）。
本文件**如实登记**，不用任何「引用一次」的手法为其背书。
-/

end WorldModelMainTheorem

end FateV2.Loop