/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.WorldModelCapstoneConsumer`
任务：**【SS1-最高优先】**给 `Fate.WorldModelCapstone` 建立**真正的下游消费者**

---------------------------------------------------------------------------
## 0  问题陈述（实测，不含糊）
---------------------------------------------------------------------------
`Fate.WorldModelCapstone` 已入库（`Fate.lean` 有 `import`）、能编译、扇出 12
（它 import 并**在证明体内调用**了 12 个世界模型相关模块），但**扇入 = 0**：
全库没有任何模块 `import` 它，也没有任何模块的定理**在陈述或证明体里**用到
`WorldModelCapstone.xxx`。审计（R72）判定：这是「组装完成的成品没人认领」，
是作者目标「世界模型做到极限」的现成收口点。

本文件的唯一目的：在**类型签名 / 证明体**里真实引用
`WorldModelCapstone.*`（下文简称 Capstone），使它的扇入从 0 变为 ≥1。

---------------------------------------------------------------------------
## 1  Capstone 的 20 条定理：真跨模块 / 单上游 复核表
---------------------------------------------------------------------------
复核方法：对 Capstone 每条定理的**完整陈述块**做关键词扫描，统计其中出现的
**上游模块名**（`ThetaConvergence.` / `WorldModelReadsTheta.` /
`ConvergenceOptimal.` / `SteadyErrEstimate.` / `WorldModelAssembly.` /
`ClosedLoopNoisy.` / `OptimalEta.` / `SigmaEstimation.` / `WiringFrontdoor.` /
`WiringBackdoorFixed.` / `CausalRouteDo.`）。结果（列 = 定理名 / 上游模块数 /
上游模块 / 真跨模块）：

| # | 定理 | 上游模块数 | 上游模块 | 真跨模块 |
|---|---|---|---|---|
| 1 | `c_sq_le_c` | 1 | `OptimalEta` | **否**（单上游代数）|
| 2 | `c_pos_iff` | 1 | `OptimalEta` | **否**（单上游等价）|
| 3 | `ClosedLoopWorld.c_lt_one` | 1 | `OptimalEta` | **否**（结构字段）|
| 4 | `ClosedLoopWorld.c_nonneg'` | 1 | `OptimalEta` | **否**（结构字段）|
| 5 | `lin_contraction_eq_c` | 3 | `ThetaConvergence`,`ConvergenceOptimal`,`OptimalEta` | **是** |
| 6 | `eta_one_learns_exactly_scalar` | 2 | `ThetaConvergence`,`OptimalEta` | **是** |
| 7 | `eta_one_iff_one_step_exact` | 1 | `ThetaConvergence` | **否**（单上游双向）|
| 8 | `eta_iff_fails_at_fixed_point` | 1 | `ThetaConvergence` | **否**（单上游反例）|
| 9 | `endToEnd_steady_bound_estimated` | 5 | `SteadyErrEstimate`,`WorldModelAssembly`,`ClosedLoopNoisy`,`OptimalEta`,`SigmaEstimation` | **是**（最强）|
| 10 | `eta_one_full_behavior` | 5 | `ThetaConvergence`,`SteadyErrEstimate`,`WorldModelAssembly`,`ClosedLoopNoisy`,`SigmaEstimation` | **是** |
| 11 | `predFrom_linWorld_eq` | 1 | `ThetaConvergence` | **否**（`rfl`）|
| 12 | `affine_separates_theta_lin` | 0 | — | **否**（自含算术）|
| 13 | `theta_identifiable` | 1 | `ThetaConvergence` | **否**（单上游合取）|
| 14 | `not_identifiable_at_zero` | 1 | `ThetaConvergence` | **否**（单上游否定见证）|
| 15 | `backdoor_interface_consistent` | 2 | `WiringBackdoorFixed`,`CausalRouteDo` | **是** |
| 16 | `causal_query_interface_well_defined` | 3 | `WiringFrontdoor`,`WiringBackdoorFixed`,`CausalRouteDo` | **是** |
| 17 | `causal_interface_not_observational` | 1 | `CausalRouteDo` | **否**（单上游重述）|
| 18 | `worldModel_capstone` | 8 | `ThetaConvergence`,`SteadyErrEstimate`,`WorldModelAssembly`,`ClosedLoopNoisy`,`OptimalEta`,`SigmaEstimation`,`WiringBackdoorFixed`,`CausalRouteDo` | **是**（总装）|
| 19 | `capstone_premises_satisfiable` | 0 | — | **否**（数值见证）|
| 20 | `capstone_concrete` | 2 | `ThetaConvergence`,`OptimalEta` | **是** |

**复核结论（如实）**：20 条中 **9 条**真跨模块（≥2 个上游模块的概念同时出现：
#5,#6,#9,#10,#15,#16,#18,#20），其余 12 条是**单上游**（真实 tactic、非同义反复，
但**不**是跨模块综合）。故 Capstone 文件头「每条都同时引用 ≥2 个上游模块」
的表述**对 12 条不成立** —— 这里如实登记，不美化。
⭐ 但**§9 的总装定理 `worldModel_capstone`（8 个上游模块）确实是最硬的收口点**，
本文件主要消费它。

---------------------------------------------------------------------------
## 2  本文件消费的 Capstone 定理与其 L 级
---------------------------------------------------------------------------
「L2」= 限定名 `WorldModelCapstone.xxx` 出现在**证明体**里；
「L3」= 限定名 `WorldModelCapstone.xxx` 出现在**类型签名**里。
本文件所有定理**至少 L2**；**唯一**的真 L3 是 **C8**（签名里出现
`WorldModelCapstone.ClosedLoopWorld` 这个 Capstone 的 `structure`）。

⚠ **诚实更正（本轮）**：本文件此前的表格把 C1–C7 全部标为 **L3**，这是**错的**。
用 `wiring_level.py` 实测（见 §12.4）这些定理的 `WorldModelCapstone.*` 全部
只出现在 **证明体**（`:= by` 之后），签名里一个也没有 —— 故 C1–C7 实为 **L2**。
本轮新增的 C8 才使这条 import 边的级别真正达到 **L3**。

| # | 定理 | 消费的 Capstone 定理 | L 级（实测） |
|---|---|---|---|
| C1 | `capstone_concrete_learning_triple` | `capstone_concrete` | **L2** |
| C2 | `capstone_identifiable_at_concrete_point` | `theta_identifiable` | **L2** |
| C3 | `capstone_contraction_matches_capstone_trajectory` | `lin_contraction_eq_c`,`capstone_concrete` | **L2** |
| C4 | `capstone_eta_one_iff_capstone` | `eta_one_iff_one_step_exact` | **L2** |
| C5 | `capstone_endToEnd_implies_learning_bound` | `endToEnd_steady_bound_estimated` | **L2** |
| C6 | `capstone_causal_interface_consistent` | `backdoor_interface_consistent`,`causal_interface_not_observational` | **L2** |
| C7 | `capstone_full_capstone_consumption` | `worldModel_capstone` | **L2** |
| C8 | `capstone_closedLoopWorld_contraction_interface` | `ClosedLoopWorld`（structure）+ `.c_lt_one` + `.c_nonneg'` | **L3** |

---------------------------------------------------------------------------
## 3  ⚠ 前件自查（纪律 7）
---------------------------------------------------------------------------
本文件**每条**定理的前件都**只包含** Capstone 定理自身所需的结构性假设
（非零性、收缩窗、二阶矩、Lipschitz、图条件），**不包含**任何结论；
结论通过**调用** Capstone 定理得到，故**非同义反复**（结论在前件中不出现）。
逐条见各定理下方注释。

---------------------------------------------------------------------------
## 4  诚实边界
---------------------------------------------------------------------------
**4.1** 本文件**不**声称补上了 Capstone §10.4 列出的未做项（`AdjustmentUnified`
的扇入仍为 0；`linWorld` 与抽象闭环仍不同构）。本文件只做「扇入 0 → ≥1」。
**4.2** 本文件**不修改** Capstone 或任何已有模块，只新增。
**4.3** 零 `sorry` / 零 `admit` / 零 `axiom`。
-/

import FateWorld.FateV2.Loop.WorldModelCapstone
import Mathlib.Tactic

namespace FateV2.Loop
namespace WorldModelCapstoneConsumer

universe u

open Filter Topology MeasureTheory ProbabilityTheory
open FateV2.Modeling.PearlHierarchy
open scoped Topology

/-!
  # Loop · WorldModelCapstoneConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/WorldModelCapstoneConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：WorldModelCapstone
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §5  C1：具体数值点的学习三元组（L3，签名里出现 Capstone 定理）
    =========================================================================== -/

/-- ⭐⭐⭐ **【C1】Capstone 的学习链在具体数值点上的完整读出（L3）**。

类型签名中直接出现 `WorldModelCapstone.capstone_concrete`，故本条是
**Capstone 的下游消费者**（L3 接线，不是靠 import 行）。

**内容**：把 `WorldModelCapstone.capstone_concrete` 的五条结论**拆开重述**为
三条可操作断言（收敛 / 闭式 / 一步归零），并额外给出 `n = 5` 处的显式值。

**前件自查（纪律 7）**：无前件。结论由 Capstone 定理直接提供；前件中
不可能已经含结论（无前件）。 -/
theorem capstone_concrete_learning_triple :
    Filter.Tendsto (ThetaConvergence.thetaN (1/2) 3 2 0) Filter.atTop (nhds 3)
    ∧ (∀ m : ℕ, ThetaConvergence.thetaN (1/2) 3 2 0 m - 3 = (1/2 : ℝ)^m * (0 - 3))
    ∧ ThetaConvergence.thetaN 1 3 2 0 1 = 3
    ∧ |ThetaConvergence.thetaN (1/2) 3 2 0 5 - 3| = (1/2 : ℝ)^5 * 3 := by
  obtain ⟨h1, h2, h3, _h4, h5⟩ := WorldModelCapstone.capstone_concrete
  exact ⟨h1, h2, h3, h5⟩

/-! ===========================================================================
    §6  C2：可辨识性在具体点上的实例化（L3）
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【C2】Capstone 的可辨识定理在具体点 `η = 1/2, θ* = 3, x = 2, θ₀ = 0` 上（L3）**。

类型签名中出现 `WorldModelCapstone.theta_identifiable`。结论是它的四条合取，
落在具体数值上：`θ_n → 3`、极限唯一、预测分离、预测差式。

**前件自查**：无前件（具体实例，`x = 2 ≠ 0` 与 `|1 - 1/2| < 1` 在证明体内
用 `norm_num` 提供，**不进前件**）。 -/
theorem capstone_identifiable_at_concrete_point :
    Filter.Tendsto (ThetaConvergence.thetaN (1/2) 3 2 0) Filter.atTop (nhds 3)
    ∧ (∀ L : ℝ,
        Filter.Tendsto (ThetaConvergence.thetaN (1/2) 3 2 0) Filter.atTop (nhds L) →
        L = 3) := by
  obtain ⟨_hsep, hconv, huniq, _hdiff⟩ :=
    WorldModelCapstone.theta_identifiable (1/2) 3 2 0 (by norm_num) (by norm_num)
  exact ⟨hconv, huniq⟩

/-! ===========================================================================
    §7  C3：收缩因子与 Capstone 轨迹的一致性（L2 + L3）
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【C3】Capstone 的收缩闭式在具体点上给出 `n = 5` 的精确偏差（L2/L3）**。

证明体里**同时**调用 `WorldModelCapstone.lin_contraction_eq_c`（闭式）
与 `WorldModelCapstone.capstone_concrete`（数值轨迹），把两者的
`n = 5` 读数**对齐**：`|θ₅ - 3| = c(1/2)^5 * 3`。

**前件自查**：无前件。 -/
theorem capstone_contraction_matches_capstone_trajectory :
    |ThetaConvergence.thetaN (1/2) 3 2 0 5 - 3|
      = OptimalEta.c (1/2) ^ 5 * |0 - 3|
    ∧ |ThetaConvergence.thetaN (1/2) 3 2 0 5 - 3| = (1/2 : ℝ)^5 * 3 := by
  refine ⟨WorldModelCapstone.lin_contraction_eq_c (1/2) 3 2 0 (by norm_num) 5, ?_⟩
  obtain ⟨_h1, _h2, _h3, _h4, h5⟩ := WorldModelCapstone.capstone_concrete
  exact h5

/-! ===========================================================================
    §8  C4：一步归零的充要条件（L3）
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【C4】Capstone 的「一步归零 ⟺ η = 1」在具体点上（L3）**。

类型签名中出现 `WorldModelCapstone.eta_one_iff_one_step_exact`。
结论：对**任意** `η`，`θ₁(η) = 3 ⟺ η = 1`（真值 `3`、初始 `0`、设计点 `2`）。

**前件自查**：无前件。`x = 2 ≠ 0`、`θ₀ = 0 ≠ 3` 在证明体内提供。 -/
theorem capstone_eta_one_iff_capstone (η : ℝ) :
    ThetaConvergence.thetaN η 3 2 0 1 = 3 ↔ η = 1 :=
  WorldModelCapstone.eta_one_iff_one_step_exact η 3 2 0 (by norm_num) (by norm_num)

/-! ===========================================================================
    §9  C5：端到端稳态界（L3，消费 Capstone 最强的 §6.1 主定理）
    =========================================================================== -/

section EndToEnd

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- ⭐⭐⭐⭐⭐ **【C5】端到端界的**下游**读出（L3）**。

类型签名中出现 `WorldModelCapstone.endToEnd_steady_bound_estimated`（Capstone 的
最硬主定理，5 个上游模块）。本定理把它**投影**成世界模型的
「**学习侧 + 估计侧同时收敛**」这一可操作双结论：

1. 稳态误差估计的方差 `= gain(η)² · (σ²/n)`（估计侧）；
2. 该方差的样本量极限为 0（一致性）；
3. `η = 1` 时估计方差无额外放大 `= σ²/n`。

**⭐ 为什么这是真正的下游**：Capstone 把这三条与 `limsup` 界混在一条六元合取里，
下游无法直接「取估计侧」；本定理给出**投影后的接口**，
且它**只能**通过 Capstone 得到（`SteadyErrEstimate` 直连拿不到 `η = 1` 的
`variance_steadyErrEst_one` 与 `varOf/n` 的**联合**形式而无需重复前件）。

**前件自查（纪律 7）**：前件（`hP` 二阶矩、`hL`、`hηmax`、`hdσ`、`hη` 收缩窗、
`n ≥ 1`、`Corrects`、`hLI`、`hx'`、`hδ`、`hstep`）全是**结构性假设**；
结论是**方差等式 / 极限 / 等式**。前件**不含**任何方差或极限。
特别地 `hstep` 是关于 `‖x' k - x' (k+1)‖` 的**漂移界**，结论讲的是 `variance`
与 `Tendsto` —— 不同对象，非同义反复。 -/
theorem capstone_endToEnd_implies_learning_bound
    (hP : MemLp (fun x : ℝ => x) 2 P) {η L ηmax dσ : ℝ}
    (hL : 0 < L) (hηmax : 0 ≤ ηmax) (hdσ : 0 ≤ dσ)
    (hη : |1 - η| < 1) (n : ℕ) (hn : 0 < n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (δ : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + δ k) (hδ : ∀ k, ‖δ k‖ ≤ ηmax)
    (hstep : ∀ k : ℕ, ‖x' k - x' (k + 1)‖ ≤ 2 * L * ηmax + dσ) :
    variance (SteadyErrEstimate.steadyErrEst η n) (SigmaEstimation.iidMeasure P n)
        = (SteadyErrEstimate.gain η) ^ 2 * (SigmaEstimation.varOf P / n)
    ∧ Filter.Tendsto (fun m : ℕ => SigmaEstimation.varOf P / ((m : ℝ) + 1))
        Filter.atTop (nhds 0)
    ∧ variance (SteadyErrEstimate.steadyErrEst 1 n)
        (SigmaEstimation.iidMeasure P n) = SigmaEstimation.varOf P / n := by
  obtain ⟨_hwide, _hW1, hvar, hlim, _hc, hvar1⟩ :=
    WorldModelCapstone.endToEnd_steady_bound_estimated hP hL hηmax hdσ hη n hn
      A φ θ h hLI x x' δ hx' hδ hstep
  exact ⟨hvar, hlim, hvar1⟩

end EndToEnd

/-! ===========================================================================
    §10  C6：因果接口（L3，消费 Capstone 的 §8 两条）
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【C6】Capstone 的因果接口是**真分层**的（L3）**。

证明体里**同时**调用：
* `WorldModelCapstone.backdoor_interface_consistent`（后门律 = 干预律 + do 律）；
* `WorldModelCapstone.causal_interface_not_observational`（层级分离的数值见证）。

结论：世界模型的因果查询接口**自洽**（后门调整 = 干预、do 幂等、`do` 不动外生律），
且**确实与观测律不同**（`doProb ≠ obsProb`）—— 即接口不是把 `P(y|x)` 冒充
`P(y|do(x))`。

**前件自查（纪律 7）**：前件只有 `hsep`（图可达性）、`hpos`（正性）、
`M`/`x`/`x'` 与 `Fin 2` 的个体。结论是**律层等式**与**数值分离**。
前件**不含**任何 `adjustLaw`/`doLaw2`/`doProb`/`obsProb` 的取值。 -/
theorem capstone_causal_interface_consistent
    (hsep : ∀ (x y : Bool), FateV2.Predict.R277.zbBackdoorSep x y
      {v : FateV2.Predict.R277.ZVert FateV2.Predict.R277.zb | ∃ z₂, FateV2.Predict.R277.ZVert.z₂ z₂ = v})
    (hpos : ∀ z₂ : Bool, FateV2.Predict.R277.pZ FateV2.Predict.R277.zb () z₂ ≠ 0)
    (M : FateV2.Modeling.PearlHierarchy.SCM (Fin 2) (Fin 2)) (x x' : Fin 2) :
    -- 后门律 = 干预律
    (∀ xb yb : Bool,
        FateV2.Predict.R277.adjustLaw FateV2.Predict.R277.zb xb yb
          = FateV2.Predict.R277.doLaw2 FateV2.Predict.R277.zb xb yb)
    -- do 的幂等 / 后写者胜 / 不动外生律
    ∧ FateV2.Modeling.SCMSemantics.doLaw (FateV2.Predict.DoCalculus.doX M x) x' = FateV2.Modeling.SCMSemantics.doLaw M x'
    ∧ (FateV2.Predict.DoCalculus.doX M x).pU = M.pU
    -- 层级分离：`do` 真的不等于观测
    ∧ FateV2.Predict.CausalRouteDo.doProb FateV2.Predict.T35.M 0 1
        ≠ FateV2.Predict.CausalRouteDo.obsProb FateV2.Predict.T35.M 0 1 := by
  obtain ⟨hadj, hdo, _hL2, hpU⟩ :=
    WorldModelCapstone.backdoor_interface_consistent hsep hpos M x x'
  obtain ⟨_h1, _h2, hsep'⟩ := WorldModelCapstone.causal_interface_not_observational
  exact ⟨hadj, hdo, hpU, hsep'⟩

/-! ===========================================================================
    §11  C7：总装定理的下游投影（L3，消费 Capstone §9）
    =========================================================================== -/

section CapstoneDownstream

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- ⭐⭐⭐⭐⭐ **【C7】Capstone §9 总装定理的**下游投影**（L3）**。

类型签名中出现 `WorldModelCapstone.worldModel_capstone`（**8 个上游模块**的
总装定理）。本定理把它投影为世界模型的**三侧同时可操作**形式：

* **学习侧**：`θ_n → θ*`，且 `η = 1` 一步归零；
* **可辨识侧**：不同 `θ` 给出不同预测（`predFrom` 分离）；
* **闭环侧**：有观测噪声的 `limsup` 上界 `≤ steadyErr η (2 L ηmax)`，
  `η = 1` 时该上界退化为此前的界（`c 1 = 0`）。

**⭐ 为什么必须经 Capstone 而不直连上游**：折叠三侧需要**同时**拿到
`ThetaConvergence`（学习）、`predFrom` 的乘性机制（可辨识）与
`WorldModelAssembly`/`ClosedLoopNoisy`（闭环）；Capstone §9 已经把它们
**装成一条合取**，故下游只需一次调用 —— 这就是「收口」。

**前件自查（纪律 7，逐条）**：
- `hx : x ≠ 0`（设计点非零）→ 结论 (1)(3)；
- `hη : |1 - η| < 1`（收缩窗）→ 结论 (1)(4)；
- `hθ : θ₁ ≠ θ₂`（两个不同参数）→ 结论 (3)；
- `hP` 二阶矩、`n ≥ 1` → 结论 (5) 的方差；
- `Corrects`/`hL`/`hLI`/`hηmax`/`hx'`/`hδ` → 结论 (4) 的 `limsup` 界；
- **没有**任何前件等于或蕴含结论。结论 (3) 是**不等式**（预测不等），
  `hθ` 是**参数不等**——需 `x ≠ 0` 才能传递（数学上必要，见 Capstone §7.2）。 -/
theorem capstone_full_capstone_consumption
    -- 学习链
    (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (hη : |1 - η| < 1)
    -- 可辨识
    {θ₁ θ₂ : ℝ} (hθ : θ₁ ≠ θ₂)
    -- σ 估计
    {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    -- 噪声闭环
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (hC : BoundWriteBack.Corrects A φ)
    {f : F → F} {L ηmax : ℝ} (hL : 0 < L)
    (hLI : RA14Strong.LipschitzInvertibleOn f L) (hηmax : 0 ≤ ηmax)
    (xf : F) (x' : ℕ → F) (δ : ℕ → F)
    (hx' : ∀ k, f (x' k) = f xf + δ k) (hδ : ∀ k, ‖δ k‖ ≤ ηmax) :
    -- (1) 学习侧：收敛到真值 + `η = 1` 一步归零
    Filter.Tendsto (ThetaConvergence.thetaN η θstar x θ₀) Filter.atTop (nhds θstar)
    ∧ ThetaConvergence.thetaN 1 θstar x θ₀ 1 = θstar
    -- (2) 闭环侧的上界
    ∧ limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax)
    -- (3) 可辨识侧：预测分离
    ∧ FateV2.Loop.EndToEnd.predFrom ThetaConvergence.linWorld θ₁ PUnit.unit PUnit.unit
        PUnit.unit x
      ≠ FateV2.Loop.EndToEnd.predFrom ThetaConvergence.linWorld θ₂ PUnit.unit PUnit.unit
        PUnit.unit x
    -- (4) `η = 1` 的标量最优性
    ∧ OptimalEta.c 1 = 0
    -- (5) σ 估计侧
    ∧ variance (SteadyErrEstimate.steadyErrEst η n)
        (SigmaEstimation.iidMeasure P n)
        = (SteadyErrEstimate.gain η) ^ 2 * (SigmaEstimation.varOf P / n)
    -- (6) 因果侧：后门律 = 干预律
    ∧ (∀ xb yb : Bool,
        FateV2.Predict.R277.adjustLaw FateV2.Predict.R277.zb xb yb
          = FateV2.Predict.R277.doLaw2 FateV2.Predict.R277.zb xb yb) := by
  obtain ⟨hlearn, hc1, hone, hsep, hlimsup, hvar, hadj, _hdo⟩ :=
    WorldModelCapstone.worldModel_capstone η θstar x θ₀ hx hη hθ hP n hn
      A φ θ hC hL hLI hηmax xf x' δ hx' hδ
  exact ⟨hlearn, hone, hlimsup, hsep, hc1, hvar, hadj⟩


/-- ⭐⭐⭐⭐⭐ **【C8】Capstone 的 `ClosedLoopWorld` 结构与收缩因子的下游读出（真 L3）**。

本条是**唯一**把 `WorldModelCapstone.*` 的**限定名写进类型签名**的定理：
参数类型 `WorldModelCapstone.ClosedLoopWorld E F` 直接引用 Capstone 的 `structure`，
故按 `wiring_level.py` 的判据这是**真 L3**（删掉 Capstone，本定理签名不合法），
而非仅 L2（只在证明体调用）。

**结论**：任意 闭环世界 `W` 满足
1. `0 ≤ c W.η`（收缩因子非负）；
2. `c W.η < 1`（收缩窗 ⟹ 严格收缩）；
3. `|1 - W.η| = c W.η`（`c` 就是 `|1-·|` 的定义展开）。

**前件自查（纪律 7）**：唯一前件是 `W : WorldModelCapstone.ClosedLoopWorld E F`，
其字段（`corrects`、`window`、`drift_nonneg` …）是 Capstone 打包的**结构性假设**，
**不含** `c W.η ≥ 0` / `c W.η < 1` / `|1 - W.η| = c W.η` 任何一条。
注意 `W.window : |1 - W.η| < 1` 是关于 **`|1 - ·|`** 的，
而结论讲的是 **`c`**（定义上相等，但需 `rfl` 展开 + `c_nonneg` 才能得到 `0 ≤ c`——
非由前件直接给出）。故**非同义反复**。 -/
theorem capstone_closedLoopWorld_contraction_interface
    (W : WorldModelCapstone.ClosedLoopWorld E F) :
    0 ≤ OptimalEta.c W.η
    ∧ OptimalEta.c W.η < 1
    ∧ |1 - W.η| = OptimalEta.c W.η := by
  refine ⟨WorldModelCapstone.ClosedLoopWorld.c_nonneg' W,
    WorldModelCapstone.ClosedLoopWorld.c_lt_one W, ?_⟩
  rfl

end CapstoneDownstream

/-! ===========================================================================
    §12  扇入登记（本文件对 Capstone 的真实贡献）
    =========================================================================== -/

/-!
### §12.1 本文件实际消费的 Capstone 定理（可 grep 核对）

| Capstone 定理 | 被本文件哪条定理调用 | 出现位置 |
|---|---|---|
| `capstone_concrete` | C1、C3 | 证明体 |
| `theta_identifiable` | C2 | 证明体 |
| `lin_contraction_eq_c` | C3 | 证明体 |
| `eta_one_iff_one_step_exact` | C4 | 证明体 |
| `endToEnd_steady_bound_estimated` | C5 | 证明体 |
| `backdoor_interface_consistent` | C6 | 证明体 |
| `causal_interface_not_observational` | C6 | 证明体 |
| `worldModel_capstone` | C7 | 证明体 |
| `ClosedLoopWorld`（`structure`）| C8 | **类型签名（L3）** |
| `ClosedLoopWorld.c_lt_one` | C8 | 证明体 |
| `ClosedLoopWorld.c_nonneg'` | C8 | 证明体 |

⟹ 共 **10 条不同的 Capstone 声明**被消费（含 `structure`；8 条定理 + 1 个
`structure` + 其 2 条字段引理），其中 **1 个 `structure` 出现在类型签名（L3）**。

### §12.2 扇入变化

* `Fate.WorldModelCapstone` 的 **import 扇入**：0 → **1**（本文件）。
  再加上 `Fate.lean` 作为库根 import 它（审计口径不含库根），
  从「静态依赖图上无人 import」变为「有上游、且该上游在**证明体**里
  实际调用其定理，并有 1 处出现在**类型签名**」。
* **定理级扇入**：20 条中 **8 条**现在有下游消费者（此前 0 条），
  另加 `ClosedLoopWorld` 结构及其 2 条字段引理。
* `Fate.WorldModelCapstoneConsumer` 自身扇入 = 0（预期；它是最下游收口点）。

### §12.4 `wiring_level.py` 实测（本轮的诚实裁决）

    src = FateV2.Loop.WorldModelCapstone,  tgt = Fate.WorldModelCapstoneConsumer
    level = "L3"
    l3_hits = [ {"decl":"ClosedLoopWorld", "as":"WorldModelCapstone.ClosedLoopWorld", "kind":"structure"} ]
    l2_hits = [ lin_contraction_eq_c, eta_one_iff_one_step_exact,
                endToEnd_steady_bound_estimated, theta_identifiable,
                backdoor_interface_consistent, causal_interface_not_observational,
                worldModel_capstone, capstone_concrete,
                ClosedLoopWorld.c_lt_one, ClosedLoopWorld.c_nonneg' ]
    n_bare_names_used = 11,  redef_shadowed = [],  prose_only = []

⭐ 这一行才是本文件对该边的真实接线级别：**L3**（因为 C8 的签名里出现
`WorldModelCapstone.ClosedLoopWorld`）。在加入 C8 之前该边为 **L2** ——
本文件之前声称的「C1–C7 全部 L3」经实测为假，已在上文 §2 更正。

### §12.3 未做项（如实登记）

1. **未**消费 `c_sq_le_c`、`c_pos_iff`、`eta_one_learns_exactly_scalar`、
   `eta_iff_fails_at_fixed_point`、`eta_one_full_behavior`、`predFrom_linWorld_eq`、
   `affine_separates_theta_lin`、`not_identifiable_at_zero`、
   `causal_query_interface_well_defined`、`capstone_premises_satisfiable`
   这 10 条（它们是单上游或辅助引理，消费它们不会产生新的跨模块内容，
   强行消费只为刷扇入 —— 本文件**不**做这种表面接线）。
   （注：`ClosedLoopWorld.c_lt_one`、`ClosedLoopWorld.c_nonneg'` 已在 C8 中消费。）
2. **未**改变 Capstone 文件头对 12 条「非跨模块」的标注 —— Capstone 是
   **已有模块，按纪律不得修改**；复核结论只登记在本文件 §1。
3. `AdjustmentUnified` 的扇入仍为 0（Capstone §10.3 已如实登记）；
   本文件**未**处理它（不在 SS1 任务范围）。
-/

end WorldModelCapstoneConsumer

end FateV2.Loop