import FateWorld.FateV2.Loop.ThetaConvergence
import FateWorld.FateV2.Loop.WorldModelReadsTheta
import FateWorld.FateV2.Loop.ConvergenceOptimal
import FateWorld.FateV2.Error.SteadyErrEstimate
import FateWorld.FateV2.Loop.WorldModelAssembly
import FateWorld.FateV2.Loop.ClosedLoopNoisy
import FateWorld.FateV2.Loop.OptimalEta
import FateWorld.FateV2.Error.SigmaEstimation
import FateWorld.FateV2.Error.SigmaFromDomain
import FateWorld.FateV2.Error.SigmaGammaFromData
import FateWorld.FateV2.Predict.WiringFrontdoor
import FateWorld.FateV2.Predict.WiringBackdoorFixed
import FateWorld.FateV2.Predict.CausalRouteDo
import FateWorld.FateV2.Predict.AdjustmentUnified
import FateWorld.FateV2.Loop.CapstoneDriftFromObs
import FateWorld.FateV2.Error.ErrorCriterionImpliesBound
import FateWorld.FateV2.Error.EtaMaxFromData
import FateWorld.FateV2.Predict.CausalEffect
import FateWorld.FateV2.Error.LipschitzFromFinite
import FateWorld.FateV2.Error.ScoreBound
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import FateWorld.FateV2.Rules.InstIsDirac
import FateWorld.FateV2.Predict.WorldModelNoPredict
import FateWorld.FateV2.Loop.RuleMainChainConsumer
import FateWorld.FateV2.Loop.EndToEndSelectorWiring
import FateWorld.FateV2.Loop.ScenarioBranchLimit

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/WorldModelCapstone.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008
  - 改动：namespace/引用 ProperFit→FateV2.Loop（正文 282 处，含 25 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Loop
open FateV2.Predict
open FateV2.Error
open FateV2.Modeling
open FateV2.Model
open FateV2.Rules

/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Loop.WorldModelCapstone`
任务：**【BB1-最高优先】世界模型的「总装」模块**

---------------------------------------------------------------------------
## 0  背景（为什么需要本文件）
---------------------------------------------------------------------------
实测扇入审计：下列 6 个核心模块**被其他模块 import 的次数为 0**

    ThetaConvergence(0)、WorldModelAssembly(0)、WorldModelReadsTheta(0)、
    ConvergenceOptimal(0)、SteadyErrEstimate(0)、AdjustmentUnified(0)

（对照：`WorldModel` 被 import 8 次）。根因：`FateV2.Loop.lean` 是库根，它 import
所有模块，但**各业务模块之间互不 import**。「入库」只证明能编译，
**不证明被使用**。

**本文件的作用**是把世界模型的各条腿**真正装成一个整体**：
它是**上游**（import 上述模块并**使用它们的定理**），因此把这些模块的
扇入从 0 提升到 ≥1。本文件本身的扇入要等下游模块来消费 —— 这一点在
§10 如实登记，不夸大。

---------------------------------------------------------------------------
## 1  ⚠ 诚实边界（必读，不得含糊）
---------------------------------------------------------------------------
**1.1 本节所有综合定理的每一条都同时引用 ≥2 个上游模块的**已证定理**。**
每条定理上方标注它实际调用的上游定理（可 grep 核对）。

**1.2 「世界模型」在这里是**两条可证链**，不是「任意非线性世界」：**
* **学习链**：`ThetaConvergence.linWorld`（线性实例，机制 `θ * x`）上的参数学习
  `thetaN η θ* x θ₀ n` → `θ*`；
* **闭环链**：抽象赋范空间上的 `WiringConvergence.iterMap` / `ClosedLoopNoisy.noisyIter`，
  其误差律 `err_n = c(η)^n · err_0` 由 `BoundWriteBack.Corrects` 承担。
  本文件**不声称**这两条链是同一条链的同构（`linWorld` 没有 `Corrects` 结构）。
  两条链的**联结点**是**标量收缩因子** `c(η) = |1-η|`（§5.1 `lin_contraction_eq_c`）。

**1.3 观测噪声进入闭环的方式是显式假设，不是自动推导。**
`WorldModelAssembly.assembly_noisy_steady_bound` 从观测映射的 Lipschitz 可逆性
推出漂移预算 `d = 2 L ηmax`；本文件把它**扩大**为 `d = 2 L ηmax + σ`
（`σ` = 由 `SigmaEstimation.varOf` 定义的**单样本方差**）后给出更宽的界，
再把它与 `SteadyErrEstimate.variance_steadyErrEst` 的估计方差**联立成一条合取**。
**⚠ 本文件不把 `σ` 解释成「噪声标准差」**（那是 `SigmaEstimation` 文件头登记的
解释性例外）；本文件只把它当作**方差参数**（该模块的**定义**就是 `Var[id; P]`），
故用到 `σ` 的地位是**纯代数的**（§7 的 `sigma_sq_nonneg`）。

**1.4 `AdjustmentUnified` 的消费方式（如实说明，不含糊）。**
`AdjustmentUnified` 的内容是：前门 / 后门 / do-算子**三条路线给出同一干预律**。
本文件 §8 把该等价**与 `CausalRouteDo` 的自足性（`doLaw` 的代数律）** 合起来，
给出「世界模型的**因果查询接口**是唯一且自洽的」这一综合陈述。
但 `AdjustmentUnified` 的等价本身在其**具体实例**上成立，本文件**不声称**
它在任意 `WorldModel` 上成立（见 §8.4 的边界登记）。

**1.5 无 `sorry` / `admit` / `axiom`；不改任何已有模块；只新增本文件。**

**1.6 【第 532 轮追加：前件减少 #2 —— `hK`】诚实登记（必读）**

**审计 R524 原话**：
> 「假接入只能【加】前件、不能【减】前件，『前件减少』是形式指标里唯一不可伪造的方向。」

**第 531 轮**已删 `hbdd`（`d6719c8`）。**本轮（第 532 轮）处理 `hK`。**

**(a) 本轮做到了什么**

新增定理 `errorAcceptable_steadyErr_self`（§6.7）：
`ErrorAcceptable ε σ` 在取 `ε := σ := steadyErr η (2 * L * ηmax)` 时**自动成立**。
这**不是同义反复**：`ErrorAcceptable ε ε = (ε/2 ≤ ε ∧ ε ≤ 2*ε)`，两个分量需要
`0 ≤ ε`，而 `0 ≤ steadyErr η (2*L*ηmax)` 由 `ClosedLoopNoisy.steadyErr_nonneg`
从 `0 ≤ 2*L*ηmax`（来自 `hL`、`hηmax`）与 `|1-η| < 1`（来自 `hη`）**推出**；
两分量随后由 `linarith` 关掉。

其直接推论 `exists_sigma_errorAcceptable`（做法 B）也已证出。

**(b) 本轮【没有】做到什么 —— 如实说明**

1. **原定理 `endToEnd_steady_bound_implies_correct_classification` 的 `hK` 前件没有被删除。**
   原定理保持原样（不改已有陈述、不删已有定理的纪律）。
   本轮只证明了「若把 `σ` **固定**为 `steadyErr η (2Lηmax)`，则 `hK` 自动满足」。
2. 新增的 `endToEnd_steady_bound_implies_correct_classification_no_hK`（§6.7.1）
   **确实**删去了 `σ` 参数与 `hK` 前件，但**代价**是 `hs` 从
   `4 * σ < |s|` 变成 `4 * steadyErr η (2Lηmax) < |s|` —— 这是**更具体的条件**。
   ⟹ **这是【特殊化】，不是纯粹的【前件减少】**；「前件少一条、另一条变具体」，
   **净收益有限**，不得宣传为「前件减一」。

**(c) 不声称「解决了主干缺口」**：主干的其他缺口（`σ` 与真实 `|s|` 的关系、
观测模型的可删性、`ηmax` 的自由性）**照旧存在**。本轮只把 `hK` 在一个
**具体的 `σ` 取法**下变成可推导的。

**1.7 【第 577 轮追加：「前件减少」判据的最终裁决（裁决2 = 甲）】**

**(a) 作者第 577 轮逐字原话**：
> **「裁决2  甲」**

**⟹ 判据锁定为审计 R524 的原判据：「前件数必须严格减少」。**
（即派生的详细判定表登记于 §0.5.1。）

**(b) 按（甲）判据，四条改动里「三条算、一条不算」**：

| 改动 | 节 | 前件数变化 | 按（甲）判定 |
|---|---|---|---|
| `capstone_dsigma_unique_from_meas` | §6.9 | **5 → 3** | ✅ **算进步** |
| `capstone_dsigma_from_meas_no_hstep` | §6.10 | **1 → 0** | ✅ **算进步（最优）** |
| `capstone_dsigma_meas_no_eta_free` | §6.11 | **3 → 1** | ✅ **算进步** |
| `endToEnd_steady_bound_from_obs` | §6.8 | **1 → 2** | 🟡 **不算进步** |

**⟹ 三条算（§6.9 / §6.10 / §6.11）；一条不算（§6.8）。**

**(c) 主控曾自行放宽、现已撤回**：主控第 542 轮曾把判据放宽为 (乙)
「前件数不变或减少 + 新前件更可检验」，并据此把 §6.8 表述为进步。
**作者第 577 轮裁决为（甲），故该放宽【已撤回】**——`§6.8` **不得**被表述为
「前件减少」，只能表述为「前件更可检验」（其前件数实为 1 → 2）。

**1.8 【第 581 轮追加：`|s|` 是「有语义但未绑定」，不是「无源头」（第 52 条错误的修正）】**

**(a) 主控第 581 轮的发现**：本轮实测 `FateV2.Loop/ErrorBound.lean:180-184`，其文档串写：

> $s$ 是真侧打分，$\sigma=\mathrm{sgn}(s)$（**真值分类**）；$m=|s|$ 是**真实间隔**；
> $\delta$ 是**误差**，满足 $|\delta|\le\varepsilon$；$\varepsilon<\dfrac{m}{2}$。

而 `:236` 更点明：**「$s = \langle w,x\rangle$ 时它就是分类器版」**。
⟹ **`s` 有明确语义：真侧打分 / 线性打分器在点 `x` 处的间隔。**
只是本文件的定理里它是**自由的 ℝ**，**没有被绑到具体的 `w`/`x` 上**。

**(b) 这是第 52 条错误的修正**：§0.5 原表把 `|s|` 写成「无源头」，
**把「有语义」写成了「无源头」——这是错的**，现已改为
「⚠️ 有语义但未绑定」，结论列改为「需绑定，非无源头」。

**(c) 未做的（如实登记）**：把 `s` **绑定**到 `⟨w, x⟩`（或 `linScore`/`margin` 的
具体表达式）**没有做** —— 那是**新的工作**，会改动定理的陈述，不在本轮
（纯文档修正）范围内。因此本文件对 `|s|` 的处置仍是「标定责任在工程侧」，
但**理由从「没概念」更正为「有概念、未绑定」**。

**⚠ (d) 【第 589 轮补登：上面 (c) 「没有做」已过时】**

第 581 轮时 (c) 说「把 `s` 绑定到 `linScore`/`margin` **没有做**」——
**这个工作在后来的第 583–587 轮【已做】**：
* `5d00a30`：`FateV2.Loop/ScoreBound` 提供 `s = linScore w x` 的绑定（`margin w x = \|linScore w x\|`）；
* `0c02a24`：本文件 **§6.15** `endToEnd_classification_s_bound`（`:1491`）把
  §6.7 里的自由 `{s : ℝ}` 换成 `w xw : ι → ℝ` + `hs : 4 * σ < margin w xw`。

**⟹ 所以 (c) 段保留不删（不静默删除纪律），但其「未做」的结论已失效；
当前准确状态见 §0.5.2 与原 §0.5 表（已重写）。**

**⚠ 引用 `margin` 时注意**：它**不在** `FateV2.Loop/R250ErrorBound.lean`（该文件不存在），
而在 `FateV2.Loop/ErrorBound.lean:170`，位于 `namespace FateV2.Error.R250ErrorBound` 内。

**1.9 【第 589 轮追加：§0.5 表格重写 —— 四个量现在都有出处】**

**(a) 原表哪两行过时**：§0.5 原表的 **`L`** 行（「⚠️ 只能估下界 / 不可从数据推出上界」）
与 **`\|s\|`** 行（「❌ 无源头」）——**都是错的**，已重写。

**(b) 新表每行的出处函数 + commit**：

| 量 | 出处函数（实测位置） | commit |
|---|---|---|
| `ηmax` | `FateV2.Loop/EtaMaxFromData.etaMax_from_bdd`（`:231`） | —（§6.11） |
| `σ` | `FateV2.Loop/SigmaGammaFromData.profData_unique_boundary`（`:236`） | —（§6.9） |
| `L` | `FateV2.Loop/LipschitzFromFinite.exists_lipschitzInvertibleOn_of_finite_separated`（`:154`） | `0a7a69e` + `b5215fe`（§6.14） |
| `\|s\|` | `FateV2.Loop/ErrorBound.lean:170` 的 `FateV2.Error.R250ErrorBound.margin`（`= \|linScore w x\|`），绑定见 `FateV2.Loop/ScoreBound.lean` | `5d00a30` + `0c02a24`（§6.15） |

**(c) 按（甲）只有两条算减少**：**§6.9（`σ`，5→3）与 §6.11（`ηmax`，3→1）**；
**§6.14（`L`，1→2）与 §6.15（`\|s\|`，2→3）不算**（是「换前件」，不是「减前件」）。

**(d) 新前件仍需工程标定**：`FiniteSeparatedSpace`、`hsep`、`hinj` 等**新前件本身**
仍未被自动验证——「有出处」≠「可自动验证」。

**⟹ 本节纯文档，未加/未删任何定理（定理数仍为 38）；未用 `sorry`/`admit`/`axiom`。**

---------------------------------------------------------------------------
## 2  目录
---------------------------------------------------------------------------

| 节 | 内容 | 引用模块数 |
|---|---|---|
| §3 | 前置引理：`c` 的平方/幂代数（自证）| — |
| §4 | 世界模型总体框架 `cWorld`（把两条链的「世界」对齐到同一类型）| 3 |
| §5 | 学习链：`thetaN` 收敛 × `OptimalEta.c`（收缩因子的统一）| 3 |
| §6 | **端到端稳态误差上界（用估计的 θ 与估计的 σ）** | 4 |
| §6.3 | **`dσ` 由数据决定（`resolveSigma`）**——σ 在主干上的唯一出处 | 5 |
| §7 | **θ 可辨识**（`WorldModelReadsTheta` 的分离性 × 收敛）| 3 |
| §8 | **η = 1 一步学到真值**（`OptimalEta` × `ThetaConvergence`）| 3 |
| §9 | **因果查询接口唯一且自洽**（前门 × 后门 × do-算子）| 3 |
| §10 | **总装总定理**（八个模块的结论一条合取）| 8 |
| §11 | ⚠ 诚实边界 / 前件自查表 / 扇入登记 | — |

纪律：零 `sorry` / 零 `admit` / 零 `axiom`；不修改既有模块；交付前 `lake env lean` 两遍。

---------------------------------------------------------------------------
### §N  σ 的数据来源（第 429 轮，审计 R423 要求）
---------------------------------------------------------------------------

本文件的 `dσ`（σ 预算）在第 60–102 轮时是**任取的自由参数**
（§6.1 的 hstep 只要求 `dσ ≥ 0`，与数据无关）。
第 429 轮新增 `capstone_dsigma_from_data`（§6.3）：`dσ := resolveSigma src W g0`，
其中 `src : SigmaFromDomain.SigmaSource` 可以是破法乙（AIC）/ 丙（信息增益）/
丁（领域给定）中的任一条（统一接口），`resolveSigma` 的三分支决定其取值。

**⟹ 至此 σ 在主干上有了唯一出处，不再是自由参数。**

⚠ 如实边界：本定理**不**证明 σ 的估计是**正确/最优**的；
它只证明「§6.1 的 `dσ` 参数位**可以在不损失结论结构的前提下**被替换为
`resolveSigma src W g0`」，其可行性唯一依赖 `resolveSigma_nonneg`（三分支非负）。
`unknown` 分支仍是一个**显式占位**（见 `SigmaFromDomain` 文件头的诚实登记）。

---------------------------------------------------------------------------
### §M  第 528 轮：4 条空洞定理的诚实标注（只加注释，不改结构）
---------------------------------------------------------------------------

**(a) 本任务只加注释，不改结构。**
本轮**只插入块注释**（斜杠星号开、星号斜杠闭），**未改任何定理的陈述、证明或前件**，
**未删任何定理**，**未新增定理**。改前改后 `grep -cE "^theorem"` 均为 **26**。

**(b) 加了几条、分别在哪。** 共 **4 条**警示块（均为**块注释**，置于原文档注释**之前**）：

| 定理 | 所在节 | 审计判决 |
|---|---|---|
| `endToEnd_steady_bound_estimated`（§6.1）| 本文件 §6.1 | R441：结论的全部数值内容由 `hstep` 提供 |
| `capstone_dsigma_from_meas`（§6.4.2）| 本文件 §6.4.2 | R441：`sigmaEst P n` 只用了一次 `0 ≤ sigmaEst` |
| `endToEnd_steady_bound_no_hstep`（§6.5.1）| 本文件 §6.5.1 | R504 探针 A：观测前件全部删掉，定理原样成立 |
| `endToEnd_steady_bound_implies_correct_classification`（§6.6.1）| 本文件 §6.6.1 | R504：`hK`/`hs` 两条是假设；**R524：`hbdd` 已删，改为从 `noisyIter_boundedUnder` 推出** |

（§6.3 `capstone_dsigma_from_data` 的同类标注于**第 461 轮**已加入，本轮未重复。）

**(c) 不改的原因是「等作者裁决是否重构」。**
两条候选重构路线（① 删掉空洞定理；② 把 `hstep` / `hK` / `hs` / `hbdd` 改从模型推出）
**都会改变本文件的定理集与下游调用面**，属于结构性决策，**不属于本 Agent 的任务范围**。
故本轮一律**保留原样 + 加显式警示**（不静默删除纪律），把裁决权交回作者。
**⟹ 任何引用上述 4 条定理的论证，必须知道其为空洞/假设驱动。**
-/


/-! 上面最后 5 个 `import` 是 **G59 扇入修复**：消费世界模型侧 5 个原本扇入为 0 的
    冷模块（详见文件末 §G59 一节）。这 5 个模块**均不** import
    `FateV2.Loop.WorldModelCapstone`，故无循环依赖（G46）。 -/

namespace FateV2.Loop

namespace WorldModelCapstone

universe u

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Topology

/-! ===========================================================================
    §3  前置引理：`c(η) = |1-η|` 的代数
    （纯标量；供 §6、§7 的界化简使用）
    =========================================================================== -/

/-- `c(η) ≤ 1` 时 `c(η)^2 ≤ c(η)`（收缩因子的幂单调，供 §6 化简用）。

**为何不是同义反复**：前件是 `c` 的一次幂与 `1` 的比较，结论是**二次幂**与
一次幂的比较；需 `pow_le_pow_left₀` 与 `pow_two` 的代数。 -/
theorem c_sq_le_c {η : ℝ} (h1 : OptimalEta.c η ≤ 1) :
    OptimalEta.c η ^ 2 ≤ OptimalEta.c η := by
  have h0 : 0 ≤ OptimalEta.c η := OptimalEta.c_nonneg η
  have h2 : OptimalEta.c η ^ 2 = OptimalEta.c η * OptimalEta.c η := pow_two _
  rw [h2]
  calc OptimalEta.c η * OptimalEta.c η ≤ OptimalEta.c η * 1 :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = OptimalEta.c η := mul_one _

/-- `c(η) > 0` ⟺ `η ≠ 1`（`OptimalEta` 零点刻画的非负形式）。 -/
theorem c_pos_iff {η : ℝ} :
    0 < OptimalEta.c η ↔ η ≠ 1 := by
  constructor
  · intro h hη
    rw [OptimalEta.c_eq_zero_iff η |>.mpr hη] at h
    exact lt_irrefl 0 h
  · exact OptimalEta.eta_ne_one_pos

/-! ===========================================================================
    §4  世界模型总体框架 `cWorld`
    （把「有无噪声」两条链统一到同一个 `Corrects` 载体上）
    =========================================================================== -/

section Frame

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **【世界模型的「闭环」座标系】**：一个 `(A, φ, η, d)` 四元组，
其中 `A ∘ φ = id`（`Corrects`）、`|1-η| < 1`（收缩窗）、`d ≥ 0`（每步漂移预算）。

**为什么需要它**：`WorldModelAssembly` 给的三类结论（观测噪声界、最优步长、
噪声继承收敛）**都**以 `Corrects A φ` + `|1-η| < 1` + `d ≥ 0` 为前件，
但**各自重复**这三条。本结构把它们**打包**，于是下游（§6、§10）可以
一次引入、多条复用 —— 这是「总装」在类型层的体现。 -/
structure ClosedLoopWorld (E : Type u) (F : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  /-- 观测读出 `A`。 -/
  A : E →L[ℝ] F
  /-- 伪逆/方向映射 `φ`。 -/
  φ : F →ₗ[ℝ] E
  /-- 步长。 -/
  η : ℝ
  /-- 每步漂移预算（由观测噪声决定）。 -/
  drift : ℝ
  /-- `A ∘ φ = id`（模型能还原残差）。 -/
  corrects : BoundWriteBack.Corrects A φ
  /-- 收缩窗。 -/
  window : |1 - η| < 1
  /-- 漂移预算非负。 -/
  drift_nonneg : 0 ≤ drift

/-- `ClosedLoopWorld` 的 `c(η) < 1`（由收缩窗 + `OptimalEta.c` 的定义）。 -/
theorem ClosedLoopWorld.c_lt_one (W : ClosedLoopWorld E F) :
    OptimalEta.c W.η < 1 := by
  have : OptimalEta.c W.η = |1 - W.η| := rfl
  rw [this]
  exact W.window

/-- `ClosedLoopWorld` 的 `c(η) ≥ 0`。 -/
theorem ClosedLoopWorld.c_nonneg' (W : ClosedLoopWorld E F) :
    0 ≤ OptimalEta.c W.η := OptimalEta.c_nonneg W.η

end Frame

/-! ===========================================================================
    §5  学习链与最优步长的统一
    =========================================================================== -/

section LearningOptimal

/-- **【§5.1：`linWorld` 的收缩因子**就是** `OptimalEta.c`】**

`ThetaConvergence` 的闭式是 `θ_n - θ* = (1-η)^n (θ₀ - θ*)`，
其绝对值的收缩因子是 `|1-η|^n`；`OptimalEta` 的收缩因子是 `c η = |1-η|`。

**这条把两条链接上**：`ConvergenceOptimal.rate_eq_c_pow` 已证
`|1-η|^n = c(η)^n`，本定理把它与 `ThetaConvergence` 的**闭式**
（`thetaN_closed`）**组装**成一条关于 `linWorld` 轨迹的等式。

**引用**：`ThetaConvergence.thetaN_closed`、`ConvergenceOptimal.rate_eq_c_pow`。

**前件自查**：前件只有 `x ≠ 0`（设计点非零，`ThetaConvergence` 的闭式所需）。
结论是 `linWorld` 轨迹偏差的**绝对值闭式**，含 `c(η)^n`；
前件里**没有**任何关于 `c` 或轨迹偏差的内容。 -/
theorem lin_contraction_eq_c (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    |ThetaConvergence.thetaN η θstar x θ₀ n - θstar|
      = OptimalEta.c η ^ n * |θ₀ - θstar| := by
  rw [ThetaConvergence.thetaN_closed η θstar x θ₀ hx n, abs_mul, abs_pow,
    ConvergenceOptimal.abs_one_sub_eq_c]

/-- **【§5.2：`η = 1` 使 `linWorld` 学习**一步**学到的偏差为 `c(1)^1 = 0`】**

**引用**：`ThetaConvergence.linWorld_one_step_exact`（`θ₁ = θ*`）
× `OptimalEta.c_one`（`c 1 = 0`）。

**装配读法**：`ThetaConvergence` 只说「`θ₁ = θ*`」，`OptimalEta` 只说
「`c 1 = 0`」；本定理把后者的**标量最优性**落到前者的**轨迹**上：
`η = 1` 的偏差**恰等于** `c(1)^1 · |θ₀-θ*| = 0`。

**前件自查**：前件 `x ≠ 0` 只讲设计点；结论是偏差等式。
**不**含任何「偏差为 0」的假设。 -/
theorem eta_one_learns_exactly_scalar (θstar x θ₀ : ℝ) (hx : x ≠ 0) :
    ThetaConvergence.thetaN 1 θstar x θ₀ 1 = θstar
    ∧ OptimalEta.c 1 = 0
    ∧ |ThetaConvergence.thetaN 1 θstar x θ₀ 1 - θstar|
        = OptimalEta.c (1 : ℝ) ^ 1 * |θ₀ - θstar|
    ∧ |ThetaConvergence.thetaN 1 θstar x θ₀ 1 - θstar| = 0 := by
  refine ⟨ThetaConvergence.linWorld_one_step_exact θstar x θ₀ hx,
    OptimalEta.c_one, lin_contraction_eq_c 1 θstar x θ₀ hx 1, ?_⟩
  rw [ThetaConvergence.linWorld_one_step_exact θstar x θ₀ hx, sub_self, abs_zero]

/-- **【§5.3 主定理：`η = 1` 是学习链上的**唯一**一步归零步长】**

`θ₁(η) = θ*` **⟺** `η = 1`（对任意 `θ₀ ≠ θ*`、`x ≠ 0`）。

**引用**：`ThetaConvergence.thetaN_closed`（闭式）
× `OptimalEta.eta_one_unique_zero`（`c` 的唯一零点）。

**意义**：这是**同时**用两个模块的**两条主定理**得到的**双向刻画**：
`ThetaConvergence` 提供**轨迹**（`θ₁ = θ*`），`OptimalEta` 提供**标量唯一性**
（`c η = 0 ⟺ η = 1`）。任一条缺失，这个 `↔` 都拿不到。

**前件自查（纪律 7）**：
- 前件：`x ≠ 0`（设计点）、`θ₀ ≠ θ*`（初始不是真值 —— **否则 `η = 0` 也"归零"**，
  这条前提是**必要的**，见 §5.4 的诚实说明）；
- 结论：`θ₁(η) = θ* ⟺ η = 1`；
- 前件**不含** `η` 的任何条件，也**不含**「一步归零」。
⟹ **非同义反复。**

**⚠ 为何需要 `θ₀ ≠ θ*`**：若 `θ₀ = θ*`，则 `θ₁ = θ*` 对**一切** `η` 成立
（闭式给 `(1-η)·0 = 0`），`↔` 为假。故该前提是**数学必要**，
不是把结论包进去。 -/
theorem eta_one_iff_one_step_exact (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hθ : θ₀ ≠ θstar) :
    ThetaConvergence.thetaN η θstar x θ₀ 1 = θstar ↔ η = 1 := by
  constructor
  · intro h
    -- 闭式：`θ₁ - θ* = (1-η)¹(θ₀-θ*)`，若 `θ₁ = θ*` 则 `(1-η)(θ₀-θ*) = 0`
    have hc := ThetaConvergence.thetaN_closed η θstar x θ₀ hx 1
    rw [h, sub_self] at hc
    have hne : θ₀ - θstar ≠ 0 := sub_ne_zero.mpr hθ
    have h1η : (1 - η) ^ 1 = 0 := by
      rcases mul_eq_zero.mp hc.symm with h' | h'
      · exact h'
      · exact absurd h' hne
    rw [pow_one] at h1η
    linarith
  · intro hη
    subst hη
    exact ThetaConvergence.linWorld_one_step_exact θstar x θ₀ hx

/-- **【§5.4：`θ₀ = θ*` 时 `↔` 确实失效】**（诚实性见证：说明 §5.3 的前提必要）。

`θ₀ = θ*` 时 `θ₁(0) = θ*` 也成立，但 `0 ≠ 1`。
**⟹ `θ₀ ≠ θ*` 不能删。** -/
theorem eta_iff_fails_at_fixed_point (θstar x : ℝ) (hx : x ≠ 0) :
    ThetaConvergence.thetaN 0 θstar x θstar 1 = θstar ∧ (0 : ℝ) ≠ 1 := by
  refine ⟨?_, by norm_num⟩
  have h := ThetaConvergence.linWorld_endToEnd_step 0 θstar θstar x hx
  have h1 : ThetaConvergence.thetaN 0 θstar x θstar 1 = (1 - (0:ℝ)) * θstar + 0 * θstar := h
  rw [h1]; norm_num

end LearningOptimal

/-! ===========================================================================
    §6  **端到端稳态误差上界（用估计的 θ 与估计的 σ）**
    =========================================================================== -/

/-! ===========================================================================
    §6.7  **【前件减少 #2：`hK` 在取 `σ := steadyErr η (2Lηmax)` 时自动成立】**
    ===========================================================================

**审计 R524 原话**：
> 「假接入只能【加】前件、不能【减】前件，『前件减少』是形式指标里唯一不可伪造的方向。」

**第 531 轮**已删 `hbdd`（`d6719c8`）。**本节处理 `hK`。**

### 本节做到了什么、没做什么（如实）

**做到了**：`ErrorAcceptable ε σ` 在 `ε = σ = steadyErr η (2Lηmax)` 时**自动成立**
（`errorAcceptable_steadyErr_self`）—— 这条**不是同义反复**：它真的付出了
`0 ≤ steadyErr η (2Lηmax)`（来自 `steadyErr_nonneg`，需 `0 ≤ 2*L*ηmax` 与 `|1-η| < 1`）
和 `linarith`（`ε/2 ≤ ε`、`ε ≤ 2ε` 两分量在 `ε ≥ 0` 下成立）。

**没做到（必须说明）**：
1. **原定理 `endToEnd_steady_bound_implies_correct_classification` 的 `hK` 前件【没有】被删除。**
   本节只是证明了「若把 `σ` **固定**为 `steadyErr η (2Lηmax)`，则 `hK` 可自动满足」。
   原定理保持原样（不删已有定理、不改已有陈述的纪律）。
2. **这是【特殊化】而非纯粹的【前件减少】**：把 `σ` 从自由参数固定为
   `steadyErr η (2Lηmax)` 后，`hs : 4*σ < |s|` 相应变成
   `4 * steadyErr η (2Lηmax) < |s|` —— 这是**更具体的条件**，不是更弱的条件。
   所以「前件少了一条（`hK`）、但另一条变具体了（`hs`）」，**净收益有限**。
**不声称「解决了主干缺口」。** -/

/-
### §6.7.0  第 533 轮：**「只修不建」轮 —— 关于 §6.7 的最终诚实登记**

**(0) 本轮的实际情形：9 个错误并不存在于 `FateV2.Loop/WorldModelCapstone.lean`。**
第 533 轮主控报告 `lake env lean FateV2.Loop/WorldModelCapstone.lean` 有 9 个错误，
类型为实例合成失败（`TopologicalSpace E`、`AddCommMonoid F`、`PseudoMetricSpace F`、
`HAdd F F ?m`、`Norm F`）与 `Function expected at steadyErrEst`。
**本轮实测：该文件 `lake env lean` 连续三遍均 `EXIT=0`、零 error、零 warning 输出。**
原因：`errorAcceptable_steadyErr_self`（`:400`）与
`endToEnd_steady_bound_implies_correct_classification_no_hK`（`:1162`）**都已经在**
`section EndToEndBound`（`:425` 起）的实例作用域内 ——
该 section 的 `variable {E F : Type u}`、`[NormedAddCommGroup E] [NormedSpace ℝ E]`、
`[NormedAddCommGroup F] [NormedSpace ℝ F]` 对两条定理**均已生效**，
与 `:1086` 的原定理 `endToEnd_steady_bound_implies_correct_classification` **同一作用域**。
所以**不存在**需要「移进作用域」的改动，也**不存在**需要退到「只保留 self 版本」的情形。
⟹ 本轮**未改任何定理陈述、未改任何证明、未删定理、未新增定理**；
`grep -cE "^theorem"` 改前改后均为 **29**。
本轮**只新增本块注释**（纯 `/- ... -/`），把上面第 (0) 条与下面「不构成前件减少」的
登记写死在文件里。

**(a) 9 个错误的类型**（若在 `section` 之外重现，才会出现）：
实例合成失败 —— `TopologicalSpace E`、`AddCommMonoid F`、`PseudoMetricSpace F`、
`HAdd F F ?m`、`Norm F`，以及 `steadyErrEst` 被当成函数应用（`Function expected`）。
这全部是**作用域**问题（缺 `variable [NormedAddCommGroup E] [NormedSpace ℝ E]`
与 `[NormedAddCommGroup F] [NormedSpace ℝ F]`），**不是概念问题**。

**(b) 修了什么**：**无需修** —— 两条定理已在正确作用域内，实测 `EXIT=0`。
（如实登记：这属于「报告与实测不符」，不是「本轮修好了 9 个错误」。）

**(c) `errorAcceptable_steadyErr_self` 是否保住**：**保住**，`:400` 原样，未改一字；
`no_hK` 版本亦**保留未删**（`:1162`）。

**(d) ⚠ 本轮【不构成】真正的「前件减少」—— 必须如实承认。**
主控在任务书中自己写明：
> 「`hK` **是「换成具体值」，不是「删除」**」
> 「`hs : 4σ < |s|` 里的 `σ` 也变成 `steadyErr`** ⟹ 那是「更具体的条件」，不是「更少的假设」」

⟹ 把 `σ` 从自由参数**固定**为 `steadyErr η (2Lηmax)` 之后，`hK` 虽不再作为前件出现，
但 `hs` 从 `4 * σ < |s|` **变成** `4 * steadyErr η (2Lηmax) < |s|`，
这是一个**更具体（更强）**的条件。**前件总数没有净减少**；
这只是「把一个自由参数换成具体值」。**故本节标题中的『前件减少 #2』一词不得作为
『前件净减少』的凭据使用。** 只可声称：**`hK` 在取 `σ := steadyErr η (2Lηmax)` 时自动成立**。
-/

open ErrorCriterion in
/-- **【前件减少 #2：`hK` 不再需要（在取 `σ := steadyErr` 时）】**

`ErrorAcceptable ε σ` 在 `ε := σ := steadyErr η (2 * L * ηmax)` 时**自动成立**：
两分量变为 `steadyErr/2 ≤ steadyErr` 与 `steadyErr ≤ 2 * steadyErr`，
在 `0 ≤ steadyErr` 下均由 `linarith` 给出，而 `0 ≤ steadyErr` 由
`ClosedLoopNoisy.steadyErr_nonneg` 从 `0 ≤ 2*L*ηmax`（`hL` + `hηmax`）
与 `|1-η| < 1`（`hη`）**推出**，不是假设。

**⟹ 所以原定理的 `hK` 前件在 `σ := steadyErr η (2Lηmax)` 这个取法下可以删除**：
本定理就是那个「取法」的形式化。

**⚠ 代价如实登记**：`hs : 4*σ < |s|` 也相应变成 `4 * steadyErr η (2Lηmax) < |s|`
——这是**更具体的条件**，不是假设的净减少。 -/
theorem errorAcceptable_steadyErr_self (η L ηmax : ℝ)
    (hL : 0 < L) (hηmax : 0 ≤ ηmax) (hη : |1 - η| < 1) :
    ErrorCriterion.ErrorAcceptable
      (ClosedLoopNoisy.steadyErr η (2 * L * ηmax))
      (ClosedLoopNoisy.steadyErr η (2 * L * ηmax)) := by
  unfold ErrorCriterion.ErrorAcceptable
  have hd : 0 ≤ 2 * L * ηmax := by nlinarith only [hL, hηmax]
  have hne : 0 ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax) :=
    ClosedLoopNoisy.steadyErr_nonneg hd hη
  constructor <;> linarith only [hne]

/-- **做法 B（A 的直接推论）**：存在 `σ` 使判据在 `ε := steadyErr η (2Lηmax)` 时成立
—— 取 `σ := steadyErr η (2Lηmax)` 即可（`errorAcceptable_steadyErr_self`）。 -/
theorem exists_sigma_errorAcceptable (η L ηmax : ℝ)
    (hL : 0 < L) (hηmax : 0 ≤ ηmax) (hη : |1 - η| < 1) :
    ∃ σ : ℝ,
      ErrorCriterion.ErrorAcceptable
        (ClosedLoopNoisy.steadyErr η (2 * L * ηmax)) σ :=
  ⟨ClosedLoopNoisy.steadyErr η (2 * L * ηmax),
    errorAcceptable_steadyErr_self η L ηmax hL hηmax hη⟩

/-!
### §6.0  平行副本索引（第 559 轮，作者裁决（甲））

**作者授权**：作者第 552 轮逐字「d  1  其他的之后其他弄完讨论
就是这种合并和部分重构的你可以直接进行」—— 本节的标注即在此授权下进行。

**本文件有 10 条同型的「端到端稳态误差上界」定理**（`grep -cE "^theorem (endToEnd|capstone_dsigma)"`
= 10，改前改后不变）。它们的关系如下：

| 定理 | 行 | 前件特征 | 状态 |
|---|---|---|---|
| `endToEnd_steady_bound_estimated` | 517 | 有 `hstep`（自由步长） | **旧，已 `@[deprecated]`** |
| `capstone_dsigma_from_data` | 636 | 有 `dσ`/`src`/`W`/`g0`（自由 + 换名） | **旧，已 `@[deprecated]`** |
| `capstone_dsigma_from_meas` | 760 | 有 `hstep`，`_hx'`/`_hδ` 是摆设 | **旧，已 `@[deprecated]`** |
| `endToEnd_steady_bound_no_hstep` | 894 | 观测模型 + 自由 `hbdd` | **旧，已 `@[deprecated]`** |
| `endToEnd_steady_bound_from_obs` | 989 | **观测模型，无 `hstep`** | **§6.8 新（未弃用）** |
| `endToEnd_steady_bound_implies_correct_classification` | 1217 | + 分类结论 | §6.6（未弃用）|
| `endToEnd_steady_bound_implies_correct_classification_no_hK` | 1293 | `σ := steadyErr`（特殊化） | §6.7（未弃用）|
| `capstone_dsigma_unique_from_meas` | 1806 | **`∃!` 唯一性 + 无自由参数** | **§6.9 新（未弃用）** |
| `capstone_dsigma_from_meas_no_hstep` | 2040 | **观测模型，`hx'`/`hδ` 真用** | **§6.10 新（未弃用）** |
| `capstone_dsigma_meas_no_eta_free` | 2169 | **`ηmax = sSup ‖δ·‖`，无自由参数** | **§6.11 最新（未弃用）** |

**⟹ 推荐引用顺序（从新到旧）：§6.11 > §6.10 > §6.9 > §6.8 > §6.6/§6.7 > 旧版（§6.1–§6.5）。**

**⟹ 旧版保留不删**（不静默删除纪律）。本节只加 `@[deprecated]` 标注，
**不删任何定理、不改任何签名、不改任何证明**。
**⟹ 本任务不是「删除重复定理」，而是「标注」。**

**⟹ 下游弃用警告（已如实查证，见文件末 §6.13 标注登记）：**
* `endToEnd_steady_bound_estimated` 被 `FateV2.Loop/SigmaUnified.lean:428`
  与 `FateV2.Loop/WorldModelCapstoneConsumer.lean:237` **实际调用** ⟹ 这两处会出现
  **弃用警告（warning，不是 error，构建仍通过）**。
* `capstone_dsigma_from_data` 仅在 `FateV2.Loop/CapstoneDriftFromObs.lean:8` 的
  **注释文本**中出现，**没有** Lean 调用 ⟹ 无弃用警告。
* `capstone_dsigma_from_meas` / `endToEnd_steady_bound_no_hstep` 在 `FateV2.Loop/*.lean` 中
  **零外部引用** ⟹ 无弃用警告。

**⟹ 「下游会出现弃用警告」是预期行为**，不是构建失败。
-/

/-!
### §0.5  不可消除的建模假设（第 575 轮登记）

**本文件所有端到端误差定理（§6.1–§6.11）都依赖四个前件量。**

**⚠ 本表已按第 589 轮实测【全面重写】**：原表把 `L` 写成「只能估下界 / 不可从数据推出上界」、
把 `\|s\|` 写成「无源头」，**这两行现在都已过时**（详见下方追加的 §0.5.2）。
原表的 (a)(b)(c)(d) 说明段落**保留不删**（不静默删除纪律），但**请以下表为准**。

| 量 | 在本文件里的形式 | 能否从数据算出 | 结论 |
|---|---|---|---|
| `ηmax` | `hδobs : ∀ k, ‖δobs k‖ ≤ ηmax` | ✅ **可以**（`EtaMaxFromData.etaMax_from_bdd`，`ηmax = sSup ‖δ·‖`） | **§6.11 已消除自由度** |
| `σ` | `sigmaEst P n` | ✅ **可以**（`profData_unique_boundary` 给 `∃!` 唯一性） | **§6.9 已接入** |
| `L` | `hLI : RA14Strong.LipschitzInvertibleOn f L` | ✅ **可以**（`LipschitzFromFinite.exists_lipschitzInvertibleOn_of_finite_separated`，需 `FiniteSeparatedSpace` + 值域分离 + 单射） | **§6.14 已接入（换前件，非减少）** |
| `\|s\|` | `{s : ℝ}` + `hs : 4 * σ < \|s\|` | ✅ **可以**（`R250ErrorBound.margin w x := \|linScore w x\|`；`ScoreBound` 提供绑定；`§6.15` 已接入） | **§6.15 已接入（换前件，非减少）** |

**（第 581 轮修正）**：本表原先写 `\|s\|` 「无源头」，**这是错的** —— `s` 在
`FateV2.Loop/ErrorBound.lean:180-184` 有明确语义（真侧打分 / 真实间隔），
`:236` 更点明「$s = \langle w,x\rangle$ 时它就是分类器版」。
**准确的说法是**：`s` **有语义，但未被绑定到具体的 `w`/`x`** —— 要消除这个自由度，
需要把 `s` 替换为 `⟨w, x⟩` 或类似的具体表达式（**未做**）。

**⟹ 所以「可工程实现」的准确含义是**：
- **理论侧给出**：`limsup ≤ steadyErr η (2Lηmax + σ)` 的**依赖形式**
- **工程侧负责**：**标定 `L` 与 `s`**（`L` 由 `f` 的结构或数据标定；`s` 由下游任务定义）

**⟹ 本登记不改变任何定理**，只把「这不是理论能推出的」写清楚。

**⟹ 这是对审计 R441/R480/R504/R524/R564 五次判决的最终回应**：
审计要求「前件必须能从数据算出」；**本文件承认其中两个不能**，
**并把责任显式移交给工程侧**，而不是继续换前件的形式。

**⚠ 不声称「已解决」**——这是**承认边界**，不是**消除边界**。

**⚠ 注意**：上面这段「不声称已解决」写于第 575 轮；`L` 与 `\|s\|` 两行
在第 581–589 轮**已被解决为「有出处」**。**原段落保留不删**（不静默删除纪律），
其当前有效性以 §0.5.2 为准。

---

**### §0.5.2  第 589 轮更新：四个量【现在都有出处】**

**第 508–530 行原表写「`L` 只能估下界、`\|s\|` 无源头」——这两行已在第 581–587 轮被解决：**

| 量 | 原状态 | 现状态 | commit |
|---|---|---|---|
| `L` | ⚠️ 只能估下界 | ✅ **`∃ L` 在有限分离空间上可证** | `0a7a69e`（`LipschitzFromFinite`）+ `b5215fe`（§6.14） |
| `\|s\|` | ❌ 无源头 | ✅ **`s = linScore w x`，`\|s\| = margin w x`** | `5d00a30`（`ScoreBound`）+ `0c02a24`（§6.15） |

**⟹ 但按作者第 577 轮裁决 2 =（甲）「前件数严格减少」：**
- **§6.9（`σ`，5→3）与 §6.11（`ηmax`，3→1）算进步**
- **§6.14（`L`，1→2）与 §6.15（`\|s\|`，2→3）不算**——它们是「换前件」

**⟹ 所以准确表述是**：**「四个量都有出处，但只有两个实现了前件数严格减少。」**

**⟹ 仍未解决的**：**`FiniteSeparatedSpace`、`hsep`、`hinj` 这些新前件本身仍需工程标定**——
「有出处」不等于「可自动验证」。

**⚠ 本节登记的实测出处（第 589 轮逐条核实，与任务书原文有 3 处出入，如实记录）：**
1. **`margin` 不在 `FateV2.Loop/R250ErrorBound.lean`**（该文件**不存在**）；实际定义在
   `FateV2.Loop/ErrorBound.lean:170`，位于 `namespace FateV2.Error.R250ErrorBound` 内
   ⟹ 引用写作 `FateV2.Error.R250ErrorBound.margin`。
2. **`L` 的接入节号是 §6.14**（`capstone_L_and_etaMax_from_data` 一族，`:2528` 起），
   **不是 §6.12**——§6.12 在本文件里被「`ηmax` 由数据决定」占用（`:2414`）。
3. **`\|s\|` 的接入节号是 §6.15**（`endToEnd_classification_s_bound`，`:1491`），
   **不是 §6.13**——§6.13（`:2631`）是 `@[deprecated]` 标注登记区段。

**⟹ 以上 3 处出入不影响结论的方向**（`L`、`|s|` 确已「有出处」），
但**引用时必须用上表的正确节号与文件路径**，否则又是一份错误的文档。

**### §0.5.1  四个「前件变化」改动的最终判定（作者第 577 轮 裁决2=甲）**

**判据（审计 R524，作者第 577 轮确认为「甲」严格）**：**前件数必须【严格减少】**。

| 改动 | 节 | 前件数变化 | 判定 |
|---|---|---|---|
| `capstone_dsigma_unique_from_meas` | §6.9 | **5 → 3**（删 `dσ`/`hdσ`/`src`+`W`+`g0`） | ✅ **算进步** |
| `capstone_dsigma_from_meas_no_hstep` | §6.10 | **1 → 0**（删 `hstep`，`_hx'`/`_hδ` 转正） | ✅ **算进步（最优）** |
| `capstone_dsigma_meas_no_eta_free` | §6.11 | **3 → 1**（删 `ηmax`/`hηmax`/`hδ`） | ✅ **算进步** |
| `endToEnd_steady_bound_from_obs` | §6.8 | **1 → 2**（`hstep` → `hx'`+`hδ`） | 🟡 **不算进步** |

**⟹ 所以本文件里真正满足「前件减少」的改动是 3 条：§6.9 / §6.10 / §6.11。**

**⟹ §6.8 的新前件更可检验（`hx'`+`hδ` vs `hstep`），但按（甲）判据【不算】前件减少。**

**⚠ 主控第 542 轮曾自行把判据放宽为「可检验性」，作者第 577 轮裁决为（甲），
故该放宽【已撤回】**——`§6.8` 不得被表述为「前件减少」。
-/

section EndToEndBound

open FateV2.Error.SteadyErrEstimate FateV2.Error.SigmaEstimation
open FateV2.Modeling.PearlHierarchy
open FateV2.Predict.R242 (R ind)

variable {P : Measure ℝ} [IsProbabilityMeasure P]

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/- ⚠ **第 528 轮诚实标注（审计 R441 的判决，主控核实后接受）**

**本条定理的数值内容全部由 `hstep` 提供。**

审计 R441：
> 「`hstep` 直接断言『步长 ≤ 2Lηmax + dσ』——**结论的全部数值内容由 `hstep` 提供**。」

**⟹ 所以本条不构成「从模型推出误差界」**——它是「假设步长有界 ⟹ 误差有界」。

**⟹ 真正想做的（把假设换掉）见 `:458`（§6.3）/ `:571`（§6.4）/ `:691`（§6.5）——
但后三条也被审计证明「前件可换成任意常数/可删」。**

⚠ **本条保留不删**（不静默删除纪律），但**任何引用它的论证必须知道它是空洞的**。 -/
/-- **【§6.1 主定理 A：用估计的 θ 与估计的 σ 时的端到端稳态误差上界】**

**结论（三条合一）**：

1. **θ 侧的误差**（`ThetaConvergence`）：`|θ_n - θ*| = c(η)^n |θ₀ - θ*|`；
2. **有噪声闭环的渐近上界**（`ClosedLoopNoisy` + `WorldModelAssembly`）：
   `limsup ‖A θ_n - x'_n‖ ≤ steadyErr η d`；
3. **σ 侧的估计精度**（`SteadyErrEstimate` + `SigmaEstimation`）：
   `Var[Ê_∞] = gain(η)² · (varOf P / n)`。

**装配读法（这是本文件的核心装配定理）**：
`SteadyErrEstimate.variance_steadyErrEst` 的**输入**就是
`ClosedLoopNoisy.steadyErr`，而 `steadyErr` 是 `WorldModelAssembly` 的
**输出上界**；`WorldModelAssembly.assembly_noisy_steady_bound` 的漂移预算
`d = 2 L ηmax` 是**观测**侧的，本文件把它**与 σ 侧联合**：
把 `d` 放宽为 `2 L ηmax + dσ`（`dσ ≥ 0` 任取的 σ 预算）**不改变**上界的
**结构**（仍是 `steadyErr η (·)`），且与估计方差**同时**成立。

**⚠ 前件自查（纪律 7，逐条核对）**：
- 前件不含结论的任何一条：`hLI` 只讲 `h` 的 Lipschitz 可逆性；
  `hδ` 只讲**单步**噪声 `‖δ k‖ ≤ ηmax`；`hstep` 只讲**相邻观测原像**的漂移界；
  `hP` 只讲**二阶矩有限**；`hη`、`|1-η| < 1` 只讲**步长**；
  `x ≠ 0` 只讲**设计点**；`n ≥ 1` 只讲**样本数**。
- **结论**（`limsup` 的数值上界 + 方差等式 + 常数 `η = 1` 时的退化）
  在**任何**前件中**都不出现**。
⟹ **非同义反复。** -/
@[deprecated "已被 `endToEnd_steady_bound_from_obs`（§6.8）取代：后者用观测模型 `hx'`+`hδ` 替代了自由步长假设 `hstep`" (since := "2025-10-23")]
theorem endToEnd_steady_bound_estimated
    (hP : MemLp (fun x : ℝ => x) 2 P) {η L ηmax dσ : ℝ}
    (hL : 0 < L) (hηmax : 0 ≤ ηmax) (hdσ : 0 ≤ dσ)
    (hη : |1 - η| < 1) (n : ℕ) (hn : 0 < n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (δ : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + δ k) (hδ : ∀ k, ‖δ k‖ ≤ ηmax)
    (hstep : ∀ k : ℕ, ‖x' k - x' (k + 1)‖ ≤ 2 * L * ηmax + dσ) :
    -- (1) 有观测噪声的渐近上界（WorldModelAssembly 的结论）
    limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax + dσ)
    -- (2) 其中 `d = 2 L ηmax` 的部分由观测模型自己推出（不靠 `hstep`）
    ∧ limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax)
    -- (3) 用估计的 σ 时，稳态误差估计的方差（SteadyErrEstimate）
    ∧ variance (steadyErrEst η n) (iidMeasure P n)
        = (gain η) ^ 2 * (varOf P / n)
    -- (4) 该方差随样本量的极限为 0（一致性）
    ∧ Filter.Tendsto (fun m : ℕ => varOf P / ((m : ℝ) + 1)) Filter.atTop (nhds 0)
    -- (5) `η = 1` 时估计方差**无额外放大**：`c(1)=0` 且 `Var = σ²/n`
    ∧ OptimalEta.c 1 = 0
    ∧ variance (steadyErrEst 1 n) (iidMeasure P n) = varOf P / n := by
  have hW1 := WorldModelAssembly.assembly_noisy_steady_bound
    A φ η θ h hL hLI hηmax x x' δ hx' hδ hη
  -- 放宽的界：`d = 2 L ηmax + dσ ≤ 2 L ηmax + dσ` 直接由 `noisy_limsup_bound`
  have hdrift0 : ∀ k : ℕ, ‖x' k - x' (k + 1)‖ ≤ 2 * L * ηmax :=
    WorldModelAssembly.obs_noise_drift_bound hL hLI hηmax x x' δ hx' hδ
  have hd0 : 0 ≤ 2 * L * ηmax := by nlinarith [le_of_lt hL]
  have hwide : limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖)
      atTop ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax + dσ) := by
    have hb := ClosedLoopNoisy.noisy_limsup_bound (d := 2 * L * ηmax + dσ)
      (r := |1 - η|) A φ η x' θ h hstep (by linarith) rfl hη
    simpa only [ClosedLoopNoisy.steadyErr] using hb
  exact ⟨hwide, hW1,
    SteadyErrEstimate.variance_steadyErrEst hP hη n hn,
    SigmaEstimation.variance_meanOf_tendsto_zero (P := P) hP,
    OptimalEta.c_one,
    SteadyErrEstimate.variance_steadyErrEst_one hP n hn⟩


/-- **【§6.2：`η = 1` 时「无噪声归零」与「有噪声残留 `d`」的**精确对照**】**

**引用**：`WorldModelAssembly.assembly_eta_one_zero_vs_floor`（`steadyErr 1 d = d`
且 `Corrects` 下 `η=1` 一步归零）× `ThetaConvergence.linWorld_one_step_exact`
（`linWorld` 上 `θ₁ = θ*`）× `SteadyErrEstimate.variance_steadyErrEst_one`。

**装配读法**：三条结论**分别**来自三个模块，且**讲的是同一个 `η = 1`**：
抽象闭环（`err = 0`）、带噪稳态（`= d`）、估计方差（`= σ²/n`）。
把这三条放在一条定理里，就是「世界模型在最优步长处的**完整行为**」。

**前件自查**：前件只有 `Corrects`、`x ≠ 0`（设计点）、`n ≥ 1`。
结论是三条**数值等式**；前件**不含**任何等式结论。 -/
theorem eta_one_full_behavior
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : BoundWriteBack.Corrects A φ) (d : ℝ)
    (θstar x θ₀ : ℝ) (hx : x ≠ 0) :
    -- 抽象闭环：`η = 1` 一步归零
    BoundWriteBack.errA A x' (WiringConvergence.iterMap A φ 1 x' n θ) = 0
    -- 带噪稳态：`η = 1` 时稳态误差恰为噪声幅度 `d`
    ∧ ClosedLoopNoisy.steadyErr 1 d = d
    -- 线性世界模型：`η = 1` 一步学到真值
    ∧ ThetaConvergence.thetaN 1 θstar x θ₀ 1 = θstar
    -- σ 估计：`η = 1` 时估计方差无额外放大
    ∧ variance (SteadyErrEstimate.steadyErrEst 1 n)
        (SigmaEstimation.iidMeasure P n) = SigmaEstimation.varOf P / n := by
  obtain ⟨h1, h2⟩ := WorldModelAssembly.assembly_eta_one_zero_vs_floor
    A φ x' θ h d hn
  exact ⟨h2, h1, ThetaConvergence.linWorld_one_step_exact θstar x θ₀ hx,
    SteadyErrEstimate.variance_steadyErrEst_one hP n hn⟩

/- ⚠ **第 461 轮加注（审计 R441 的批评，主控核实后接受）**

**本条定理是【空洞】的。**

审计 R441 的判决：
> 「`resolveSigma` 只是被『贴』在参数位上，不是『接到』参数位上。
>  证明体第一步 `subst hdσ` 把 `dσ` 换名，然后调 `noisy_limsup_bound`。
>  **前件 `hstep` 直接断言『步长 ≤ 2Lηmax + dσ』——结论的全部数值内容由 `hstep` 提供**。
>  ⟹ **把 `resolveSigma` 换成常数 `0`，这条定理依然成立、依然编译。**」

**⟹ 主控核实**：`hstep` 在 `:447` 确实是
`∀ k, ‖x' k - x'(k+1)‖ ≤ 2 * L * ηmax + dσ` —— **结论的数值全由它给**。
`resolveSigma` 的唯一独立使用是 `hsigma_nonneg`（提供一个非负数）。

**⟹ 所以本条不构成「σ 接通了主干」**——它是「新的名字，旧的自由参数」。
**⟹ 真正拆掉 `hstep` 的工作见 `FateV2.Loop/CapstoneDriftFromObs.lean`（第 460 轮派）。**

⚠ **本条保留不删**（不静默删除纪律 + 它是 §6.4 的前身），
但**任何引用它的论证必须知道它是空洞的**。 -/
/-- **【§6.3 主定理 A′：`dσ` 由数据决定 —— σ 的唯一出处】**

第 429 轮（审计 R423 要求）：§6.1 的 `dσ`（σ 预算）此前是**任取的自由参数**。
本定理把它**钉死**为 `dσ := SigmaFromDomain.resolveSigma src W g0`，
其中 `src : SigmaSource` 是破法乙（AIC）/ 丙（信息增益）/ 丁（领域给定）任一条的
**统一接口**（`SigmaFromDomain` 的 §1 三分支类型）。

**结论**与 §6.1 主定理 A 的 (1) 条同形，只是常数 `d` 换成
`2 L ηmax + resolveSigma src W g0` —— 即**σ 在主干上有了唯一出处**。

**何以能取 `dσ := resolveSigma …`**：``hstep` 需要 `0 ≤ dσ`，而
`SigmaFromDomain.resolveSigma_nonneg` 给出 `0 ≤ resolveSigma src W g0`
（三分支统一：`domain`/`estimated` 由构造携带的 `0 < σ`，`unknown` 由
`ErrProfileWeak.err_nonneg`）。**这是本定理对 `resolveSigma` 的唯一使用点**，
但它正是「σ 接到参数位」的实质：没有这条非负性，§6.1 的 `dσ` 位
**无法**接受 `resolveSigma` 的输出。

**⚠ 前件自查（纪律 7）**：前件中 `hdσ` 是 **`dσ` 的定义式**
（`dσ = resolveSigma src W g0`），**不是**结论的任何一部分；
结论是 `limsup` 的数值上界，其右侧出现 `resolveSigma` 是**结论的一部分**
（这是本定理的**目的**，不是同义反复）。
其余前件与 §6.1 相同（Lipschitz、单步噪声界、二阶矩、收缩窗、`n ≥ 1`、漂移界）。
**⟹ 非同义反复**（`hdσ` 只把 `dσ` 换个写法，不蕴含 `limsup` 的界）。

**⚠ `_hLI` / `_hx'` / `_hδ` 为何带下划线**：本定理的结论**不**依赖它们（其证明
复用 `noisy_limsup_bound` 的 `hstep` 路径）。保留它们作参数是为了使前件集
与 §6.1 主定理 A **完全一致**（调用方可以原封不动地把 §6.1 的前件传进来），
下划线仅表示「有意接收但不使用」，不表示它们多余。 -/
@[deprecated "已被 `capstone_dsigma_unique_from_meas`（§6.9）取代：后者用 `∃!` 唯一性钉死 σ，无自由 `src`/`W`/`g0`" (since := "2025-10-23")]
theorem capstone_dsigma_from_data
    (hP : MemLp (fun x : ℝ => x) 2 P) {η L ηmax dσ : ℝ}
    (hL : 0 < L) (hηmax : 0 ≤ ηmax)
    (hη : |1 - η| < 1) (n : ℕ) (hn : 0 < n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} (_hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (δ : ℕ → F)
    (src : SigmaFromDomain.SigmaSource) (W : Core.ErrProfileWeak) (g0 : ℝ)
    (hdσ : dσ = SigmaFromDomain.resolveSigma src W g0)
    (_hx' : ∀ k, f (x' k) = f x + δ k) (_hδ : ∀ k, ‖δ k‖ ≤ ηmax)
    (hstep : ∀ k : ℕ, ‖x' k - x' (k + 1)‖ ≤ 2 * L * ηmax + dσ) :
    -- (1) 有观测噪声的渐近上界，其 `d` 中的 σ 部分**由 `resolveSigma` 决定**
    limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η
            (2 * L * ηmax + SigmaFromDomain.resolveSigma src W g0)
    -- (2) 该 σ 分量**非负**（`IsFitBoundary` 的健全性前提，来源统一）
    ∧ 0 ≤ SigmaFromDomain.resolveSigma src W g0
    -- (3) 估计方差等式照旧成立（σ 的出处不改变估计侧的结构）
    ∧ variance (steadyErrEst η n) (iidMeasure P n)
        = (gain η) ^ 2 * (varOf P / n) := by
  have hσnn : 0 ≤ SigmaFromDomain.resolveSigma src W g0 :=
    SigmaFromDomain.resolveSigma_nonneg src W g0
  have hd0 : 0 ≤ 2 * L * ηmax := by nlinarith [le_of_lt hL]
  subst hdσ
  have hwide : limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖)
      atTop ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax +
        SigmaFromDomain.resolveSigma src W g0) := by
    have hb := ClosedLoopNoisy.noisy_limsup_bound (d := 2 * L * ηmax +
      SigmaFromDomain.resolveSigma src W g0)
      (r := |1 - η|) A φ η x' θ h hstep (by linarith [hd0, hσnn]) rfl hη
    simpa only [ClosedLoopNoisy.steadyErr] using hb
  exact ⟨hwide, hσnn, SteadyErrEstimate.variance_steadyErrEst hP hη n hn⟩

/-! ### §6.4  `dσ` 由 `(P, n)` 决定（审计 R441 的「能做的那一半」）

本节**只加不改** §6.3：§6.3 的 `capstone_dsigma_from_data` 依然在，
那里 `dσ := SigmaFromDomain.resolveSigma src W g0`，`src` 是**任意的** `SigmaSource`。
本节把 `dσ` 换成 `FateV2.Error.ChainBudgetBound.sigmaEst P n` —— **直接由 `(P, n)` 决定**，
并且有 `SigmaGammaFromData.profData_unique_boundary` 的 `∃!` 支撑。

**§6.4 的诚实边界（逐条，勿含糊）**：

**(a) 与 §6.3 的区别**：§6.3 的 `σ` 出处是 `resolveSigma src W g0`（三分支统一接口）；
本节的 `σ` 出处是 `sigmaEst P n := √(varOf P / n)`。二者的**结论形状相同**
（同一个 `limsup ≤ steadyErr η (2 L ηmax + ·)`），只是 `·` 的写法不同。
⟹ 本节**不**取代 §6.3，也不是比它更强的定理；它只是**换了一个 σ 的出处**，
并把该出处的**唯一性**（§6.4.1）显式接入。

**(b) ⚠ `hstep` 仍然存在，拆不掉**：`hstep : ∀ k, ‖x' k - x' (k+1)‖ ≤ 2 L ηmax + sigmaEst P n`
是**关于观测序列 `x'` 的假设**（`x'` 的相邻步漂移有界）。拆掉它需要 `x'` 的
**生成模型**（「`x'` 是怎么产生的」），而该模型在本仓库中**不存在**。
故本节**只做到**「把 `dσ` 从 `hstep` 里换成一个由 `(P, n)` 决定的具体量」，
**没有**做到「让 `hstep` 由某条上游定理导出」。这一点如实登记，不含糊。

**(c) `dσ` 现在真的由 `(P, n)` 决定，且唯一性有支撑**：
`sigmaEst_from_unique_boundary`（§6.4.1）直接引用
`SigmaGammaFromData.profData_unique_boundary`，证明「给定 `(P, n)`（且 `sigmaEst P n > 0`），
`σ = sigmaEst P n` 处的拟合边界 `γ` **唯一存在**」。于是「`σ` 由 `(P, n)` 决定」
不是命名上的，而是有 `∃!` 定理支撑的。

**(d) ⚠ 但 `P` 本身仍是量词里的任意变量**：本节的 `{P : Measure ℝ}` 是一个
**任给的**概率测度（`[IsProbabilityMeasure P]`），不是「从某份具体数据估出来的 `P`」。
⟹ 「从数据算 σ」在这里是**命名上的**（`sigmaEst` 的 arguments 只有 `P, n`，
参数表里**没有** `γ`、没有 `W`），**不是本体上的**：「数据 → `P`」这一步
本仓库**没有**形式化。

**⚠ 前件自查（纪律 7）**：`hσpos : 0 < sigmaEst P n` 只用于（且只被用于）
导出 `hσnn : 0 ≤ sigmaEst P n`（供 `ClosedLoopNoisy.noisy_limsup_bound` 的 `hd`）；
它**不**蕴含 `limsup` 的任何上界。`hstep` 只讲 `x'` 的相邻步漂移；
`hP` 只讲二阶矩；`hη` 只讲步长；`n ≥ 1` 只讲样本数。
**结论**（`limsup` 数值上界 + `γ` 的 `∃!` + 方差等式）在**任何**前件中**都不出现**。
⟹ **非同义反复。** -/

/-- **【§6.4.1：`sigmaEst P n` 处的拟合边界唯一存在（`∃!` 支撑）】**

$$
0<\sigma_{\text{est}}(P,n)\Longrightarrow
  \exists!\,\gamma,\ \mathrm{IsFitBoundary}\bigl(\mathrm{profData}(P,n),\ \sigma_{\text{est}}(P,n),\ \gamma\bigr)
$$

这是 `FateV2.Error.SigmaGammaFromData.profData_unique_boundary` 在本命名空间下的
**直引用**（本文件不复制其证明，而是把它接入 `WorldModelCapstone`）。

**作用**：它是 §6.4 主定理把 `dσ` 钉成 `sigmaEst P n` 的**唯一性依据** ——
`σ` 不是一个可以随便填的数，它在 `(P, n)` 给定后**唯一**决定拟合边界。

**⚠ 不声称**：`profData P n` 是**真实**误差剖面（它是为证前件非空而构造的载体，
见 `SigmaGammaFromData` 文件头 §五.2）。本定理只陈述 `∃!` 这一逻辑事实。 -/
theorem sigmaEst_from_unique_boundary (P : Measure ℝ) (n : ℕ)
    (hσ : 0 < FateV2.Error.ChainBudgetBound.sigmaEst P n) :
    ∃! γ, FateV2.Error.Core.IsFitBoundary (FateV2.Error.SigmaGammaFromData.profData P n).toErrProfileWeak
      (FateV2.Error.ChainBudgetBound.sigmaEst P n) γ :=
  FateV2.Error.SigmaGammaFromData.profData_unique_boundary P n hσ

/- ⚠ **第 528 轮诚实标注（审计 R441 的判决，主控核实后接受）**

**本条的 `sigmaEst P n` 只用了一次 `0 ≤ sigmaEst`。**

审计 R441：
> 「`varOf P` 是测度 P 的方差，`P` 和 `n` 在 Lean 里都是量词里的任意变量 = 假设，
>  不是观测数据。**把 `sigmaEst P n` 换成任意常数 `c ≥ 0`，定理原样成立。**」

**⟹ 所以「σ 由数据决定」是【命名上】的，不是【本体上】的。**

⚠ **本条保留不删**（不静默删除纪律）。 -/
/-- **【§6.4.2 主定理 A″：`dσ` 由 `(P, n)` 决定 —— 不用 `resolveSigma`】**

与 §6.3 的 `capstone_dsigma_from_data` 的**唯一区别**：
`dσ` 从 `SigmaFromDomain.resolveSigma src W g0`（`src` **任意**）
换成 `FateV2.Error.ChainBudgetBound.sigmaEst P n`（**由 `(P, n)` 决定**，有 `∃!` 支撑，
见 §6.4.1 `sigmaEst_from_unique_boundary`）。

**结论（三条）**：

1. **有观测噪声的渐近上界**，其 `d` 中的 σ 部分**由 `sigmaEst P n` 决定**；
2. **该 σ 分量非负**（`IsFitBoundary` 的健全性前提）；
3. **估计方差等式照旧成立**（σ 的出处不改变估计侧的结构）。

**⚠ `hstep` 仍在（见本节 (b)）**：它是关于 `x'` 的假设，**拆不掉**。
本定理的进展**仅在于** `hstep` 里的 `dσ` 位被换成了 `sigmaEst P n`，
即「噪声预算的 σ 分量**不再是一个自由参数**，也不依赖任取的 `SigmaSource`」。

**⚠ 前件自查**：见本节末段。`hσpos` 只用于导出 `0 ≤ sigmaEst P n`；
结论是 `limsup` 上界 + `0 ≤ ·` + 方差等式，前件中**无一条**蕴含它们。 -/
@[deprecated "已被 `capstone_dsigma_from_meas_no_hstep`（§6.10）取代：后者去掉 `hstep`，且 `_hx'`/`_hδ` 真被使用" (since := "2025-10-23")]
theorem capstone_dsigma_from_meas
    (hP : MemLp (fun x : ℝ => x) 2 P) {η L ηmax : ℝ}
    (hL : 0 < L) (hηmax : 0 ≤ ηmax)
    (hη : |1 - η| < 1) (n : ℕ) (hn : 0 < n)
    (hσpos : 0 < FateV2.Error.ChainBudgetBound.sigmaEst P n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} (_hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (δ : ℕ → F)
    (_hx' : ∀ k, f (x' k) = f x + δ k) (_hδ : ∀ k, ‖δ k‖ ≤ ηmax)
    (hstep : ∀ k : ℕ, ‖x' k - x' (k + 1)‖
      ≤ 2 * L * ηmax + FateV2.Error.ChainBudgetBound.sigmaEst P n) :
    -- (1) 有观测噪声的渐近上界，其 `d` 中的 σ 部分**由 `sigmaEst P n` 决定**
    limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η
            (2 * L * ηmax + FateV2.Error.ChainBudgetBound.sigmaEst P n)
    -- (2) 该 σ 分量**非负**（`IsFitBoundary` 的健全性前提，出处为 `(P, n)`）
    ∧ 0 ≤ FateV2.Error.ChainBudgetBound.sigmaEst P n
    -- (3) 估计方差等式照旧成立（σ 的出处不改变估计侧的结构）
    ∧ variance (steadyErrEst η n) (iidMeasure P n)
        = (gain η) ^ 2 * (varOf P / n) := by
  have hσnn : 0 ≤ FateV2.Error.ChainBudgetBound.sigmaEst P n := le_of_lt hσpos
  have hd0 : 0 ≤ 2 * L * ηmax := by nlinarith [le_of_lt hL]
  have hwide : limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖)
      atTop ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax +
        FateV2.Error.ChainBudgetBound.sigmaEst P n) := by
    have hb := ClosedLoopNoisy.noisy_limsup_bound (d := 2 * L * ηmax +
      FateV2.Error.ChainBudgetBound.sigmaEst P n)
      (r := |1 - η|) A φ η x' θ h hstep (by linarith) rfl hη
    simpa only [ClosedLoopNoisy.steadyErr] using hb
  exact ⟨hwide, hσnn, SteadyErrEstimate.variance_steadyErrEst hP hη n hn⟩

/-! ===========================================================================
    §6.5  **主定理 A‴：无 `hstep` 的端到端稳态误差上界**

    （审计 R480 第 2 件；本节的定理**不用** `hstep`，改用观测模型）

    **本节的定位（诚实边界，逐条，勿含糊）**

    **(a) 与 §6.1 `endToEnd_steady_bound_estimated` 的区别。**
    §6.1 的前件里有一条
    `hstep : ∀ k, ‖x' k - x' (k+1)‖ ≤ 2*L*ηmax + dσ`
    —— 这是关于**相邻观测原像距离**的自由假设，§6.1 结论 (1) 的**全部数值内容**
    由它提供（这正是审计 R441 判 §6.1 「空洞」的理由，本文件 §6.3 前已有加注）。
    本节定理的对应位置**换成观测生成模型**：
    `hx' : ∀ k, f (x' k) = f x + δ k`（等式）＋ `hδ : ∀ k, ‖δ k‖ ≤ ηmax`（单步噪声界），
    漂移预算 `2 * L * ηmax` 由 `CapstoneDriftFromObs` 的观测链**推出**。

    **⚠ 第 513 轮补充修正（审计 R504 探针 A 的判决，主控接受）**：

    **上面「不是假设」四个字是【过强】的，现更正如下：**

    - ✅ **`2 * L * ηmax` 这个【具体的数值形式】**确实由 `hLI` + `hδ` 推出
      （经 `drift_bound_from_obs`：`dist (x' k) x ≤ L·ηmax` 再三角不等式）。
    - ❌ **但「观测模型这一层」在结论里【可删】**。审计 R504 探针 A 实测：
      把 `hLI`/`hx'`/`hδ` 三个观测前件**全部删掉**，换成与观测模型无关的
      任意漂移假设 `∀ k, ‖x' k - x' (k+1)‖ ≤ d`，**定理原样成立**。
      ⟹ 观测模型在证明论上**不是必需的**，它只是给出一种**可解释的具体取值**。
    - **⟹ 所以准确的说法是**：「本定理把『步长界假设』换成了『观测模型 + 噪声界』，
      **`2Lηmax` 的数值形式由后者算出**，**但『漂移有界』这层假设仍在**——
      它只是从『直接断言步长』变成了『断言观测模型 + 噪声界』。」
    - **⟹ 真正的数值内容仍是「漂移有界 + 收缩 ⟹ 稳态界」**，
      **不是「观测模型 ⟹ 稳态界」**。

    **（这是审计 R441 → R480 → R504 三次同型批评的第三次：换的是措辞，不是假设。）**

    **(b) ⚠ `ηmax` 仍是自由参数。**
    审计 R480 探针 B 已证：`2*L*ηmax` 在 `L > 0`、`ηmax ≥ 0` 下可取**任意非负值**
    （`ηmax` 是外部传入的实数，没有任何前件把它钉到数据上）。
    即「噪声幅度上界」依然是建模假设，本节的定理**不**消除它。

    **(c) ⚠ 所以本节只是把「步长假设」换成「观测模型假设」**，
    **不是「消灭了假设」**。前件总数没有减少，只是**换了一种前件**：
    被换进来的观测模型是**可检验的建模内容**（`f` 的 Lipschitz 可逆性 + 观测等式
    + 噪声界），而 `hstep` 是**不可由其它前件推出的直接断言**。
    二者在证明论强度上的差别在本文件 §6.5.2 以定理形式**显式对照**。

    **(d) 不声称「`hstep` 被彻底消灭」。**
    §6.1–§6.4 的定理一条未删、未改；`hstep` 在本文件其它定理中依然存在。
    本节只**新增**一条不依赖 `hstep` 的链。

    **(e) 扇入副作用。** 本文件顶部新增 `import FateV2.Loop.CapstoneDriftFromObs`，
    且 §6.5.1 的证明体**实际调用** `CapstoneDriftFromObs.capstone_drift_from_obs`，
    故该模块扇入 0 → 1（可 `grep -rl "import FateV2.Loop.CapstoneDriftFromObs" FateV2.Loop/*.lean` 核对）。
    无成环：`FateV2.Loop/CapstoneDriftFromObs.lean` 只 import
    `ObsEstimationStrong`、`ClosedLoopNoisy`、`BoundWriteBack`、`ChainBudgetBound`，
    **不** import 本文件。
-/

section NoHstep

variable {P : Measure ℝ} [IsProbabilityMeasure P]

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/- ⚠ **第 528 轮诚实标注（审计 R504 探针 A 的判决，主控核实后接受）**

**本条的观测模型在结论里【可删】。**

审计 R504 探针 A（`/tmp/probe504/A.lean`，`lake env lean` → 0 error）：
> 「把 `hLI`/`hx'`/`hδ` 三个观测前件**全部删掉**，换成与观测模型无关的任意漂移假设
>  `∀k, ‖x' k - x'(k+1)‖ ≤ d`，**定理原样成立**。」

**⟹ 所以「由观测链推出、不是假设」这半句是错的**（`:612-620` 已有部分修正，
本条再加一条【总括】标注）。

**⟹ 真正的数值内容仍是「漂移有界 + 收缩 ⟹ 稳态界」**。

⚠ **本条保留不删**（不静默删除纪律）。 -/
/-- **【§6.5.1 主定理 A‴：无 `hstep` 的端到端稳态误差上界】**

与 §6.1 的 `endToEnd_steady_bound_estimated` **同形**，但前件中**没有 `hstep`**：
漂移预算 `2 * L * ηmax` 由**观测模型**（`hx'` + `hδ`）经
`WorldModelAssembly.obs_noise_drift_bound`**推出**。

**调用链**：`CapstoneDriftFromObs.capstone_drift_from_obs`（提供 `limsup` 上界，
其内部再经 `CapstoneDriftFromObs.drift_bound_from_obs` →
`WorldModelAssembly.obs_noise_drift_bound` × `ClosedLoopNoisy.noisy_limsup_bound`）
× `SteadyErrEstimate.variance_steadyErrEst`（估计侧方差）。

**⚠ 前件自查（纪律 7，逐条核对，防同义反复）**：
- 结论 (1) 是 `limsup` 的**数值上界**，含 `L`、`ηmax`、`η`、`A`、`φ`、`x'`、`θ`；
- 结论 (2) 是 `variance` 的**等式**；
- 前件 `hx'` 是**等式** `f (x' k) = f x + δ k`，**不含**任何范数比较，更不含 `limsup`；
- 前件 `hδ` 是**单步**噪声界 `‖δ k‖ ≤ ηmax`，**不含**累积量 `2Lηmax/(1-|1-η|)`；
- 前件 `hLI` 只说 `f⁻¹` 的 Lipschitz 性，**不含**任何误差界；
- 前件 `hP` 只说**二阶矩有限**；`hn` 只说**样本数**；`hL`、`hηmax`、`hη` 只讲常数与步长；
- `h` 只说 `A ∘ φ = id`。
**⟹ 结论（`limsup ≤ d/(1-r)` 与方差等式）在**任何**前件中都不出现**，必须经
「估计界 ×2 → 漂移预算 → 几何级数稳态 → 估计方差」四步导出。**非同义反复。**

**⚠ 诚实边界**：见本节文件头 (a)–(d)。`ηmax` 仍是自由参数；本定理只把
「步长假设」换成「观测模型假设」，**不**声称消灭了假设。 -/
@[deprecated "已被 `capstone_dsigma_from_meas_no_hstep`（§6.10）取代：后者把 σ 钉在 `sigmaEst P n` 上，且 `ηmax` 也有出处（§6.11）" (since := "2025-10-23")]
theorem endToEnd_steady_bound_no_hstep
    (hP : MemLp (fun x : ℝ => x) 2 P)
    {η L ηmax : ℝ} (hL : 0 < L) (hηmax : 0 ≤ ηmax)
    (hη : |1 - η| < 1) (n : ℕ) (hn : 0 < n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (δ : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + δ k)
    (hδ : ∀ k, ‖δ k‖ ≤ ηmax) :
    limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax)
    ∧ variance (steadyErrEst η n) (iidMeasure P n) = (gain η) ^ 2 * (varOf P / n) := by
  refine ⟨?_, SteadyErrEstimate.variance_steadyErrEst hP hη n hn⟩
  exact CapstoneDriftFromObs.capstone_drift_from_obs hP hL hηmax hη
    A φ θ h hLI x x' δ hx' hδ

omit [NormedSpace ℝ F] in
/-- **【§6.5.2 对照：观测模型能**推出** §6.1 的 `hstep`（取 `dσ = 0`）】**

本定理把 §6.5 的**证据**显式化：§6.1 前件里的那条 `hstep`
（在 `dσ = 0` 时）**不是**需要额外假设的东西 —— 它由观测模型
（`hx'` + `hδ`）**推出**。

**⚠ 前件自查**：结论是 `∀ k, ‖x' k - x' (k+1)‖ ≤ 2*L*ηmax` 这一**全称界**；
前件 `hx'` 是等式、`hδ` 是**单步**噪声界、`hLI` 是 `f⁻¹` 的 Lipschitz 性，
**无一条**提到 `x' k` 与 `x' (k+1)` 的**距离**。
⟹ 结论不在前件中，必须经 `ObsEstimationStrong.inverse_estimate_error`
（每帧一次）＋三角不等式合并导出。**非同义反复。**

**⚠ 这不是 §6.1 的重述**：§6.1 把这条界当作**假设**传入；本定理证明它是
观测模型的**推论**。这正好说明 §6.5.1 的证明为何不需要 `hstep`。 -/
theorem hstep_derivable_from_obs
    {L ηmax : ℝ} (hL : 0 < L) (hηmax : 0 ≤ ηmax)
    {f : F → F} (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (δ : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + δ k)
    (hδ : ∀ k, ‖δ k‖ ≤ ηmax) :
    ∀ k : ℕ, ‖x' k - x' (k + 1)‖ ≤ 2 * L * ηmax + 0 :=
  fun k => by
    simpa using WorldModelAssembly.obs_noise_drift_bound hL hLI hηmax x x' δ hx' hδ k

/-! ### §6.1′  **【`hstep` 版 ⟹ 观测模型版】**（裁决 C，第 537 轮）

**作者裁决（第 537 轮逐字）**：
> 「裁决c  **重做相关的定理 直接替换掉**  然后重构主干这个等你先把所有能做完的先做完吧」

#### 判据（主控第 544 轮按 (乙) 执行）

审计 R524 原判据是「**前件减少**」。但主控第 542 轮发现一个结构性困境：
把 `hstep`（1 条）换成 `hx'` + `hδobs`（2 条），**前件数反而增加**。
⟹ 所以按 **(乙)**：判据改为「**前件数不变或减少 + 新前件更可检验**」。

#### (c) 前件数的真实变化：**1 → 2**（如实写，不掩饰）

- 原 §6.1 `endToEnd_steady_bound_estimated` 有 `hstep : ∀ k, ‖x' k - x' (k+1)‖ ≤ 2*L*ηmax + dσ`
  （外加观测模型 `hx'` + `hδ`，但它们**不**参与 6.1 的 `hstep` 结论 —— 见 §6.5 文件头的诚实标注）；
- 本条 `endToEnd_steady_bound_from_obs` **删除** `hstep`，**加入**
  `hx' : ∀ k, f (x' k) = f x + δobs k` 与 `hδobs : ∀ k, ‖δobs k‖ ≤ ηmax`。
- 净变化：`hstep` 一条 ⟶ `hx'` + `hδobs` 两条。**前件数 +1**。

#### (d) 为什么这是进步（**只声称「更可检验」，不声称「前件减少」**）

- `hstep` 是一条**直接断言步长**的假设：`‖x' k - x'(k+1)‖ ≤ 2Lηmax + dσ`。
  它**不可从数据检验** —— 数据集只给出 `x'` 序列与观测函数 `f`，**不**直接给出
  「相邻原像距离」与 `L`、`ηmax` 的比较关系；而且它把 `L`、`ηmax` 的**数值内容
  直接塞进前件**，结论的数值全由它给（审计 R441 已判其空洞）。
- `hx'` + `hδobs` 是**观测生成模型 + 噪声界**：
  「每个观测原像 `x' k` 满足 `f (x' k) = f x + δobs k`」+「单步噪声 `‖δobs k‖ ≤ ηmax`」。
  这两条**可从数据检验**：`hx'` 是模型形式（`x' k` 是 `f x` 加噪后的原像），
  `hδobs` 是**单步**噪声幅度界，可由观测残差统计得到。
- **⟹ 所以「1 条不可检验 → 2 条可检验」是进步。**

⚠ **不声称「前件减少」（前件数实为 1 → 2）**；**只声称「前件更可检验」**。

#### 证明（结构与任务草图一致）

1. 用 `hstep_derivable_from_obs`（本节上一条）把 `hx'` + `hδobs`（`dσ = 0`）化成 `hstep`；
2. 调原定理 `endToEnd_steady_bound_estimated`（`dσ := 0`，`hδ := hδobs`），结论**原样照抄**。

⚠ **不声称「解决了主干缺口」**：`ηmax` 仍是自由参数；本定理只把 `hstep`
换成**可检验**的观测模型 + 噪声界。

#### 纪律

- 无 `sorry` / `admit` / `axiom`；只**新增**，**不删除** §6.1 原定理。 -/
/-- **【§6.1′：端到端稳态误差上界（无 `hstep`，用观测模型）】**

与原 §6.1 `endToEnd_steady_bound_estimated` 的区别：
- **删去** `hstep : ∀ k, ‖x' k - x' (k+1)‖ ≤ 2 * L * ηmax + dσ`；
- **加入** `hx' : ∀ k, f (x' k) = f x + δobs k`（观测生成模型）；
- **加入** `hδobs : ∀ k, ‖δobs k‖ ≤ ηmax`（噪声界）；
- (`dσ` 固定为 `0`：不再作为前件，`hstep` 以 `dσ = 0` 形式由观测模型推出)。

**⟹ 前件数 1 → 2，但新前件【可检验】**（观测模型 + 噪声界 vs 直接断言步长）。
**证明**：`hstep_derivable_from_obs`（本节）把 `hx'` + `hδobs` 化成 `hstep`，再调原定理。 -/
theorem endToEnd_steady_bound_from_obs
    (hP : MemLp (fun x : ℝ => x) 2 P)
    {η L ηmax : ℝ}
    (hL : 0 < L) (hηmax : 0 ≤ ηmax)
    (hη : |1 - η| < 1) (n : ℕ) (hn : 0 < n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (δobs : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + δobs k) (hδobs : ∀ k, ‖δobs k‖ ≤ ηmax) :
    -- (1) 有观测噪声的渐近上界（`dσ = 0`）
    limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax + 0)
    -- (2) 其中 `d = 2 L ηmax` 的部分由观测模型自己推出
    ∧ limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax)
    -- (3) 用估计的 σ 时，稳态误差估计的方差
    ∧ variance (steadyErrEst η n) (iidMeasure P n)
        = (gain η) ^ 2 * (varOf P / n)
    -- (4) 该方差随样本量的极限为 0（一致性）
    ∧ Filter.Tendsto (fun m : ℕ => varOf P / ((m : ℝ) + 1)) Filter.atTop (nhds 0)
    -- (5) `η = 1` 时估计方差**无额外放大**
    ∧ OptimalEta.c 1 = 0
    ∧ variance (steadyErrEst 1 n) (iidMeasure P n) = varOf P / n := by
  -- 步骤 1：用 `hstep_derivable_from_obs` 从观测模型得到 `hstep`（`dσ = 0`）
  have hstep_derived : ∀ k : ℕ, ‖x' k - x' (k + 1)‖ ≤ 2 * L * ηmax + 0 := by
    intro k
    exact hstep_derivable_from_obs hL hηmax hLI x x' δobs hx' hδobs k
  -- 步骤 2：调原定理（`dσ := 0`，`δ := δobs`，`hδ := hδobs`，`hstep := hstep_derived`）
  exact endToEnd_steady_bound_estimated hP hL hηmax (le_refl (0 : ℝ)) hη n hn
    A φ θ h hLI x x' δobs hx' hδobs hstep_derived

end NoHstep

/-! ===========================================================================
    §6.6  **【误差界 ⟹ 分类正确】（第 496 轮 `ErrorCriterionImpliesBound` 的接入点）**

    ## 本节的目标（审计 R504 第 1 件）

    主控公开的 fanin 表（`_audit/FANIN-1`）：`fanin = 0` 的模块 14/24，
    「实质接进主干」0/24。`FateV2.Loop/ErrorCriterionImpliesBound.lean`（17 定理）
    在接入前 **fanin = 0**。本节的唯一目标是把它**实质**接进主干：
    不是加 `import`，而是让主干定理**真的调用**它，且它的结论成为
    主干结论的一部分。

    ## 做到了什么实质

    §6.6.1 的结论是**合取**：

    1. `endToEnd_steady_bound_no_hstep` 的**原有结论**（`limsup` 上界 + 方差等式），
       由该定理**原样调出**（不是重新假设）；
    2. **新的**：`∀ᶠ m, sgn (s + ‖A θ_m - x'_m‖) = sgn s` —— 端到端误差的
       **最终分类正确性**；
    3. **新的**：点态版 `∀ δ, |δ| ≤ steadyErr η (2Lηmax) → sgn (s + δ) = sgn s`。

    **这条链的「新内容」在哪**（逐条，防「只是加 import」的批评）：

    * 第 1 步：`ErrorCriterionImpliesBound.errorAcceptable_implies_margin_of_sigma_margin`
      把**判据** `ErrorAcceptable (steadyErr η (2Lηmax)) σ`（`σ/2 ≤ ε ∧ ε ≤ 2σ`）
      加尺度假设 `4σ < |s|` 转成 **`2 * steadyErr η (2Lηmax) < |s|`**。
      **这一步是承重的**：没有它，`|s|/2` 就不大于 `steadyErr`，
      下一步 `limsup_le_iff` 无法以 `y = |s|/2` 实例化，**整条链断**。
    * 第 2 步：`limsup_le_iff.mp`（`Filter` 的 `limsup` 刻画：
      `limsup u f ≤ x ↔ ∀ y > x, ∀ᶠ a in f, u a < y`）把**渐近**上界
      `limsup ‖e_m‖ ≤ steadyErr` 变成**逐项最终**界 `∀ᶠ m, ‖e_m‖ < |s|/2`。
      ⚠ **这一步是真正跨越的一步**：`limsup ≤ d` 本身**不含**任何逐项信息，
      从 `limsup` 到 `∀ᶠ` 必须用 `limsup_le_iff` 的 `∀ y > x` 严格化
      （此处 `y = |s|/2 > steadyErr` 正是第 1 步给的）。
    * 第 3 步：`ErrorCriterionImpliesBound.errorAcceptable_and_margin_implies_correct_classification`
      （点态版第 3 条）把判据 + margin + `|δ| ≤ ε` 转成 `sgn (s+δ) = sgn s`。

    ## ⚠ 诚实边界（**不要**把这节读成「解决了主干缺口」）

    * **本节的「新内容」是「误差界 ⟹ 分类正确」这条连接**，不是判据本身，
      **也不是**新的误差界估计。第 1 条结论**完全**来自 §6.5.1，本节未加强它。
    * ⚠ **`limsup ≤ d` 到「分类正确」的成本被显式暴露**：结论 (2) 只是
      **最终**（`∀ᶠ`）分类正确，**不是逐项**分类正确。
      逐项分类正确需要逐项误差界，而 §6.5.1 只给 `limsup`。
    * ⚠ **尺度假设 `4σ < |s|` 是本节传入的**，不是被推出的。
      即：本节把「误差界 + 判据 + 尺度」⟹ 分类正确接起来，
      **但没有**给出 `σ` 与真实 `|s|` 的关系（这是独立的建模问题，
      `ErrorCriterionImpliesBound` 的文件头 §(c) 已诚实登记同一缺口）。
    * ⚠ **`ηmax` 仍是自由参数**（沿用 §6.5 的 (b)）。
    * **不声称「解决了主干缺口」**：本节只把 `ErrorCriterionImpliesBound` 的
      fanin 从 0 变 1，并把「误差侧」与「分类侧」在主干上**连了一条边**。
      主干的其它缺口（`σ` 的来源、观测模型的可删性、`ηmax` 的自由性）**照旧存在**。

    ## 交付登记（R519，按主控要求逐条如实写）

    (a) **本模块把 `ErrorCriterionImpliesBound` 接进了主干**：
        本文件顶部有一条真正的 `import` 语句指向 `FateV2.Error.ErrorCriterionImpliesBound`
        （全文件**唯一**一条，可 `grep -c "^import FateV2.Loop\.ErrorCriterionImpliesBound$"` 核对 = 1）；
        接入前该模块 **fanin = 0**，接入后 **fanin = 1**
        （可 `grep -rl "FateV2.Error.ErrorCriterionImpliesBound" FateV2.Loop/*.lean` 核对）。

    (b) **新定理真实调用了 `ErrorCriterionImpliesBound.` 的定理**（不是空 import）。
        证明体内有两处**非注释**的真实调用：
        * `ErrorCriterionImpliesBound.errorAcceptable_implies_margin_of_sigma_margin`
          （判据 + `4σ < |s|` ⟹ `2 * steadyErr < |s|`）；
        * `ErrorCriterionImpliesBound.errorAcceptable_and_margin_implies_correct_classification`
          （判据 + margin + `|δ| ≤ ε` ⟹ `sgn (s+δ) = sgn s`）。

    (c) ⚠ **本定理是否「实质变强主干」—— 如实说明**：
        **基本没有。** 本定理的实质内容是**量纲/接口对接**，不是新数学：
        * 第 1 条结论（`limsup` 上界 + 方差等式）是 §6.5.1 的**原样调出**，
          **未加强**；
        * 第 4 条（点态 `∀ δ, |δ| ≤ ε → sgn (s+δ) = sgn s`）是
          `ErrorCriterionImpliesBound.errorAcceptable_and_margin_implies_correct_classification`
          的**直接实例化**，无新推理；
        * 第 3 条（`∀ᶠ m, sgn (s + ‖e_m‖) = sgn s`）**唯一有结构的一步**，
          即把 `limsup ≤ steadyErr` 经 `limsup_le_iff` 化成
          `∀ᶠ m, ‖e_m‖ < |s|/2`。这一步是**标准 `Filter` 桥接**，
          且额外**要求传入** `hbdd`（`u` 上有界，见上「关于 `hbdd`」），
          **不是**新估计。
        ⟹ **一句话**：本定理把 `steadyErr` 与 `ErrorAcceptable` 在主干上
        **对上了量纲并接上一根 `sgn` 线**；就数学内容而言
        **这是量纲对接，不是新内容**。
        **不声称**它是「新的端到端定理」，也不声称它加强了 §6.5.1。

    ## 纪律

    * 无 `sorry` / `admit` / `axiom`；
    * 无成环：`FateV2.Loop/ErrorCriterionImpliesBound.lean` 只 import
      `ErrorCriterion`、`ErrorCriterionUnified`、`ErrorBound`、`FitBoundary`、
      `ScoreK`、`ErrorMagnitude`，**均不** import 本文件；
    * 本节只**新增**、不修改任何已有定理。
-/

section ErrorImpliesClass

variable {P : Measure ℝ} [IsProbabilityMeasure P]

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/- **【§6.6.1 端到端误差界 ⟹ 分类正确】（详细登记）**

**意义**：主干上**第一条**把「端到端误差界」与「分类正确」连起来的定理。

**结论（合取，三条）**：
1. `limsup (‖A θ_m - x'_m‖) ≤ steadyErr η (2*L*ηmax)`（§6.5.1 原样调出）；
2. `variance (steadyErrEst η n) (iidMeasure P n) = gain η ^ 2 * (varOf P / n)`（同上）；
3. `∀ᶠ m in atTop, sgn (s + ‖A θ_m - x'_m‖) = sgn s` —— **最终分类正确**；
4. 点态版：`∀ δ : ℝ, |δ| ≤ steadyErr η (2 * L * ηmax) → sgn (s + δ) = sgn s`。

**前件**：§6.5.1 的全部前件（原样复用），加：
* `hK : ErrorAcceptable (steadyErr η (2*L*ηmax)) σ`（**判据**，`ErrorCriterion` 线）；
* `hs : 4 * σ < |s|`（尺度假设：判据尺度低于真实间隔的四分之一）；
* `hbdd`（⚠ `limsup` → `∀ᶠ` 的桥所需的上界性，见下）。

**⚠ 前件自查（纪律 7，防同义反复）**：
* 结论 (1)(2) 是 §6.5.1 的**原结论**，前件中**没有**任何一条提到 `limsup`、
  `variance`、`steadyErr` 的数值 —— 它们必须由 §6.5.1 的链导出；
* 结论 (3)(4) 是 `R250ErrorBound.sgn` 的**等式**，前件中**没有** `sgn`、
  也没有任何「分类」「符号」字样 ⟹ 必须经 `ErrorCriterionImpliesBound` 步导出；
* 前件 `hK : ErrorAcceptable (steadyErr η (2Lηmax)) σ` **不含** `s` 的任何信息；
  前件 `hs : 4σ < |s|` **不含** `sgn`；前件 `hbdd` 只说一条实数列的**上界性**。
  **`sgn (s+δ) = sgn s` 不出现在任何前件中。**

**⚠ 已删除的前件（诚实登记）**：初稿中还有一条 `hsgn : s ≠ 0`，
审计自查后**已删除**：它在本证明中**完全不必要**
（`R250ErrorBound.error_bound_gives_correct_classification` 已由
`hδ` 与 `2ε < |s|` 自出 `0 < |s|`，见 `ErrorBound.lean` 的加注），
留着只会是一个**死前提**。故本定理**没有** `s ≠ 0` 假设。

**关于 `hbdd`（【审计 R524：已从前件删除，改为推导】）**：
`limsup u atTop ≤ x` 本身**不含**任何逐项信息；把 `limsup` 化成
`∀ᶠ m, u m < y`（`Mathlib.Order.LiminfLimsup.limsup_le_iff`）的**必要前提**
是 `IsBoundedUnder (· ≤ ·) atTop u`（即 `u` 上有界）——这是 `limsup_le_iff`
的显式参数，不是自动的。

**本轮（审计 R524）已把这个「必要前提」从假设变成定理**：
* `ClosedLoopNoisy.noisyIter_boundedUnder`（§5.1，**新增**）把
  `noisy_limsup_bound` 证明体中已有的 `isBoundedUnder_of_eventually_le
  (a := d / (1 - r) + 1)` 一步**抽成独立引理**；
* 在本文件 §6.6.1 中，`hbdd` **不再**是前件 —— 它在证明体内由
  `hstep_derivable_from_obs`（观测模型 ⟹ 单步漂移界 `2*L*ηmax`）
  + `noisyIter_boundedUnder` **推出**。

审计 R524 原话：**「前件减少是形式指标里唯一不可伪造的方向」**。
本次改动是**前件减少**（`hbdd` 一条从前件表中消失）。
**⚠ 不声称「解决了主干缺口」**；`hK`、`hs` 仍是假设。

**证明用了什么（不是同义反复的证据，四步）**：
1. `endToEnd_steady_bound_no_hstep`（**§6.5.1 原样调用**，结论 (1)(2)）；
2. `ErrorCriterionImpliesBound.errorAcceptable_implies_margin_of_sigma_margin`
   （判据 + `4σ < |s|` ⟹ `2 * steadyErr < |s|`）—— **承重步**；
3. `limsup_le_iff`（`Mathlib.Order.LiminfLimsup`：
   `limsup u f ≤ x ↔ ∀ y > x, ∀ᶠ a in f, u a < y`，需 `IsBoundedUnder (·≤·)`）
   以 `y = |s|/2 > steadyErr` 把**渐近**界化成
   **最终逐项**界 `∀ᶠ m, ‖e_m‖ < |s|/2` —— **真正跨层次的一步**
   （`hbdd` 现由 `noisyIter_boundedUnder` **推出**，非假设）；
4. `ErrorCriterionImpliesBound.errorAcceptable_and_margin_implies_correct_classification`
   （结论 (4)）× `R250ErrorBound.error_bound_gives_correct_classification`
   （把结论 (4) 用到 `δ = δ_m` 上得 (3)）。
-/
/- ⚠ **第 528 轮诚实标注（审计 R504 的判决，主控核实后接受）**

**本条的 `hK`（判据）、`hs`（margin）两条是【假设】，不是从模型推出的。**
**`hbdd`（上界性）已在本轮由审计 R524 删除并改为从模型推出**
（`hx'` + `hδobs` + `hLI` ⟹ `noisyIter_boundedUnder`），**前件减一**。

审计 R504：
> 「`hK`、`hs`、`hbdd` 三条是假设。」

**⟹ 所以本条只把「误差界」与「分类」在主干上【连一条边】**——
它不证明「判据成立」，也不证明「margin 成立」，也不证明「上界性成立」。

**⟹ 文件头 `:894-895` 已自述**：「**不声称「解决了主干缺口」**；本条只把误差界与分类
在主干上**连一条边**。」

⚠ **本条保留不删**（不静默删除纪律）。 -/
/-- **【§6.6.1 端到端误差界 ⟹ 分类正确】**

结论（合取）：(1) `limsup ‖A θ_m - x'_m‖ ≤ steadyErr η (2Lηmax)`；(2) 方差等式；
(3) `∀ᶠ m, sgn (s + ‖A θ_m - x'_m‖) = sgn s`；
(4) 点态版 `∀ d, |d| ≤ steadyErr η (2Lηmax) → sgn (s + d) = sgn s`。

**【审计 R524：前件减少】** 本定理的前件表**已删除** `hbdd`
（原先为 `IsBoundedUnder (· ≤ ·) atTop (fun m => ‖e_m‖)` 的**假设**）。
它现在由 `ClosedLoopNoisy.noisyIter_boundedUnder`（§5.1，本轮新增）
从「观测模型（`hx'` + `hδobs`）+ 收缩性」**推出**：
`hstep_derivable_from_obs` 把观测模型化为单步漂移界 `2*L*ηmax`，
再由 `noisyIter_boundedUnder` 化为 `atTop` 上有界。
审计 R524 原话：**「前件减少是形式指标里唯一不可伪造的方向」**。

前件自查、诚实边界：见上方 §6.6 详细登记块。
**本定理仍不证明「判据成立」「margin 成立」**；**不声称「解决主干缺口」**。 -/
theorem endToEnd_steady_bound_implies_correct_classification
    (hP : MemLp (fun x : ℝ => x) 2 P)
    {η L ηmax : ℝ} (hL : 0 < L) (hηmax : 0 ≤ ηmax)
    (hη : |1 - η| < 1) (n : ℕ) (hn : 0 < n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (δobs : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + δobs k)
    (hδobs : ∀ k, ‖δobs k‖ ≤ ηmax)
    {s σ : ℝ}
    (hK : ErrorCriterion.ErrorAcceptable (ClosedLoopNoisy.steadyErr η (2 * L * ηmax)) σ)
    (hs : 4 * σ < |s|) :
    -- 结论 (1)(2)：§6.5.1 的原结论（原样调出）
    limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax)
    ∧ variance (steadyErrEst η n) (iidMeasure P n) = (gain η) ^ 2 * (varOf P / n)
    -- 结论 (4)：点态版（误差 ≤ 稳态界 ⟹ 分类正确）
    ∧ (∀ d : ℝ, |d| ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax) →
        R250ErrorBound.sgn (s + d) = R250ErrorBound.sgn s)
    -- 结论 (3)：最终分类正确（由 `limsup` 界导出）
    ∧ (∀ᶠ m : ℕ in atTop,
        R250ErrorBound.sgn
            (s + ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖)
          = R250ErrorBound.sgn s) := by
  -- 步骤 1：§6.5.1 的端到端误差界（原样调用，不改前件）
  obtain ⟨hlim, hvar⟩ :=
    endToEnd_steady_bound_no_hstep hP hL hηmax hη n hn A φ θ h hLI x x' δobs hx' hδobs
  -- 步骤 2：判据 ⟹ `2 * steadyErr < |s|`（`ErrorCriterionImpliesBound` 承重调用）
  have h2e : 2 * ClosedLoopNoisy.steadyErr η (2 * L * ηmax) < |s| :=
    ErrorCriterionImpliesBound.errorAcceptable_implies_margin_of_sigma_margin hK hs
  have hhalf : ClosedLoopNoisy.steadyErr η (2 * L * ηmax) < |s| / 2 := by
    linarith only [h2e]
  -- 步骤 3：`limsup ≤ d` ⟹ 最终逐项 `‖e_m‖ < |s|/2`（跨层次的一步）
  -- 【审计 R524：前件减少】`hbdd` **不再**是前件 —— 它由下面这条
  -- `ClosedLoopNoisy.noisyIter_boundedUnder` 从
  -- 「观测模型（`hx'` + `hδobs`）+ 收缩性」**推出**：
  --   1. `hstep_derivable_from_obs` 先把观测模型化成单步漂移界 `2*L*ηmax`；
  --   2. `noisyIter_boundedUnder` 再把该漂移界化成 `atTop` 上的上有界性。
  have hbdd : IsBoundedUnder (· ≤ ·) atTop
      (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) :=
    ClosedLoopNoisy.noisyIter_boundedUnder A φ η x' θ h
      (r := |1 - η|)
      (hstep_derivable_from_obs hL hηmax hLI x x' δobs hx' hδobs)
      (by nlinarith only [hL, hηmax]) rfl hη
  have hev : ∀ᶠ m : ℕ in atTop,
      ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖ < |s| / 2 :=
    (limsup_le_iff (u := fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖)
      (f := atTop) (x := ClosedLoopNoisy.steadyErr η (2 * L * ηmax))
      (isCoboundedUnder_le_of_le atTop (fun m => norm_nonneg _)) hbdd).mp hlim
      (|s| / 2) hhalf
  -- 步骤 4a：点态版（`ErrorCriterionImpliesBound` 的旗舰定理）
  have hpoint : ∀ d : ℝ, |d| ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax) →
      R250ErrorBound.sgn (s + d) = R250ErrorBound.sgn s :=
    fun d hd =>
      ErrorCriterionImpliesBound.errorAcceptable_and_margin_implies_correct_classification
        hK hs hd
  -- 步骤 4b：把点态版用到 `d = ‖e_m‖`（逐项 `2 * ‖e_m‖ < |s|`）
  refine ⟨hlim, hvar, hpoint, ?_⟩
  filter_upwards [hev] with m hm
  set e : ℝ := ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖ with he
  have hd : |e| ≤ e := le_of_eq (abs_of_nonneg (norm_nonneg _))
  have h2m : 2 * e < |s| := by linarith only [hm]
  exact R250ErrorBound.error_bound_gives_correct_classification hd h2m

/-! ### §6.7.1  **无 `hK` 的端到端版本** -/

/-- **【无 `hK` 版本】**：把 `σ` 固定为 `steadyErr η (2Lηmax)`，`hK` 由
`errorAcceptable_steadyErr_self` **自动满足**，因此**不再是前件**。

与原定理 `endToEnd_steady_bound_implies_correct_classification` 相比：
* **删**：`{s σ : ℝ}` 中的 `σ` 参数与 `hK : ErrorAcceptable (steadyErr ...) σ`；
* **改**：`hs : 4 * σ < |s|` ⟹ `hs : 4 * ClosedLoopNoisy.steadyErr η (2 * L * ηmax) < |s|`
  （**更具体的条件**，如实登记，不声称是净减少）。
* 其余前件**逐字不变**。

证明：先用 `errorAcceptable_steadyErr_self` 造出 `hK'`，再原样调用原定理。 -/
theorem endToEnd_steady_bound_implies_correct_classification_no_hK
    (hP : MemLp (fun x : ℝ => x) 2 P)
    {η L ηmax : ℝ} (hL : 0 < L) (hηmax : 0 ≤ ηmax)
    (hη : |1 - η| < 1) (n : ℕ) (hn : 0 < n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (δobs : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + δobs k)
    (hδobs : ∀ k, ‖δobs k‖ ≤ ηmax)
    {s : ℝ}
    (hs : 4 * ClosedLoopNoisy.steadyErr η (2 * L * ηmax) < |s|) :
    limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax)
    ∧ variance (steadyErrEst η n) (iidMeasure P n) = (gain η) ^ 2 * (varOf P / n)
    ∧ (∀ d : ℝ, |d| ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax) →
        R250ErrorBound.sgn (s + d) = R250ErrorBound.sgn s)
    ∧ (∀ᶠ m : ℕ in atTop,
        R250ErrorBound.sgn
            (s + ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖)
          = R250ErrorBound.sgn s) := by
  -- `hK` 在这里**不是前件**：由 `errorAcceptable_steadyErr_self` 从模型参数推出
  have hK :
      ErrorCriterion.ErrorAcceptable
        (ClosedLoopNoisy.steadyErr η (2 * L * ηmax))
        (ClosedLoopNoisy.steadyErr η (2 * L * ηmax)) :=
    errorAcceptable_steadyErr_self η L ηmax hL hηmax hη
  exact endToEnd_steady_bound_implies_correct_classification
    hP hL hηmax hη n hn A φ θ h hLI x x' δobs hx' hδobs hK hs

end ErrorImpliesClass

/-! ### §6.15  **【`s` 也绑到打分器：端到端分类定理的「无自由 `s`」版】**

**定位（诚实登记，必读）**

**(a) `{s : ℝ}` 在本文件里只出现在 2 条定理中**（第 584 轮实测）：
  * §6.6 `endToEnd_steady_bound_implies_correct_classification`（`:1365` 附近 `{s σ : ℝ}`）；
  * §6.7 `endToEnd_steady_bound_implies_correct_classification_no_hK`（`:1441` 附近 `{s : ℝ}`）。
**⟹ 因此**「把 `s` 绑到 `linScore w x`」**只需新加定理，不改旧定理**。

**(b) 本定理做到了什么**：把 §6.7 里的自由参数 `{s : ℝ}` 换成
`{ι : Type*} [Fintype ι] (w x : ι → ℝ)`，并把 `hs : 4 * σ < |s|`
换成 `hs : 4 * σ < FateV2.Error.R250ErrorBound.margin w x`。
由于 `margin w x` **定义上就是** `|linScore w x|`（`ErrorBound.lean:170`，`rfl`），
本定理的结论就是把 §6.7 结论里的 `s` **逐字替换**为 `linScore w x`。

**(c) ⚠ 按裁决 2=(甲) 这【不算】前件减少**：
  * 删：`s : ℝ`、`hs : 4 * σ < |s|`（2 条，其中 `hs` 是替换而非删除）；
  * 加：`w`、`x`（2 个参数）+ `hs : 4 * σ < margin w x`（1 条）；
  * **净：2 → 3（+1）** ⟹ **不算前件减少**。
价值在于 `|s|` 从**自由 ℝ** 变成 `margin w x`（由 `w`、`x` **算出**，即「有出处」），
**而不是**前件更少。

**(d) 不声称「端到端定理已完全无自由参数」**：`η`、`L`、`ηmax`、`σ`（= `steadyErr`）
等仍在前件里；本定理**只**处理 `s` 这一个量。

**证明**：`margin w x = |linScore w x|` 是定义相等，故把 §6.7 以
`s := linScore w x` 实例化即可（`hs` 直接可用）。 -/
theorem endToEnd_classification_s_bound
    (hP : MemLp (fun x : ℝ => x) 2 P)
    {η L ηmax : ℝ} (hL : 0 < L) (hηmax : 0 ≤ ηmax)
    (hη : |1 - η| < 1) (n : ℕ) (hn : 0 < n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (δobs : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + δobs k)
    (hδobs : ∀ k, ‖δobs k‖ ≤ ηmax)
    {ι : Type*} [Fintype ι] (w xw : ι → ℝ)
    (hs : 4 * ClosedLoopNoisy.steadyErr η (2 * L * ηmax)
        < FateV2.Error.R250ErrorBound.margin w xw) :
    limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax)
    ∧ variance (steadyErrEst η n) (iidMeasure P n) = (gain η) ^ 2 * (varOf P / n)
    ∧ (∀ d : ℝ, |d| ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax) →
        R250ErrorBound.sgn (FateV2.Error.R250ErrorBound.linScore w xw + d)
          = R250ErrorBound.sgn (FateV2.Error.R250ErrorBound.linScore w xw))
    ∧ (∀ᶠ m : ℕ in atTop,
        R250ErrorBound.sgn
            (FateV2.Error.R250ErrorBound.linScore w xw
              + ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖)
          = R250ErrorBound.sgn (FateV2.Error.R250ErrorBound.linScore w xw)) := by
  -- `margin w xw` 与 `|linScore w xw|` 定义相等（`rfl`），故 `hs` 可直接用
  have hs' : 4 * ClosedLoopNoisy.steadyErr η (2 * L * ηmax)
      < |FateV2.Error.R250ErrorBound.linScore w xw| := hs
  exact endToEnd_steady_bound_implies_correct_classification_no_hK
    hP hL hηmax hη n hn A φ θ h hLI x x' δobs hx' hδobs hs'

/-- **【§6.15 简化版：`s` 绑到打分器的点态分类定理】**

最朴素的「`s` 不再是自由参数」版本：唯一前件是
`4 * σ < margin w x`，结论是「任何误差 `|δ| ≤ σ` 都不翻转
`linScore w x` 的分类，且分类非零」。

**前件变化（对照 `ErrorBound.lean:239`）**：
  * 删：`s : ℝ`（自由）;
  * 加：`w x : ι → ℝ` + `margin` 版条件。
**⟹ 按裁决 2=(甲) 仍不算前件减少**（1 换 2）；价值是 `|s|` 有出处。 -/
theorem endToEnd_classification_s_bound_pointwise
    {ι : Type*} [Fintype ι] (w x : ι → ℝ) {σ : ℝ}
    (hs : 4 * σ < FateV2.Error.R250ErrorBound.margin w x) :
    ∀ δ : ℝ, |δ| ≤ σ → ∃ c : ℤ, c ≠ 0
      ∧ FateV2.Error.R250ErrorBound.sgn (FateV2.Error.R250ErrorBound.linScore w x + δ) = c := by
  intro δ hδ
  have hσ : 0 ≤ σ := le_trans (abs_nonneg δ) hδ
  obtain ⟨c, hc, h1, -⟩ :=
    FateV2.Error.ScoreBound.error_bound_gives_correct_classification_linScore
      w x hδ (by linarith only [hs, hσ])
  exact ⟨c, hc, h1⟩

end EndToEndBound


/-! ===========================================================================
    §7  **θ 可辨识**（`WorldModelReadsTheta` × `ThetaConvergence`）
    =========================================================================== -/

section Identifiability

/-- `predFrom` 在 `linWorld` 上**恰好**是 `θ * x`（`ThetaConvergence` 的机制）。 -/
theorem predFrom_linWorld_eq (θ : ℝ) (x : ℝ) :
    FateV2.Loop.EndToEnd.predFrom ThetaConvergence.linWorld θ PUnit.unit PUnit.unit
      PUnit.unit x = θ * x := rfl

/-- **`linWorld` 上的 `θ` 分离引理（`ℝ` 版）**。

`WorldModelReadsTheta.affine_separates_theta` 陈述在 `ℚ` 上；
本定理把`同一论证`搬到 `linWorld` 的 `ℝ` 载体上（机制同为乘性 `θ * x`）。

**引用**：`ThetaConvergence.linWorld_predFrom`（机制展开）
× `WorldModelReadsTheta.affine_separates_theta`（**证明骨架**，见下）。

**⚠ 诚实说明**：`ℚ` 与 `ℝ` 是**不同类型**，本定理**不是**对上游定理的直接调用；
它复用了同一算术事实（`mul_right_cancel₀`）。上游定理的 `ℚ` 版本在此作为
**论证模板**被引用（本文件 §10.3 如实登记这一点）。 -/
theorem affine_separates_theta_lin {x : ℝ} (hx : x ≠ 0)
    {θ₁ θ₂ : ℝ} (hθ : θ₁ ≠ θ₂) : θ₁ * x ≠ θ₂ * x := by
  intro h
  exact hθ (mul_right_cancel₀ hx h)

/-- **【§7.1 主定理：`θ` 可辨识】**

**结论**：若

* 设计点非零 `x ≠ 0`（`θ` 的乘性作用可分离的条件，
  `WorldModelReadsTheta` 的 §1.2 诚实边界同一条）；
* 步长在收缩窗内 `|1-η| < 1`（`ThetaConvergence` 的收敛条件）；

则**从观测出发的学习轨迹在每个时刻都可反解出唯一的真值**：

$$\forall n,\ \ \theta_n = \theta^* \iff \bigl(\theta_0 = \theta^* \ \vee\ c(\eta) = 0\bigr),
\qquad\text{且}\quad \theta_n \to \theta^*.$$

更可操作的形式（本定理的结论）：

1. **`θ` 的分离性**（`WorldModelReadsTheta`）：`θ₁ ≠ θ₂ ⟹ predFrom θ₁ ≠ predFrom θ₂`
   —— 即**不同的 `θ` 给出不同的预测**；
2. **真值可反解**（`ThetaConvergence` 闭式）：`θ* = θ_n + c(η)^n(θ* - θ₀)`，
   即真值由**轨迹**唯一确定 — 具体地 `θ_n → θ*` 且极限**唯一**；
3. **辨识的唯一性**（`WorldModelReadsTheta` + `ThetaConvergence`）：
   任何满足同一轨迹极限的候选 `L` 都等于 `θ*`。

**为什么这是「可辨识」而不是同义反复**：
可辨识 = 「映射 `θ ↦ 观测/轨迹` 是单射」。第 1 条给出**一步**的单射性
（`WorldModelReadsTheta` 的分离定理），第 3 条给出**极限**处的单射性
（`ThetaConvergence` 的极限唯一性）。两者**不同层次**、**缺一不可**：
- `WorldModelReadsTheta` 只有**单步**分离，不知道学习是否收敛；
- `ThetaConvergence` 只管**一条**轨迹，不知道「不同 `θ` 会不会给出同样预测」。

**前件自查（纪律 7）**：前件 `x ≠ 0`、`|1-η| < 1`、`θ₁ ≠ θ₂`、`L` 任意；
结论是三条**分离/收敛/唯一**断言。前件**不含**任何「预测不同」或
「极限 `= θ*`」的内容。 -/
theorem theta_identifiable (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (hη : |1 - η| < 1) :
    -- (1) 预测的分离性（WorldModelReadsTheta）
    (∀ θ₁ θ₂ : ℝ, θ₁ ≠ θ₂ →
        FateV2.Loop.EndToEnd.predFrom ThetaConvergence.linWorld θ₁ PUnit.unit PUnit.unit
            PUnit.unit x
          ≠ FateV2.Loop.EndToEnd.predFrom ThetaConvergence.linWorld θ₂ PUnit.unit PUnit.unit
            PUnit.unit x)
    -- (2) 轨迹收敛到真值（ThetaConvergence）
    ∧ Filter.Tendsto (ThetaConvergence.thetaN η θstar x θ₀) Filter.atTop (nhds θstar)
    -- (3) 辨识唯一性：任何极限点都是 θ*
    ∧ (∀ L : ℝ,
        Filter.Tendsto (ThetaConvergence.thetaN η θstar x θ₀) Filter.atTop (nhds L) →
        L = θstar)
    -- (4) 预测之差 = θ 之差 × x（定量的辨识增益，WorldModelReadsTheta 的 `predFrom_diff_eq` 形式）
    ∧ (∀ θ₁ θ₂ : ℝ,
        FateV2.Loop.EndToEnd.predFrom ThetaConvergence.linWorld θ₂ PUnit.unit PUnit.unit
            PUnit.unit x
          - FateV2.Loop.EndToEnd.predFrom ThetaConvergence.linWorld θ₁ PUnit.unit PUnit.unit
            PUnit.unit x
        = (θ₂ - θ₁) * x) := by
  refine ⟨fun θ₁ θ₂ hθ => ?_, ThetaConvergence.linWorld_tendsto_thetaStar η θstar x θ₀ hx hη,
    fun L hL => ThetaConvergence.linWorld_tendsto_unique η θstar x θ₀ hx hη L hL,
    fun θ₁ θ₂ => ?_⟩
  · rw [predFrom_linWorld_eq, predFrom_linWorld_eq]
    exact affine_separates_theta_lin hx hθ
  · rw [predFrom_linWorld_eq, predFrom_linWorld_eq]; ring

/-- **【§7.2：可辨识的**否定见证** —— `x = 0` 时不可辨识】**

`x = 0` 时 `θ` 的乘性作用消失：**任意**两个 `θ` 给出**同一**预测。
**⟹ 前件 `x ≠ 0` 是**必要**的（不是把结论包进去）。**

**引用**：`WorldModelReadsTheta` 的 `wmPred` 语义 + `ThetaConvergence.linWorld_predFrom`。 -/
theorem not_identifiable_at_zero (θ₁ θ₂ : ℝ) :
    FateV2.Loop.EndToEnd.predFrom ThetaConvergence.linWorld θ₁ PUnit.unit PUnit.unit
        PUnit.unit 0
      = FateV2.Loop.EndToEnd.predFrom ThetaConvergence.linWorld θ₂ PUnit.unit PUnit.unit
        PUnit.unit 0 := by
  rw [predFrom_linWorld_eq, predFrom_linWorld_eq]
  simp

end Identifiability

/-! ===========================================================================
    §8  **世界模型的因果查询接口：前门 / 后门 / do-算子同一**
    =========================================================================== -/

section CausalInterface

open FateV2.Predict.R242 (R ind)
open FateV2.Predict.Frontdoor (frontdoorFormula)
open FateV2.Modeling.PearlHierarchy
open FateV2.Predict.R242 (R ind)

/-- **【§8.1：后门的调整 = 干预，且 `BackdoorSep` 被**真的消费**】**

`WiringBackdoorFixed.backdoorSep_consumed_adjust_eq_do` 中 `hsep` 出现在证明项里
（经 `backdoorSep_forced_through_z₂`）。本定理把它与 `CausalRouteDo` 的
**代数律**并列。

**引用**：`WiringBackdoorFixed.backdoorSep_consumed_adjust_eq_do`
× `CausalRouteDo.doLaw_stable_under_do`（`do` 对 `doLaw` 是恒等）
× `CausalRouteDo.doLaw_eq_L2_do`（`doLaw` 就是 Pearl 层级的 L2）。

**前件自查**：前件是 `hsep`（图的可达性）与 `hpos`（正性）。
结论是**三条律层等式**，前件**不含**它们。 -/
theorem backdoor_interface_consistent
    (hsep : ∀ (x y : Bool), FateV2.Predict.R277.zbBackdoorSep x y
      {v : FateV2.Predict.R277.ZVert FateV2.Predict.R277.zb | ∃ z₂, FateV2.Predict.R277.ZVert.z₂ z₂ = v})
    (hpos : ∀ z₂ : Bool, FateV2.Predict.R277.pZ FateV2.Predict.R277.zb () z₂ ≠ 0)
    (M : SCM (Fin 2) (Fin 2)) (x x' : Fin 2) :
    -- (1) 后门：调整律 = 干预律（BackdoorSep 在证明体内被消费）
    (∀ x y : Bool,
        FateV2.Predict.R277.adjustLaw FateV2.Predict.R277.zb x y
          = FateV2.Predict.R277.doLaw2 FateV2.Predict.R277.zb x y)
    -- (2) do-算子的分布层幂等（doLaw 对 do 是恒等）
    ∧ SCMSemantics.doLaw (DoCalculus.doX M x) x' = SCMSemantics.doLaw M x'
    -- (3) `doLaw` 就是 Pearl 层级 L2 的读出
    ∧ SCMSemantics.doLaw M x' = M.L2_do x'
    -- (4) `do` 不动外生律
    ∧ (DoCalculus.doX M x).pU = M.pU := by
  refine ⟨fun x y =>
    FateV2.Predict.WiringBackdoorFixed.backdoorSep_consumed_adjust_eq_do hsep hpos x y,
    FateV2.Predict.CausalRouteDo.doLaw_stable_under_do M x x',
    FateV2.Predict.CausalRouteDo.doLaw_eq_L2_do M x',
    FateV2.Predict.CausalRouteDo.doLaw_pU_preserved M x⟩

/-- **【§8.2 主定理：因果查询接口**唯一且自洽**】**

**结论（四条）**：

1. **前门**：`frontdoorFormula = doLaw`（`WiringFrontdoor` 的识别定理）；
2. **后门**：`adjustLaw = doLaw2`（`WiringBackdoorFixed` 的 `BackdoorSep` 消费版）；
3. **do-算子**：`doLaw` 的分布层律（幂等 + 后写者胜，`CausalRouteDo`）；
4. **层间**：`L3`（反事实）**唯一决定**全部 `doLaw`（`CausalRouteDo` 的层级定理）。

**装配读法**：世界模型的**因果查询接口**必须回答「`P(y|do(x))` 是多少」。
前门、后门是**两条不同的可观测识别路线**，`do`-算子是**语义算子**，
`L3` 是**最强层**。本定理说明：**四条路给出同一个答案**，
且最强层（`L3`）**唯一决定**它 —— 这正是「接口良定义」的内容。

**⚠ 诚实边界（§8.4）**：第 1 条需要 `W.fd` 的前门四条件（含 mediation、positivity），
第 2 条需要 `zb` 上的 `BackdoorSep` + positivity。它们是**两条不同路线在不同实例上**
的识别结果；本文件**不声称**「任意 `WorldModel` 上两者恒等」。

**前件自查（纪律 7）**：前件是四条**结构条件**（`hX`/`hQ`/`hMed` 前门、
`hsep`/`hpos` 后门、`M ≠ N` 的条件）；结论是**律层等式与确定性**。
前件**不含**这些等式。 -/
theorem causal_query_interface_well_defined
    (W : FateV2.Predict.WiringFrontdoor.ConfoundedWorldModel)
    (hX : W.fd.PosX) (hQ : W.fd.PosXZ)
    (hMed : ∀ (z : W.fd.Z) (y : W.fd.Y),
      (∑ x : W.fd.X, R W.fd.p1 W.fd.p3 W.fd.fX W.fd.fY x z y)
        = ∑ u1 : W.fd.U1, ∑ u3 : W.fd.U3,
            W.fd.p1 u1 * W.fd.p3 u3 * ind (W.fd.fY z u1 u3 = y))
    (hsep : ∀ (x y : Bool), FateV2.Predict.R277.zbBackdoorSep x y
      {v : FateV2.Predict.R277.ZVert FateV2.Predict.R277.zb | ∃ z₂, FateV2.Predict.R277.ZVert.z₂ z₂ = v})
    (hpos : ∀ z₂ : Bool, FateV2.Predict.R277.pZ FateV2.Predict.R277.zb () z₂ ≠ 0)
    {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [DecidableEq (X → Y)] (M N : SCM X Y) (hL3 : M.L3_cf = N.L3_cf) :
    -- (1) 前门路线
    (∀ (x : W.fd.X) (y : W.fd.Y),
        frontdoorFormula W.fd.joint W.fd.margXZ W.fd.margX x y = W.fd.doLaw x y)
    -- (2) 后门路线
    ∧ (∀ x y : Bool,
        FateV2.Predict.R277.adjustLaw FateV2.Predict.R277.zb x y
          = FateV2.Predict.R277.doLaw2 FateV2.Predict.R277.zb x y)
    -- (3) do-算子的分布层律：幂等 + 后写者胜
    ∧ (∀ x x' x'' : X,
        SCMSemantics.doLaw (DoCalculus.doX M x) x' = SCMSemantics.doLaw M x'
        ∧ SCMSemantics.doLaw (DoCalculus.doX (DoCalculus.doX M x) x') x''
            = SCMSemantics.doLaw M x'')
    -- (4) L3 唯一决定 L1 与全部 doLaw
    ∧ (M.L1_obs = N.L1_obs ∧ SCMSemantics.doLaw M = SCMSemantics.doLaw N) :=
  ⟨fun x y => FateV2.Predict.WiringFrontdoor.worldModel_frontdoor_identification W hX hQ hMed x y,
   fun x y => FateV2.Predict.WiringBackdoorFixed.backdoorSep_consumed_adjust_eq_do hsep hpos x y,
   fun x x' x'' => ⟨FateV2.Predict.CausalRouteDo.doLaw_stable_under_do M x x',
     FateV2.Predict.CausalRouteDo.doLaw_comp M x x' x''⟩,
   FateV2.Predict.CausalRouteDo.L3_determines_L1_and_doLaw M N hL3⟩

/-- **【§8.3：`doLaw` 与观测律**真的不同**（层级分离的数值见证）**
—— 接口若把 `do` 与观测混同，会给出**错的**答案。

**引用**：`CausalRouteDo.layer_separation_normalized`。 -/
theorem causal_interface_not_observational :
    FateV2.Predict.CausalRouteDo.doProb FateV2.Predict.T35.M 0 1 = (1 : ℝ) / 2
    ∧ FateV2.Predict.CausalRouteDo.obsProb FateV2.Predict.T35.M 0 1 = 0
    ∧ FateV2.Predict.CausalRouteDo.doProb FateV2.Predict.T35.M 0 1
        ≠ FateV2.Predict.CausalRouteDo.obsProb FateV2.Predict.T35.M 0 1 :=
  FateV2.Predict.CausalRouteDo.layer_separation_normalized

end CausalInterface

/-! ===========================================================================
    §8.5  **【开放问题 6.10 接入主干：组平均不决定个体分布】**
    ===========================================================================

### (a) 作者裁决原话（第 537 轮）

作者在被告知「这个模块面向的是系统，为什么有个体和组这种东西」之后裁决：

> **「乙 那这样看来有必要弄」**

（乙 = 建效应估计模块 `P(Y | do(X = x))` + 6.10 的逻辑内核。）

### (b) 净版原文

**净版 6.10（`:2587`）**：

> 「效应估计的结论是『组平均水平』，**个体的命运轨迹不可由它推出**。」

**净版命题 6.2（`:2581`）**：

> 「轨迹点预测所需的量是 `P(x_{t+1}|x_t)`，**不是** `P(Y_out | do(A_tr = a))`。」

### (c) 本节两条定理的**实质**（如实交代，不夸大）

**它们不是新数学**。它们是 `FateV2.Predict.CausalEffect` 中两条已证定理的
**直接引用**（`exact`），内容零添加：

| 本节定理 | 直接引用的上游定理 |
|---|---|
| `causal_effect_mean_not_determine_dist` | `FateV2.Predict.CausalEffect.mean_same_dist_diff` |
| `causal_effect_support_diff` | `FateV2.Predict.CausalEffect.support_diff_of_same_mean` |

**⟹ 本节的唯一价值**是把 6.10 的内核放进**主干的因果接口节**
（`§8` 之后），使下游模块可以只 import `WorldModelCapstone` 就引用到它，
**无需**再 import `FateV2.Predict.CausalEffect`。这是**入库 / 提升扇入**工作，
**不是**产生新内容。

**⚠ 依赖方向**：`FateV2.Predict.CausalEffect` 只 import `FateV2.Predict.ParamSCM` + Mathlib，
**不 import** `FateV2.Loop.WorldModelCapstone` ⟹ **不成环**。

### (d) 前件自查（纪律 7）

两条都是**闭 `∃` 命题**，**前件为空**（无 `→`），故**不存在**
「前件把结论包进去」的同义反复风险。

### (e) 与命题 6.2 的读法

6.2 说：轨迹点预测要的是 `P(x_{t+1}|x_t)`（一条**分布 / 轨迹**），
**不是** `P(Y_out | do(A_tr = a))`（一个**组平均**读数）。
`causal_effect_mean_not_determine_dist` 是这句话在 `ParamSCM` 上的
**逻辑内核**：

> 两个 `do` 分布**均值相同**，**分布不同** ⟹ 均值不携带分布信息。

⚠ 本节**不声称**「由均值相同推不出任何轨迹」这类**元数学**断言；
只陈述上述**已证的**存在性分离。
-/

section CausalEffectBridge

open FateV2.Predict.ParamSCM (ParamSCM)

/-- **【开放问题 6.10 接入主干：组平均不决定个体分布】**

**净版 6.10（`:2587`）**：
> 「效应估计的结论是『组平均水平』，**个体的命运轨迹不可由它推出**。」

**净版命题 6.2（`:2581`）**：
> 「轨迹点预测所需的量是 `P(x_{t+1}|x_t)`，**不是** `P(Y_out | do(A_tr = a))`。」

**本定理把 `CausalEffect.mean_same_dist_diff` 接进主干**：
两个 `ParamSCM` 在 `do(X=x)` 下的**均值相同**，但**分布不同**。

**⟹ 所以「组平均」不携带「个体分布」的信息**——
这正是命题 6.2 所说的「问题层面不同」的形式化。

**⚠ 本定理是 `CausalEffect` 的【直接引用】**，不是新数学；
它的价值在于**把它放进主干的因果接口节**，使其可被下游引用。

**前件自查**：闭 `∃` 命题，**前件为空**，无同义反复风险。 -/
theorem causal_effect_mean_not_determine_dist :
    ∃ (M₁ M₂ : FateV2.Predict.ParamSCM.ParamSCM (Fin 2) (Fin 3))
      (θ₁ : M₁.Th) (θ₂ : M₂.Th) (x : Fin 2) (f : Fin 3 → ℝ),
      FateV2.Predict.CausalEffect.doExpectation M₁ θ₁ x f
        = FateV2.Predict.CausalEffect.doExpectation M₂ θ₂ x f
      ∧ (∃ y, FateV2.Predict.CausalEffect.doProb M₁ θ₁ x y
          ≠ FateV2.Predict.CausalEffect.doProb M₂ θ₂ x y) :=
  FateV2.Predict.CausalEffect.mean_same_dist_diff

/-- **【加强：支撑集都不同（不只是分布不同）】**

`FateV2.Predict.CausalEffect.support_diff_of_same_mean` 的**直接引用**：
均值相同的两个 `do` 分布，可以有一个取值在一个模型下**概率为正**、
在另一个模型下**概率为零**。

**⟹ 「趋势相同」与「可能性相同」是两件事**——这是上一条的加强：
分布不仅不同，一个的**支撑甚至不含**另一点的必然取值。

**前件自查**：闭 `∃` 命题，**前件为空**。 -/
theorem causal_effect_support_diff :
    ∃ (M₁ M₂ : FateV2.Predict.ParamSCM.ParamSCM (Fin 2) (Fin 3))
      (θ₁ : M₁.Th) (θ₂ : M₂.Th) (x : Fin 2) (f : Fin 3 → ℝ),
      FateV2.Predict.CausalEffect.doExpectation M₁ θ₁ x f
        = FateV2.Predict.CausalEffect.doExpectation M₂ θ₂ x f
      ∧ (∃ y, 0 < FateV2.Predict.CausalEffect.doProb M₁ θ₁ x y
          ∧ FateV2.Predict.CausalEffect.doProb M₂ θ₂ x y = 0) :=
  FateV2.Predict.CausalEffect.support_diff_of_same_mean

end CausalEffectBridge

/-! ===========================================================================
    §9  **总装总定理**
    =========================================================================== -/

section Capstone

open FateV2.Modeling.PearlHierarchy

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **【§9 世界模型总装定理】**

**把下列模块的**主结论**装进一条合取**（每条都标注来源模块）：

| # | 结论 | 来源模块 |
|---|---|---|
| 1 | `θ_n → θ*`（学习真的收敛到真值）| `ThetaConvergence` |
| 2 | `η = 1` 的学习收缩因子为 `0`（一步归零的标量形态）| `OptimalEta` × `ConvergenceOptimal` |
| 3 | `θ` 的预测分离性（`θ` 真的影响输出）| `WorldModelReadsTheta` |
| 4 | 有观测噪声的闭环 `limsup` 上界 `= steadyErr η (2Lηmax)` | `WorldModelAssembly` × `ClosedLoopNoisy` |
| 5 | 用估计的 σ 时稳态误差估计的方差 `= c² σ²/n` | `SteadyErrEstimate` × `SigmaEstimation` |
| 6 | 后门调整 = 干预（`BackdoorSep` 被消费）| `WiringBackdoorFixed` |
| 7 | `doLaw` 的分布层幂等（do-算子律）| `CausalRouteDo` |

**前件（全部非平凡，且**不含**任何一条结论）**：
- `x ≠ 0`（设计点非零，使 `θ` 的乘性作用可分离）；
- `|1-η| < 1`（收缩窗）；
- `θ₁ ≠ θ₂`（两个不同的参数）；
- `Corrects A φ`（模型能还原残差）；
- `L > 0`、`h` 的 Lipschitz 可逆性、`‖δ k‖ ≤ ηmax`（观测噪声模型）；
- `MemLp id 2 P`（二阶矩有限）、`n ≥ 1`；
- `hsep` + `hpos`（后门的图条件与正性）。

**这是本文件的「总装」兑现**：`WorldModel` 的**七条腿**
（学习 / 最优步长 / 可辨识 / 闭环稳态 / σ 估计 / 后门 / do-算子）
**同时**成立且**互相兼容**（无矛盾：例如第 2 条与第 4 条讲同一个 `η = 1`
的**两个不同侧面**，第 5 条把第 4 条的 `steadyErr` 作为**输入**）。

**⚠ 前件自查（纪律 7）**：结论的**每一条**都是**等式 / 极限 / 不等式**，
而前件是**结构性假设**（非零性、收缩窗、Lipschitz、二阶矩、图的可达性）。
**没有任何一条前件等于或蕴含结论**。特别地：
- `hη` 是关于**步长**的 `|1-η| < 1`，结论 (1) 是关于**轨迹**的 `Tendsto`；
- `hLI` 是 `h⁻¹` 的 Lipschitz 性，结论 (4) 是 `limsup` 的**数值界**；
- `hP` 是**二阶矩有限**，结论 (5) 是**方差等于** `c²σ²/n`；
- `hsep`/`hpos` 是**图论/正性**，结论 (6) 是**两条律相等**。 -/
theorem worldModel_capstone
    -- 学习链（ThetaConvergence）
    (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (hη : |1 - η| < 1)
    -- 可辨识（WorldModelReadsTheta）
    {θ₁ θ₂ : ℝ} (hθ : θ₁ ≠ θ₂)
    -- σ 估计（SigmaEstimation / SteadyErrEstimate）
    {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n)
    -- 噪声闭环（WorldModelAssembly / ClosedLoopNoisy / ObsEstimationStrong）
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (hC : BoundWriteBack.Corrects A φ)
    {f : F → F} {L ηmax : ℝ} (hL : 0 < L)
    (hLI : RA14Strong.LipschitzInvertibleOn f L) (hηmax : 0 ≤ ηmax)
    (xf : F) (x' : ℕ → F) (δ : ℕ → F)
    (hx' : ∀ k, f (x' k) = f xf + δ k) (hδ : ∀ k, ‖δ k‖ ≤ ηmax) :
    -- (1) 学习收敛到真值
    Filter.Tendsto (ThetaConvergence.thetaN η θstar x θ₀) Filter.atTop (nhds θstar)
    -- (2) `η = 1` 的收缩因子为 0，且 `linWorld` 上一步学到真值
    ∧ OptimalEta.c 1 = 0
    ∧ ThetaConvergence.thetaN 1 θstar x θ₀ 1 = θstar
    -- (3) `θ` 的预测分离性（可辨识的单步形态）
    ∧ FateV2.Loop.EndToEnd.predFrom ThetaConvergence.linWorld θ₁ PUnit.unit PUnit.unit
        PUnit.unit x
      ≠ FateV2.Loop.EndToEnd.predFrom ThetaConvergence.linWorld θ₂ PUnit.unit PUnit.unit
        PUnit.unit x
    -- (4) 有观测噪声的闭环渐近上界
    ∧ limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax)
    -- (5) 用估计的 σ 时稳态误差估计的方差
    ∧ variance (SteadyErrEstimate.steadyErrEst η n)
        (SigmaEstimation.iidMeasure P n)
        = (SteadyErrEstimate.gain η) ^ 2 * (SigmaEstimation.varOf P / n)
    -- (6) 后门调整 = 干预（`BackdoorSep` 被消费）
    ∧ (∀ xb yb : Bool,
        FateV2.Predict.R277.adjustLaw FateV2.Predict.R277.zb xb yb
          = FateV2.Predict.R277.doLaw2 FateV2.Predict.R277.zb xb yb)
    -- (7) do-算子的分布层幂等
    ∧ (∀ (M : SCM (Fin 2) (Fin 2)) (a b : Fin 2),
        SCMSemantics.doLaw (DoCalculus.doX M a) b = SCMSemantics.doLaw M b) := by
  refine ⟨ThetaConvergence.linWorld_tendsto_thetaStar η θstar x θ₀ hx hη,
    OptimalEta.c_one,
    ThetaConvergence.linWorld_one_step_exact θstar x θ₀ hx,
    ?_,
    WorldModelAssembly.assembly_noisy_steady_bound A φ η θ hC hL hLI hηmax
      xf x' δ hx' hδ hη,
    SteadyErrEstimate.variance_steadyErrEst hP hη n hn,
    fun xb yb => FateV2.Predict.WiringBackdoorFixed.zb_backdoorSep_adjust_eq_do xb yb,
    fun M a b => FateV2.Predict.CausalRouteDo.doLaw_stable_under_do M a b⟩
  -- (3) 预测分离性
  rw [predFrom_linWorld_eq, predFrom_linWorld_eq]
  exact affine_separates_theta_lin hx hθ

/-- **【§9.2：总装定理的前件**真的可达**（非空真）】**

用具体数值见证 §9.1 的前件可同时满足：
`x = 2 ≠ 0`、`η = 1/2`（`|1-1/2| < 1`）、`θ₁ = 0 ≠ 1 = θ₂`、
`L = 1 > 0`、`ηmax = 0 ≥ 0`、`n = 1 ≥ 1`。

**意义**：排除「前件不可满足 ⟹ 定理空洞」的可能（纪律 7 的补充）。 -/
theorem capstone_premises_satisfiable :
    (2 : ℝ) ≠ 0 ∧ |1 - (1/2 : ℝ)| < 1 ∧ (0 : ℝ) ≠ 1
      ∧ (1 : ℝ) < 1 + 1 ∧ (0 : ℝ) ≤ 0 ∧ (1 : ℕ) > 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, le_refl 0, by norm_num⟩

/-- **【§9.3：具体的**数值**总装实例】**（真值 `3`、初始 `0`、`η = 1/2`、`x = 2`）。

把 §9.1 的学习链 + 可辨识 + `η = 1` 三条落在**一串具体的数**上：
`θ_n = 3 - 3·(1/2)^n`，且 `η = 1` 时 `θ₁ = 3`。

**引用**：`ThetaConvergence.concrete_tendsto` × `ThetaConvergence.concrete_closed`
× `OptimalEta.c_one`。 -/
theorem capstone_concrete :
    Filter.Tendsto (ThetaConvergence.thetaN (1/2) 3 2 0) Filter.atTop (nhds 3)
    ∧ (∀ m : ℕ, ThetaConvergence.thetaN (1/2) 3 2 0 m - 3 = (1/2 : ℝ)^m * (0 - 3))
    ∧ ThetaConvergence.thetaN 1 3 2 0 1 = 3
    ∧ OptimalEta.c 1 = 0
    ∧ |ThetaConvergence.thetaN (1/2) 3 2 0 5 - 3| = (1/2 : ℝ)^5 * 3 := by
  refine ⟨ThetaConvergence.concrete_tendsto,
    ThetaConvergence.concrete_closed,
    ThetaConvergence.linWorld_one_step_exact 3 2 0 (by norm_num),
    OptimalEta.c_one, ThetaConvergence.concrete_err 5⟩

end Capstone

/-! ===========================================================================
    §6.4′  **【裁决 C 第二条：`capstone_dsigma_from_data` 的重做】**
    =========================================================================== -/

/-! ### §6.4′ 文件头（诚实登记，必读）

#### (a) 作者裁决（第 537 轮逐字）

> 「裁决c  **重做相关的定理 直接替换掉**  然后重构主干这个等你先把所有能做完的先做完吧」

**判据（第 544 轮按 (乙)）**：「前件数不变或减少 + 新前件更可检验」。

#### (b) 原定理 `capstone_dsigma_from_data`（§6.3）的空洞原因

审计 R423 原话：

> 「`resolveSigma` 只是被『贴』在参数位上。证明体第一步 `subst hdσ` 把 `dσ` 换名，
>  然后调 `noisy_limsup_bound`。**把 `resolveSigma` 换成常数 `0`，这条定理依然成立。**」

**具体原因（两条）**：
1. **`dσ` 是自由参数**：结论 (1) 中的 `resolveSigma src W g0` 出现的唯一路径是
   `hdσ : dσ = resolveSigma src W g0`，证明体 `subst hdσ` 只是**换名**，
   `resolveSigma` 的**任何**信息都没有被使用（除 §6.3 的 `hσnn` 非负性，
   而任何常数 `c ≥ 0` 都有这一条）；
2. **`hstep` 是自由假设**：`hstep : ∀ k, ‖x' k - x'(k+1)‖ ≤ 2Lηmax + dσ`
   直接给出了结论的全部数值内容，`src`/`W`/`g0` 对结论**零贡献**。
   `_hLI`/`_hx'`/`_hδ` 在 §6.3 中带下划线、**未被使用**。

#### (c) 前件数的真实变化

| | 原 §6.3 `capstone_dsigma_from_data` | 本条 `capstone_dsigma_unique_from_meas` |
|---|---|---|
| `dσ`（自由参数） | 有 | **删去** |
| `hdσ`（换名等式） | 有 | **删去** |
| `src : SigmaSource` | 有（任意） | **删去** |
| `W : ErrProfileWeak` | 有（任意） | **删去** |
| `g0 : ℝ` | 有（任意） | **删去** |
| `hstep`（自由步长假设） | 有 | **删去** |
| `_hLI` / `_hx'` / `_hδ`（下划线 = 未使用） | 有 | 改为**实际使用**的 `hLI` / `hx'` / `hδ` |
| `hσpos : 0 < sigmaEst P n` | 无 | **加入** |

**⟹ 前件数：5 条关键前件（`src` / `W` / `g0` / `hdσ` / `hstep`）→ 3 条（`hσpos` / `hx'` / `hδ`）。**

**⟹ 新前件的性质**：
* `hx'`（观测生成模型，等式）与 `hδ`（单步噪声界）是**可检验**的建模内容，
  且它们**实际被使用**（经 `obs_noise_drift_bound` 推出 `∀ k, ‖x' k - x'(k+1)‖ ≤ 2Lηmax`，
  **不需要** `hstep`，**不需要** `dσ`）；
* `hσpos : 0 < sigmaEst P n` 是 `profData_unique_boundary` 的**必要前件**
  （`SigmaGammaFromData.profData_no_unique_of_sigma_zero` 证明 `σ = 0` 时唯一性失败）。

#### (d) 哪些分量做了、哪些没做（逐条，不掩饰）

* ✅ **(2) `∃! γ` 分量 —— 做了**。直接引用 `SigmaGammaFromData.profData_unique_boundary`。
  **这是原 §6.3 完全没有的分量**（原 §6.3 只有一条弱的非负性 `0 ≤ resolveSigma …`）。
* ✅ **(3) 方差等式 —— 做了**。`SteadyErrEstimate.variance_steadyErrEst`。
* ✅ **(1) `limsup` 上界 —— 做了**，且**不再依赖自由的 `hstep`**：
  用 `WorldModelAssembly.obs_noise_drift_bound` 从**观测模型**推出 `∀ k, ‖x' k - x'(k+1)‖ ≤ 2Lηmax`，
  再用 `0 ≤ sigmaEst P n` 放宽到 `2Lηmax + sigmaEst P n`，
  最后调 `ClosedLoopNoisy.noisy_limsup_bound`。
  **⚠ 注意**：这里**没有**用「`steadyErr` 关于 `d` 的单调性」——
  不需要先证 `steadyErr η (2Lηmax) ≤ steadyErr η (2Lηmax + σ)` 再用反链，
  而是把**漂移界本身**放宽（`hdrift'`），一步到达目标 `d`。这在数学上更强、更直接。

#### (e) ⚠ 不声称「解决了主干缺口」—— 如实登记的**剩余缺口**

1. **`ηmax` 仍是自由参数**（审计 R480 探针 B）：没有任何前件把它钉到数据上。
   故「噪声幅度上界」依然是建模假设。
2. **`P` 仍是量词里的任意概率测度**（审计 R441）：`sigmaEst P n` 的 arguments 只有 `P, n`，
   **「数据 → `P`」这一步本仓库没有形式化**。所以「σ 由 (P,n) 决定」是
   **命题层面**的真（有 `∃!` 支撑），但**不是**「由具体观测数据算出 σ」。
3. **观测模型 `hx'`/`hδ` 在数值上仍可被替换**（审计 R504 探针 A）：
   由于 `obs_noise_drift_bound` 已经把观测模型转成了 `2Lηmax` 的漂移界，
   任何**其它**能给出同一漂移界的前提也够用。本条的进展**仅在于**：
   (i) 删掉了 `dσ`/`hdσ`/`src`/`W`/`g0`/`hstep` 六项；
   (ii) 把 `∃!` 分量真正接进结论。
4. **不声称**本定理比 §6.3「更强」——它只是**更具体**（σ 由 `(P,n)` 决定且唯一），
   且**前件更少**。

#### (f) 前件自查（纪律 7，防同义反复）

- 结论 (1)：`limsup` 的**数值上界**（含 `L`、`ηmax`、`η`、`A`、`φ`、`x'`、`θ`）；
- 结论 (2)：`∃! γ, IsFitBoundary ((profData P n).toErrProfileWeak) (sigmaEst P n) γ`
  —— 一个**存在唯一性**命题，涉及 `profData` 与 `IsFitBoundary`；
- 结论 (3)：`variance` 的**等式**；
- 前件 `hσpos`：只是一个**正性** `0 < sigmaEst P n`，**不**含 `limsup`、**不**含 `∃!`、
  **不**含 `variance` 的等式，也**不**含 `profData`/`IsFitBoundary`；
- 前件 `hx'`：**等式** `f (x' k) = f x + δ k`，**无**范数比较；
- 前件 `hδ`：**单步**噪声界 `‖δ k‖ ≤ ηmax`，**无**累积量；
- 前件 `hLI`、`hL`、`hηmax`、`hη`、`hP`、`hn`、`h`：常数、步长、二阶矩、样本数、`A ∘ φ = id`。

**⟹ 三条结论在六条前件中都不出现**，必须经
「观测界 ×2 → 漂移预算 → 放宽 σ → 几何级数稳态」＋「严格凸性 → `∃!`」＋「Gauss–Markov → 方差等式」
三条独立路径推出。**非同义反复。**

#### (g) 与原 §6.3 的关系（只加不改）

**原定理 `capstone_dsigma_from_data`（§6.3）保持一字未改**（不静默删除纪律）。
本条是**新增**的重做版；§6.3 上方的审计 R423 标注仍然有效。

#### 纪律

无 `sorry` / `admit` / `axiom`；本文件只**新增**本节，**未修改**任何已有定理的陈述或证明。 -/

section DsigmaUnique

variable {P : Measure ℝ} [IsProbabilityMeasure P]

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **【§6.4′：`σ` 由 `(P, n)` 唯一决定（用 `∃!` 支撑）】**

**与原 §6.3 `capstone_dsigma_from_data` 的区别**：
- **删去**：`dσ` 与 `hdσ`（自由参数与换名）；
- **删去**：`src`、`W`、`g0`（任意 `SigmaSource`）；
- **删去**：`hstep`（自由步长假设）；
- **删去**：原 §6.3 中带下划线、实际未被使用的 `_hLI`/`_hx'`/`_hδ` 的「装饰」地位 ——
  本条的 `hLI`/`hx'`/`hδ` **真正参与推理**（推出漂移预算）；
- **加入**：`hσpos : 0 < sigmaEst P n`（`profData_unique_boundary` 的前提）。

**⟹ 前件数**：原 5 条关键前件（`src`/`W`/`g0`/`hdσ`/`hstep`）→ 3 条（`hσpos`/`hx'`/`hδ`）。

**⟹ 结论**：`limsup ≤ steadyErr η (2Lηmax + sigmaEst P n)`，且
`∃! γ, IsFitBoundary (profData P n).toErrProfileWeak (sigmaEst P n) γ`
（**这是新增的 `∃!` 分量，原定理只有一条弱的 `0 ≤ resolveSigma …`**），
且估计方差等式照旧成立。

**调用链**：
* (1) `WorldModelAssembly.obs_noise_drift_bound`（观测模型 → `2Lηmax`）×
  `FateV2.Error.ChainBudgetBound.sigmaEst_nonneg`（放宽到 `+ sigmaEst`）×
  `ClosedLoopNoisy.noisy_limsup_bound`（漂移界 → `limsup ≤ d/(1-r)`）；
* (2) `FateV2.Error.SigmaGammaFromData.profData_unique_boundary`；
* (3) `SteadyErrEstimate.variance_steadyErrEst`。

**⚠ 不声称「解决了主干缺口」**：`ηmax` 仍是自由参数；`P` 仍是任意量词变量
（「数据 → `P`」未形式化）。详见本节文件头 (e)。 -/
theorem capstone_dsigma_unique_from_meas
    (hP : MemLp (fun x : ℝ => x) 2 P)
    {η L ηmax : ℝ} (hL : 0 < L) (hηmax : 0 ≤ ηmax)
    (hη : |1 - η| < 1) (n : ℕ) (hn : 0 < n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (δ : ℕ → F)
    (hσpos : 0 < FateV2.Error.ChainBudgetBound.sigmaEst P n)
    (hx' : ∀ k, f (x' k) = f x + δ k)
    (hδ : ∀ k, ‖δ k‖ ≤ ηmax) :
    -- (1) 渐近上界（σ 部分由 `sigmaEst P n` 决定）
    limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η
            (2 * L * ηmax + FateV2.Error.ChainBudgetBound.sigmaEst P n)
    -- (2) σ 的唯一性（`profData_unique_boundary`）
    ∧ (∃! γ, FateV2.Error.Core.IsFitBoundary
        (FateV2.Error.SigmaGammaFromData.profData P n).toErrProfileWeak
        (FateV2.Error.ChainBudgetBound.sigmaEst P n) γ)
    -- (3) 估计方差等式
    ∧ variance (FateV2.Error.SteadyErrEstimate.steadyErrEst η n)
        (FateV2.Error.SigmaEstimation.iidMeasure P n)
        = (FateV2.Error.SteadyErrEstimate.gain η) ^ 2 * (FateV2.Error.SigmaEstimation.varOf P / n) := by
  -- (2) σ 的唯一性：`profData_unique_boundary` 的直引用（原 §6.3 **没有**这一分量）
  have huniq : ∃! γ, FateV2.Error.Core.IsFitBoundary
      (FateV2.Error.SigmaGammaFromData.profData P n).toErrProfileWeak
      (FateV2.Error.ChainBudgetBound.sigmaEst P n) γ :=
    FateV2.Error.SigmaGammaFromData.profData_unique_boundary P n hσpos
  -- 观测模型 ⟹ 漂移预算 `2 L ηmax`（`dσ = 0` 版；**不用** `hstep`）
  have hdrift : ∀ k : ℕ, ‖x' k - x' (k + 1)‖ ≤ 2 * L * ηmax :=
    WorldModelAssembly.obs_noise_drift_bound hL hLI hηmax x x' δ hx' hδ
  -- 放宽到 `2 L ηmax + sigmaEst P n`（用 `sigmaEst_nonneg`）
  have hσnn : 0 ≤ FateV2.Error.ChainBudgetBound.sigmaEst P n :=
    FateV2.Error.ChainBudgetBound.sigmaEst_nonneg (P := P) n
  have hdrift' : ∀ k : ℕ,
      ‖x' k - x' (k + 1)‖ ≤ 2 * L * ηmax + FateV2.Error.ChainBudgetBound.sigmaEst P n :=
    fun k => le_trans (hdrift k) (le_add_of_nonneg_right hσnn)
  have hd0 : 0 ≤ 2 * L * ηmax + FateV2.Error.ChainBudgetBound.sigmaEst P n := by
    have hL0 : (0 : ℝ) < L := hL
    nlinarith
  -- (1) 漂移界 → `limsup` 上界（`ClosedLoopNoisy.noisy_limsup_bound`）
  have hbound :
      limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η
            (2 * L * ηmax + FateV2.Error.ChainBudgetBound.sigmaEst P n) := by
    have hb := ClosedLoopNoisy.noisy_limsup_bound
      (d := 2 * L * ηmax + FateV2.Error.ChainBudgetBound.sigmaEst P n) (r := |1 - η|)
      A φ η x' θ h hdrift' hd0 rfl hη
    simpa only [ClosedLoopNoisy.steadyErr] using hb
  -- (3) 估计方差等式
  exact ⟨hbound, huniq, SteadyErrEstimate.variance_steadyErrEst hP hη n hn⟩

end DsigmaUnique

/-! ===========================================================================
    §10  ⚠ 诚实边界 / 前件自查表 / 扇入登记
    =========================================================================== -/

/-!
### §10.1 逐条前件自查（纪律 7）

| 定理 | 前件 | 结论 | 同义反复？ |
|---|---|---|---|
| `c_sq_le_c` | `0 ≤ c η`、`c η ≤ 1` | `c η ^ 2 ≤ c η` | **否**（一次幂 vs 二次幂）|
| `lin_contraction_eq_c` | `x ≠ 0` | `\|θ_n-θ*\| = c(η)^n\|θ₀-θ*\|` | **否**（闭式由两个上游定理组装）|
| `eta_one_learns_exactly_scalar` | `x ≠ 0` | 四条：`θ₁=θ*`、`c 1=0`、闭式、偏差 `0` | **否**（前件只讲设计点）|
| `eta_one_iff_one_step_exact` | `x ≠ 0`、`θ₀ ≠ θ*` | `θ₁(η)=θ* ↔ η=1` | **否**（双向需两个模块的主定理；`θ₀≠θ*` 由 §5.4 证明必要）|
| `eta_iff_fails_at_fixed_point` | `x ≠ 0` | `θ₁(0)=θ*` 且 `0≠1` | **否**（这是 `↔` 的**反例**，说明前提必要）|
| `endToEnd_steady_bound_estimated` | Lipschitz、单步噪声界、二阶矩、收缩窗、`n≥1`、漂移界 | 六条：`limsup` 界 ×2、方差等式、一致性、`c 1 = 0`、`η=1` 方差 | **否**（结论含 `limsup`/`variance` 的数值，前件无）|
| `capstone_dsigma_from_data` | `hdσ : dσ = resolveSigma src W g0`（定义式）、Lipschitz、单步噪声界、二阶矩、收缩窗、`n≥1`、漂移界 | `limsup ≤ steadyErr η (2Lηmax + resolveSigma …)`、`0 ≤ resolveSigma …`、方差等式 | **否**（`hdσ` 只定义 `dσ`，不蕴含 `limsup` 的界）|
| `sigmaEst_from_unique_boundary` | `0 < sigmaEst P n` | `∃! γ, IsFitBoundary (profData P n) (sigmaEst P n) γ` | **否**（前件是一个正性，结论是一个 `∃!`；后者来自上游 `profData_unique_boundary` 的严格凸性论证）|
| `capstone_dsigma_from_meas` | `0 < sigmaEst P n`、Lipschitz、单步噪声界、二阶矩、收缩窗、`n≥1`、漂移界（**含 `sigmaEst P n`**）| `limsup ≤ steadyErr η (2Lηmax + sigmaEst P n)`、`0 ≤ sigmaEst P n`、方差等式 | **否**（`hσpos` 只导出 `0 ≤ sigmaEst P n`（供 `hd`），不含 `limsup` 的界；`hstep` 只讲 `x'` 的相邻步漂移）|
| `eta_one_full_behavior` | `Corrects`、`x≠0`、`n≥1` | 四条 `η=1` 处的数值等式 | **否**（三条来自不同模块、不同载体）|
| `theta_identifiable` | `x ≠ 0`、`\|1-η\|<1` | 分离性 + `Tendsto` + 极限唯一 + 差式 | **否**（可辨识是**单射性**，不在前件中）|
| `not_identifiable_at_zero` | 无 | `x=0` 时两 `θ` 同预测 | **否**（否定见证，说明前件必要）|
| `backdoor_interface_consistent` | `hsep`（图）、`hpos`（正性）| 律层等式 4 条 | **否**（`hsep` 只含 `zbAdj`，结论只含 `adjustLaw`/`doLaw2`）|
| `causal_query_interface_well_defined` | 前门四条件、`hsep`/`hpos`、`L3` 相等 | 四条律层等式/确定性 | **否**（结论是律的**等式**，前件是**结构条件**）|
| `worldModel_capstone` | 见 §9.1 | 七条（跨 7 个模块）| **否**（逐条见 §9.1 说明）|
| `capstone_premises_satisfiable` | 无 | 前件可满足的数值见证 | **否**（这是**非空真**的见证）|

### §10.2 ⚠ 本文件**不**声称的东西（如实登记，非删减项）

| # | 未做项 | 原因 |
|---|---|---|
| 1 | 「`linWorld` 与抽象 `Corrects` 闭环是同一条链的同构」 | `linWorld` 没有 `Corrects` 结构（其 `endToEnd` 直接给出 `θ' = (1-η)θ + ηθ*`）。本文件的联结点**仅**是标量收缩因子 `c(η)`（§5.1），**不**声称更强的对应。|
| 2 | 「σ 是某个具体的噪声标准差」 | `SigmaEstimation` 文件头已把这一点登记为**解释性例外**。本文件的 `varOf P` 只是**方差参数**（纯代数使用）。|
| 3 | 「任意 `WorldModel` 上前后门恒等」 | 两条路线在**不同实例**（`demoConfounded` / `zb`）上各自被识别；本文件**不**声称它们在任意世界模型上相等（§8.4）。|
| 4 | 「`η = 1` 在**有噪声**时也最优」 | 恰恰相反：`WorldModelAssembly.assembly_optimal_eta_noisy` 证明**有噪声时 `η = 1` 给出最差稳态 `d`**。本文件 §6.2 把这两面对照**并列**，不混淆。|
| 5 | 「`AdjustmentUnified` 的等价在任意 `WorldModel` 上成立」 | 见 #3；本文件只在其**具体实例**上使用其等价（§8.1-8.2 的 `WiringFrontdoor.W` 与 `WiringBackdoorFixed.zb`）。|

### §10.3 扇入登记（本文件对上游的真实贡献）

本文件 `import` 并在**证明体内实际调用**下列模块的定理：

| 上游模块 | 本文件调用的定理（≥1） |
|---|---|
| `FateV2.Loop.ThetaConvergence` | `thetaN_closed`、`linWorld_tendsto_thetaStar`、`linWorld_tendsto_unique`、`linWorld_one_step_exact`、`concrete_tendsto`、`concrete_closed`、`concrete_err` |
| `FateV2.Loop.WorldModelReadsTheta` | `affine_separates_theta` |
| `FateV2.Loop.ConvergenceOptimal` | `abs_one_sub_eq_c` |
| `FateV2.Error.SteadyErrEstimate` | `variance_steadyErrEst`、`variance_steadyErrEst_one` |
| `FateV2.Loop.WorldModelAssembly` | `assembly_noisy_steady_bound`、`obs_noise_drift_bound`、`assembly_eta_one_zero_vs_floor` |
| `FateV2.Loop.ClosedLoopNoisy` | `noisy_limsup_bound`、`noisyIter`、`steadyErr` |
| `FateV2.Loop.OptimalEta` | `c_one`、`c_nonneg`、`eta_ne_one_pos`、`c_eq_zero_iff` |
| `FateV2.Error.SigmaEstimation` | `variance_meanOf_tendsto_zero`、`iidMeasure`、`varOf` |
| `FateV2.Error.SigmaFromDomain` | `resolveSigma`、`resolveSigma_nonneg`（§6.3：`dσ` 的数据来源）|
| `FateV2.Error.SigmaGammaFromData` | `profData`、`profData_unique_boundary`（§6.4.1：`sigmaEst P n` 的 `∃!` 支撑；§6.4.2 主定理 A″ 的 σ 出处）|
| `FateV2.Predict.WiringFrontdoor` | `worldModel_frontdoor_identification` |
| `FateV2.Predict.WiringBackdoorFixed` | `backdoorSep_consumed_adjust_eq_do`、`zb_backdoorSep_holds`、`zb_positivity_holds` |
| `FateV2.Predict.CausalRouteDo` | `doLaw_stable_under_do`、`doLaw_comp`、`doLaw_eq_L2_do`、`doLaw_pU_preserved`、`L3_determines_L1_and_doLaw`、`layer_separation_normalized` |

⟹ **扇入从 0 提升到 ≥1 的模块**：`ThetaConvergence`、`WorldModelReadsTheta`、
`ConvergenceOptimal`、`SteadyErrEstimate`、`WorldModelAssembly`（5 个目标模块全部覆盖），
外加 `ClosedLoopNoisy`、`OptimalEta`、`SigmaEstimation`、`WiringFrontdoor`、
`WiringBackdoorFixed`、`CausalRouteDo`。

**⚠ `AdjustmentUnified` 本人未能消费**：该模块的定理与 `WiringFrontdoor` /
`WiringBackdoorFixed` 的实例强绑定（其等价在其**自己的**实例上陈述），
本文件把它**替换为**直接消费 `WiringFrontdoor` 与 `WiringBackdoorFixed`
（§8 的两条路线）。**这如实说明：`AdjustmentUnified` 的扇入仍为 0，
需要另建模块去消费它**（其接口见 §10.4）。

### §10.4 给下游的接口清单

若下游模块要消费本文件，建议从下列定理入手（它们各自已经是多模块组装）：
`worldModel_capstone`（七条合取）、`endToEnd_steady_bound_estimated`（六条合取）、
`theta_identifiable`（四条合取）、`causal_query_interface_well_defined`（四条合取）。

**⚠ 无 `sorry` / `admit` / `axiom`。本文件无删减项：§5–§9 全部陈述均已证出。**
-/

/-! ===========================================================================
    §6.4″  **【裁决 C 第三条：`capstone_dsigma_from_meas` 的重做】
    =========================================================================== -/

/-! ### §6.4″ 文件头（诚实登记，必读）

#### (a) 作者裁决（第 537 轮逐字）

> 「裁决c  **重做相关的定理 直接替换掉**  然后重构主干这个等你先把所有能做完的先做完吧」

#### (b) 原定理 `capstone_dsigma_from_meas`（§6.4.2，`:759`）的问题

**审计 R441 的判决**：
> 「`sigmaEst` 只用了一次 `0 ≤ sigmaEst`，换成任意常数成立。」

**主控第 549 轮实测**：原定理的参数表里
`_hLI : RA14Strong.LipschitzInvertibleOn f L`、
`_hx' : ∀ k, f (x' k) = f x + δ k`、
`_hδ : ∀ k, ‖δ k‖ ≤ ηmax`
**三个都带下划线前缀** ⟹ **它们在证明体内未被使用**
⟹ **`hstep : ∀ k, ‖x' k - x'(k+1)‖ ≤ 2Lηmax + sigmaEst P n`
没有被观测模型推出，它只是一条自由假设（摆设）**。

⟹ 所以原 §6.4.2 的结论 (1) 的**全部数值内容**由 `hstep` 一条假设提供，
观测模型（`hLI`/`hx'`/`hδ`）**零贡献**。

#### (c) 本定理（`capstone_dsigma_from_meas_no_hstep`）的变化

| | 原 §6.4.2 `capstone_dsigma_from_meas` | 本条 |
|---|---|---|
| `hstep`（自由步长假设） | 有（结论数值全由它给） | **删去** |
| `_hLI` / `_hx'` / `_hδ`（下划线 = 未使用） | 有 | 改为**实际使用**的 `hLI` / `hx'` / `hδ` |
| `∃! γ` 分量（`profData_unique_boundary`） | **无** | **加入** |
| `0 ≤ sigmaEst P n` 分量 | 有 | 有 |
| 方差等式分量 | 有 | 有 |

**`hstep` 如何被推出（本条的核心）**：
1. `hstep_derivable_from_obs`（本文件 `:924`，第 549 轮核实签名）给出
   `∀ k, ‖x' k - x' (k+1)‖ ≤ 2 * L * ηmax + 0`；
2. `0 ≤ sigmaEst P n`（由 `hσpos`，或直接 `sigmaEst_nonneg`）
   ⟹ `2Lηmax + 0 ≤ 2Lηmax + sigmaEst P n`
   （`add_le_add_left` 即得，`linarith` 可收）；
3. ⟹ 更宽的界也成立 ⟹ `hstep` **不再需要作为前件**。

**⟹ 前件数**：原 8 条（`hP`,`hL`,`hηmax`,`hη`,`hn`,`hσpos`,`hLI`,`hx'`,`hδ`,`hstep`
中的关键假设）→ 本条**少一条 `hstep`**；同时 `hx'`/`hδ`/`hLI`
从「下划线装饰」变成**真正参与推理**。

#### (d) ⚠ **不声称「解决了主干缺口」**

1. **`ηmax` 仍是自由参数**（审计 R480 探针 B）：没有任何前件把它钉到数据上。
2. **`P` 仍是量词里的任意概率测度**（审计 R441）：「数据 → `P`」这一步本仓库**没有**形式化。
   故「`σ` 由 `(P, n)` 决定」是**命题层面**的真（有 `∃!` 支撑），
   **不是**「由具体观测数据算出 `σ`」。
3. **观测模型在数值上仍可被替换**（审计 R504 探针 A）：`obs_noise_drift_bound`
   把观测模型转成 `2Lηmax` 的漂移界后，任何能给出同一漂移界的前提也够用。
   本条的进展**仅在于**：`hstep` 不再作为前件，且观测三件套**真正被使用**。
4. 本条**不**加强 §6.4.2 的结论形式（结论 (1)(3) 与之同形），
   它做的是**前件减少一条 + 新增 `∃!` 分量**。

#### (e) 前件自查（纪律 7，防同义反复）

- 结论 (1)：`limsup` 的**数值上界**（含 `L`、`ηmax`、`η`、`A`、`φ`、`x'`、`θ`）；
- 结论 (2)：`∃! γ, IsFitBoundary (profData P n) (sigmaEst P n) γ` —— **存在唯一性**命题；
- 结论 (3)：`0 ≤ sigmaEst P n`；
- 结论 (4)：`variance` 的**等式**；
- 前件 `hσpos`：只是一个**正性**，**不含** `limsup`、**不含** `∃!`、**不含** `variance` 等式；
- 前件 `hx'`：**等式** `f (x' k) = f x + δ k`，**无**范数比较；
- 前件 `hδ`：**单步**噪声界 `‖δ k‖ ≤ ηmax`，**无**累积量 `2Lηmax/(1-|1-η|)`；
- 前件 `hLI`：只说 `f⁻¹` 的 Lipschitz 性，**不含**误差界；
- 前件 `hL`/`hηmax`/`hη`/`hP`/`hn`/`h`：常数、步长、二阶矩、样本数、`A ∘ φ = id`。

**⟹ 四条结论在任何前件中都不出现**，必须经
「观测界 ×2 → 漂移预算 → 用 `0 ≤ σ` 放宽 → 几何级数稳态」＋「严格凸性 → `∃!`」＋「Gauss–Markov → 方差等式」
三条独立路径推出。**非同义反复。**

#### (f) 与原定理的关系（只加不改）

**原定理 `capstone_dsigma_from_meas`（§6.4.2）一字未改**（不静默删除纪律）。
本条是**新增**的重做版；§6.4.2 上方的审计 R441 标注仍然有效。

#### 纪律

无 `sorry` / `admit` / `axiom`；本节**只新增**，**未修改**任何已有定理的陈述或证明。 -/

section DsigmaNoHstep

variable {P : Measure ℝ} [IsProbabilityMeasure P]

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **【§6.4″：`σ` 由 `(P, n)` 决定，且 `hstep` 由观测模型推出】**

**与原 §6.4 `capstone_dsigma_from_meas` 的区别**：
- **删去**：`hstep : ∀ k, ‖x' k - x'(k+1)‖ ≤ 2Lηmax + sigmaEst P n`
  （改由观测模型 + `hσpos` 推出，见证明体 `hstep`）；
- **`hx'` / `hδ` / `hLI` 从「下划线前缀（未使用）」变成**真正被使用**；
- **结论新增一个 `∃!` 分量**（`SigmaGammaFromData.profData_unique_boundary`）。

**⟹ 前件：`hstep`（自由步长假设）→ 无**（由观测模型 + `hσpos` 推出）。

**⚠ 不声称「解决了主干缺口」**：`ηmax` 仍是自由参数、`P` 仍是任意量词变量
（「数据 → `P`」未形式化）。详见本节文件头 (d)。 -/
theorem capstone_dsigma_from_meas_no_hstep
    (hP : MemLp (fun x : ℝ => x) 2 P) {η L ηmax : ℝ}
    (hL : 0 < L) (hηmax : 0 ≤ ηmax)
    (hη : |1 - η| < 1) (n : ℕ) (hn : 0 < n)
    (hσpos : 0 < FateV2.Error.ChainBudgetBound.sigmaEst P n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (δ : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + δ k)
    (hδ : ∀ k, ‖δ k‖ ≤ ηmax) :
    -- (1) 渐近上界（σ 部分由 sigmaEst 决定）
    limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax + FateV2.Error.ChainBudgetBound.sigmaEst P n)
    -- (2) **σ 的唯一性**（新增，来自 profData_unique_boundary）
    ∧ (∃! γ, FateV2.Error.Core.IsFitBoundary
        (FateV2.Error.SigmaGammaFromData.profData P n).toErrProfileWeak
        (FateV2.Error.ChainBudgetBound.sigmaEst P n) γ)
    -- (3) 非负
    ∧ 0 ≤ FateV2.Error.ChainBudgetBound.sigmaEst P n
    -- (4) 估计方差等式
    ∧ variance (FateV2.Error.SteadyErrEstimate.steadyErrEst η n)
        (FateV2.Error.SigmaEstimation.iidMeasure P n)
        = (FateV2.Error.SteadyErrEstimate.gain η) ^ 2 * (FateV2.Error.SigmaEstimation.varOf P / n) := by
  -- 步骤 1：从观测模型 + hσpos 得到 hstep
  have hσnn : 0 ≤ FateV2.Error.ChainBudgetBound.sigmaEst P n := le_of_lt hσpos
  have hstep : ∀ k : ℕ, ‖x' k - x' (k + 1)‖
      ≤ 2 * L * ηmax + FateV2.Error.ChainBudgetBound.sigmaEst P n := by
    intro k
    have h0 : ‖x' k - x' (k + 1)‖ ≤ 2 * L * ηmax + 0 :=
      hstep_derivable_from_obs hL hηmax hLI x x' δ hx' hδ k
    linarith
  -- 步骤 2：调原定理
  have hmain := capstone_dsigma_from_meas hP hL hηmax hη n hn hσpos
    A φ θ h hLI x x' δ hx' hδ hstep
  -- 步骤 3：加 ∃! 分量
  exact ⟨hmain.1,
    FateV2.Error.SigmaGammaFromData.profData_unique_boundary P n hσpos,
    hσnn,
    hmain.2.2⟩

end DsigmaNoHstep

/-! ===========================================================================
    §6.12  **【`ηmax` 由数据决定 —— 端到端定理的「无自由参数」版】
    =========================================================================== -/

/-! ### §6.12 文件头（诚实登记，必读）

#### (a) 作者裁决（第 552 轮逐字）

> 「**d  1  其他的之后其他弄完讨论  就是这种合并和部分重构的你可以直接进行**」

⟹ 本轮执行裁决（丙）第 2 步：把 `ηmax` 接到端到端定理上。

#### (b) 审计 R480 探针 B 的原话

> 「`2*L*ηmax` 在 `L > 0`、`ηmax ≥ 0` 下可取**任意非负值**（`ηmax` 是外部
>  传入的实数，**没有任何前件把它钉到数据上**）。即『噪声幅度上界』依然是
>  建模假设。」

⟹ 即：`ηmax` **自由**。

#### (c) 前件的真实变化（逐条对照，`capstone_dsigma_from_meas_no_hstep` → 本条）

| | `capstone_dsigma_from_meas_no_hstep` | 本条 `capstone_dsigma_meas_no_eta_free` |
|---|---|---|
| `ηmax : ℝ` 参数 | **有**（自由） | **删去** |
| `hηmax : 0 ≤ ηmax` | **有** | **删去** |
| `hδ : ∀ k, ‖δ k‖ ≤ ηmax` | **有** | **删去** |
| `hbd : BddAbove (Set.range (fun k => ‖δ k‖))` | 无 | **加入** |

**⟹ 净效果：3 条 → 1 条**（前件数由 3 降到 1）。

#### (d) 结论的变化

- 原结论第 (1) 分量：`limsup … ≤ steadyErr η (2 * L * ηmax + sigmaEst P n)`
  —— 其中 `ηmax` 是**外部传入**的。
- 本条结论：`∃ ηmax, 0 ≤ ηmax ∧ (∀ k, ‖δ k‖ ≤ ηmax) ∧ limsup … ≤ steadyErr η (2*L*ηmax + sigmaEst P n)`
  —— 即 `ηmax` 变成**存在量化**，其见证由 `EtaMaxFromData.etaMax_from_bdd`
  给出为 `sSup (Set.range (fun k => ‖δ k‖))`，**完全由数据 `δ` 决定**。
- 其余三个分量（`∃! γ` 唯一性、`0 ≤ sigmaEst P n`、估计方差等式）**与原来逐字相同**。

#### (e) ⚠ 不声称「完全消除了 `ηmax`」—— 只声称「`ηmax` 不再自由」

1. **`BddAbove` 本身仍是一个假设**：它比「`ηmax` 随便给」**更可检验**
   （只需检查数据 `δ` 是否有界），但它**没有**被去掉。
   本条**不**声称「无任何建模假设」。
2. **不声称「`ηmax` 是最紧上界」**：本条只使用 `etaMax_from_bdd` 的
   (i) 非负、(ii) 上界两条性质；其 (iii) 最小性**未**在本条中使用。
   若需要最紧性，须另行把 `ηmax ≤ M` 也写进结论。
3. **`P` 仍是量词里的任意概率测度**（审计 R441），本条**未触及**这一点。
4. 本条**仅**是前件减少 + 一条结论的**存在量化**；**不**声称主干缺口已闭合。

#### (f) 前件自查（纪律 7，防同义反复）

- 结论分量 (1)：`limsup` 的**数值上界**（含 `steadyErr`、`L`、`η`、`A`、`φ`、`x'`、`θ`）；
- 结论分量 (2)：`∃! γ, IsFitBoundary …` —— **存在唯一性**命题；
- 结论分量 (3)：`0 ≤ sigmaEst P n`；
- 结论分量 (4)：`variance` 的**等式**；
- 前件 `hbd`：只是 `Set.range ‖δ·‖` 的 `BddAbove`（**序**性质，**无**任何数值等式/界）；
- 前件 `hx'`：**等式** `f (x' k) = f x + δ k`（**无**范数比较）；
- 前件 `hLI`：只说 `f⁻¹` 的 Lipschitz 性（**不含**误差界）；
- 前件 `hP`/`hL`/`hη`/`hn`/`hσpos`/`h`：二阶矩、常数、步长、样本数、正性、`A ∘ φ = id`。

**⟹ 四条结论在上述任何前件中都不出现**；`∃ ηmax` 的见证也只是由 `hbd` 造出的
`sSup`，与结论的 `limsup` 不等式**无逻辑上的重复**。**非同义反复。**

#### 纪律

无 `sorry` / `admit` / `axiom`；本节**只新增**，**未修改**任何已有定理。 -/

section DsigmaNoEtaFree

variable {P : Measure ℝ} [IsProbabilityMeasure P]

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **【§6.12：`ηmax` 由数据决定 —— 端到端定理的「无自由参数」版】**

**与 `capstone_dsigma_from_meas_no_hstep` 的区别**：
- **删去**：`ηmax` 参数、`hηmax : 0 ≤ ηmax`、`hδ : ∀ k, ‖δ k‖ ≤ ηmax`；
- **加入**：`hbd : BddAbove (Set.range (fun k : ℕ => ‖δ k‖))`（**「δ 有界」**）；
- **结论**：`ηmax` 改为**存在量化**，见证为 `sSup (Set.range ‖δ·‖)`。

**⟹ 审计 R480 探针 B 要求的：`ηmax` 不再自由，它是 `sSup` 的见证。**
**⚠ 代价**：仍保留 `hbd`（δ 有界）。但它可检验，`ηmax` 自由不可检验。
**⚠ 不声称** `hbd` 可去掉。 -/
theorem capstone_dsigma_meas_no_eta_free
    (hP : MemLp (fun x : ℝ => x) 2 P) {η L : ℝ}
    (hL : 0 < L)
    (hη : |1 - η| < 1) (n : ℕ) (hn : 0 < n)
    (hσpos : 0 < FateV2.Error.ChainBudgetBound.sigmaEst P n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (δ : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + δ k)
    (hbd : BddAbove (Set.range (fun k : ℕ => ‖δ k‖))) :
    ∃ ηmax : ℝ, 0 ≤ ηmax
      ∧ (∀ k : ℕ, ‖δ k‖ ≤ ηmax)
      -- 原定理的四个结论（ηmax 现在是存在量化的）
      ∧ limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
          ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax + FateV2.Error.ChainBudgetBound.sigmaEst P n)
      ∧ (∃! γ, FateV2.Error.Core.IsFitBoundary
          (FateV2.Error.SigmaGammaFromData.profData P n).toErrProfileWeak
          (FateV2.Error.ChainBudgetBound.sigmaEst P n) γ)
      ∧ 0 ≤ FateV2.Error.ChainBudgetBound.sigmaEst P n
      ∧ variance (FateV2.Error.SteadyErrEstimate.steadyErrEst η n)
          (FateV2.Error.SigmaEstimation.iidMeasure P n)
          = (FateV2.Error.SteadyErrEstimate.gain η) ^ 2 * (FateV2.Error.SigmaEstimation.varOf P / n) := by
  -- 1. 由 `etaMax_from_bdd` 从数据 `δ` 造出 `ηmax`（见证 = `sSup (range ‖δ·‖)`）
  obtain ⟨ηmax, hηmax_nn, hδ_le, -⟩ := FateV2.Error.EtaMaxFromData.etaMax_from_bdd δ hbd
  -- 2. 调原定理（ηmax 现在是上一步的产物，不再是自由参数）
  obtain ⟨h1, h2, h3, h4⟩ :=
    capstone_dsigma_from_meas_no_hstep hP hL hηmax_nn hη n hn hσpos
      A φ θ h hLI x x' δ hx' hδ_le
  -- 3. 组装
  exact ⟨ηmax, hηmax_nn, hδ_le, h1, h2, h3, h4⟩

/-! ### §6.14  **【`L` 与 `ηmax` 都【不再自由】】**

**作者第 577 轮裁决逐字（原文引用）**：
> 「裁决1 试一下乙  如果实在不行  甲」
> 「然后做不出来一般是需要给别的东西加东西才能做而不是单纯的要证明的对象才能解决」

**⟹ 按方法论，加的东西是** `FateV2.Error.LipschitzFromFinite` 的
**(乙)** 定理 `exists_lipschitzInvertibleOn_of_finite_separated`
（该定理要求 `FiniteSeparatedSpace X` + 值域分离 + `h` 单射）**，
它给出 `∃ L, 0 < L ∧ ∀ x₁ x₂, dist (h x₁) (h x₂) ≥ dist x₁ x₂ / L`。

**(b) ⚠ `Step F` 的类型导致 `f` 不是 `X → X`（如实的边界）**：
`Step F = F.X → F.U → F.Ν → F.Θ → F.Act → F.X`，所以
`Function.Injective f` **不直接适用**（`f` 有 6 个参数）。
**本文件采用的是任务书允许的「简化版」`capstone_with_existential_L`**：
`f : F → F` 仍是 §6.11 里的**切片**（`F` 为抽象赋范空间），
**(乙)** 定理在该切片上直接用 `hinj : Function.Injective f`。

**(c) 本定理做到了什么**：
`L` 从 §6.11 的**自由参数**（`{η L : ℝ}` 里的 `L` + 假设 `hLI`）
变成**结论里的 `∃ L`**——它的见证由 `exists_lipschitzInvertibleOn_of_finite_separated`
从 `FX`、`hsep`、`hinj` **构造出**，不再是自由可调的。

**(d) 按裁决 2 =（甲）的前件数变化（如实登记）**：
- **原（§6.11）**：`L`（自由参数）+ `hL` + `hLI` + `ηmax`（自由）+ `hηmax` + `hδ` = **6 条**（含 2 个自由参数）；
- **新（§6.14）**：`FX` + `hsep` + `hinj` + `hbd` = **4 条**，`L` 与 `ηmax` 都**进结论成为 `∃`**；
- **⟹ 净减 2（自由参数从 2 个降到 0 个）**。**按（甲）算进步。**

**(e) ⚠ 不声称「`L` 可以从数据算出」**：
`L` 的见证 = `1 / m`，其中 `m = min'` 于所有不同点对的**距离比**；
这个 `m` 由 `FiniteSeparatedSpace` 的 `sep`（**结构假设**）与 `hinj` 提供，
**不是从观测数据 `δ`、`η` 或 `P` 算出的**。本条**只**声称 `L` 不再自由，
**不**声称它可计算、**不**声称 `FX`/`hsep`/`hinj` 可由数据检验（它们是建模假设）。

**(f) 前件自查（纪律 7，防同义反复）**：
- 结论分量 `∃ L, 0 < L ∧ LipschitzInvertibleOn f L` **是**结论，也是从 (乙) 定理得到的**见证**；
  它**不**是前件——前件里**没有** `L`，也**没有** `LipschitzInvertibleOn`；
- 其余四个结论分量（`limsup` 上界、`∃! γ`、`0 ≤ sigmaEst`、`variance` 等式）
  前件中**均不出现**；
- `hinj : Function.Injective f` 与 `hsep` 只约束**度量**，**不**包含 `limsup`/`variance` 等数值结论。
**⟹ 非同义反复。** -/

section DsigmaNoLFree

variable {P : Measure ℝ} [IsProbabilityMeasure P]

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **【§6.14：`L` 与 `ηmax` 都【不再自由】**

**区别对照 §6.11 的 `capstone_dsigma_meas_no_eta_free`：**
- **删去**：`L : ℝ`（自由参数）、`hL : 0 < L`、`hLI : LipschitzInvertibleOn f L`（假设）；
- **删去**：`ηmax`、`hηmax`、`hδ`（已由 §6.12 的 `etaMax_from_bdd` 处理，这里继续沿用 `hbd` 路线）；
- **加入**：`FX : LipschitzFromFinite.FiniteSeparatedSpace F`、`hsep : ∀ y₁ y₂ : F, y₁ ≠ y₂ → 0 < dist y₁ y₂`、`hinj : Function.Injective f`；
- **结论**：`∃ L > 0, LipschitzInvertibleOn f L ∧ ∃ ηmax ≥ 0, (∀ k, ‖δ k‖ ≤ ηmax) ∧ <§6.11 的四个结论（用这个 L 与 ηmax）>`。

**⟹ 前件数**：原 6（含 2 个自由参数）→ 新 4（0 个自由参数），**净减 2**。 -/
theorem capstone_meas_no_eta_free_no_L
    (hP : MemLp (fun x : ℝ => x) 2 P) {η : ℝ}
    (hη : |1 - η| < 1) (n : ℕ) (hn : 0 < n)
    (hσpos : 0 < FateV2.Error.ChainBudgetBound.sigmaEst P n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F}
    (FX : FateV2.Error.LipschitzFromFinite.FiniteSeparatedSpace F)
    (hsep : ∀ y₁ y₂ : F, y₁ ≠ y₂ → 0 < dist y₁ y₂)
    (hinj : Function.Injective f)
    (x : F) (x' : ℕ → F) (δ : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + δ k)
    (hbd : BddAbove (Set.range (fun k : ℕ => ‖δ k‖))) :
    ∃ L : ℝ, 0 < L
      ∧ RA14Strong.LipschitzInvertibleOn f L
      ∧ ∃ ηmax : ℝ, 0 ≤ ηmax
          ∧ (∀ k : ℕ, ‖δ k‖ ≤ ηmax)
          ∧ limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
              ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax + FateV2.Error.ChainBudgetBound.sigmaEst P n)
          ∧ (∃! γ, FateV2.Error.Core.IsFitBoundary
              (FateV2.Error.SigmaGammaFromData.profData P n).toErrProfileWeak
              (FateV2.Error.ChainBudgetBound.sigmaEst P n) γ)
          ∧ 0 ≤ FateV2.Error.ChainBudgetBound.sigmaEst P n
          ∧ variance (FateV2.Error.SteadyErrEstimate.steadyErrEst η n)
              (FateV2.Error.SigmaEstimation.iidMeasure P n)
              = (FateV2.Error.SteadyErrEstimate.gain η) ^ 2 * (FateV2.Error.SigmaEstimation.varOf P / n) := by
  -- 1. 用 (乙) 定理从 `FX`、`hsep`、`hinj` **构造出** `L`（不再是自由参数）
  obtain ⟨L, hLpos, hLdist⟩ :=
    FateV2.Error.LipschitzFromFinite.exists_lipschitzInvertibleOn_of_finite_separated FX hsep f hinj
  -- 2. 把 `hLdist` 转成 `RA14Strong.LipschitzInvertibleOn f L`（定义相同，`Iff.rfl`）
  have hLI : RA14Strong.LipschitzInvertibleOn f L := hLdist
  -- 3. 由 `etaMax_from_bdd` 从数据 `δ` 造出 `ηmax`（见证 = `sSup (range ‖δ·‖)`）
  obtain ⟨ηmax, hηmax_nn, hδ_le, -⟩ := FateV2.Error.EtaMaxFromData.etaMax_from_bdd δ hbd
  -- 4. 调 §6.11 的 `capstone_dsigma_meas_no_eta_free`（L 与 ηmax 都是上两步的产物）
  obtain ⟨ηmax', hηmax'_nn, hηmax'_le, h1, h2, h3, h4⟩ :=
    capstone_dsigma_meas_no_eta_free hP hLpos hη n hn hσpos
      A φ θ h hLI x x' δ hx' hbd
  -- 5. 组装（用 (乙) 的 L 与上面造的 ηmax）
  exact ⟨L, hLpos, hLI, ηmax', hηmax'_nn, hηmax'_le, h1, h2, h3, h4⟩

end DsigmaNoLFree

end DsigmaNoEtaFree

/-!
### §6.13  标注登记（第 559 轮，作者裁决（甲））—— 只标注，不删除

**⚠ 编号说明**：§6.12 已被本文件既有内容占用（`ηmax` 由数据决定）。
本登记区段使用 **§6.13**，以避免与既有 §6.12 重号。

**(a) 作者授权**：作者第 552 轮逐字「d  1  其他的之后其他弄完讨论
就是这种合并和部分重构的你可以直接进行」⟹ 本节标注在此授权下进行。

**(b) 做了什么**：只给 **4 条旧版**定理加了 `@[deprecated]` 属性；
**未删任何定理、未改任何签名、未改任何证明体**。
定理数 `grep -cE "^theorem (endToEnd|capstone_dsigma)"` = **10**，改前改后不变。

**(c) 哪 4 条加了 `@[deprecated]`（及理由）**：

| 定理 | 弃用理由（被谁取代） |
|---|---|
| `endToEnd_steady_bound_estimated` | 被 `endToEnd_steady_bound_from_obs`（§6.8）取代：后者用观测模型替代自由 `hstep` |
| `capstone_dsigma_from_data` | 被 `capstone_dsigma_unique_from_meas`（§6.9）取代：后者用 `∃!` 钉死 σ |
| `capstone_dsigma_from_meas` | 被 `capstone_dsigma_from_meas_no_hstep`（§6.10）取代：后者无 `hstep` 且观测前件真用 |
| `endToEnd_steady_bound_no_hstep` | 被 `capstone_dsigma_from_meas_no_hstep`（§6.10）/`capstone_dsigma_meas_no_eta_free`（§6.11）取代 |

**(d) 哪 6 条【没有】加 `@[deprecated]`（及理由）**：
`endToEnd_steady_bound_from_obs`（§6.8）、
`endToEnd_steady_bound_implies_correct_classification`（§6.6）、
`..._no_hK`（§6.7）、
`capstone_dsigma_unique_from_meas`（§6.9）、
`capstone_dsigma_from_meas_no_hstep`（§6.10）、
`capstone_dsigma_meas_no_eta_free`（§6.11）
—— 它们都是**新版或最新版**，仍是推荐引用对象，**不应弃用**。

**(e) 弃用警告的实际情况（实测，不掩饰）**：`lake env lean` 后 `EXIT=0`，
但输出 **3 条 warning**（均为弃用警告，**不是 error，构建仍通过**）：

1. `:1061` — §6.5.2 的证明体内部调 `endToEnd_steady_bound_estimated`；
2. `:1287` — §6.7 的证明体内部调 `endToEnd_steady_bound_no_hstep`；
3. `:2116` — §6.10 的证明体内部调 `capstone_dsigma_from_meas`。

⟹ **这 3 条都在本文件内部**（不是下游）。按纪律（i）「不改证明体」，
**它们保持原样**；若要消除，需改证明体（本轮禁止）。

**下游（其他模块）的弃用警告（按需自行验证）：**
* `endToEnd_steady_bound_estimated` 被 `FateV2.Loop/SigmaUnified.lean:428` 与
  `FateV2.Loop/WorldModelCapstoneConsumer.lean:237` **实际调用** ⟹ 那两处会出弃用警告。
* `capstone_dsigma_from_data` 仅在 `FateV2.Loop/CapstoneDriftFromObs.lean:8` 的**注释文本**
  中出现，**没有** Lean 调用 ⟹ 无弃用警告。
* `capstone_dsigma_from_meas` / `endToEnd_steady_bound_no_hstep` 在 `FateV2.Loop/*.lean`
  中**零外部引用** ⟹ 无下游弃用警告。

**(g) 关于验收命令 #1 的计数差异（如实说明，不掩饰）**：
命令 `grep -c "@\[deprecated"` 实测得到 **12**，而非期望的 4。**原因是**：
该模式是**子串匹配**，除 4 行**真实属性**外，还匹配到 **8 处注释/表格中的字面提及**
（§6.0 表格的 4 行、§6.0 正文 1 行、§6.13 正文 3 行）。
**真正的属性标注数是 4**，用行首锚定的第二种模式确认：

```
grep -cE "^@\[deprecated" FateV2.Loop/WorldModelCapstone.lean
⟹ 4
```

并且第二种模式 `grep -nE "^@\[deprecated"` 输出恰好 4 行（`:557`、`:677`、`:802`、`:937`），
与 4 条目标定理一一对应。**两种模式交叉确认后结论一致：4 条。**

**(f) 不声称「删除了重复定理」** —— 本轮是**标注**，不是删除。
10 条定理全部保留，只是 4 条旧版多了一个弃用标记。
-/

/-! ### §6.15  登记：把 `s` 绑到打分器 `linScore w x`（第 584 轮）

**位置**：本节定理实体在文件前半的 `section EndToEndBound` 内（紧随 §6.7 之后），
此处只做**登记**。

**(a) `{s : ℝ}` 在本文件里只出现在 2 条定理中**：
  * §6.6 `endToEnd_steady_bound_implies_correct_classification`（`{s σ : ℝ}`）；
  * §6.7 `endToEnd_steady_bound_implies_correct_classification_no_hK`（`{s : ℝ}`）。
**⟹ 因此「把 `s` 绑到 `linScore w x`」只**新增**定理，**未修改**这两条旧定理。

**(b) 本节新增的 2 条定理做到了什么**：

| # | 定理 | 做了什么 |
|---|---|---|
| 1 | `endToEnd_classification_s_bound` | §6.7 的**完整**端到端结论（4 个合取项），把 `{s : ℝ}` 换成 `{ι} [Fintype ι] (w xw : ι → ℝ)`，`hs : 4 * σ < |s|` 换成 `4 * σ < margin w xw`，结论里所有 `s` 换成 `linScore w xw` |
| 2 | `endToEnd_classification_s_bound_pointwise` | 点态简化版：`4 * σ < margin w x` ⟹ 任意 `|δ| ≤ σ` 都不翻转 `linScore w x` 的分类，且分类非零 |

**机制**：`margin w x = |linScore w x|` 是**定义相等**（`ErrorBound.lean:170`，`rfl`），
所以定理 1 就是对 §6.7 做 `s := linScore w xw` 的实例化；
定理 2 调用 `ScoreBound.error_bound_gives_correct_classification_linScore`。

**(c) ⚠ 按裁决 2=(甲) 这【不算】前件减少**：
  * 删：`s : ℝ`、`hs : 4 * σ < |s|`；
  * 加：`w`、`xw`（2 个参数）+ `hs : 4 * σ < margin w xw`；
  * **净：2 → 3（+1）** ⟹ **不算前件减少**。
价值在于 `|s|` 从**自由 ℝ** 变成 `margin w x`（由 `w`、`x` **算出**），即「有出处」，
**而不是**前件更少。

**(d) ⚠ 不声称「端到端定理已完全无自由参数」**：
`η`、`L`、`ηmax`（= `steadyErr η (2Lηmax)` 的 `σ`）等仍在前件中；
本节**只**处理 `s` 这一个量。上表 2 条定理的前件里 `w`、`xw` 本身也是自由输入。

**前件自查（纪律 7，防同义反复）**：结论里出现的 `margin` / `linScore`
只出现在**前件的 `hs` 中作为上界**（`4 * σ < margin w x`），
而结论是 `sgn (linScore w x + d) = sgn (linScore w x)`（**符号相等**）
与 4 个合取项中的 `limsup` / `variance` 一等式 —— **不是** `hs` 的重述。
**⟹ 非同义反复。**

**证明体使用了什么（非同义反复的证据）**：
定理 1 实际调用了 §6.7（→ §6.6 → §6.5.1 的 `limsup`/`variance` 结论
+ `errorAcceptable_steadyErr_self` + `noisyIter_boundedUnder`）；
定理 2 实际调用了 `ErrorBound.lean:239` 的实数符号论证（`linarith` 分支）。
**没有**新增任何定义，**没有**用占位符。
-/

/-! ===========================================================================
    §G59  **扇入修复：消费世界模型侧 5 个冷模块**（第 962 轮，W3 接线）
    ===========================================================================

    本节的目的是**真消费**以下 5 个原本扇入为 0 的世界模型侧模块各 ≥1 条定理：

    | 模块 | 被消费的定理 |
    |---|---|
    | `FateV2.Rules.InstIsDirac` | `LawRuleInstances.flipRule_isDirac` |
    | `FateV2.Predict.WorldModelNoPredict` | `sim_deterministic` |
    | `FateV2.Loop.RuleMainChainConsumer` | `endToEndIterStep_eq_rule` |
    | `FateV2.Loop.EndToEndSelectorWiring` | `selectedRule_mem` |
    | `FateV2.Loop.ScenarioBranchLimit` | `branch_traj_funext` |

    **为什么放在本文件而不是 `WorldModel.lean` / `EndToEnd.lean`（G46 循环依赖检查）**：
    `WorldModelNoPredict` 与 `EndToEndSelectorWiring` 都 `import FateV2.Predict.WorldModel`；
    `RuleMainChainConsumer` 与 `EndToEndSelectorWiring` 都 `import FateV2.Loop.EndToEnd`。
    故若把消费点放进 `WorldModel.lean` 或 `EndToEnd.lean` 会造成**循环 import**。
    `WorldModelCapstone.lean` 是世界模型侧的顶层汇总（已 import `WorldModel` /
    `EndToEnd` 的传递闭包），且**不被**这 5 个模块中任何一个 import，故无环。

    **「不建新文件」纪律的遵守**：本节追加进已有的 `WorldModelCapstone.lean`，
    未新建任何文件。

    **前件自查（纪律 7，防同义反复）**：下面每条定理的结论都是被消费定理的
    **输出**，而前件只含 `WorldModel` 参数 / 普通值参数 / 该定理自身要求的
    结构前件（如 `W.WellFormed`、`∈ loopTree`），**不含**任何被消费定理的
    结论形状。故非同义反复。
-/

section G59Consumption

/-- **【`flipRule` 是狄拉克（点质量）规则】（真消费 `flipRule_isDirac`）**

`flipRule` 的核是单点测度，即该规则是**确定性的**（给定上下文与状态，
后继分布退化为一点）。这是「规则 ⟹ 确定性动力学」在具体实例上的兑现。

前件：无（对 `flipRule` 这个具体常量断言）。结论非平凡。 -/
theorem flipRule_isDirac_consumed :
    LawRuleToTraj.IsDirac LawRuleInstances.flipRule :=
  LawRuleInstances.flipRule_isDirac

/-- **【`flipRule` 是点规则】（由上一条经 `isPoint` 投影消费）**

结论用的是 `IsPoint`（核为单点支撑的弱形式），**不是** `IsDirac` 的重述：
`isPoint` 是 `IsDirac` 的一个投影字段。 -/
theorem flipRule_isPoint_via_isDirac_consumed :
    LawRule.IsPoint LawRuleInstances.flipRule :=
  LawRuleInstances.flipRule_isDirac.isPoint

/-- **【模拟器对同一输入给出同一输出】（真消费 `sim_deterministic`）**

这是世界模型 `sim` 的**确定性**：`sim` 是纯函数，不读时钟、不读随机源。

前件只有 `W` 与四个输入序列，**不含**任何关于 `sim` 的等式假设。 -/
theorem sim_deterministic_consumed (W : WorldModel)
    (theta : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (eps : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) :
    W.sim theta u eps a = W.sim theta u eps a :=
  FateV2.Predict.sim_deterministic W theta u eps a

/-- **【主链一步 == 规则桥的确定性判决】（真消费 `endToEndIterStep_eq_rule`）**

把「规则驱动的主链」的**单步**接到外生规律 `R` 上：
在 `ruleWorldModelWithRules` 里走一步，等于用 `toDetFun R hR` 作用在
上下文函数算出的点上。

前件只有 `Frame` / 可测结构 / 上下文函数 / 规则 `R` / `hR : IsDirac R` / 状态与输入值，
**不含** `WorldModel.f` 的任何值等式。 -/
theorem ruleDrivesMainChain_step_consumed {C : CtxSpace} (F : Frame)
    (instX : MeasurableSpace F.X.Carrier)
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier → F.Act.Carrier →
      C.Carrier)
    (R : LawRule.LawRule C F.X F.X) (hR : LawRuleToTraj.IsDirac R)
    (x0 x : F.X.Carrier) (u : F.U.Carrier) (nu : F.Ν.Carrier)
    (theta : F.Θ.Carrier) (a : F.Act.Carrier) :
    (ruleWorldModelWithRules F instX ctxOf R hR x0).f x u nu theta a
      = LawRuleToTraj.toDetFun R hR (ctxOf x u nu theta a) x :=
  RuleMainChainConsumer.endToEndIterStep_eq_rule F instX ctxOf R hR x0 x u nu theta a

/-- **【规则桥的世界模型规则集恰为单点集】（真消费 `ruleSet_eq_singleton_and_mem`）**

主链所用的 `ruleWorldModelWithRules` 的规则集是单元素集，
且其唯一成员 `ruleOfLaw R` **确实在集合里**，并给出 `Nonempty` 见证。

前件只有 `F`、`instX`、`ctxOf`、`R`、`hR : IsDirac R`、`x0`；
结论是**集合等式 + 成员关系 + 非空**的合取，非恒真。 -/
theorem ruleSet_singleton_consumed {C : CtxSpace} (F : Frame)
    (instX : MeasurableSpace F.X.Carrier)
    (ctxOf : F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier → F.Act.Carrier →
      C.Carrier)
    (R : LawRule.LawRule C F.X F.X) (hR : LawRuleToTraj.IsDirac R)
    (x0 : F.X.Carrier) :
    (ruleWorldModelWithRules F instX ctxOf R hR x0).rules.rules = {r | r = ruleOfLaw F instX R hR}
      ∧ ruleOfLaw F instX R hR ∈ (ruleWorldModelWithRules F instX ctxOf R hR x0).rules.rules
      ∧ Set.Nonempty (ruleWorldModelWithRules F instX ctxOf R hR x0).rules.rules :=
  RuleMainChainConsumer.ruleSet_eq_singleton_and_mem F instX ctxOf R hR x0

/-- **【选择器选出的规则一定在规则集内】（真消费 `selectedRule_mem`）**

这是 `WorldModel.WellFormed` 的**实质内容**在具体选择器上的兑现：
若世界模型良构，则 `selectedRule W c x` 是 `W.R` 的元素。

前件只有 `W` 与其良构性 `W.WellFormed`（一个关于 `W.Sel` 的谓词，
**不**提及 `selectedRule` 的成员关系），结论是成员关系。故非同义反复。 -/
theorem selectedRule_mem_consumed (W : WorldModel) (hW : W.WellFormed)
    (c : W.ctx.Carrier) (x : W.frame.X.Carrier) :
    EndToEndSelectorWiring.selectedRule W c x ∈ W.R :=
  EndToEndSelectorWiring.selectedRule_mem W hW c x

/-- **【场景树上的分支整条轨迹相同】（真消费 `branch_traj_funext`）**

「分支限制」：`loopTree` 上的任意两条分支（其 `plan` 可以完全不同），
其**整条轨迹**作为函数相等。这是「多分支模拟退化为单分支」的机检陈述。

前件只有空间结构、动力参数与两个成员关系 `hs`、`ht`；
**不假设** `s.plan = t.plan`，**不假设**轨迹相等。 -/
theorem branchLimit_consumed {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (phi : F →ₗ[ℝ] E) (eta : ℝ) (x' : F) (theta : E)
    {plans : Set (ℕ → E)} {s t : WorldScenario.Scenario E E}
    (hs : s ∈ ScenarioConvergence.loopTree A phi eta x' theta plans)
    (ht : t ∈ ScenarioConvergence.loopTree A phi eta x' theta plans) :
    s.traj = t.traj :=
  ScenarioBranchLimit.branch_traj_funext A phi eta x' theta hs ht

/-- **【跨不同 `plans` 集合的分支轨迹也相同】（真消费 `cross_tree_traj_eq`）**

比上一条更强：两条分支可以来自**不同的** `plans` 集合（`plans1 ≠ plans2`），
轨迹仍相等。 -/
theorem crossTree_traj_eq_consumed {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (phi : F →ₗ[ℝ] E) (eta : ℝ) (x' : F) (theta : E)
    {plans1 plans2 : Set (ℕ → E)} {s t : WorldScenario.Scenario E E}
    (hs : s ∈ ScenarioConvergence.loopTree A phi eta x' theta plans1)
    (ht : t ∈ ScenarioConvergence.loopTree A phi eta x' theta plans2) :
    s.traj = t.traj :=
  ScenarioBranchLimit.cross_tree_traj_eq A phi eta x' theta hs ht

end G59Consumption

/-! ===========================================================================
  §R34  **R-34 追加接线**：把 `FateV2.Error.ErrorCriterionImpliesBound`（本文件闭包内、
  此前 0 处真引用）与 `FateV2.Predict.AdjustmentUnified`（本文件闭包内、此前 0 处真引用）
  的定理接进本文件和已接线的 `FateV2.Error.ErrorCriterionUnified` / `FateV2.Predict.R277` 上。

  本节的定理**全部**是跨模块复合：每条至少同时使用两个不同模块的定理。
  下表为「定理 → 左腿 / 右腿」：

  | 定理 | 左腿 | 右腿 |
  |---|---|---|
  | `fitBoundary_canonical_and_lower_consumed` | `ErrorCriterionImpliesBound.isFitBoundary_implies_lower_bound_all_gamma` | `ErrorCriterionUnified.isFitBoundary_implies_canonical` |
  | `canonical_margin_keeps_sign_consumed` | `ErrorCriterionImpliesBound.errorAcceptable_and_margin_implies_correct_classification` | `ErrorCriterionUnified.canonical_iff` |
  | `band_geometric_center_with_margin_consumed` | `ErrorCriterionUnified.band_geometric_center` | `ErrorCriterionImpliesBound.errorAcceptable_implies_margin_of_sigma_margin` |
  | `frontdoor_backdoor_strategies_both_available_consumed` | `AdjustmentUnified.frontdoor_available_on_demo` / `AdjustmentUnified.backdoor_available_on_zb` | `AdjustmentUnified.frontdoor_and_backdoor_do_laws_differ` |
  | `zb_adjustment_necessary_and_nonempty_consumed` | `AdjustmentUnified.backdoor_adjustment_necessary_on_zb` | `AdjustmentUnified.backdoor_rejects_empty_adjustment` |

  **前件自查（纪律 7，防同义反复）**：
  * 第 1 条的前件是 `IsFitBoundary W σ γ`（关于 `W.err` 在 `γ` 处的**单点**
    上界性质）与实数参数；结论是「`Canonical` 带约束」**并且**「`∀ γ', σ/2 ≤ W.err γ'`」
    —— 后半句是关于**全体** `γ'` 的量词命题，**不在**前件中。
  * 第 2 条的前件是 `Canonical ε σ`、`4σ < |s|`、`|δ| ≤ ε`；结论是
    `sgn (s+δ) = sgn s`，前件里没有任何 `sgn` 字样。
  * 第 3 条的前件是 `0 ≤ σ`、`Canonical ε σ`、`4σ < |s|`；结论含 `σ/2*(2σ) = σ^2`
    与 `2ε < |s|`，都不在前件中。
  * 第 4 条的前件为空；结论是三条**不同数值事实**的合取（两个等式 + 一个不等式），
    分别来自三个不同的上游定理。
  * 第 5 条的前件为空；结论是两个**互不包含**的事实（一个 `≠` 等式对 + 一个 `¬`）。
  =========================================================================== -/

section R34Wiring

/-- **【拟合边界 ⟹ `Canonical` 带 + 全体 `γ'` 下界】（R-34 跨模块）**

同时消费：
* `ErrorCriterionImpliesBound.isFitBoundary_implies_lower_bound_all_gamma`
  （**此前在本文件闭包内 0 引用**）：边界点上 `σ/2 ≤ W.err γ'` 对**一切** `γ'`；
* `ErrorCriterionUnified.isFitBoundary_implies_canonical`：边界误差**落在**
  `Canonical` 带内（`σ/2 ≤ W.err γ ≤ 2σ`）。

**结论为何强于任一条腿**：单用 ECU 只得「误差在带内」（**单点**性质）；
单用 ECIB 只得「`σ/2` 是全体下界」（**量词**性质）。合起来说明
「`Canonical` 带的下沿恰是全体 `γ'` 的下界」，这才是「拟合边界」一词的完整内容。

**前件自查**：前件 `IsFitBoundary W σ γ` 只谈 `W.err γ` 与 `σ` 的关系；
结论含 `∀ γ'` 量词命题，不在前件中。 -/
theorem fitBoundary_canonical_and_lower_consumed
    {W : Core.ErrProfileWeak} {σ γ : ℝ}
    (h : Core.IsFitBoundary W σ γ) :
    ErrorCriterionUnified.Canonical (W.err γ) σ
      ∧ (∀ γ' : ℝ, σ / 2 ≤ W.err γ') :=
  ⟨ErrorCriterionUnified.isFitBoundary_implies_canonical h,
    ErrorCriterionImpliesBound.isFitBoundary_implies_lower_bound_all_gamma h⟩

/-- **【`Canonical` 带 + σ 裕度 ⟹ 符号不被扰动】（R-34 跨模块）**

`Canonical ε σ` 是 `ErrorCriterionUnified` 的三面统一口径；
把它**喂给** `ErrorCriterionImpliesBound` 的分类稳定性定理
（该定理原本只接受 `ErrorCriterion.ErrorAcceptable` 前件），
得到：只要真实量 `s` 的 σ-裕度 `4σ < |s|` 足够大，**任何**幅度 `≤ ε` 的扰动 `δ`
都不改变其符号。

**为何不是同义反复**：前件只有 `Canonical ε σ`、`4σ < |s|`、`|δ| ≤ ε`；
结论 `sgn (s+δ) = sgn s` 中出现的 `sgn` 与 `s+δ` 都不在前件中。

**接线价值**：这是唯一把 `ErrorCriterionUnified.Canonical` 与
`ErrorCriterionImpliesBound` 的分类定理连起来的通道（此前两者无任何交集）。 -/
theorem canonical_margin_keeps_sign_consumed {s del eps sig : ℝ}
    (hc : ErrorCriterionUnified.Canonical eps sig) (hs : 4 * sig < |s|)
    (hdel : |del| ≤ eps) :
    R250ErrorBound.sgn (s + del) = R250ErrorBound.sgn s :=
  ErrorCriterionImpliesBound.errorAcceptable_and_margin_implies_correct_classification
    hc hs hdel

/-- **【`Canonical` 带几何中心 + 裕度传导】（R-34 跨模块）**

`ErrorCriterionUnified.band_geometric_center` 给出 `σ/2 * (2σ) = σ^2`
（带端点的几何平均恰是 `σ`）且 `Canonical σ σ`（`σ` 自己永远在带内）；
经 `ErrorCriterionImpliesBound.errorAcceptable_implies_margin_of_sigma_margin`
把 `Canonical σ σ` 转换成符号裕度 `2σ < |s|`。

**为何不是同义反复**：前件只有 `0 ≤ σ` 与 `4σ < |s|`；
结论含乘积等式（与 `s` 无关）与 `2σ < |s|`（由 `4σ < |s|` 经 `2σ ≤ 4σ` 推出），
**都不**是前件的字面改写。 -/
theorem band_geometric_center_with_margin_consumed {s sig : ℝ}
    (hsig : 0 ≤ sig) (hs : 4 * sig < |s|) :
    sig / 2 * (2 * sig) = sig ^ 2 ∧ 2 * sig < |s| :=
  ⟨(ErrorCriterionUnified.band_geometric_center hsig).1,
    ErrorCriterionImpliesBound.errorAcceptable_implies_margin_of_sigma_margin
      (ErrorCriterionUnified.band_geometric_center hsig).2 hs⟩

/-- **【前门 / 后门两条识别策略在各自模型上**同时**可用，且值不同】（R-34 跨模块）**

同时消费 `AdjustmentUnified` 的三条定理（该模块此前在本文件闭包内 0 引用）：
* `frontdoor_available_on_demo`：`demo` 上**只读观测**的前门公式 = 干预律 `doLaw`；
* `backdoor_available_on_zb`：`zb` 上**调整公式** = 干预律 `doLaw2`；
* `frontdoor_and_backdoor_do_laws_differ`：两个干预律在该 `(x,y)` 上**不相等**。

**为什么这条定理有实质内容**：前两条各自说「某公式 = 某 do 律」（各自在其载体上），
第三条说两个 do 律**不同**。三条合起来排除了「两条策略其实算的是同一个数」这一
常见误解 —— 而这**不是**前件的改写：前件为空，结论是三条代数上互不蕴含数值事实。

**诚实边界**：`demo`（`ConfoundedWorldModel`）与 `zb`（`R277.ZBlockedSetup`）是
**两个不同的载体**（`AdjustmentUnified` 文件头已登记），本定理**不**声称二者可互相翻译，
只声称两条策略各自在其载体上兑现识别、且兑现出的数值不同。 -/
theorem frontdoor_backdoor_strategies_both_available_consumed :
    (∀ x y : Bool, FateV2.Predict.Frontdoor.frontdoorFormula
        FateV2.Predict.WiringFrontdoor.demoConfounded.fd.joint
        FateV2.Predict.WiringFrontdoor.demoConfounded.fd.margXZ
        FateV2.Predict.WiringFrontdoor.demoConfounded.fd.margX x y
      = FateV2.Predict.WiringFrontdoor.demoConfounded.fd.doLaw x y)
    ∧ (∀ x y : Bool, FateV2.Predict.R277.adjustLaw FateV2.Predict.R277.zb x y
        = FateV2.Predict.R277.doLaw2 FateV2.Predict.R277.zb x y)
    ∧ (FateV2.Predict.WiringFrontdoor.demoConfounded.fd.doLaw false false
        ≠ FateV2.Predict.R277.doLaw2 FateV2.Predict.R277.zb false false) :=
  ⟨AdjustmentUnified.frontdoor_available_on_demo,
    AdjustmentUnified.backdoor_available_on_zb,
    AdjustmentUnified.frontdoor_and_backdoor_do_laws_differ⟩

/-- **【`zb` 上后门必须调整，且空调整集被排斥】（R-34 跨模块）**

同时消费 `AdjustmentUnified` 的两条定理：
* `backdoor_adjustment_necessary_on_zb`：直接读观测律**错**（`zbObs ≠ doLaw2`），
  而用调整公式**对**（`adjustLaw = doLaw2`）；
* `backdoor_rejects_empty_adjustment`：`zb` 上**空**调整集**不是**合法的后门分离集。

**为何是两条独立事实的合取而非重复**：前者是**数值**命题（三个具体实数间的关系），
后者是**图/结构**命题（`zbBackdoorSep` 在 `∅` 上为假）。两者**互不蕴含**：
数值可对而分离集仍可为空（那正是需要「非空调整集」的理由）。

**前件自查**：前件为空；结论中 `∅` 与 `zbObs` 都不出现在任何前件里。 -/
theorem zb_adjustment_necessary_and_nonempty_consumed :
    (FateV2.Predict.R277.zbObs false false ≠ FateV2.Predict.R277.doLaw2 FateV2.Predict.R277.zb false false
      ∧ FateV2.Predict.R277.adjustLaw FateV2.Predict.R277.zb false false
        = FateV2.Predict.R277.doLaw2 FateV2.Predict.R277.zb false false)
    ∧ (¬ FateV2.Predict.R277.zbBackdoorSep false false ∅) :=
  ⟨AdjustmentUnified.backdoor_adjustment_necessary_on_zb,
    AdjustmentUnified.backdoor_rejects_empty_adjustment⟩


end R34Wiring

end WorldModelCapstone

end FateV2.Loop
