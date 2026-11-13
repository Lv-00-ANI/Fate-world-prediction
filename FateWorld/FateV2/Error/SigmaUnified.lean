import FateWorld.FateV2.Error.SigmaFromAIC
import FateWorld.FateV2.Error.SigmaFromInfoGain
import FateWorld.FateV2.Error.SigmaFromDomain
import FateWorld.FateV2.Loop.WorldModelCapstone
import Mathlib.Tactic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/SigmaUnified.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 35 处，含 4 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Loop
open FateV2.Predict
open FateV2.Error
open FateV2.Modeling
open FateV2.Model
open FateV2.Rules

/-
  命运理论 · **σ 三条破解路径的汇合层（`SigmaUnified`）**

  ============================================================================
  ⚠ 本文件的定位与诚实边界（**必读，不得略过**）
  ============================================================================

  **背景（审计 R399）**：三个 σ 模块

    - `FateV2.Error/SigmaFromAIC.lean`      （破法**乙** · AIC/BIC，21 定理）
    - `FateV2.Error/SigmaFromInfoGain.lean` （破法**丙** · 信息增益，13 定理）
    - `FateV2.Error/SigmaFromDomain.lean`   （破法**丁** · 领域参数，13 定理）

  **互不 `import`、扇入全为 0**。审计给出的验收命令

      grep -rn "sigmaAIC\|sigmaCriterion\|resolveSigma" FateV2.Error/ | grep -v SigmaFrom | wc -l

  在**本文件新建前**结果为 **0**。本文件的**唯一目的**是让这个数字 > 0，
  即让三条路径至少**被同一个下游消费一次**，并把「哪条破了循环、哪条没破」
  用定理而不是散文固定下来。

  ----------------------------------------------------------------------------
  §一  (a) 三条路径的**真实强度**（逐条核对源码后如实登记）
  ----------------------------------------------------------------------------

  **⚠ 结论先行：三条路径【都没有破】裁决 K §六·补三 的循环。**
  审计的判定正确。逐条证据（均可 grep 核对，行号为写作时实测）：

  1. **破法乙（`SigmaFromAIC`）—— 没破，但它是三条里唯一有一条「实质定理」的。**
     - `SigmaFromAIC.lean:521` 的 `isFitBoundary_sigmaAIC`：文件头 `:511-514`
       **自己声明**「把结论的第二分量放在了前件里 ⟹ 本文件如实登记：
       这条定理是【同义反复】」。**审计指认成立**，本文件复核无误。
     - `SigmaFromAIC.lean:543` 的 `isFitBoundary_sigmaAIC_of_argmin` 与
       `SigmaFromAIC.lean:484` 的 `err_le_of_aic_argmin` **是实质的**：
       `err_le_of_aic_argmin` 从「**AIC 的 argmin**」推出「**误差的 argmin**」
       （两个不同泛函的最小点重合，需 `Real.log` 单调 + `n > 0`），
       其前件（AIC argmin / n>0 / err 正 / γ∈S）**不含**结论。
     - **但它仍没破循环**：`aicOfErr` 里那个 `k`（模型维数）是**自由参数**，
       而 `sigmaAIC W γ := W.err γ`（`SigmaFromAIC.lean:457`）**就是误差本身**。
       「σ_AIC」不是新的信息源，它是**误差剖面在一点的值**。
       ⟹ 循环「估 σ 需先有分辨率」**原样保留**。
     - **`le_sigmaAIC_of_hasFitBoundary`（`:566`）是 `h.2 γ` 的直接应用**
       （证明即 `exact hγ₀.2 γ`），无独立内容。

  2. **破法丙（`SigmaFromInfoGain`）—— 没破，且缺的东西最多。**
     - 文件头 §四 自己登记：判据 σ 与 `IsFitBoundary` 的 σ **是否同一未证**，
       「桥接假设 `FitGainBridge`（`:296`）只定义、不证」。
     - 真定理只有：`klDiv_nonneg`（KL 非负）、`sigmaCriterion_nonneg`、
       `sigmaCriterion_le`、`sigmaCriterion_eq_zero`。
       `sigmaCriterion_le` 是 `csInf_le` 的**一行应用**（下确界的基本性质），
       不是关于信息增益的特殊事实 —— 任何实值 `f` 都成立。
     - **⟹ 循环没破**：`sigmaCriterion` 吃的是**任意的** `f : ℝ → ℝ`，
       没有任何一处把它接到误差剖面 `W.err` 上（`FitGainBridge` 未实例化）。

  3. **破法丁（`SigmaFromDomain`）—— 没破，且它自己最先承认。**
     - 文件头 §一 明写：「`FateV2.Error/FitBoundary.lean:268` 的
       `IsFitBoundary (W) (σ γ)` **已经把 σ 作参数传入** ⟹ 破法丁
       在 `FitBoundary` 里**已经是现状**，本文件**不新增数学**」。
     - `resolveSigma`（`:212`）的 `unknown` 分支返回 `W.err g0`，
       文件头 §二 与 §4 用两条定理
       （`unknown_placeholder_is_placeholder`、`resolveSigma_unknown_not_unique`）
       **主动证明它只是一个占位、依赖 `g0`、不唯一**。
     - **⟹ 循环没破。** 破法丁是**接口统一**，不是数学突破。

  **⚠ 我不声称发现了任何一条「其实破了」。** 复核结论与审计一致：
  三条都没破。**本文件因此不得声称「循环已破」（见 §四.4）。**

  ----------------------------------------------------------------------------
  §二  (b) 本文件**做到了什么 / 没做到什么**
  ----------------------------------------------------------------------------

  **做到了**（只列本文件实际给出的定理，逐条可 `#check`）：

  * §3 **破法 → `SigmaSource` 的映射**：`sourceOfAIC` / `sourceOfInfoGain` /
    `sourceOfDomain` / `sourceOfUnknown`，把三种破法的输出都映到
    `FateV2.Error.SigmaFromDomain.SigmaSource`（构造子名经 `#check` 确认，未猜）。
  * §3.2 **统一入口的事实**：三条提供者经 `resolveSigma` 之后
    `domain`/`estimated` 两条**逐字返回**其 σ（`rfl` 级，如实标注），
    `unknown` 落到 `W.err g0`。
  * §4 **两条上界型结果的对齐**：
    - `sigmaAIC_eq_of_isFitBoundary`：把 `le_sigmaAIC_of_hasFitBoundary` 的
      **`≤` 在边界点处收紧为 `=`**（新内容：`SigmaFromAIC` 里没有）。
    - `no_sigmaCriterion_eq_sigmaAIC_pointwise`：**分离定理** ——
      证明**不存在**任何 `f` 使 `sigmaCriterion f` 逐个 γ 等于 `sigmaAIC W γ`
      （对某个 err 非常值的 `W`）。这是本文件**唯一有实质数学内容**的定理。
  * §5 **下游消费（验收关键）**：`capstone_sigmaFromData` ——
    把 `SigmaFromDomain.resolveSigma` 提供的 σ 塞进
    `FateV2.Loop.WorldModelCapstone.endToEnd_steady_bound_estimated` 的**自由 σ 参数位**
    `dσ`，从而该参数不再自由，**且非负性由 `resolveSigma_nonneg` 免费给出**
    （不需要额外假设 `0 ≤ dσ`）。

  **没做到**（缺什么，逐条登记）：

  * **没有**构造 `SigmaFromInfoGain.FitGainBridge` 的具体实例 `Wof`
    （缺：`infoGain` 的参数分布族 `p_γ`，Mathlib 无；见 `SigmaFromInfoGain` §五）。
    ⟹ **判据 σ 与 `IsFitBoundary` 的 σ 的同一性仍未证**，
    §4 的分离定理只是把「不能**直接**等同」的**一个**障碍钉死，
    **不**等于「不存在任何桥接」。
  * **没有**证明 `sigmaAIC W γ` 等于某个「真噪声尺度」。
    它在定义上就是 `W.err γ`（`SigmaFromAIC.lean:457`），**不可证**为真 σ
    （那是建模断言，`SigmaFromAIC` §二.4 已登记）。
  * **没有**修改 `FateV2.Error/WorldModelCapstone.lean`（纪律：不改已入链模块）。
    §5 因此走「**新 σ 提供者 + 引用 Capstone 既有定理**」这条路，
    即把 Capstone 的自由 σ 参数**喂**进去，而不是改它的签名。
  * **没有**把 `sigmaCriterion` 接到 Capstone 上。
    Capstone 的 σ 位是**方差预算** `dσ : ℝ`，而 `sigmaCriterion` 是
    「增益阈值」的下确界，二者**量纲与语义都不同**，接上去只能靠空假设。

  ----------------------------------------------------------------------------
  §三  (c) ⚠ 本文件**不**声称「循环已破」
  ----------------------------------------------------------------------------
  本文件是**接线层（wiring layer）**，不是**攻坚层**。
  它把三条路径的全部输出统一到一个 `SigmaSource`，
  从而下游**可以**只接一个口；它**不**提供任何新的 σ 估计方法，
  **不**提供任何 `σ = 真噪声尺度` 的定理，**不**消除
  「估 σ 需先有分辨率」的循环。**循环状态：未破（unchanged）。**

  ----------------------------------------------------------------------------
  §四  纪律
  ----------------------------------------------------------------------------
  零 `sorry` / 零 `admit` / 零 `axiom`；只新建本文件，**不改任何已有模块**；
  所有被调用的标识符均经 `#check` 确认；交付前 `lake env lean` 两遍。
  -/


namespace FateV2.Error

namespace SigmaUnified

universe u

open Filter Topology
open scoped Topology

open FateV2.Error.SigmaFromDomain (SigmaSource resolveSigma resolveSigma_nonneg
  resolveSigma_domain resolveSigma_estimated resolveSigma_unknown)

/-! ===========================================================================
  §3  阶段 1：破法 → `SigmaSource` 的映射
  =========================================================================== -/

/-! ### §3.1  三个提供者（+ 一个「未给」提供者）

**设计要点**：`SigmaSource` 的三个构造子（`domain` / `estimated` / `unknown`）
本身**已经**是「σ 从哪来」的三分。本节的映射把三种**破法的输出**分别
落到**语义正确**的那一支上：

| 破法 | 输出是什么 | 落到哪一支 | 理由 |
|---|---|---|---|
| 丁 `SigmaFromDomain` | 外部给定的 σ | `domain` | 它是**领域参数**，不是数据推得 |
| 乙 `SigmaFromAIC` | `W.err γ`（一点误差） | `estimated` | 它**由数据/剖面算出** ⟹ 是估计 |
| 丙 `SigmaFromInfoGain` | `sigmaCriterion f`（增益阈值下确界） | `estimated` | 同样**由数据算出** |
| （无） | 无 | `unknown` | 兜底走 `elbow` 路径 |

**⚠ 这一步的强度如实登记**：`sourceOfAIC` / `sourceOfInfoGain`
的**唯一实质内容**是把「正性证明」从调用方**搬到提供者里**——
`SigmaSource.estimated` 要求 `0 < σ`，故提供者必须**先证**这个正的。
下面三条定理（`sourceOfAIC_*` 等）证明了这一点在他们各自的前提下**可做**，
即「破法乙/丙的输出确实够格当 `estimated`」。**这不是平凡的重言**：
若 `W.err γ = 0`（`profHinge` 在 `γ = ±1`），`sourceOfAIC` **无法构造**，
这条路径**必须**退回 `unknown` —— 见 `sourceOfAIC_zero_is_unknown_route`。 -/

/-- **破法丁的提供者**：外部领域参数 σ 直接映射为 `SigmaSource.domain`。 -/
def sourceOfDomain (σ : ℝ) (hpos : 0 < σ) : SigmaSource :=
  SigmaSource.domain σ hpos

/-- **破法乙的提供者**：AIC 路径的 σ（即 `sigmaAIC W γ = W.err γ`）
映射为 `SigmaSource.estimated`。

**要求**：`0 < W.err γ` —— 这正是 `estimated` 构造子的义务。
**⚠ 它在误差为 0 处不可构造**（见 `sourceOfAIC_zero_is_unknown_route`）。 -/
def sourceOfAIC (W : Core.ErrProfileWeak) (γ : ℝ) (hpos : 0 < W.err γ) : SigmaSource :=
  SigmaSource.estimated (SigmaFromAIC.sigmaAIC W γ) (by
    rw [SigmaFromAIC.sigmaAIC_eq_err]; exact hpos)

/-- **破法丙的提供者**：信息增益判据 σ 映射为 `SigmaSource.estimated`。

**要求**：`0 < sigmaCriterion f`。
**⚠ 若增益在 0 处取下确界（`sigmaCriterion_eq_zero` 的典型情形），
本提供者不可构造** —— 此时信息判据**不给出**正 σ，须退回 `unknown`。 -/
noncomputable def sourceOfInfoGain (f : ℝ → ℝ)
    (hpos : 0 < SigmaFromInfoGain.sigmaCriterion f) : SigmaSource :=
  SigmaSource.estimated (SigmaFromInfoGain.sigmaCriterion f) hpos

/-- **「未给」的提供者**：无 σ 信息时使用。 -/
def sourceOfUnknown : SigmaSource := SigmaSource.unknown

/-! ### §3.2  `resolveSigma` 对四个提供者的行为（⚠ 弱的如实标注） -/

/-- **破法丁：`domain` 分支原样返回**（`rfl` 级）。 -/
theorem resolveSigma_sourceOfDomain (σ : ℝ) (hpos : 0 < σ)
    (W : Core.ErrProfileWeak) (g0 : ℝ) :
    resolveSigma (sourceOfDomain σ hpos) W g0 = σ :=
  resolveSigma_domain σ hpos W g0

/-- **破法乙：`estimated` 分支原样返回 `W.err γ`，且与 `g0`、与所传剖面无关**
（`rfl` 级 —— 后者是「乙的结论进入统一接口后**逐字不变**」的形式载体）。 -/
theorem resolveSigma_sourceOfAIC (W : Core.ErrProfileWeak) (γ : ℝ) (hpos : 0 < W.err γ)
    (W' : Core.ErrProfileWeak) (g0 : ℝ) :
    resolveSigma (sourceOfAIC W γ hpos) W' g0 = W.err γ := by
  show SigmaFromAIC.sigmaAIC W γ = W.err γ
  exact SigmaFromAIC.sigmaAIC_eq_err W γ

/-- **破法丙：`estimated` 分支原样返回 `sigmaCriterion f`**（`rfl` 级）。 -/
theorem resolveSigma_sourceOfInfoGain (f : ℝ → ℝ)
    (hpos : 0 < SigmaFromInfoGain.sigmaCriterion f) (W : Core.ErrProfileWeak) (g0 : ℝ) :
    resolveSigma (sourceOfInfoGain f hpos) W g0 = SigmaFromInfoGain.sigmaCriterion f :=
  resolveSigma_estimated _ hpos W g0

/-- **未给：落到肘点兜底**（`rfl` 级）。 -/
theorem resolveSigma_sourceOfUnknown (W : Core.ErrProfileWeak) (g0 : ℝ) :
    resolveSigma sourceOfUnknown W g0 = W.err g0 :=
  resolveSigma_unknown W g0

/-- **统一契约：四个提供者的 `resolveSigma` 输出恒非负**。

**内容**：无论 σ 来自丁、乙、丙还是「未给」，经统一入口后
`0 ≤ resolveSigma src W g0` 都成立 —— 这是把「σ 非负」这条
`IsFitBoundary` 的健全性前提**在这个接口上一次付清**。

**⚠ 强度如实登记**：结论由 `SigmaFromDomain.resolveSigma_nonneg` 得出，
**不是新数学**。**这不是同义反复**（前件只声明 `src` 是四个提供者之一，
不含任何关于 `resolveSigma` 输出符号的假设），但内容确实很薄：
它只是把「接口契约」在四个提供者上**逐点检查一遍**。
它的**用途**是让 §5 的 Capstone 装配**免掉** `0 ≤ dσ` 这个假设。 -/
theorem resolveSigma_provider_nonneg (src : SigmaSource) (W : Core.ErrProfileWeak) (g0 : ℝ) :
    0 ≤ resolveSigma src W g0 :=
  resolveSigma_nonneg src W g0

/-- **破法乙在误差为 0 处**无法**给出 `estimated` 分支** ——
必须退回 `unknown`。**这是 §3.1 映射的负面见证**（映射不是全的）。

**内容**：存在剖面 `W`（取 `profHinge` 之外的 `profBiasOnly` 的对偶情形，
本定理用 `profBiasOnly` 在 `γ = 0`：`E(0) = 0`）与分辨率 `γ`，
使 `W.err γ = 0`，故 `0 < W.err γ` **不成立**，
`sourceOfAIC W γ ·` **不可构造**，只能走 `sourceOfUnknown`。

**⚠ 前件自查**：前件只有「`W := profBiasOnly`、`γ = 0`」——
**不含**结论（结论是「`¬ 0 < W.err γ`」与「必须用 `unknown`」）。
`¬ 0 < W.err γ` 由 `profBiasOnly` 的具体数值 `E(0) = 0` 算出，**非重言**。 -/
theorem sourceOfAIC_zero_is_unknown_route :
    ∃ (W : Core.ErrProfileWeak) (γ : ℝ), ¬ (0 < W.err γ) ∧
      resolveSigma (sourceOfUnknown) W γ = W.err γ := by
  refine ⟨Core.ErrProfile.profBiasOnly.toErrProfileWeak, 0, ?_,
    resolveSigma_unknown _ 0⟩
  show ¬ (0 < Core.ErrProfile.profBiasOnly.bias 0 + Core.ErrProfile.profBiasOnly.var 0)
  simp only [Core.ErrProfile.profBiasOnly]
  norm_num

/-! ===========================================================================
  §4  阶段 2：两条**上界型**结果的对齐
  =========================================================================== -/

/-! ### §4.0  两条结果的**形状**对照（这是「同」与「不同」的精确表述）

| | 破法乙 | 破法丙 |
|---|---|---|
| 定理 | `SigmaFromAIC.le_sigmaAIC_of_hasFitBoundary` | `SigmaFromInfoGain.sigmaCriterion_le` |
| 形状 | `σ_fit ≤ sigmaAIC W γ` | `sigmaCriterion f ≤ ε` |
| 左端（**被上界者**） | 边界 σ（自由参数） | 判据 σ（**下确界**） |
| 右端（**上界**） | `W.err γ`（**随 γ 变的函数值**） | `ε`（**外部阈值**） |
| 依赖的数据 | 误差剖面 `W` | 增益函数 `f`（**与 W 无关**） |
| 方向 | `≤` | `≤` |

**⟹ 相同之处**：两者都是「某个 σ 类对象 `≤` 某个上界」，**比较方向一致**。
**⟹ 不同之处**：右端一个是 `γ` 的函数值、一个是与 `γ` 无关的标量；
左端一个是自由参数、一个是 `sInf`。**它们不是同一命题的两种写法。**
**本节不为了凑定理而强行等同** —— 相反，§4.2 给出**分离定理**。 -/

/-- **对齐（收紧）**：在**边界点**上，`SigmaFromAIC` 的上界 `σ ≤ sigmaAIC W γ`
其实取到**等号**。

$$\mathrm{HasFitBoundary}\ W\ \sigma
  \;\Longrightarrow\; \mathrm{IsFitBoundary}\ W\ \sigma\ \gamma
  \;\Longrightarrow\; \sigma_{\mathrm{AIC}}(W,\gamma) = \sigma.$$

**为何有内容（非同义反复）**：
- 前件一 `HasFitBoundary W σ` 是**存在**命题（`∃ γ, IsFitBoundary W σ γ`）；
- 前件二 `IsFitBoundary W σ γ` 是**得到见证点 γ 之后**的第一分量
  `W.err γ = σ` 的**来源**；
- 结论是 `sigmaAIC W γ = σ`，其中 `sigmaAIC` 是**另一个模块**（`SigmaFromAIC`）
  定义的函数。
- 前件里**没有**出现 `sigmaAIC` 这个词，也没有出现 `W.err γ = σ`
  **以 sigmaAIC 形式**的陈述。必须用 `sigmaAIC_eq_err`（`SigmaFromAIC:461`）
  把跨模块的定义**桥**过来。
- **⚠ 但强度如实登记**：桥接是 `rfl` 级的，故本定理的数学深度**很低**；
  它的真实用途是把已入链的 `le_sigmaAIC_of_hasFitBoundary`
  从 `≤` **收紧到 `=`**，从而给出「两条上界在边界点重合」的**精确**陈述。 -/
theorem sigmaAIC_eq_of_isFitBoundary (W : Core.ErrProfileWeak) {σ γ : ℝ}
    (_h : Core.HasFitBoundary W σ) (hγ : Core.IsFitBoundary W σ γ) :
    SigmaFromAIC.sigmaAIC W γ = σ := by
  rw [SigmaFromAIC.sigmaAIC_eq_err]
  exact hγ.1

/-- **推论：乙的上界在边界点既 ≤ 又 =**（与 `SigmaFromAIC` 的原定理对照用）。

结论同时给出 `≤`（复用 `le_sigmaAIC_of_hasFitBoundary`）与 `=`（§4.1），
以证明**两条式子相容、方向一致**。 -/
theorem le_and_eq_sigmaAIC_at_boundary (W : Core.ErrProfileWeak) {σ γ : ℝ}
    (h : Core.HasFitBoundary W σ) (hγ : Core.IsFitBoundary W σ γ) :
    σ ≤ SigmaFromAIC.sigmaAIC W γ ∧ SigmaFromAIC.sigmaAIC W γ = σ :=
  ⟨SigmaFromAIC.le_sigmaAIC_of_hasFitBoundary W h γ,
    sigmaAIC_eq_of_isFitBoundary W h hγ⟩

/-- **分离定理**：**没有任何**增益函数 `f` 的判据 σ 能逐个 `γ`
等于某个**误差非常值**剖面的 `sigmaAIC`。

$$\exists W,\ \forall f,\ \neg\,\bigl(\forall \gamma,\
  \sigma_{\mathrm{crit}}(f) = \sigma_{\mathrm{AIC}}(W,\gamma)\bigr).$$

**为何这是本文件唯一的实质定理**：
- 它**不是**把某个已有定理换个说法：它断言的是「丙的 σ 与乙的 σ
  **在函数层面无法认同**」，这**排除了**一条可能的「廉价桥接」
  （即「把 `sigmaCriterion f` 定义为 `sigmaAIC W γ` 就好了」）。
- **证明是实质的**：要证**否定**命题，必须**用** `sigmaAIC W ·` 的
  **非常值性**反推矛盾。取 `W := profBiasOnly`（`E(γ) = max 0 γ`），
  `E(0) = 0` 而 `E(1) = 1`；若逐点相等，则
  `sigmaCriterion f = sigmaAIC W 0 = 0` 且 `= sigmaAIC W 1 = 1`，
  得 `0 = 1`，矛盾。
- **前件自查（纪律 7）**：本定理**没有前件**（是全称否定命题），
  故不可能「把结论包进前件」。结论 `¬ ∀ γ, …` 是**证出来的**。
- **⚠ 边界如实登记**：本定理**只**排除「点式恒等」这一种桥接；
  它**不**排除「存在某个 `Wof f` 使 `sigmaCriterion f = min_γ sigmaAIC (Wof f) γ`」
  这类**较弱**的桥接（那正是 `SigmaFromInfoGain.FitGainBridge` 要的样子，
  **本文件未构造、未证**）。**⟹ 这不是「循环已破」的证据，恰恰相反：
  它把「两条路径不能直接等同」钉死。** -/
theorem no_sigmaCriterion_eq_sigmaAIC_pointwise :
    ∃ W : Core.ErrProfileWeak,
      ∀ f : ℝ → ℝ,
        ¬ (∀ γ : ℝ, SigmaFromInfoGain.sigmaCriterion f = SigmaFromAIC.sigmaAIC W γ) := by
  refine ⟨Core.ErrProfile.profBiasOnly.toErrProfileWeak, fun f hpt => ?_⟩
  have h0 : Core.ErrProfile.profBiasOnly.toErrProfileWeak.err 0 = 0 := by
    show Core.ErrProfile.profBiasOnly.bias 0 + Core.ErrProfile.profBiasOnly.var 0 = 0
    simp only [Core.ErrProfile.profBiasOnly]
    norm_num
  have h1 : Core.ErrProfile.profBiasOnly.toErrProfileWeak.err 1 = 1 := by
    show Core.ErrProfile.profBiasOnly.bias 1 + Core.ErrProfile.profBiasOnly.var 1 = 1
    simp only [Core.ErrProfile.profBiasOnly]
    norm_num
  have e0 := hpt 0
  have e1 := hpt 1
  rw [SigmaFromAIC.sigmaAIC_eq_err, h0] at e0
  rw [SigmaFromAIC.sigmaAIC_eq_err, h1] at e1
  linarith

/-! ===========================================================================
  §5  阶段 3：让下游消费 —— σ 提供者接进 `WorldModelCapstone`
  =========================================================================== -/

/-! ### §5.0  Capstone 的 σ 位在哪（先 grep 定位，实测结果如实抄录）

    $ grep -n "dσ" FateV2.Error/WorldModelCapstone.lean
    307:     把 `d` 放宽为 `2 L ηmax + dσ`（`dσ ≥ 0` 任取的 σ 预算）**不改变**上界的
    319:    (hP : ...) {η L ηmax dσ : ℝ}
    320:    (hL : 0 < L) (hηmax : 0 ≤ ηmax) (hdσ : 0 ≤ dσ)
    ...

**定位结论**：Capstone 的 σ 参数位就是
`FateV2.Loop.WorldModelCapstone.endToEnd_steady_bound_estimated` 的
**自由实数参数 `dσ`**（`:319`），它以**假设 `hdσ : 0 ≤ dσ`**（`:320`）
的形式被要求非负，并被用作漂移预算 `d = 2 L ηmax + dσ`。

**⚠ 该文件是已入链模块，本次**不改**它（纪律 2）。
故采用审计给出的**备用方案**：「在 `SigmaUnified` 里定义一个新的 σ 提供者，
并证明它与 Capstone 现有 σ 用法相容」——
相容性的体现是下面的 `capstone_sigmaFromData`：它**引用** Capstone 的
`endToEnd_steady_bound_estimated`，把 `dσ` **替换成**
`resolveSigma src W g0`，从而

  (i) `dσ` **不再是自由参数**（由 `src` + `W` + `g0` 决定）；
  (ii) `hdσ : 0 ≤ dσ` 这个假设**被删掉** —— 由 `resolveSigma_nonneg` **证出**。

**这是本阶段真正交付的东西**：Capstone 那条定理的 σ 侧假设从
「调用方必须提供 `0 ≤ dσ`」变成「σ 由统一提供者给出，非负自动成立」。 -/

/-- **阶段 3 主定理：`Capstone` 的 σ 位由 `resolveSigma` 供给**。

**结论**：

$$\mathrm{limsup}_m \|A\,\theta_m - x'_m\| \;\le\;
  \mathrm{steadyErr}\ \eta\ \bigl(2L\eta_{\max} + \mathrm{resolveSigma}(\mathrm{src}, W, g_0)\bigr)
  \;\wedge\; 0 \le \mathrm{resolveSigma}(\mathrm{src}, W, g_0).$$

**引用**：`FateV2.Loop.WorldModelCapstone.endToEnd_steady_bound_estimated` 的第一分量
（`FateV2.Error/WorldModelCapstone.lean:319`）+ `FateV2.Error.SigmaFromDomain.resolveSigma_nonneg`
（`FateV2.Error/SigmaFromDomain.lean:246`）。

**为何不是同义反复（纪律 7 逐条）**：
- 前件中**不出现** `resolveSigma`，也不出现任何关于
  `steadyErr η (2 L ηmax + ·)` 上界的陈述，更**不出现** `0 ≤ dσ`
  （那一条被**删掉**了，正是本定理的改进点）。
- 前件只有：`hP`（二阶矩有限）、`hL`（`0 < L`）、`hηmax`（`0 ≤ ηmax`）、
  `hη`（步长）、`n`/`hn`（样本数）、`A φ θ` 与 `h`（写回修正）、
  `hLI`（Lipschitz 可逆）、`x x' δ` 与 `hx' hδ`（观测模型）、
  以及 `hstep`（**关于 `resolveSigma` 的漂移界** —— 这是唯一出现
  `resolveSigma` 的前件，它是**输入数据**，不是结论）。
- 结论的两个分量（`limsup` 的数值上界、`resolveSigma` 非负）
  在 Capstone 的对应定理里**分别**是结论与**假设**；本定理把后者
  **降级**为结论，这是**加强**（前件更弱）。

**⚠ 诚实登记**：本定理**不**给出任何新的数值估计 —— `dσ` 换成
`resolveSigma src W g0` 之后，界的形式**逐字不变**（`steadyErr η (2Lηmax + ·)`）。
它的价值是**接口**：σ 从此有**唯一出处**，且出处可以是破法乙/丙/丁中的任一条。 -/
theorem capstone_sigmaFromData
    {P : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure P]
    {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hP : MeasureTheory.MemLp (fun x : ℝ => x) 2 P)
    {η L ηmax : ℝ} (hL : 0 < L) (hηmax : 0 ≤ ηmax)
    (hη : |1 - η| < 1) (n : ℕ) (hn : 0 < n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (δ : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + δ k) (hδ : ∀ k, ‖δ k‖ ≤ ηmax)
    (src : SigmaSource) (W : Core.ErrProfileWeak) (g0 : ℝ)
    (hstep : ∀ k : ℕ, ‖x' k - x' (k + 1)‖
      ≤ 2 * L * ηmax + resolveSigma src W g0) :
    limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax + resolveSigma src W g0)
      ∧ 0 ≤ resolveSigma src W g0 := by
  refine ⟨?_, resolveSigma_nonneg src W g0⟩
  exact (WorldModelCapstone.endToEnd_steady_bound_estimated hP hL hηmax
    (resolveSigma_nonneg src W g0) hη n hn A φ θ h hLI x x' δ hx' hδ hstep).1

/-- **实例化：σ 来自破法丁（领域参数）时的 Capstone 界**。

把 `src := sourceOfDomain σ hσ` 代入 §5.1，得到 σ **逐字就是**外部给定的 σ —
即 Capstone 的 σ 位可以**完全由领域知识决定**，而非从数据估。 -/
theorem capstone_sigmaFromDomain
    {P : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure P]
    {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hP : MeasureTheory.MemLp (fun x : ℝ => x) 2 P)
    {η L ηmax : ℝ} (hL : 0 < L) (hηmax : 0 ≤ ηmax)
    (hη : |1 - η| < 1) (n : ℕ) (hn : 0 < n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (δ : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + δ k) (hδ : ∀ k, ‖δ k‖ ≤ ηmax)
    (σ : ℝ) (hσ : 0 < σ) (W : Core.ErrProfileWeak) (g0 : ℝ)
    (hstep : ∀ k : ℕ, ‖x' k - x' (k + 1)‖ ≤ 2 * L * ηmax + σ) :
    limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax + σ)
      ∧ 0 < σ := by
  have hstep' : ∀ k : ℕ, ‖x' k - x' (k + 1)‖
      ≤ 2 * L * ηmax + resolveSigma (sourceOfDomain σ hσ) W g0 := by
    intro k
    rw [resolveSigma_sourceOfDomain]
    exact hstep k
  obtain ⟨h1, _⟩ := capstone_sigmaFromData hP hL hηmax hη n hn A φ θ h hLI
    x x' δ hx' hδ (sourceOfDomain σ hσ) W g0 hstep'
  refine ⟨?_, hσ⟩
  rwa [resolveSigma_sourceOfDomain] at h1

/-- **实例化：σ 来自破法乙（AIC）时的 Capstone 界**。

σ 位被填成 `SigmaFromAIC.sigmaAIC W γ = W.err γ`（并要求它在 `γ` 处为正），
从而 **AIC 路径的 σ 第一次被下游真的用上**（改进了审计指出的 fanin = 0）。 -/
theorem capstone_sigmaFromAIC
    {P : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure P]
    {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hP : MeasureTheory.MemLp (fun x : ℝ => x) 2 P)
    {η L ηmax : ℝ} (hL : 0 < L) (hηmax : 0 ≤ ηmax)
    (hη : |1 - η| < 1) (n : ℕ) (hn : 0 < n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (δ : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + δ k) (hδ : ∀ k, ‖δ k‖ ≤ ηmax)
    (W : Core.ErrProfileWeak) (γ : ℝ) (hpos : 0 < W.err γ) (W' : Core.ErrProfileWeak)
    (g0 : ℝ)
    (hstep : ∀ k : ℕ, ‖x' k - x' (k + 1)‖ ≤ 2 * L * ηmax + W.err γ) :
    limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax + W.err γ)
      ∧ 0 < W.err γ := by
  have hstep' : ∀ k : ℕ, ‖x' k - x' (k + 1)‖
      ≤ 2 * L * ηmax + resolveSigma (sourceOfAIC W γ hpos) W' g0 := by
    intro k
    rw [resolveSigma_sourceOfAIC]
    exact hstep k
  obtain ⟨h1, _⟩ := capstone_sigmaFromData hP hL hηmax hη n hn A φ θ h hLI
    x x' δ hx' hδ (sourceOfAIC W γ hpos) W' g0 hstep'
  refine ⟨?_, hpos⟩
  rwa [resolveSigma_sourceOfAIC] at h1

/-- **实例化：σ 来自破法丙（信息增益）时的 Capstone 界**。

σ 位被填成 `SigmaFromInfoGain.sigmaCriterion f`。**⚠ 这是三条里最弱的一环**：
`f` 与 Capstone 的误差剖面**没有任何已证的联系**（`FitGainBridge` 未实例化），
故本定理的 `hstep` 实际上**必须由调用方独立提供** —— 它**不**从 `f` 推出。
本定理的用途**仅**是证明「接口接得上」，**不是**「信息判据给出了 Capstone 的界」。 -/
theorem capstone_sigmaFromInfoGain
    {P : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure P]
    {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hP : MeasureTheory.MemLp (fun x : ℝ => x) 2 P)
    {η L ηmax : ℝ} (hL : 0 < L) (hηmax : 0 ≤ ηmax)
    (hη : |1 - η| < 1) (n : ℕ) (hn : 0 < n)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (δ : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + δ k) (hδ : ∀ k, ‖δ k‖ ≤ ηmax)
    (g : ℝ → ℝ) (hg : 0 < SigmaFromInfoGain.sigmaCriterion g) (W : Core.ErrProfileWeak)
    (g0 : ℝ)
    (hstep : ∀ k : ℕ, ‖x' k - x' (k + 1)‖
      ≤ 2 * L * ηmax + SigmaFromInfoGain.sigmaCriterion g) :
    limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax + SigmaFromInfoGain.sigmaCriterion g)
      ∧ 0 < SigmaFromInfoGain.sigmaCriterion g := by
  have hstep' : ∀ k : ℕ, ‖x' k - x' (k + 1)‖
      ≤ 2 * L * ηmax + resolveSigma (sourceOfInfoGain g hg) W g0 := by
    intro k
    rw [resolveSigma_sourceOfInfoGain]
    exact hstep k
  obtain ⟨h1, _⟩ := capstone_sigmaFromData hP hL hηmax hη n hn A φ θ h hLI
    x x' δ hx' hδ (sourceOfInfoGain g hg) W g0 hstep'
  refine ⟨?_, hg⟩
  rwa [resolveSigma_sourceOfInfoGain] at h1

/-! ===========================================================================
  §6  ⚠ 本文件**未**做到的事（与 §一/§二 呼应，防止误读）
  =========================================================================== -/

/-!
**⚠ 逐条登记（不要把这些当成已做）**

1. **循环未破。** 本文件的任何定理都**不**给出「σ 可由数据无循环地定出」。
   §5 的三条 Capstone 实例化都**保留**了 `hstep`（漂移界）作为前件 ——
   即「σ 的数值」仍然**由调用方提供**（`hstep` 里出现 `W.err γ` /
   `sigmaCriterion g` / 外部 `σ`），**不是**由本文件从数据反推的。

2. **破法丙的桥接 `FitGainBridge` 仍未实例化。** `capstone_sigmaFromInfoGain`
   的 `hstep` **不**从 `g` 推出任何东西；本文件**不**声称信息判据给出了
   Capstone 的数值界。

3. **`sigmaCriterion` 与 `sigmaAIC` 的**不可**点式等同**已由
   `no_sigmaCriterion_eq_sigmaAIC_pointwise` **证否**（这是一个**否定**结果）。
   故「三条路径统一成一个数」在本文件里**没有**发生；
   发生的只是「三类来源统一成一个**类型**」`SigmaSource`。

4. **未修改 `FateV2.Error/WorldModelCapstone.lean`。** §5 是**外部消费**，
   不是**改动**。Capstone 的自由参数 `dσ` 在其原文件中**依然自由**；
   本文件只证明它可以被**填**。

**⟹ 诚实结论：本文件把三条路径的**接口**收成一条（`SigmaSource` + `resolveSigma`），
并让 `WorldModelCapstone` 真的消费了它（fanin 0 → ≥1）。
它**没有**把三条路径的**数学**收成一条。**
-/

end SigmaUnified

end FateV2.Error

/-! ===========================================================================
  §7  公理检查（`#print axioms`）—— 确认零 `sorry` / 零 `axiom`
  =========================================================================== -/

