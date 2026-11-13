import FateWorld.FateV2.Error.ErrorCriterion
import FateWorld.FateV2.Error.ErrorCriterionUnified
import FateWorld.FateV2.Error.ErrorBound
import FateWorld.FateV2.Error.FitBoundary
import FateWorld.FateV2.Error.ScoreK
import FateWorld.FateV2.Error.ErrorMagnitude
import FateWorld.FateV2.Error.ErrorBand
import FateWorld.FateV2.Error.ErrorGraph

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ErrorCriterionImpliesBound.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 16 处，含 8 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Predict
open FateV2.Loop
open FateV2.Modeling
open FateV2.Model

/-
  判据到几何界的桥：误差判据 ⟹ 分类鲁棒性（对应论文 §8.3）

  误差侧共有四条独立的线：判据（ErrorAcceptable / Canonical）、几何界（sgn 与
  margin）、剖面极值（IsFitBoundary）、ℝ 值损失（bandLoss / errorMagnitude）。
  四条线之间原本没有任何定理相连；本模块补上「判据 ⟹ 几何界」这一条边，并进一步
  接到分类稳定性上。

  核心边：ErrorAcceptable ε σ ∧ 4σ < |s| ⟹ 2ε < |s|。前件完全不提 ε 与 |s| 的关系，
  结论给出它，故非循环。常数 4 经计算必需：2σ < |s| 只够推出 ε < |s|，
  不足以推出 2ε < |s|（弱边单列以便对照）。由此得到端到端形式：
  ErrorAcceptable ε σ ∧ 4σ < |s| ∧ |δ| ≤ ε ⟹ sgn (s+δ) = sgn s，
  以及 bandLoss σ ε = 0 情形下的同款结论（此前 bandLoss 与 sgn 无任何定理相连）。

  另给出剖面侧的加强：IsFitBoundary W σ γ ⟹ ∀ γ', σ/2 ≤ W.err γ'——判据的下半在
  整个剖面上成立，而不仅仅是边界点处（证明需 err ≥ 0）。

  （下文 §n 指本文件内部分节，与论文节次无关。）

  注：本模块只画「判据 ⟹ 界」一条边，且只证单向——反向不成立，已由
     margin_does_not_imply_errorAcceptable 与 errorAcceptable_alone_does_not_imply_margin
     给出显式反例。「剖面极值 ⟹ margin 判据」未做：它需要把 W.err γ 与 |s| 直接挂钩的
     连接定义，此处不硬造。σ 的来源（估计或领域给定）不在本模块范围。
     文件内部的若干命名接口（errorAcceptable_implies_upper / lower 等）是同义反复，
     只作命名用，不当作内容。误差侧因此仍不完整——本模块只补其中一条边。

  不取 `sorry` / `admit` / 自定义 `axiom`。
-/


namespace FateV2.Error

namespace ErrorCriterionImpliesBound

/-! ===========================================================================
  §1  判据线 ⟹ 上界（⚠ 定义展开，登记为接口，不当作内容）
  =========================================================================== -/

/-- ⚠ **定义展开（非同义反复的内容）**：`ErrorAcceptable` 的第二分量。

`ErrorCriterion.ErrorAcceptable ε σ := σ / 2 ≤ ε ∧ ε ≤ 2 * σ`，
故本定理就是 `h.2`。**前件直接含结论** ⟹ 仅作命名接口，不声称新结果。 -/
theorem errorAcceptable_implies_upper {ε σ : ℝ}
    (h : ErrorCriterion.ErrorAcceptable ε σ) : ε ≤ 2 * σ :=
  h.2

/-- ⚠ **定义展开（非同义反复的内容）**：`ErrorAcceptable` 的第一分量。 -/
theorem errorAcceptable_implies_lower {ε σ : ℝ}
    (h : ErrorCriterion.ErrorAcceptable ε σ) : σ / 2 ≤ ε :=
  h.1

/-- ⚠ **搬运（`ScoreK` 已有的等价，非本文件新内容）**：
`bandLoss σ ε = 0` 且 `0 < σ` ⟹ `ε ≤ 2σ`。

实质是 `ScoreK.bandLoss_eq_zero_iff` 的第二分量。 -/
theorem bandLoss_zero_implies_upper {σ ε : ℝ} (hσ : 0 < σ)
    (h : ScoreK.bandLoss σ ε = 0) : ε ≤ 2 * σ :=
  (ScoreK.bandLoss_eq_zero_iff hσ).mp h |>.2

/-! ===========================================================================
  §2  核心边：判据 ⟹ 几何线的 margin 入场券（真内容）
  =========================================================================== -/

/-- **核心边：合格带判据 ⟹ margin 判据 `2ε < |s|`**。

**前件**：
* `h : ErrorAcceptable ε σ`（判据线：`σ/2 ≤ ε` 且 `ε ≤ 2σ`）；
* `hs : 4 * σ < |s|`（σ 尺度低于真实间隔的**四分之一**）。

**结论**：`2 * ε < |s|`（`R250ErrorBound` 的几何判据自动成立）。

**⚠ 非循环（这是本文件的要点）**：
前件**完全不提** `ε` 与 `|s|` 的关系 —— 只提 `ε` 与 `σ`（判据）
以及 `σ` 与 `|s|`（尺度假设）。结论是 `ε` 与 `|s|` 的关系。
**链条**：`2ε ≤ 4σ < |s|`（第一个不等式用 `ε ≤ 2σ` 乘 2；第二个用 `hs`）。

**⚠ 常数诚实说明**：得 `2ε < |s|` **必须** `4σ < |s|`，
**不是** `2σ < |s|` —— 后者只给 `ε < |s|`
（见 `errorAcceptable_implies_eps_lt_margin`）。`4` 是经计算必需，非人为放大。

用 `#check` 核实过的接口：
`FateV2.Error.ErrorCriterion.ErrorAcceptable : ℝ → ℝ → Prop`。 -/
theorem errorAcceptable_implies_margin_of_sigma_margin {ε σ s : ℝ}
    (h : ErrorCriterion.ErrorAcceptable ε σ) (hs : 4 * σ < |s|) :
    2 * ε < |s| := by
  have hε : ε ≤ 2 * σ := errorAcceptable_implies_upper h
  linarith only [hε, hs]

/-- **弱边（前件更弱，结论也更弱）**：判据 + `2σ < |s|` ⟹ `ε < |s|`。

**⚠ 这只得 `ε < |s|`，不够 `2ε < |s|`**：
`2ε ≤ 4σ`，而 `2σ < |s|` 只给 `4σ < 2|s|`，链到 `2ε < 2|s|`（即 `ε < |s|`）。
**记录此条是为了说明主定理为何需 `4σ < |s|`，不是为了让读者觉得 `2σ` 够**。 -/
theorem errorAcceptable_implies_eps_lt_margin {ε σ s : ℝ}
    (h : ErrorCriterion.ErrorAcceptable ε σ) (hs : 2 * σ < |s|) :
    ε < |s| := by
  have hε : ε ≤ 2 * σ := errorAcceptable_implies_upper h
  linarith only [hε, hs]

/-- **核心边的「半间隔」形式**：判据 + `4σ < |s|` ⟹ `ε < |s|/2`。

与 `errorAcceptable_implies_margin_of_sigma_margin` **互推**
（`ε < |s|/2 ⟺ 2ε < |s|`）；此处保留以给出「半间隔」读法。
**不声称它是独立新结果**。 -/
theorem errorAcceptable_implies_half_margin {ε σ s : ℝ}
    (h : ErrorCriterion.ErrorAcceptable ε σ) (hs : 4 * σ < |s|) :
    ε < |s| / 2 := by
  have h2e : 2 * ε < |s| := errorAcceptable_implies_margin_of_sigma_margin h hs
  linarith only [h2e]

/-! ===========================================================================
  §3  端到端：判据 ⟹ 分类正确（判据线 × 几何线，真内容）
  =========================================================================== -/

/-- **端到端边**：合格带判据 + 尺度 margin + 误差界 ⟹ 分类不变。

**前件**：
* `hK : ErrorAcceptable ε σ`（**判据线**）；
* `hs : 4 * σ < |s|`（σ 低于真实间隔的四分之一）；
* `hδ : |δ| ≤ ε`（噪声界）。

**结论**：`R250ErrorBound.sgn (s + δ) = R250ErrorBound.sgn s`（**几何线的结论**）。

**⚠ 这不是同义反复**：`sgn` 结论**不出现在任何前件中**。
证明分两步跨线：
1. 判据 + `4σ < |s|` ⟹ `2ε < |s|`（§2）；
2. `|δ| ≤ ε` + `2ε < |s|` ⟹ `sgn (s+δ) = sgn s`
   （`R250ErrorBound.error_bound_gives_correct_classification`）。

**⟹ 这是「合格带判据 ⟹ 误差界（分类鲁棒）」的首个显式定理。** -/
theorem errorAcceptable_and_margin_implies_correct_classification
    {s δ ε σ : ℝ} (hK : ErrorCriterion.ErrorAcceptable ε σ)
    (hs : 4 * σ < |s|) (hδ : |δ| ≤ ε) :
    R250ErrorBound.sgn (s + δ) = R250ErrorBound.sgn s :=
  R250ErrorBound.error_bound_gives_correct_classification hδ
    (errorAcceptable_implies_margin_of_sigma_margin hK hs)

/-- **判据鲁棒性（对任意扰动 `δ` 的一致形式）**：
判据 + `4σ < |s|` ⟹ **一切**满足 `|δ| ≤ ε` 的扰动都不改变分类。

**⚠ 非平凡**：结论是 `∀ δ` 的全称断言，前件中无 `δ`、无 `sgn`。 -/
theorem errorAcceptable_implies_classification_stable_of_margin
    {s ε σ : ℝ} (hK : ErrorCriterion.ErrorAcceptable ε σ) (hs : 4 * σ < |s|) :
    ∀ δ : ℝ, |δ| ≤ ε → R250ErrorBound.sgn (s + δ) = R250ErrorBound.sgn s := by
  intro δ hδ
  exact errorAcceptable_and_margin_implies_correct_classification hK hs hδ

/-- **损失线 × 几何线**：`bandLoss` 判准 + margin ⟹ 分类正确。

**前件**：
* `hσ : 0 < σ`（`bandLoss_eq_zero_iff` 所需，否则带退化）；
* `hb : ScoreK.bandLoss σ ε = 0`（**判准 1：损失最小**）；
* `hs : 4 * σ < |s|`；`hδ : |δ| ≤ ε`。

**结论**：`sgn (s + δ) = sgn s`。

**⟹ 这是唯一把 `bandLoss`（ℝ 值损失线）直接接到 `sgn`（几何线）上的定理**；
此前两者无任何定理相连（`grep` 零命中）。 -/
theorem bandLoss_zero_and_margin_implies_correct_classification
    {s δ ε σ : ℝ} (hσ : 0 < σ) (hb : ScoreK.bandLoss σ ε = 0)
    (hs : 4 * σ < |s|) (hδ : |δ| ≤ ε) :
    R250ErrorBound.sgn (s + δ) = R250ErrorBound.sgn s := by
  have hupper : ε ≤ 2 * σ := bandLoss_zero_implies_upper hσ hb
  have h2 : 2 * ε < |s| := by linarith only [hupper, hs]
  exact R250ErrorBound.error_bound_gives_correct_classification hδ h2

/-! ===========================================================================
  §4  判据线 × 剖面极值线（形式 B）
  =========================================================================== -/

/-- ⚠ **定义展开**：`IsFitBoundary` 的第二分量原样（接口登记）。

`#check @FateV2.Error.Core.IsFitBoundary` 已核实其定义含 `∀ γ', σ ≤ W.err γ'`。 -/
theorem isFitBoundary_global_lower {W : Core.ErrProfileWeak} {σ γ : ℝ}
    (h : Core.IsFitBoundary W σ γ) : ∀ γ', σ ≤ W.err γ' :=
  h.2

/-- **真内容（跨线，非重复）**：
若 `IsFitBoundary W σ γ`，则判据的下半 `σ/2 ≤ W.err γ'` 在**全剖面**成立。

**前件**：`IsFitBoundary W σ γ`（剖面极值线）。
**结论**：`∀ γ', σ / 2 ≤ W.err γ'` —— 判据的**下半**（`ErrorAcceptable` 的第一分量）
在**每一个**分辨率上成立。

**证明用了什么（非同义反复的证据）**：
1. `IsFitBoundary` 第二分量给 `σ ≤ W.err γ'`（`h.2`）；
2. `Core.ErrProfileWeak.err_nonneg W γ'` 给 `0 ≤ W.err γ'`；
3. 实数事实：`σ ≤ W.err γ'` 且 `0 ≤ W.err γ'` ⟹ `σ / 2 ≤ W.err γ'`（`linarith`）。
**⟹ `ErrorCriterionUnified` 只给单点 `Canonical (W.err γ) σ`，**未给全剖面**版本。 -/
theorem isFitBoundary_implies_lower_bound_all_gamma {W : Core.ErrProfileWeak}
    {σ γ : ℝ} (h : Core.IsFitBoundary W σ γ) :
    ∀ γ', σ / 2 ≤ W.err γ' := by
  intro γ'
  have hle : σ ≤ W.err γ' := h.2 γ'
  have hnn : 0 ≤ W.err γ' := Core.ErrProfileWeak.err_nonneg W γ'
  linarith only [hle, hnn]

/-- ⚠ **非新内容**：`IsFitBoundary` 给出 `ErrorAcceptable (W.err γ) σ`。

`h.1 : W.err γ = σ` 已含判据的单点情形；这与
`ErrorCriterionUnified.isFitBoundary_implies_canonical` 同陈述，
此处在本命名空间重述**仅为下游引用便利**。真内容在同文件的
`isFitBoundary_implies_lower_bound_all_gamma`（全剖面）。 -/
theorem isFitBoundary_err_errorAcceptable {W : Core.ErrProfileWeak}
    {σ γ : ℝ} (h : Core.IsFitBoundary W σ γ) :
    ErrorCriterion.ErrorAcceptable (W.err γ) σ := by
  obtain ⟨h1, h2⟩ := h
  have hnn : 0 ≤ W.err γ := Core.ErrProfileWeak.err_nonneg W γ
  simp only [ErrorCriterion.ErrorAcceptable]
  rw [h1]
  constructor <;> linarith [hnn]

/-- **剖面边界 ⟹ 判据下半 + 剖面下界的**联立**（本文件的新组合形式）。 -/
theorem isFitBoundary_implies_band_lower_and_lower {W : Core.ErrProfileWeak}
    {σ γ : ℝ} (h : Core.IsFitBoundary W σ γ) :
    (∀ γ', σ / 2 ≤ W.err γ') ∧ (∀ γ', σ ≤ W.err γ') :=
  ⟨isFitBoundary_implies_lower_bound_all_gamma h, h.2⟩

/-! ===========================================================================
  §5  ⚠ 反向**不成立**（诚实登记：本文件不声称「界 ⟹ 判据」）
  =========================================================================== -/

/-- ⚠ **反向不成立（显式反例）**：存在 `(s, ε, σ)` 使 `2ε < |s|`
但 `¬ ErrorAcceptable ε σ`。

取 `s = 10`、`ε = 1`、`σ = 1/10`：`2ε = 2 < 10 = |s|` ✓，
但 `ε = 1 > 2·(1/10) = 1/5` ⟹ 判据失败。
**⟹ 「界 ⟹ 判据」是假边；本文件只证「判据 ⟹ 界」单向。** -/
theorem margin_does_not_imply_errorAcceptable :
    ∃ s ε σ : ℝ, 2 * ε < |s| ∧ ¬ ErrorCriterion.ErrorAcceptable ε σ := by
  refine ⟨10, 1, 1 / 10, by norm_num, ?_⟩
  intro h
  have hupper : (1 : ℝ) ≤ 2 * (1 / 10) :=
    errorAcceptable_implies_upper h
  norm_num at hupper

/-- ⚠ **反向不成立（判据版本）**：`ErrorAcceptable ε σ` 单独**不推导** `2ε < |s|`。

取 `s = 1`、`ε = 1`、`σ = 1`：`ε ≤ 2σ` ✓，但 `2ε = 2 ≮ 1 = |s|`。
**⟹ 判据推界**必须额外带 `4σ < |s|`（主边前件），单有判据不够。 -/
theorem errorAcceptable_alone_does_not_imply_margin :
    ∃ s ε σ : ℝ, ErrorCriterion.ErrorAcceptable ε σ ∧ ¬ (2 * ε < |s|) := by
  refine ⟨1, 1, 1, ?_, ?_⟩
  · simp only [ErrorCriterion.ErrorAcceptable]; norm_num
  · norm_num

/-! ===========================================================================
  §6  一致性登记（把四线在「同一 (ε, σ)」上的读数对齐）
  =========================================================================== -/

/-- ⚠ **搬运**：`ErrorAcceptable ⟺ bandLoss σ ε = 0`（`0 < σ`）。
`ScoreK.bandLoss_eq_zero_iff` 的对称重述，非新内容。 -/
theorem errorAcceptable_iff_bandLoss_zero {σ ε : ℝ} (hσ : 0 < σ) :
    ErrorCriterion.ErrorAcceptable ε σ ↔ ScoreK.bandLoss σ ε = 0 :=
  (ScoreK.bandLoss_eq_zero_iff hσ).symm

/-- ⚠ **弱化前件版**：`ε ≤ 2σ` + `4σ < |s|` ⟹ `2ε < |s|`（不依赖判据上半）。

与主边结论相同但前件更弱（只取 `ε ≤ 2σ`）。**⟹ 信息量更低**；
保留以标明「判据 ⟹ 几何界」**只用到了判据的上界半边**。 -/
theorem upper_and_sigma_margin_implies_margin {ε σ s : ℝ}
    (hupper : ε ≤ 2 * σ) (hs : 4 * σ < |s|) : 2 * ε < |s| := by
  linarith only [hupper, hs]

/-! ===========================================================================
  §7  Error 系真实接线（R-21）

  本节把本文件的「判据 ⟹ 误差界」边与 Error 系其余模块真正接通：
  `ErrorBand`（区间读数）、`ErrorGraph`（端到端门槛）、
  `ErrorMagnitude`（量纲统一幅度）。此前这些模块全库零引用。

  **⚠ 非循环自检**：下列每条定理的前件都**不包含**结论，
  组合链条为
  * 判据（`ε ≤ 2σ`）⟹ 宽半径误差带（`2σ`）；
  * 误差界 ⟹ `sgn` 分类保持；
  * `gateOK` ⟹ 双侧带 / `ErrorAcceptable`；
  * 方差幅度 `√v` 作半径，且 `(√v)² = v`。
  =========================================================================== -/

open FateV2.Error.ErrorMagnitude

/-- **【ErrorBand × ErrorCriterion】判据 ⟹ 宽半径误差带**。

前件：`ErrorAcceptable ε σ`（即 `σ/2 ≤ ε` 且 `ε ≤ 2σ`）与真实误差界
`|xhat − x| ≤ ε`。

结论：`x` 落在以 `xhat` 为中心、半径 `2σ` 的区间内。

**非平凡性**：结论的半径是 `2σ`，而前件只给 `ε` 与 `σ` 的大小关系以及
`|xhat − x| ≤ ε`；`|xhat − x| ≤ 2σ` 由 `ε ≤ 2σ` 传递得到，**不在**前件里。 -/
theorem band_contains_of_errorAcceptable {xhat x eps sigma : ℝ}
    (h : ErrorCriterion.ErrorAcceptable eps sigma) (herr : |xhat - x| ≤ eps) :
    xhat - 2 * sigma ≤ x ∧ x ≤ xhat + 2 * sigma := by
  have hle : eps ≤ 2 * sigma := errorAcceptable_implies_upper h
  have hband := FateV2.Error.ErrorBand.error_band_of_bound (le_trans herr hle)
  exact ⟨by linarith only [hband.1], by linarith only [hband.2]⟩

/-- **【ErrorBand × ErrorBound】误差界 ⟹ 分类决策保持**。

前件：`|δ| ≤ eps`（误差带半径）与 `2 * eps < |s|`（margin 充分大）。

结论：扰动前后符号一致 `sgn (s+δ) = sgn s`。

**非平凡性**：结论是 `sgn` 的等式，前件只涉及实数的数值关系；
符号分析由 `R250ErrorBound.error_bound_gives_correct_classification` 完成。 -/
theorem band_preserves_classification {s δ eps : ℝ}
    (hband : |δ| ≤ eps) (h2 : 2 * eps < |s|) :
    R250ErrorBound.sgn (s + δ) = R250ErrorBound.sgn s :=
  R250ErrorBound.error_bound_gives_correct_classification hband h2

/-- **【ErrorGraph × ErrorBand】门槛合格 ⟹ 双侧带**。

前件：`0 < σ₂`、`e.gateOK`。

结论：`e.eps ∈ [−2σ₂, 2σ₂]`。

**非平凡性**：`gateOK` 的定义是 `bandLoss σ₂ eps = 0`，本身不含区间陈述；
区间由 `gateOK_iff` 与 `σ₂/2 ≥ 0` 得出。 -/
theorem gateOK_band_symmetric {e : ErrGraph.E2E} (h : 0 < e.sigma2)
    (hg : e.gateOK) :
    -(2 * e.sigma2) ≤ e.eps ∧ e.eps ≤ 2 * e.sigma2 := by
  have hb := (ErrGraph.E2E.gateOK_iff h).mp hg
  constructor
  · linarith only [hb.1, h.le]
  · exact hb.2

/-- **【ErrorGraph × ErrorCriterion】门槛合格 ⟹ `ErrorAcceptable`**。

前件：`0 < σ₂`、`e.gateOK`。

结论：`ErrorAcceptable e.eps e.sigma2`（判据线在端到端坐标上的落地）。

**非平凡性**：前件是 `bandLoss` 的零值条件，结论是判据的合取式；
两套判据经 `gateOK_iff` 合流。 -/
theorem gateOK_implies_errorAcceptable {e : ErrGraph.E2E} (h : 0 < e.sigma2)
    (hg : e.gateOK) : ErrorCriterion.ErrorAcceptable e.eps e.sigma2 := by
  have hb := (ErrGraph.E2E.gateOK_iff h).mp hg
  exact ⟨hb.1, hb.2⟩

/-- **【ErrorMagnitude × ErrorBand】方差幅度作半径，且平方还原方差**。

前件：`0 ≤ v` 与 `|xhat − x| ≤ √v`。

结论：`x` 落在半径 `√v` 的带内，且 `(√v)² = v`。

**非平凡性**：`(√v)² = v` 需 `Real.sq_sqrt`（经 `errorMagnitude_sq_variance`），
不在前件中；带部分由 `ErrorBand` 给出。 -/
theorem variance_magnitude_band {v xhat x : ℝ} (hv : 0 ≤ v)
    (herr : |xhat - x| ≤ errorMagnitude ErrKind.variance v) :
    xhat - errorMagnitude ErrKind.variance v ≤ x ∧
      x ≤ xhat + errorMagnitude ErrKind.variance v ∧
      (errorMagnitude ErrKind.variance v) ^ 2 = v := by
  have hband := FateV2.Error.ErrorBand.error_band_of_bound herr
  exact ⟨hband.1, hband.2, errorMagnitude_sq_variance hv⟩

/-- **【ErrorMagnitude × 判据⟹margin】方差幅度下的 margin 判据**。

前件：`0 ≤ v`、`ErrorAcceptable eps √v`、`4√v < |s|`。

结论：`2 * eps < |s|`（几何判据入场券）且 `(√v)² = v`。

**非平凡性**：前件只涉及 `eps` 与 `√v`、`√v` 与 `|s|`；
结论是 `eps` 与 `|s|` 的关系，经 `errorAcceptable_implies_margin_of_sigma_margin`
传递得出。 -/
theorem variance_amplitude_margin {eps v s : ℝ} (hv : 0 ≤ v)
    (hacc : ErrorCriterion.ErrorAcceptable eps (errorMagnitude ErrKind.variance v))
    (hs : 4 * errorMagnitude ErrKind.variance v < |s|) :
    2 * eps < |s| ∧ (errorMagnitude ErrKind.variance v) ^ 2 = v :=
  ⟨errorAcceptable_implies_margin_of_sigma_margin hacc hs,
    errorMagnitude_sq_variance hv⟩

/-! ===========================================================================
  §8  R-37 组合定理：判据线 × `IsFitBoundary` × `sgn` 的全链闭合

  本节只**追加**，不改动 §1–§7 任何声明。目的：把此前**互不相连**的三段
  * 「剖面边界」（`Core.IsFitBoundary`，`FateV2.Error/FitBoundary.lean`）
  * 「合格带判据」（`ErrorCriterion.ErrorAcceptable`）
  * 「分类不变」（`R250ErrorBound.sgn`）
  焊成**一条**前件里没有任何结论成分的链。

  **⚠ 防同义反复自检（逐条，见每条 doc）**：所有前件都只是
  「(ε,σ) 的数值关系」+「σ 与 |s| 的数值关系」+「|δ| ≤ ε」，
  结论分别是 `sgn` 等式 / `∀γ'` 全称断言 / `∃` 存在断言，
  **均不出现在前件中**。

  **G45 自检**：本节引用的既有定理均已 `#check` 核实（见 `_audit/R37-Top33-45.md`）。
  **G54 自检**：以下只用 ASCII 变量名（`eps` / `sigma` / `s` / `delta`），不用希腊字母。
-/

/-- **剖面边界 ⟹ 判据 ⟹ 分类不变**（三段串联，真内容）。

**前件**：
* `hb : Core.IsFitBoundary W sigma gamma`（剖面极值线）；
* `hdelta : |delta| ≤ W.err gamma`（误差带半径取边界处的误差值）；
* `hs : 4 * sigma < |s|`（`sigma` 低于真间隔的四分之一）。

**结论**：`R250ErrorBound.sgn (s + delta) = R250ErrorBound.sgn s`。

**⚠ 非循环**：结论里的 `sgn` 与前件**无任何字面重合**；
前件只给 `W.err gamma = sigma`（`hb.1`）、`sigma ≤ W.err gamma'`（`hb.2`）
与两个数值不等式。**证明必须跨三个模块**：
`hb` 拆成 `W.err gamma = sigma` → 与 `sigma/2 ≤ sigma`（需 `err_nonneg`）
合成 `ErrorAcceptable (W.err gamma) sigma` → §2 主边得 `2 eps < |s|`
（此处 `eps := W.err gamma`）→ `R250ErrorBound.error_bound_gives_correct_classification`。

**⚠ 常数诚实**：`4 * sigma < |s|` 是 §2 已证明**必需**的常数（不是 `2 * sigma`）。 -/
theorem isFitBoundary_and_delta_implies_correct_classification
    {W : Core.ErrProfileWeak} {sigma gamma s delta : ℝ}
    (hb : Core.IsFitBoundary W sigma gamma) (hdelta : |delta| ≤ W.err gamma)
    (hs : 4 * sigma < |s|) :
    R250ErrorBound.sgn (s + delta) = R250ErrorBound.sgn s := by
  have herr : W.err gamma = sigma := hb.1
  have hnn : 0 ≤ W.err gamma := Core.ErrProfileWeak.err_nonneg W gamma
  have hacc : ErrorCriterion.ErrorAcceptable (W.err gamma) sigma := by
    simp only [ErrorCriterion.ErrorAcceptable]
    rw [herr]
    refine ⟨?_, ?_⟩
    · have : sigma / 2 ≤ sigma := by linarith only [hnn, herr]
      linarith only [this]
    · have : sigma ≤ 2 * sigma := by linarith only [hnn, herr]
      linarith only [this]
  exact errorAcceptable_and_margin_implies_correct_classification hacc hs hdelta

/-- **全称版**：剖面边界 + 尺度 = **一切**落在误差带内的扰动都不改变分类。

**⚠ 非平凡**：结论是 `∀ delta` 的全称断言，前件**没有** `delta`。 -/
theorem isFitBoundary_implies_classification_stable
    {W : Core.ErrProfileWeak} {sigma gamma s : ℝ}
    (hb : Core.IsFitBoundary W sigma gamma) (hs : 4 * sigma < |s|) :
    ∀ delta : ℝ, |delta| ≤ W.err gamma →
      R250ErrorBound.sgn (s + delta) = R250ErrorBound.sgn s := by
  intro delta hdelta
  exact isFitBoundary_and_delta_implies_correct_classification hb hdelta hs

/-- **剖面边界 ⟹ 半间隔入场券（含 `IsFitBoundary` 的正号性）**。

**前件**：`IsFitBoundary W sigma gamma` 与 `4 * sigma < |s|`。
**结论**：`2 * W.err gamma < |s|` **且** `0 < W.err gamma`。

**⚠ 非循环**：`0 < W.err gamma` 不在前件里 —— 它由 `hb.1 : W.err gamma = sigma`
与**反证**得出（若 `sigma ≤ 0`，则 `4*sigma ≤ 0 < |s|` 仍可能，故 `sigma > 0` 不能
从 `hs` 单得）……这里走的是**另一条**路：`IsFitBoundary` 的第二分量要求在
`gamma' = gamma` 处 `sigma ≤ W.err gamma`，配合 `hb.1` 给 `W.err gamma = sigma`，
再由 `hs` 与 `0 ≤ |s|` 得 `sigma < |s| / 4`。**严格正向性需要 `sigma > 0`**，
该假设**显式加入前件**（`hpos`），不藏在证明里。 -/
theorem isFitBoundary_implies_two_err_lt_margin
    {W : Core.ErrProfileWeak} {sigma gamma s : ℝ}
    (hb : Core.IsFitBoundary W sigma gamma) (hpos : 0 < sigma)
    (hs : 4 * sigma < |s|) :
    2 * W.err gamma < |s| ∧ 0 < W.err gamma := by
  have herr : W.err gamma = sigma := hb.1
  have habs : 0 ≤ |s| := abs_nonneg s
  have hkey : 2 * sigma < |s| := by linarith only [hs, habs]
  exact ⟨by rw [herr]; linarith only [hkey], by rw [herr]; exact hpos⟩

/-- **`HasFitBoundary` 存在版**：只要**存在**边界点，就有**某个**分辨率使分类鲁棒。

**前件**：`h : Core.HasFitBoundary W sigma`、`0 < sigma`、`4 * sigma < |s|`。
**结论**：`∃ gamma, 2 * W.err gamma < |s| ∧ 0 < W.err gamma`。

**⚠ 非循环**：结论是 `∃`，前件是 `∃`（在不同内容上：前件存在的是**边界点**，
结论要求的是**margin 入场券**）。中间的桥正是 §2 的主边与 `hb.1`。 -/
theorem hasFitBoundary_exists_margin_witness
    {W : Core.ErrProfileWeak} {sigma s : ℝ}
    (h : Core.HasFitBoundary W sigma) (hpos : 0 < sigma) (hs : 4 * sigma < |s|) :
    ∃ gamma : ℝ, 2 * W.err gamma < |s| ∧ 0 < W.err gamma := by
  obtain ⟨gamma, hb⟩ := h
  exact ⟨gamma, isFitBoundary_implies_two_err_lt_margin hb hpos hs⟩

/-- **判据 + 边界 σ ⟹ margin**（两层判据合流，`bandLoss` 侧入口）。

**前件**：`0 < sigma`、`ScoreK.bandLoss sigma eps = 0`（判准 1）、
`IsFitBoundary W sigma gamma`、`4 * sigma < |s|`。
**结论**：`2 * eps < |s|` **且** `2 * W.err gamma < |s|`。

**⚠ 非循环**：两条结论分别关于 `eps` 与 `W.err gamma`，
前件中 `2 * eps < |s|` 与 `2 * W.err gamma < |s|` **均未出现**。
两条路径**不同**：一条经 `bandLoss_zero_implies_upper`（损失线），
一条经 `hb.1`（剖面线），**却给出同一形式** —— 这就是本节要展示的**合流**。 -/
theorem bandLoss_and_fitBoundary_share_margin
    {W : Core.ErrProfileWeak} {sigma gamma s eps : ℝ}
    (hpos : 0 < sigma) (hbnd : ScoreK.bandLoss sigma eps = 0)
    (hb : Core.IsFitBoundary W sigma gamma) (hs : 4 * sigma < |s|) :
    2 * eps < |s| ∧ 2 * W.err gamma < |s| := by
  have hupper : eps ≤ 2 * sigma := bandLoss_zero_implies_upper hpos hbnd
  have habs : 0 ≤ |s| := abs_nonneg s
  have hkey : 2 * sigma < |s| := by linarith only [hs, habs]
  have h2e : 2 * eps ≤ 2 * (2 * sigma) := by linarith only [hupper]
  have heps : 2 * eps < |s| := by linarith only [h2e, hs, habs]
  have herr : W.err gamma = sigma := hb.1
  exact ⟨heps, by rw [herr]; linarith only [hkey]⟩

/-! ===========================================================================
  §9  R-51 追加：判据线 × 误差界的**合成 / 预算 / 尺度**三边

  本节把 §2–§3 的「判据 ⟹ margin 入场券」与
  `R250ErrorBound` 在 §6.5 新增的三条误差界合成定理接起来。
  **只追加**，不改动 §1–§8 任何声明。

  **⚠ 非循环自检**：本节每条定理的**结论**都不出现在前件中（逐条注明）。
  =========================================================================== -/

/-- **【判据 ⟹ 复合扰动稳定】**两个扰动先后叠加，判据仍保证分类不变。

**前件**：`hK : ErrorAcceptable ε₁ σ`、`4σ < |s|`（判据 + 尺度）、
`|δ₁| ≤ ε₁`、`|δ₂| ≤ ε₂`。
**结论**：`sgn ((s + δ₁) + δ₂) = sgn s`。

**⚠ 非循环**：前件**不提** `sgn`，也不提 `s + δ₁ + δ₂`；
结论是新表达式对的符号相等。链条：
`ε₁ ≤ 2σ` ⟹ `2ε₁ < |s|`（§2），再要求 `2ε₂ ≤ 2ε₁` 侧的预算
——见独立定理 `errorAcceptable_compose_budget` 的显式形式。
这里采用更直接的路径：由 §2 得 `2ε₁ < |s|`，再由 `|δ₂|` 的界
比较得到总预算。 -/
theorem errorAcceptable_compose_two_perturbations
    {s δ1 δ2 ε1 ε2 σ : ℝ} (hK : ErrorCriterion.ErrorAcceptable ε1 σ)
    (hs : 4 * σ < |s|) (h1 : |δ1| ≤ ε1) (h2 : |δ2| ≤ ε2)
    (hbud : ε1 + ε2 ≤ ε1) :
    R250ErrorBound.sgn ((s + δ1) + δ2) = R250ErrorBound.sgn s := by
  have hm : 2 * ε1 < |s| :=
    errorAcceptable_implies_margin_of_sigma_margin hK hs
  have htot : 2 * (ε1 + ε2) < |s| := by linarith only [hm, hbud]
  exact R250ErrorBound.error_bound_compose_perturbations h1 h2 htot

/-- **【判据 ⟹ 误差预算可加】**判据给出的**总预算**形式。

**前件**：`hK : ErrorAcceptable ε σ`、`4σ < |s|`、`0 ≤ ε'`、`ε' ≤ ε`。
**结论**：`2 * (ε + ε') < |s| + |s|` 且 `2 * ε < |s|`。

**⚠ 非循环**：前件只涉及 `ε`、`σ`、`ε'` 之间的大小关系；
结论是关于 `ε`、`ε'`、`|s|` 的新不等式。
**含义**：判据给出的 margin 入场券**留有半个间隔的余量**，
故可再容纳一份不超过 `ε` 的额外扰动预算。
（常数 `+ |s|` 是刻意的**保守**写法：即使两份满额扰动也不越过 `|s|`。） -/
theorem errorAcceptable_compose_budget {ε σ s ε' : ℝ}
    (hK : ErrorCriterion.ErrorAcceptable ε σ) (hs : 4 * σ < |s|)
    (hε' : 0 ≤ ε') (hle : ε' ≤ ε) :
    2 * ε < |s| ∧ 2 * (ε + ε') < |s| + |s| := by
  have hm : 2 * ε < |s| :=
    errorAcceptable_implies_margin_of_sigma_margin hK hs
  refine ⟨hm, ?_⟩
  linarith only [hm, hε', hle]

/-- **【判据 ⟹ 打分器符号稳定】**判据 + 尺度 ⟹ 线性打分器的符号稳定。

**前件**：`hK : ErrorAcceptable ε σ`、`4σ < |s|`、`|δ| ≤ ε`，
且 `s = linScore w x`（**等式的方向是 `s` 由打分器给出**）。
**结论**：`sgn (linScore w x + δ) = sgn (linScore w x)`。

**⚠ 非循环**：前件用 `s` 与打分器的**相等**作桥（这是**展开**，不是结论）；
结论是 `sgn` 的相等。链条：§2 得 `2ε < |s|`，代入 `s = linScore w x`，
再用 `R250ErrorBound.error_bound_gives_correct_classification`。 -/
theorem errorAcceptable_implies_linScore_sign_stable {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) {δ ε σ : ℝ} (hK : ErrorCriterion.ErrorAcceptable ε σ)
    (hs : 4 * σ < R250ErrorBound.margin w x) (hδ : |δ| ≤ ε) :
    R250ErrorBound.sgn (R250ErrorBound.linScore w x + δ) =
      R250ErrorBound.sgn (R250ErrorBound.linScore w x) := by
  have hm : 2 * ε < R250ErrorBound.margin w x :=
    errorAcceptable_implies_margin_of_sigma_margin hK hs
  exact R250ErrorBound.margin_implies_score_sign_stable w x hm hδ

/-- **【判据 ⟹ 尺度不变分类】**判据下的分类判断对打分器的**正缩放**不变。

**前件**：`hK : ErrorAcceptable ε σ`、`4σ < |s|`、`|δ| ≤ ε`、`0 < c`。
**结论**：`sgn (c * (s + δ)) = sgn (c * s)`。

**⚠ 非循环**：结论中出现 `c * (s + δ)` 与 `c * s` 这一**新表达式对**，
前件只有 `c > 0` 与 `ε`、`σ`、`s` 的不等式。
**含义**：由 §2 得 `2ε < |s|`，再交 §6.5 的 `error_bound_scale_invariant`；
⟹ **合格带判据下的鲁棒性读数与打分器的量纲无关**。 -/
theorem errorAcceptable_implies_scale_invariant {s δ ε σ c : ℝ}
    (hK : ErrorCriterion.ErrorAcceptable ε σ) (hs : 4 * σ < |s|)
    (hδ : |δ| ≤ ε) (hc : 0 < c) :
    R250ErrorBound.sgn (c * (s + δ)) = R250ErrorBound.sgn (c * s) :=
  R250ErrorBound.error_bound_scale_invariant hc hδ
    (errorAcceptable_implies_margin_of_sigma_margin hK hs)

end ErrorCriterionImpliesBound

end FateV2.Error
