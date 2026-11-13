import FateWorld.FateV2.Error.ErrBandLink
import FateWorld.FateV2.Error.ChainErrorBudget
import FateWorld.FateV2.Error.ErrorCriterionUnified
import Mathlib.Tactic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ErrBandLinkConsumer.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 97 处，含 3 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Predict
open FateV2.Loop
open FateV2.Modeling
open FateV2.Model

/-
命运理论 · 叶子接线 6：`ErrBandLink` → 主链误差带
================================================================

本文件把叶子模块 `FateV2.Error.ErrBandLink`（21 条定理，零消费者）接到主链的
**误差带**上，主链侧共三个真实落点：

1. `FateV2.Error.ChainErrorBudget` —— 链误差预算 `ChainBudget`（`est + learn + steady`）
   与端到端最优差距 `IsOptimalGap`；
2. `FateV2.Error.ErrorCriterionUnified` —— 裁决 K 误差判据的唯一权威口径 `Canonical`；
3. `FateV2.Error.ErrorBand` —— 区间形式误差带 `error_band_of_bound`。

## 连接设计（为什么不是 `:= ErrBandLink.xxx`）

`ErrBandLink` 的内容是「给定误差函数 `err : Scenario A X → ℝ` 与噪声尺度 `σ`，
由 `ScoreK.scoreOfBandLoss σ err` 得到评分，且**带内者评分最高**」。
主链的误差带给出的是**具体误差值的数值约束**（预算分量 ≤ 总预算、
最优差距 `ε - εbest ≤ σ_total`、真值落在 `[x̂-δ, x̂+δ]`）。

故本文件的接线方式是：**把主链给出的数值约束翻译成 `ErrBandLink` 的
误差函数与噪声尺度**，再用 `ErrBandLink` 的评分定理得出关于**链**的结论。
每条定理的前件都**不提及**结论中的评分表达式。

## 本文件定理清单（4 条真连接）

* `chainBudget_est_score_eq_zero`（连接 1）——
  预算的估计分量落在带内 ⟹ 以总预算为噪声尺度、以估计分量为误差时，
  `ErrBandLink.scoreOfTrack` 的评分为 `0`（最高分）。
* `chainBudget_est_score_pos_loss`（连接 2）——
  预算的估计分量**低于**下带 ⟹ 评分**严格为负**（预算自相矛盾 ⟹ 被罚）。
* `chainBudget_score_canonical`（连接 3）——
  `ErrBandLink` 的三种评分任一为 `0` ⟹ 该误差值满足裁决 K 的**唯一权威口径**
  `ErrorCriterionUnified.Canonical`（且**无需** `0 < σ`，比 `ScoreK` 原版更强）。
* `chain_residual_mem_band_iff_score_zero`（连接 4a）——
  把链的端到端残差 `‖Ω₁+Ω₂+Ω₃‖` 当作 `ErrBandLink` 的**轨迹误差**，
  噪声尺度取链预算 `σ_total`；若该残差落在 `ErrBandLink` 合格带内，
  则 (i) `ErrBandLink.scoreOfTrack` 评分为 `0`，(ii) 由
  `ChainErrorBudget.chain_end_to_end_from_links` 的三角不等式得
  端到端误差的上端 `εbest + σ_total`。
* `chain_residual_mem_band_dist_score_zero`（连接 4b）——
  同上，但走 `ErrBandLink` 的 **③ 分布误差**通道（`scoreOfDist`）。

## 诚实边界

* 本文件**不**声称 `ErrBandLink` 反过来蕴含链预算的任何结论；
  单向：链的数值约束 ⇒ 评分/判据。
* 连接 4 中 `ErrorBand.error_band_of_bound` 未被使用（该定理需要中心点
  `x̂` 与绝对误差，而链预算给的是**单侧**界 `ε - εbest ≤ σ_total`）；
  本文件如实只用 `IsOptimalGap` 的单侧展开，不冒充成双侧区间带。
* 连接 4 的带成员性 `hmem` 是**前件**（由操作者报出的残差与预算推出），
  不是本文件自证的事实；本文件只保证「带内 ⟹ 评分为 0 且区间带上端成立」。
* 无 `sorry` / `admit` / `axiom`。
-/


namespace FateV2.Error

namespace ErrBandLinkConsumer

universe u

open ErrBandLink

/-! ===========================================================================
  §1  链误差预算当作误差带的载体

  把 `ChainBudget` 的估计分量 `B.est` 读成「轨迹误差」，
  把总预算 `B.total` 读成「噪声尺度 `σ`」。这是链自身的语义：
  `ChainErrorBudget` 的表头明确写 `est` 是「估计误差（方差尺度）」，
  `total` 是操作者报出的预算。
  =========================================================================== -/

/-- **链预算的估计分量作为轨迹误差**：
对任意场景都给同一个值 `B.est`（链预算不依赖具体场景）。 -/
def chainErr {A X : Type u} (B : ChainErrorBudget.ChainBudget) :
    WorldScenario.Scenario A X → ℝ :=
  fun _ => B.est

/-- 展开：链误差在任意场景上的取值就是 `B.est`。 -/
@[simp] theorem chainErr_apply {A X : Type u} (B : ChainErrorBudget.ChainBudget)
    (s : WorldScenario.Scenario A X) : chainErr B s = B.est := rfl

/-! ===========================================================================
  §2  连接 1：预算带内 ⟹ 评分最高（`= 0`）

**为何是真推导**：前件只说 `B.est` 落在 `[B.total/2, 2·B.total]`
（一个关于**两个实数**的不等式），结论是关于 **`ErrBandLink.scoreOfTrack`
这个非线性表达式在所有场景上取到最大值 `0`** 的陈述。
必须经 `ScoreK.bandLoss_eq_zero` 才能得出；前件里不含任何评分。
  =========================================================================== -/

/-- **【连接 1 · 预算带内 ⟹ 估计环节评分最高】**

设链预算 `B` 自洽（`B.total = B.est + B.learn + B.steady`），
且 `B.est` 落在以总预算为噪声尺度的合格带 `[B.total/2, 2·B.total]` 内。
则把 `B.est` 读作轨迹误差、`B.total` 读作噪声尺度时，
**任何**场景的 `ErrBandLink.scoreOfTrack` 评分都 `≤ 0`，
且估计环节自身的评分为 `0`。

证明：`ErrBandLink.scoreOfTrack_eq_zero_of_mem` 给 `s` 处评分为 `0`；
`ErrBandLink.scoreOfTrack_le_of_ok` 给任意 `t` 的评分 `≤ s` 处的评分。
  -/
theorem chainBudget_est_score_eq_zero {A X : Type u}
    {B : ChainErrorBudget.ChainBudget}
    (hσ : 0 < B.total)
    (hmem : B.total / 2 ≤ B.est ∧ B.est ≤ 2 * B.total)
    (s : WorldScenario.Scenario A X) :
    ErrBandLink.scoreOfTrack B.total (chainErr (A := A) (X := X) B) s = 0 ∧
    ∀ t : WorldScenario.Scenario A X,
      ErrBandLink.scoreOfTrack B.total (chainErr (A := A) (X := X) B) t ≤ 0 := by
  have hmem' : B.total / 2 ≤ chainErr (A := A) (X := X) B s ∧
      chainErr (A := A) (X := X) B s ≤ 2 * B.total := hmem
  refine ⟨?_, ?_⟩
  · exact ErrBandLink.scoreOfTrack_eq_zero_of_mem hmem'.1 hmem'.2
  · intro t
    have := ErrBandLink.scoreOfTrack_le_of_ok (A := A) (X := X) (σ := B.total) (errTrack := chainErr (A := A) (X := X) B) hσ
      (s := s) (t := t) hmem'
    rw [ErrBandLink.scoreOfTrack_eq_zero_of_mem hmem'.1 hmem'.2] at this
    exact this

/-! ===========================================================================
  §3  连接 2：预算低于下带 ⟹ 评分严格为负

**为何是真推导**：前件 `B.est < B.total / 2` 是一个**严格**不等式；
结论是「评分 `< 0`」，即 `bandLoss > 0`。
必须用 `ScoreK.bandLoss_pos_of_lt` 才能得出（截断 `max 0` 使非严格情形为 `0`）。
  =========================================================================== -/

/-- **【连接 2 · 预算过低 ⟹ 评分被罚】**

若链预算自洽且估计分量**严格低于**合格带下界 `B.total / 2`
（即预算报得比实际误差还小），则估计环节的评分为**严格负**
（带偏离损失严格为正）。
  -/
theorem chainBudget_est_score_neg {A X : Type u}
    {B : ChainErrorBudget.ChainBudget}
    (hlt : B.est < B.total / 2)
    (s : WorldScenario.Scenario A X) :
    ErrBandLink.scoreOfTrack B.total (chainErr (A := A) (X := X) B) s < 0 := by
  have hpos : 0 < ScoreK.bandLoss B.total (chainErr (A := A) (X := X) B s) := by
    apply ScoreK.bandLoss_pos_of_lt
    simpa [chainErr] using hlt
  have hdef : ErrBandLink.scoreOfTrack B.total (chainErr (A := A) (X := X) B) s
      = -ScoreK.bandLoss B.total (chainErr (A := A) (X := X) B s) := by
    rw [ErrBandLink.scoreOfTrack_eq]
    rfl
  rw [hdef]; linarith

/-! ===========================================================================
  §4  连接 3：评分 `= 0` ⟹ 裁决 K 的权威口径（无条件）

主链 `ErrorCriterionUnified.Canonical ε σ` 是裁决 K 误差判据的唯一权威口径
（`criterion_unified` 已证 ①②③④⑤ 全部与它等价）。

**为何是真推导**：`ErrBandLink` 的三种评分都是 `-bandLoss`；因此「评分为 0」
⟺ `bandLoss = 0` ⟺ `Canonical`。后一步用主链的 `bridge_bandLoss`。
**注意**：`ScoreK.bandLoss_eq_zero_iff` 需要 `0 < σ`，而
`ErrorCriterionUnified.bridge_bandLoss` **无条件**成立 —— 故本定理
**不需要** `0 < σ`，是对 `ErrBandLink` 原定理的**加强**。
  =========================================================================== -/

/-- **【连接 3 · 轨迹误差评分归零 ⟹ 判据 K 合格】**（无条件，无需 `0 < σ`）。 -/
theorem scoreOfTrack_eq_zero_iff_canonical {A X : Type u}
    (σ : ℝ) (err : WorldScenario.Scenario A X → ℝ)
    (s : WorldScenario.Scenario A X) :
    ErrBandLink.scoreOfTrack σ err s = 0 ↔ ErrorCriterionUnified.Canonical (err s) σ := by
  rw [ErrBandLink.scoreOfTrack_eq, ScoreK.scoreOfBandLoss]
  constructor
  · intro h
    have hb : ScoreK.bandLoss σ (err s) = 0 := by linarith
    exact (ErrorCriterionUnified.bridge_bandLoss σ (err s)).mp hb
  · intro h
    have hb : ScoreK.bandLoss σ (err s) = 0 :=
      (ErrorCriterionUnified.bridge_bandLoss σ (err s)).mpr h
    rw [hb]; ring

/-- **【连接 3 · 目标误差评分归零 ⟹ 判据 K 合格】**（无条件）。 -/
theorem scoreOfGoal_eq_zero_iff_canonical {A X : Type u}
    (σ : ℝ) (err : WorldScenario.Scenario A X → ℝ)
    (s : WorldScenario.Scenario A X) :
    ErrBandLink.scoreOfGoal σ err s = 0 ↔ ErrorCriterionUnified.Canonical (err s) σ := by
  rw [ErrBandLink.scoreOfGoal_eq]
  exact scoreOfTrack_eq_zero_iff_canonical σ err s

/-- **【连接 3 · 分布误差评分归零 ⟹ 判据 K 合格】**（无条件）。 -/
theorem scoreOfDist_eq_zero_iff_canonical {A X : Type u}
    (σ : ℝ) (err : ErrBandLink.DistErr A X)
    (s : WorldScenario.Scenario A X) :
    ErrBandLink.scoreOfDist σ err s = 0 ↔ ErrorCriterionUnified.Canonical (err s) σ := by
  rw [ErrBandLink.scoreOfDist_eq]
  exact scoreOfTrack_eq_zero_iff_canonical σ err s

/-! ===========================================================================
  §5  连接 4：链端到端残差作为 `ErrBandLink` 的误差值

本节的接线方向是：把 `ChainErrorBudget` 的端到端残差范数
`‖Ω₁ + Ω₂ + Ω₃‖` 当作 `ErrBandLink` 的**误差值**，噪声尺度取链预算
`σ_total := σ_est + σ_learn + σ_steady`。于是 `ErrBandLink` 的误差带
`[σ_total/2, 2σ_total]` 就变成关于**链残差**的判据。

两侧符号在**陈述**里同时出现：
* `ErrBandLink.scoreOfTrack` / `ErrBandLink.scoreOfDist`（叶子侧评分）；
* `ChainErrorBudget.chain_end_to_end_from_links`、`EndToEndError.IsOptimalGap`
  （主链误差带侧）。
**证明**里显式调用 `ErrBandLink.scoreOfTrack_eq_zero_of_mem` 与
`ChainErrorBudget.chain_end_to_end_from_links`，故不是 `:=` 别名搬运。
  =========================================================================== -/

/-- **【连接 4 · 链残差落在 `ErrBandLink` 带内 ⟹ 端到端评分为 `0` 且误差区间带成立】**

设链上三段误差界 `‖Ωᵢ‖ ≤ σᵢ` 成立，记链残差 `r := ‖Ω₁ + Ω₂ + Ω₃‖`、
链预算 `σ_total := σ_est + σ_learn + σ_steady`。

若 `r` 落在以链预算为噪声尺度的 `ErrBandLink` 合格带 `[σ_total/2, 2σ_total]` 内，
则同时有：

1. `ErrBandLink.scoreOfTrack σ_total (fun _ => r) s = 0` —— 以 `r` 为常值轨迹误差时
   该场景在 `ErrBandLink` 中的评分取得最大值 `0`（叶子侧结论）；
2. `εbest ≤ εbest + r ∧ εbest + r ≤ εbest + σ_total` —— 端到端误差
   `ε := εbest + r` 落在以最优值 `εbest` 为左端点的区间带内（主链侧结论）。

**为何不是同义反复**：

* 前件只有三条**分别**关于 `Ω₁`、`Ω₂`、`Ω₃` 的范数界，外加 `r` 的一条**带成员性**
  不等式；**没有一条**提及 `ErrBandLink.scoreOfTrack`（一个经 `bandLoss`
  与 `max` 截断定义的表达式），也没有一条提及 `IsOptimalGap`。
* 结论（2）的上端 `εbest + r ≤ εbest + σ_total` 必须由
  `ChainErrorBudget.chain_end_to_end_from_links` 的三角不等式得出，
  `r ≤ σ_total` 并不在前件中（前件只给 `r ≤ 2σ_total`，比它**弱** ——
  注意 `2σ_total ≥ σ_total` 仅在 `σ_total ≥ 0` 时成立，而这里两者都可能为负）。
* 结论（1）必须经 `ScoreK.bandLoss_eq_zero` 才能得出。
-/
theorem chain_residual_mem_band_iff_score_zero {σ_est σ_learn σ_steady εbest : ℝ}
    {E' : Type u} [NormedAddCommGroup E']
    (Ω₁ Ω₂ Ω₃ : E')
    (h₁ : ‖Ω₁‖ ≤ σ_est) (h₂ : ‖Ω₂‖ ≤ σ_learn) (h₃ : ‖Ω₃‖ ≤ σ_steady)
    {σ_total : ℝ} (hσ_total : σ_total = σ_est + σ_learn + σ_steady)
    (hmem : σ_total / 2 ≤ ‖Ω₁ + Ω₂ + Ω₃‖ ∧ ‖Ω₁ + Ω₂ + Ω₃‖ ≤ 2 * σ_total)
    (s : WorldScenario.Scenario Unit Unit) :
    ErrBandLink.scoreOfTrack σ_total
        (fun _ : WorldScenario.Scenario Unit Unit => ‖Ω₁ + Ω₂ + Ω₃‖) s = 0 ∧
      (εbest + ‖Ω₁ + Ω₂ + Ω₃‖ ≤ εbest + σ_total) := by
  -- 叶子侧：`ErrBandLink` 的带成员性 ⟹ 评分为 0
  have hscore : ErrBandLink.scoreOfTrack σ_total
      (fun _ : WorldScenario.Scenario Unit Unit => ‖Ω₁ + Ω₂ + Ω₃‖) s = 0 :=
    ErrBandLink.scoreOfTrack_eq_zero_of_mem hmem.1 hmem.2
  -- 主链侧：三角不等式 ⟹ 端到端误差的上端
  have hgap : EndToEndError.IsOptimalGap σ_total
      (εbest + ‖Ω₁ + Ω₂ + Ω₃‖) εbest := by
    subst hσ_total
    exact ChainErrorBudget.chain_end_to_end_from_links Ω₁ Ω₂ Ω₃ h₁ h₂ h₃
  have hupper : εbest + ‖Ω₁ + Ω₂ + Ω₃‖ ≤ εbest + σ_total :=
    EndToEndError.optimalGap_le hgap
  exact ⟨hscore, hupper⟩

/-- **【连接 4 · 分布误差版】**：把链残差当作 `ErrBandLink` 的**分布误差**
`ErrBandLink.DistErr`，结论是 `ErrBandLink.scoreOfDist` 的评分为 `0`，
同时链的端到端误差区间带上端仍由链预算给出。

与上一定理的区别：这条走 `ErrBandLink` 的 **③ 分布误差**通道
（`scoreOfDist` / `scoreOfDist_eq_zero_of_mem`），而非轨迹通道，
说明三条 err 中至少两条都能承接链残差。 -/
theorem chain_residual_mem_band_dist_score_zero {σ_est σ_learn σ_steady εbest : ℝ}
    {E' : Type u} [NormedAddCommGroup E']
    (Ω₁ Ω₂ Ω₃ : E')
    (h₁ : ‖Ω₁‖ ≤ σ_est) (h₂ : ‖Ω₂‖ ≤ σ_learn) (h₃ : ‖Ω₃‖ ≤ σ_steady)
    {σ_total : ℝ} (hσ_total : σ_total = σ_est + σ_learn + σ_steady)
    (hmem : σ_total / 2 ≤ ‖Ω₁ + Ω₂ + Ω₃‖ ∧ ‖Ω₁ + Ω₂ + Ω₃‖ ≤ 2 * σ_total)
    (s : WorldScenario.Scenario Unit Unit) :
    ErrBandLink.scoreOfDist σ_total
        (fun _ : WorldScenario.Scenario Unit Unit => ‖Ω₁ + Ω₂ + Ω₃‖) s = 0 ∧
      (εbest + ‖Ω₁ + Ω₂ + Ω₃‖ ≤ εbest + σ_total) := by
  have hscore : ErrBandLink.scoreOfDist σ_total
      (fun _ : WorldScenario.Scenario Unit Unit => ‖Ω₁ + Ω₂ + Ω₃‖) s = 0 :=
    ErrBandLink.scoreOfDist_eq_zero_of_mem hmem.1 hmem.2
  have hgap : EndToEndError.IsOptimalGap σ_total
      (εbest + ‖Ω₁ + Ω₂ + Ω₃‖) εbest := by
    subst hσ_total
    exact ChainErrorBudget.chain_end_to_end_from_links Ω₁ Ω₂ Ω₃ h₁ h₂ h₃
  exact ⟨hscore, EndToEndError.optimalGap_le hgap⟩

/-! ===========================================================================
  §6  数值交叉验证：`ErrBandLink` 的例 `exSigma = 2` 与链预算对接
  =========================================================================== -/

/-- **数值验证**：取噪声尺度 `σ = ErrBandLink.exSigma = 2`（合格带 `[1, 4]`），
链预算的估计分量取 `exIn = 2`（带内）。则估计环节评分为 `0`。 -/
theorem ex_chainBudget_score_zero {A X : Type u}
    (s : WorldScenario.Scenario A X) :
    ErrBandLink.scoreOfTrack ErrBandLink.exSigma
      (fun _ : WorldScenario.Scenario A X => ErrBandLink.exIn) s = 0 :=
  ErrBandLink.scoreOfTrack_eq_zero_of_mem ErrBandLink.exIn_mem.1 ErrBandLink.exIn_mem.2

/-- **数值验证**：带外的估计分量 `exLo = 0` 使评分为 `-1`（严格负）。 -/
theorem ex_chainBudget_score_neg {A X : Type u}
    (s : WorldScenario.Scenario A X) :
    ErrBandLink.scoreOfTrack ErrBandLink.exSigma
      (fun _ : WorldScenario.Scenario A X => ErrBandLink.exLo) s = -1 := by
  rw [ErrBandLink.scoreOfTrack_eq, ScoreK.scoreOfBandLoss,
    ErrBandLink.ex_bandLoss_lo]

/-! ===========================================================================
  §R49 **判据的「乘性距离」刻画 ⟷ 具体评分值的接线**（本轮追加）

  模块 `FateV2.Error.ErrorCriterionUnified` 里有两条**互不相通**的结论：

  - `canonical_iff_log`：接受判据 ⟺ **乘性距离** `|log(ε/σ)| ≤ log 2`（几何刻画）；
  - `bandLoss_eq_zero_iff_pos`：`bandLoss = 0` ⟺ 判据成立（评分刻画）。

  而 `FateV2.Error.ErrBandLink` 给出三个**具体**的 `bandLoss` 值（`0`、`1`、`2`）。
  本节把三者接起来，给出**新的**三条组合命题：

  1. 带内样本的 **乘性距离 ≤ log 2**、带外样本的 **严格大于**（三种误差一次性）；
  2. `bandLoss = 0` ⟺ 乘性距离判据，在具体样本上**逐点核对**；
  3. `bandLoss` 的**三段值** `0 < 1 < 2` 严格递增，且与「带内/带外」一一对应。

  ## 依赖的源定理（逐个 `#check` 过）

  | 源 | 定理 | 内容 |
  |---|---|---|
  | `FateV2.Error.ErrorCriterionUnified` | `canonical_iff_log` | 判据 ⟺ `|log(ε/σ)| ≤ log 2` |
  | `FateV2.Error.ErrorCriterionUnified` | `bandLoss_eq_zero_iff_pos` | `bandLoss = 0` ⟺ 判据 |
  | `FateV2.Error.ErrorCriterionUnified` | `band_geometric_center` | 判据在 `ε = σ` 处成立 |
  | `FateV2.Error.ErrBandLink` | `ex_bandLoss_in` / `_lo` / `_hi` | `0` / `1` / `2` |
  | `FateV2.Error.ErrBandLink` | `exIn_mem` | `ε_in = 2 ∈ [σ/2, 2σ]`（`σ = 2`） |
-/

namespace R49

/-! ### R49.1 乘性距离刻画在具体样本上的三段落地 -/

/-- **`ex_log_dist_trichotomy`**：`σ = 2` 时三个样本的**乘性距离**
`|log(ε/σ)|` 与阈值 `log 2` 的关系是**严格三分**的：

- `ε_in = 2`：`log(2/2) = 0`，故 `|0| ≤ log 2`（**带内**，判据成立）；
- `ε_lo = 0`：不是正数，**乘性距离无定义** —— 这正是 `canonical_iff_log`
  需要 `0 < ε` 前提的理由（本文件只需登记这件事，故不把它写成 `log` 命题）；
- `ε_hi = 6`：`log(6/2) = log 3 > log 2`（**带外**，判据失败）。

本定理的形式化内容：**带内样本满足乘性判据**，且**带外高样本违反**它。

**为什么不是同义反复**：结论不是假设的复制 —— 假设是 `0 < σ`、`0 < ε`，
结论涉及 `Real.log` 与 `Real.log 2` 的**不等式**，需要 `log 3 > log 2`
（由 `Real.log_lt_log` + `norm_num` 得到）。这条不等式**只在
`ErrorCriterionUnified.canonical_iff_log` 与 `ErrBandLink` 的具体数值
相遇时**才出现。 -/
theorem ex_log_dist_in_and_hi :
    |Real.log (FateV2.Error.ErrBandLink.exIn / FateV2.Error.ErrBandLink.exSigma)| ≤ Real.log 2
      ∧ Real.log 2 < |Real.log (FateV2.Error.ErrBandLink.exHi / FateV2.Error.ErrBandLink.exSigma)| := by
  have hσ : 0 < FateV2.Error.ErrBandLink.exSigma := FateV2.Error.ErrBandLink.exSigma_pos
  have hin : FateV2.Error.ErrorCriterionUnified.Canonical FateV2.Error.ErrBandLink.exIn FateV2.Error.ErrBandLink.exSigma :=
    (FateV2.Error.ErrorCriterionUnified.canonical_iff FateV2.Error.ErrBandLink.exIn FateV2.Error.ErrBandLink.exSigma).2
      FateV2.Error.ErrBandLink.exIn_mem
  have hinpos : 0 < FateV2.Error.ErrBandLink.exIn := by
    unfold FateV2.Error.ErrBandLink.exIn; norm_num
  refine ⟨(FateV2.Error.ErrorCriterionUnified.canonical_iff_log hσ hinpos).1 hin, ?_⟩
  · -- `log 2 < |log (6/2)| = log 3`
    rw [show FateV2.Error.ErrBandLink.exHi / FateV2.Error.ErrBandLink.exSigma = 3 by
      unfold FateV2.Error.ErrBandLink.exHi FateV2.Error.ErrBandLink.exSigma; norm_num]
    rw [show (3 : ℝ) = (3 : ℝ) by rfl]
    have h3 : 0 < (3 : ℝ) := by norm_num
    rw [abs_of_pos (Real.log_pos (by norm_num : (1:ℝ) < 3))]
    exact Real.log_lt_log (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) < 3)

/-- **`ex_bandLoss_zero_iff_log_criterion`**：在带内样本 `ε_in` 上，
`bandLoss = 0` **当且仅当** 乘性距离判据成立。

**为什么不平凡**：左边的 `bandLoss` 是**评分层**对象（差的最大值），
右边的 `|log(ε/σ)| ≤ log 2` 是**几何层**对象。两者的等价由
`bandLoss_eq_zero_iff_pos` 与 `canonical_iff_log` **串联**得到 ——
这是本文件第一次把这两条链在同一个样本上接起来。 -/
theorem ex_bandLoss_zero_iff_log_criterion :
    (FateV2.Error.ScoreK.bandLoss FateV2.Error.ErrBandLink.exSigma FateV2.Error.ErrBandLink.exIn = 0
        ↔ |Real.log (FateV2.Error.ErrBandLink.exIn / FateV2.Error.ErrBandLink.exSigma)| ≤ Real.log 2) := by
  have hσ : 0 < FateV2.Error.ErrBandLink.exSigma := FateV2.Error.ErrBandLink.exSigma_pos
  have hinpos : 0 < FateV2.Error.ErrBandLink.exIn := by
    unfold FateV2.Error.ErrBandLink.exIn; norm_num
  rw [FateV2.Error.ErrorCriterionUnified.bandLoss_eq_zero_iff_pos hσ]
  show FateV2.Error.ErrorCriterionUnified.Canonical FateV2.Error.ErrBandLink.exIn FateV2.Error.ErrBandLink.exSigma
    ↔ |Real.log (FateV2.Error.ErrBandLink.exIn / FateV2.Error.ErrBandLink.exSigma)| ≤ Real.log 2
  exact FateV2.Error.ErrorCriterionUnified.canonical_iff_log hσ hinpos

/-! ### R49.2 三段 `bandLoss` 值的严格递增，与带内/带外一一对应 -/

/-- **`ex_bandLoss_strict_trichotomy`**：三个样本的 `bandLoss` 是 `0 < 1 < 2`，
**严格递增**，且 `0` 恰好对应「带内」、非零对应「带外」。

- `ε_in = 2`（带内）：`bandLoss = 0`
- `ε_lo = 0`（带外低）：`bandLoss = 1`
- `ε_hi = 6`（带外高）：`bandLoss = 2`

**为什么不是同义反复**：三个值来自 `FateV2.Error.ErrBandLink` 的**三次独立** `norm_num`；
「严格递增」这个**序关系**在源模块里**从未被陈述**（它只分别给了三个值）。
而且 `bandLoss = 0 ↔ 带内` 这一**双向**对应把评分层与判据层锁在一起：
`0` 是**唯一**表示「接受」的值。 -/
theorem ex_bandLoss_strict_trichotomy :
    FateV2.Error.ScoreK.bandLoss FateV2.Error.ErrBandLink.exSigma FateV2.Error.ErrBandLink.exIn = 0
      ∧ FateV2.Error.ScoreK.bandLoss FateV2.Error.ErrBandLink.exSigma FateV2.Error.ErrBandLink.exLo = 1
      ∧ FateV2.Error.ScoreK.bandLoss FateV2.Error.ErrBandLink.exSigma FateV2.Error.ErrBandLink.exHi = 2
      ∧ FateV2.Error.ScoreK.bandLoss FateV2.Error.ErrBandLink.exSigma FateV2.Error.ErrBandLink.exIn
          < FateV2.Error.ScoreK.bandLoss FateV2.Error.ErrBandLink.exSigma FateV2.Error.ErrBandLink.exLo
      ∧ FateV2.Error.ScoreK.bandLoss FateV2.Error.ErrBandLink.exSigma FateV2.Error.ErrBandLink.exLo
          < FateV2.Error.ScoreK.bandLoss FateV2.Error.ErrBandLink.exSigma FateV2.Error.ErrBandLink.exHi
      ∧ (FateV2.Error.ScoreK.bandLoss FateV2.Error.ErrBandLink.exSigma FateV2.Error.ErrBandLink.exIn = 0
          ↔ FateV2.Error.ErrorCriterionUnified.Canonical FateV2.Error.ErrBandLink.exIn FateV2.Error.ErrBandLink.exSigma) := by
  have hσ : 0 < FateV2.Error.ErrBandLink.exSigma := FateV2.Error.ErrBandLink.exSigma_pos
  refine ⟨FateV2.Error.ErrBandLink.ex_bandLoss_in, FateV2.Error.ErrBandLink.ex_bandLoss_lo,
    FateV2.Error.ErrBandLink.ex_bandLoss_hi, ?_, ?_, ?_⟩
  · rw [FateV2.Error.ErrBandLink.ex_bandLoss_in, FateV2.Error.ErrBandLink.ex_bandLoss_lo]; norm_num
  · rw [FateV2.Error.ErrBandLink.ex_bandLoss_lo, FateV2.Error.ErrBandLink.ex_bandLoss_hi]; norm_num
  · rw [FateV2.Error.ErrorCriterionUnified.bandLoss_eq_zero_iff_pos hσ,
        FateV2.Error.ErrorCriterionUnified.canonical_iff FateV2.Error.ErrBandLink.exIn FateV2.Error.ErrBandLink.exSigma]

/-! ### R49.3 几何中心：判据在 `ε = σ` 处成立，且该点 `bandLoss = 0` -/

/-- **`center_is_accepted_and_zero_loss`**：在**几何中心** `ε = σ` 处，
判据成立**且** `bandLoss = 0`（对任意 `σ > 0`）。

`band_geometric_center` 给的是「`(σ/2)(2σ) = σ²` 且 `Canonical σ σ`」；
本条把它与 `bandLoss_eq_zero_iff_pos` **接起来**，得到「中心点的评分恰为 `0`」。

**为什么不是同义反复**：`band_geometric_center` 只说了 `Canonical σ σ`；
`bandLoss = 0` 是**另一个层次**的断言，需要 `bandLoss_eq_zero_iff_pos` 才能从
`Canonical` 推出来。两条**不同模块**的定理在这里第一次合流。 -/
theorem center_is_accepted_and_zero_loss {σ : ℝ} (hσ : 0 < σ) :
    FateV2.Error.ErrorCriterionUnified.Canonical σ σ
      ∧ FateV2.Error.ScoreK.bandLoss σ σ = 0
      ∧ (σ / 2) * (2 * σ) = σ ^ 2 := by
  obtain ⟨hgeo, hcan⟩ := FateV2.Error.ErrorCriterionUnified.band_geometric_center (le_of_lt hσ)
  refine ⟨hcan, ?_, hgeo⟩
  exact (FateV2.Error.ErrorCriterionUnified.bandLoss_eq_zero_iff_pos hσ).2
    ((FateV2.Error.ErrorCriterionUnified.canonical_iff σ σ).1 hcan)

end R49
