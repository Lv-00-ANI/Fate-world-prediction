import FateWorld.FateV2.Predict.WorldScenario

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ScoreK.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 3 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Predict

/-! ===========================================================================
  带偏离损失与判据的等价（对应论文 §8.2）

  干预选择有两条判准：其一为损失最小化 argminₐ E[L(x_{t+1}(a))]，其二为误差须落在
  [σ/2, 2σ]（两侧都卡）。本模块把它们统一：定义带偏离损失

    L_σ(ε) := dist(ε, [σ/2, 2σ])，

  于是 σ/2 ≤ ε ≤ 2σ 时 L_σ = 0（合格）；ε < σ/2 时 L_σ = σ/2 − ε（过拟合）；
  ε > 2σ 时 L_σ = ε − 2σ（丢信号）。由此损失最小（等于 0）等价于误差落在合格带，
  两条判准不是两个选择而是一个：把损失定义为「偏离噪声尺度的程度」之后，损失最小化
  就是判据的落实。

  （下文 §n 指本文件内部分节，与论文节次无关。）

  注：本模块只定义损失，不证明「最小者存在」——那需要场景树有限。ε 的定义（误差如何
     计算）不在本模块范围，属具体任务的问题。dist 用绝对值代替，因为误差是实数尺度；
     多维情形需换成范数。

  不取 `sorry` / `admit` / 自定义 `axiom`。
  =========================================================================== -/


namespace FateV2.Error

namespace ScoreK

universe u

/-! ### §0.1 带偏离损失 -/

/-- **带偏离损失**：误差 `ε` 到合格带 `[σ/2, 2σ]` 的距离。

**⚠ 需 `0 < σ`**（否则带退化为单点）。 -/
noncomputable def bandLoss (σ ε : ℝ) : ℝ :=
  max 0 (max (σ / 2 - ε) (ε - 2 * σ))

/-- **带内损失为零**：`σ/2 ≤ ε ≤ 2σ ⟹ bandLoss σ ε = 0`。

**⟹ 这是上述判据的直接形式化。** -/
theorem bandLoss_eq_zero {σ ε : ℝ} (h1 : σ / 2 ≤ ε) (h2 : ε ≤ 2 * σ) :
    bandLoss σ ε = 0 := by
  unfold bandLoss
  have h3 : σ / 2 - ε ≤ 0 := by linarith
  have h4 : ε - 2 * σ ≤ 0 := by linarith
  have h5 : max (σ / 2 - ε) (ε - 2 * σ) ≤ 0 := max_le h3 h4
  exact max_eq_left h5

theorem bandLoss_pos_of_lt {σ ε : ℝ} (h : ε < σ / 2) :
    0 < bandLoss σ ε := by
  unfold bandLoss
  have h3 : 0 < σ / 2 - ε := by linarith
  have h5 : 0 < max (σ / 2 - ε) (ε - 2 * σ) := lt_of_lt_of_le h3 (le_max_left _ _)
  exact lt_of_lt_of_le h5 (le_max_right _ _)

theorem bandLoss_pos_of_gt {σ ε : ℝ} (h : 2 * σ < ε) :
    0 < bandLoss σ ε := by
  unfold bandLoss
  have h4 : 0 < ε - 2 * σ := by linarith
  have h5 : 0 < max (σ / 2 - ε) (ε - 2 * σ) := lt_of_lt_of_le h4 (le_max_right _ _)
  exact lt_of_lt_of_le h5 (le_max_right _ _)

/-! ### §0.2 损失最小 ⟺ 误差合格 -/

/-- **核心等价**：`bandLoss σ ε = 0 ⟺ σ/2 ≤ ε ≤ 2σ`（在 `0 < σ` 下）。

**⟹ 这是「损失最小」与「误差落在合格带」两判准等价的形式化。**

**⚠ 反向需要 `0 < σ`** —— 否则当 `σ = 0` 时带退化为 `[0,0]`，
而 `bandLoss 0 0 = 0` 但 `ε ≠ 0` 也可能给出 `0`（因 `max 0` 的截断）。 -/
theorem bandLoss_eq_zero_iff {σ : ℝ} (hσ : 0 < σ) {ε : ℝ} :
    bandLoss σ ε = 0 ↔ σ / 2 ≤ ε ∧ ε ≤ 2 * σ := by
  constructor
  · intro h
    unfold bandLoss at h
    have h0 : max 0 (max (σ / 2 - ε) (ε - 2 * σ)) ≤ 0 := le_of_eq h
    have hm : max (σ / 2 - ε) (ε - 2 * σ) ≤ 0 := (max_le_iff.mp h0).2
    have h1 : σ / 2 - ε ≤ 0 := (max_le_iff.mp hm).1
    have h2 : ε - 2 * σ ≤ 0 := (max_le_iff.mp hm).2
    constructor <;> linarith
  · intro ⟨h1, h2⟩
    exact bandLoss_eq_zero h1 h2

/-! ### §0.3 与 `Policy` 的对接 -/

/-- **由带偏离损失构造评分**（`score` = 损失最小 ⟺ 评分最大）。

**⟹ 这样 `WorldScenario.Policy` 的 `score` 就有了具体内容。** -/
noncomputable def scoreOfBandLoss {A X : Type u} (σ : ℝ)
    (err : WorldScenario.Scenario A X → ℝ) (s : WorldScenario.Scenario A X) : ℝ :=
  -bandLoss σ (err s)

/-- **评分最大 ⟺ 误差合格** 的推论：
若某场景的误差合格，则其评分 ≥ 任何误差不合格场景的评分。

**⚠ 需 `0 < σ`。** -/
theorem scoreOfBandLoss_le_of_ok {A X : Type u} {σ : ℝ} (hσ : 0 < σ)
    {err : WorldScenario.Scenario A X → ℝ} {s t : WorldScenario.Scenario A X}
    (hs : σ / 2 ≤ err s ∧ err s ≤ 2 * σ) :
    scoreOfBandLoss σ err t ≤ scoreOfBandLoss σ err s := by
  unfold scoreOfBandLoss
  rw [bandLoss_eq_zero hs.1 hs.2]
  have : 0 ≤ bandLoss σ (err t) := by
    unfold bandLoss
    exact le_max_left _ _
  linarith

end ScoreK

end FateV2.Error
