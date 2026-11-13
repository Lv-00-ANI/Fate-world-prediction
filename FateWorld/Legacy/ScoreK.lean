import FateWorld.Legacy.WorldScenario

/-! ===========================================================================
  §0  干预选择的判准：损失最小化 ⊕ 裁决 K（作者裁决「2 和 1 都行」）

  ## 两个判准

  **判准 1（理论第 7 章）**：$a^\star = \arg\min_a \mathbb{E}[L(x_{t+1}(a))]$
  —— 损失最小化。

  **判准 2（裁决 K）**：误差必须落在 $[\sigma/2,\ 2\sigma]$ —— 两侧都卡。

  ## ⭐ 本节把它们统一

  定义**带偏离损失**：
  $$L_\sigma(\varepsilon) := \mathrm{dist}\bigl(\varepsilon,\ [\sigma/2,\ 2\sigma]\bigr)$$

  **即**：
  * $\sigma/2 \le \varepsilon \le 2\sigma$ ⟹ $L_\sigma(\varepsilon) = 0$（合格）
  * $\varepsilon < \sigma/2$ ⟹ $L_\sigma = \sigma/2 - \varepsilon$（过拟合）
  * $\varepsilon > 2\sigma$ ⟹ $L_\sigma = \varepsilon - 2\sigma$（丢信号）

  **⟹ 于是**：
  * **损失最小（= 0）⟺ 误差钉在合格带**
  * **裁决 K 的两侧约束被同一个损失函数同时表达**
  * **「选损失最小的干预」自动等于「选误差最接近合格带的干预」**

  ## 这解决了什么

  作者说「2 和 1 都行」 —— 本节显示它们**不是两个选择，而是一个**：
  **把损失定义为「偏离噪声尺度的程度」后，损失最小化**就是**裁决 K 的落实**。

  ## 诚实边界

  * **本节只定义损失，不证明「最小者存在」** —— 那需要场景树有限（见 `WorldScenario` 的
    `exists_optimal_scenario`，已给有限情形）。
  * **`ε` 的定义（误差怎么算）本节未定** —— 它是具体任务的问题。
  * **`dist` 用绝对值代替** —— 因为误差是实数尺度；多维情形需换成范数。
  =========================================================================== -/

namespace Fate

namespace ScoreK

universe u

/-! ### §0.1 ⭐ 带偏离损失（裁决 K 的损失形式） -/

/-- ⭐⭐ **带偏离损失**：误差 `ε` 到合格带 `[σ/2, 2σ]` 的距离。

**⚠ 需 `0 < σ`**（否则带退化为单点）。 -/
noncomputable def bandLoss (σ ε : ℝ) : ℝ :=
  max 0 (max (σ / 2 - ε) (ε - 2 * σ))

/-- ⭐ **带内损失为零**：`σ/2 ≤ ε ≤ 2σ ⟹ bandLoss σ ε = 0`。

**⟹ 这是裁决 K 的直接形式化。** -/
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

/-! ### §0.2 ⭐⭐ 损失最小 ⟺ 误差合格 -/

/-- ⭐⭐ **核心等价**：`bandLoss σ ε = 0 ⟺ σ/2 ≤ ε ≤ 2σ`（在 `0 < σ` 下）。

**⟹ 这是「判准 1（损失最小）⟺ 判准 2（裁决 K）」的形式化。**

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

/-! ### §0.3 ⭐ 与 `Policy` 的对接 -/

/-- ⭐⭐ **由带偏离损失构造评分**（`score` = 损失最小 ⟺ 评分最大）。

**⟹ 这样 `WorldScenario.Policy` 的 `score` 就有了具体内容。** -/
noncomputable def scoreOfBandLoss {A X : Type u} (σ : ℝ)
    (err : WorldScenario.Scenario A X → ℝ) (s : WorldScenario.Scenario A X) : ℝ :=
  -bandLoss σ (err s)

/-- ⭐⭐ **评分最大 ⟺ 误差合格** 的推论：
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

end Fate
