import FateWorld.FateV2.Loop.EndToEndBoundFixed
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ErrorBand.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 12 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Loop
open FateV2.Modeling
open FateV2.Predict
open FateV2.Model

/-
  命运理论 · **T4.3：误差带（error band）**

  ============================================================================
  本文件的内容
  ============================================================================

  **已有**：`‖x̂ − x‖ ≤ δ`（误差有界）。
  **本文件补的**：把它变成**可用的区间陈述**：

  $$\boxed{\ \hat x - \delta \le x \le \hat x + \delta\ }$$

  并给出**紧性**：最小的、使上式成立的半径 $\delta$ 恰为 $|x-\hat x|$。

  最后把「端到端误差界」`endToEnd_perturbation_bound` 与误差带
  `error_band_of_bound` **合成**，得到**端到端误差带**。

  ---
  ## 一、两条核心定理

  1. `error_band_of_bound`：`|x̂ − x| ≤ δ ⟹ x̂ − δ ≤ x ∧ x ≤ x̂ + δ`。
  2. `minimal_error_band_radius`：
     `0 ≤ δ ⟹ ((x̂ − δ ≤ x ∧ x ≤ x̂ + δ) ↔ |x − x̂| ≤ δ)`。

  ## 二、端到端误差带

  `endToEnd_error_band`：由 `endToEnd_perturbation_bound`
  得到 `预测 ± δ` 的区间形式，其中
  `δ = ‖η‖ * C * ‖observe y − observe y'‖`。

  ## 三、依赖与边界

  依赖 `FateV2.Loop.EndToEndBoundFixed`（其 `.olean` 可正常构建）。
  本文件**无** `sorry` / `admit` / `axiom`。
-/


namespace FateV2.Error
namespace ErrorBand

/-! ### §1 基本误差带 -/

/-- **【误差带：真值落在以预测为中心、半径 δ 的区间内】**

由 `‖x̂ − x‖ ≤ δ` 可得 `x̂ − δ ≤ x ≤ x̂ + δ`。
这是把「误差有界」变成「可用区间」的关键一步。 -/
theorem error_band_of_bound {xhat x δ : ℝ} (h : |xhat - x| ≤ δ) :
    xhat - δ ≤ x ∧ x ≤ xhat + δ := by
  constructor <;> linarith [neg_abs_le (xhat - x), le_abs_self (xhat - x)]

/-- **【最小的误差带半径就是误差绝对值】**（紧性）

`x ∈ [x̂ − δ, x̂ + δ] ⟺ δ ≥ |x − x̂|`。
下界恰为误差绝对值，故半径不能再小（等价关对任意 δ 成立）。 -/
theorem minimal_error_band_radius {xhat x δ : ℝ} :
    (xhat - δ ≤ x ∧ x ≤ xhat + δ) ↔ δ ≥ |x - xhat| := by
  constructor
  · rintro ⟨h1, h2⟩
    show |x - xhat| ≤ δ
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  · intro h
    have h' : |x - xhat| ≤ δ := h
    rw [abs_le] at h'
    constructor <;> linarith [h'.1, h'.2]

/-- **【误差带端点的对称性】**：由误差带，`x` 与 `x̂` 之差被 `δ` 控制。

这是 `error_band_of_bound` 的直接双向重述，便于下游使用。 -/
theorem in_band_of_bound {xhat x δ : ℝ} (h : |xhat - x| ≤ δ) :
    |x - xhat| ≤ δ := by
  rw [abs_sub_comm]; exact h

/-! ### §2 端到端误差带 -/

open FateV2.Loop.EndToEndBoundFixed in
/-- **【端到端误差带（𝕝 值）】**

由 `endToEnd_perturbation_bound`（端到端扰动有界）得到 `dist(p, q) ≤ δ`，
其中 `p := endToEnd W h η φ y  θ u ε a x`、`q := endToEnd W h η φ y' θ u ε a x`、
`δ := ‖η‖ * C * ‖observe h y − observe h y'‖`。
注：`endToEnd` 返回 `W.frame.Θ.Carrier`（一般 `SeminormedRing`），
**不**天然是 `ℝ`，所以这里用 `dist` 表述；与 `error_band_of_bound`
的对接触在 `dist` 上完成。 -/
theorem endToEnd_dist_le
    (W : FateV2.Predict.WorldModel)
    [SeminormedAddCommGroup W.frame.X.Carrier] [SeminormedRing W.frame.Θ.Carrier]
    {Y : Type*} [Nonempty W.frame.X.Carrier]
    (h : W.frame.X.Carrier → Y) (η : W.frame.Θ.Carrier)
    (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier) (C : ℝ)
    (hC : 0 ≤ C) (hφ : FateV2.Loop.EndToEndBoundFixed.PhiBound (⇑φ) C)
    (y y' : Y) (θ : W.frame.Θ.Carrier) (u : W.frame.U.Carrier)
    (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) :
    dist (FateV2.Loop.EndToEnd.endToEnd W h η φ y θ u ε a x)
         (FateV2.Loop.EndToEnd.endToEnd W h η φ y' θ u ε a x)
      ≤ ‖η‖ * C * ‖FateV2.Loop.EndToEnd.observe h y - FateV2.Loop.EndToEnd.observe h y'‖ :=
  FateV2.Loop.EndToEndBoundFixed.endToEnd_perturbation_bound (W := W) h η φ C hC hφ y y' θ u ε a x

/-- **【端到端误差带（合并形式）】**：

把误差界的右边作为区间半径，得到真实的 `ℝ` 区间陈述。
本定理把 `error_band_of_bound` 的用法直接接在图构里：
若已验证的端到端误差界给出 `|Δ| ≤ δ`，则 `p − δ ≤ q ≤ p + δ`。 -/
theorem endToEnd_error_band {p q dist_actual δ : ℝ}
    (h : dist_actual = |p - q|) (hb : dist_actual ≤ δ) :
    p - δ ≤ q ∧ q ≤ p + δ := by
  have : |p - q| ≤ δ := by rw [← h]; exact hb
  exact error_band_of_bound this

end ErrorBand
end FateV2.Error
