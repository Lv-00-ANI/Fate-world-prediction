import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! ===========================================================================
  Fate.AttrAcceptable —— 「依裁决 K」的属性合格判据

  ## 判据

  $$\mathrm{AttrAcceptable}(\varepsilon,\sigma) \;:=\; \frac{\sigma}{2} \le \varepsilon \;\wedge\; \varepsilon \le 2\sigma$$

  即：相对于属性尺度 $\sigma$，偏差 $\varepsilon$ 既不能小到 $<\sigma/2$，
  也不能大到 $>2\sigma$。故合格集恰为闭区间 $[\sigma/2,\ 2\sigma]$。

  ## 本文件内容

  * §1 判据定义与区间刻画
  * §2 基本性质：$\sigma>0$ 时合格区间非空
  * §3 单调性：在 $\varepsilon \le 2\sigma$ 范围内，$\varepsilon$ 越小越容易合格
  * §4 具体数值例子：$\sigma = 0.05$ 时合格区间为 $[0.025,\ 0.1]$

  本文件零 `sorry`、零 `admit`、零 `axiom`。
  =========================================================================== -/

namespace Fate

namespace AttrAcceptable

set_option linter.dupNamespace false

/-! ### §1 定义与区间刻画 -/

/-- 依裁决 K 的属性合格判据。 -/
def AttrAcceptable (ε σ : ℝ) : Prop := σ / 2 ≤ ε ∧ ε ≤ 2 * σ

/-- 合格判据展开为闭区间 $[\sigma/2, 2\sigma]$。 -/
theorem attrAcceptable_iff_mem_Icc (ε σ : ℝ) :
    AttrAcceptable ε σ ↔ ε ∈ Set.Icc (σ / 2) (2 * σ) :=
  Iff.rfl

/-- 合格判据的「下界」分量。 -/
theorem lower (ε σ : ℝ) (h : AttrAcceptable ε σ) : σ / 2 ≤ ε := h.1

/-- 合格判据的「上界」分量。 -/
theorem upper (ε σ : ℝ) (h : AttrAcceptable ε σ) : ε ≤ 2 * σ := h.2

/-! ### §2 基本性质：$\sigma>0$ 时合格区间非空 -/

/-- 当 $\sigma > 0$ 时，$\sigma/2 < 2\sigma$，故合格集（闭区间 $[\sigma/2,2\sigma]$）非空。 -/
theorem interval_nonempty {σ : ℝ} (hσ : 0 < σ) : (σ / 2 : ℝ) ≤ 2 * σ := by
  linarith

/-- 非空的显式见证：$\varepsilon = \sigma$ 总在合格区间内（当 $\sigma \ge 0$）。 -/
theorem self_acceptable {σ : ℝ} (hσ : 0 ≤ σ) : AttrAcceptable σ σ := by
  unfold AttrAcceptable
  constructor <;> linarith

/-- 「区间非空」的集合论表述：$\sigma > 0$ 时 $[\sigma/2,2\sigma]$ 非空。 -/
theorem set_nonempty {σ : ℝ} (hσ : 0 < σ) :
    (Set.Icc (σ / 2) (2 * σ) : Set ℝ).Nonempty :=
  ⟨σ, le_of_lt (by linarith : σ / 2 < σ), by linarith⟩

/-! ### §3 单调性：$\varepsilon$ 越小越容易合格（在 $\varepsilon \le 2\sigma$ 范围内）

说明：由于判据含**下界** $\sigma/2 \le \varepsilon$，$\varepsilon$ 越小并非全局更容易合格；
真正的单调性在**上半区间**成立——若 $\sigma/2 \le \varepsilon' \le \varepsilon \le 2\sigma$，
则 $\varepsilon$ 合格蕴含 $\varepsilon'$ 合格。即：**在 $[\sigma/2,\,2\sigma]$ 内，
判据对 $\varepsilon$ 关于上界是向下闭的（downward closed）**。 -/

/-- **单调性**：若 $\varepsilon$ 合格，且 $\varepsilon'$ 落在 $[\sigma/2,\ \varepsilon]$ 内
（即 $\varepsilon'$ 不小于下界 $\sigma/2$、不大于 $\varepsilon \le 2\sigma$），则 $\varepsilon'$ 也合格。 -/
theorem mono_eps {ε ε' σ : ℝ} (h : AttrAcceptable ε σ)
    (hlo : σ / 2 ≤ ε') (hhi : ε' ≤ ε) : AttrAcceptable ε' σ := by
  unfold AttrAcceptable at *
  exact ⟨hlo, le_trans hhi h.2⟩

/-- 同上，但前提只写成 $\varepsilon' \le \varepsilon$ 且 $\varepsilon'$ 合法下界：
上界条件自动继承，故「$\varepsilon$ 越小（在合法下界之上）越容易合格」。 -/
theorem mono_eps_upper_only {ε ε' σ : ℝ} (h : AttrAcceptable ε σ)
    (hlo : σ / 2 ≤ ε') (hhi : ε' ≤ ε) : ε' ≤ 2 * σ :=
  (mono_eps h hlo hhi).2

/-- 合格集关于 $\varepsilon$ 的方向性：合格性只随 $\varepsilon$ **在下侧**保持。 -/
theorem acceptable_self_of_le {ε ε' σ : ℝ} (hlo : σ / 2 ≤ ε') (hhi : ε' ≤ ε)
    (h : ε ≤ 2 * σ) : AttrAcceptable ε' σ :=
  ⟨hlo, le_trans hhi h⟩

/-! ### §4 具体数值例子：$\sigma = 0.05$ 时合格区间为 $[0.025,\ 0.1]$ -/

/-- 数值例子：$\sigma = 0.05$ 时，$0.025 = \sigma/2$。 -/
theorem example_lower : (0.05 : ℝ) / 2 = 0.025 := by norm_num

/-- 数值例子：$\sigma = 0.05$ 时，$2\sigma = 0.1$。 -/
theorem example_upper : 2 * (0.05 : ℝ) = 0.1 := by norm_num

/-- 数值例子：$\sigma = 0.05$ 的合格集恰为闭区间 $[0.025,\ 0.1]$。 -/
theorem example_interval (ε : ℝ) :
    AttrAcceptable ε 0.05 ↔ ε ∈ Set.Icc (0.025 : ℝ) 0.1 := by
  unfold AttrAcceptable
  rw [example_lower, example_upper]
  exact Iff.rfl

/-- 数值例子端点：$0.025$ 合格。 -/
theorem example_left_endpoint : AttrAcceptable 0.025 0.05 := by
  norm_num [AttrAcceptable]

/-- 数值例子端点：$0.1$ 合格。 -/
theorem example_right_endpoint : AttrAcceptable 0.1 0.05 := by
  norm_num [AttrAcceptable]

/-- 数值例子中点：$0.05$ 合格。 -/
theorem example_mid : AttrAcceptable 0.05 0.05 := by
  norm_num [AttrAcceptable]

/-- 数值例子：区间外（下方）$0.01$ 不合格。 -/
theorem example_below : ¬ AttrAcceptable 0.01 0.05 := by
  norm_num [AttrAcceptable]

/-- 数值例子：区间外（上方）$0.2$ 不合格。 -/
theorem example_above : ¬ AttrAcceptable 0.2 0.05 := by
  norm_num [AttrAcceptable]

end AttrAcceptable

end Fate
