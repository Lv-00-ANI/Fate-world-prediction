import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! ===========================================================================
  Fate.ErrorCriterion —— 裁决 K 的**抽象**形式：「误差判据需要噪声尺度 σ」

  ## 一、裁决 K 原文与抽象

  **原文**（作者裁决 K）：

  > 「误差必须小到不影响，即**刚好拟合与过拟合的边界**。」

  **⚠ 第 386 轮更正（作者指出，主控核实并撤回第 384 轮的误判）**

  **第 384 轮我曾在此写「容差 `[1/2,2]` 需作者裁定」——那个判断是错的，此处撤回。**
  理由：裁决 K 的判据**并非由一个数值容差定义**，而是**由实际情况算出**：
  真正的形式在 `Fate/FitBoundary.lean:268`：

  ```
  def IsFitBoundary (W : ErrProfileWeak) (σ γ : ℝ) : Prop :=
    W.err γ = σ ∧ ∀ γ'', σ ≤ W.err γ''
  ```
  即「误差恰等于噪声尺度 σ」∧「σ 是所有分辨率能达到的误差下界」——
  两个条件都从**实际的误差曲线 `W` 与实际噪声尺度 `σ`** 读出，**不含任何硬编码倍率**。
  作者原话：「裁决 k 的那个不是有了吗？那个是通过实际情况算的啊」

  **本文件 `ErrorAcceptable ε σ := σ/2 ≤ ε ∧ ε ≤ 2σ` 的定位**：它只是
  「**与 σ 同阶**」这一**必要条件**的粗糙判据（便于快速筛），
  **不是**裁决 K 的完整形式，也**不替代** `IsFitBoundary`。
  `ErrorDimUnified.lean:114 bandCriterion` 是两者之间的桥。

  **抽象**：任何误差判据都需要一个**噪声尺度** $\sigma$ 作参照；
  判据的*形式*统一（误差 $\varepsilon$ 与 $\sigma$ 同阶），而 $\sigma$ 由各类问题自定。

  本文件把这个抽象落成**一个谓词 + 一组结构性定理**，
  即：判据之所以能写成统一形式，是因为它只依赖「$\varepsilon$ 与 $\sigma$ 同阶」这一**伸缩不变**的事实。

  ## 二、本文件内容

  * §1 定义 `ErrorAcceptable ε σ`（与裁决 K 形式化一致）
  * §2 **单调性**：在 $\varepsilon \le 2\sigma$ 范围内，$\varepsilon$ 越小越容易合格
  * §3 **非空性**：$\sigma > 0$ 时合格区间非空
  * §4 **伸缩不变性**：`ErrorAcceptable (c*ε) (c*σ) ↔ ErrorAcceptable ε σ`（$c > 0$）
        —— 这正是「**同阶**」的形式化：判据不含绝对尺度，只有相对尺度
  * §5 **与既有 `Fate.AttrAcceptable` 一致**（两者定义相同，互推）
  * §6 推论：$\sigma$ 的**种类自定**——判据对 $\sigma$ 的选择不敏感，但与 $\sigma$ 的比值敏感

  ## 三、诚实边界

  本文件全部定理均为**真证明**，零 `sorry`、零 `admit`、零 `axiom`。
  §5 的「一致」是**定义层的一致**（同一谓词），不是对裁决 K 语义本身的经验断言；
  「$\sigma$ 该取多少」属于**建模选择**，不在本文件的已证范围内（见 §6 末尾的说明）。
  =========================================================================== -/

namespace Fate

namespace ErrorCriterion

set_option linter.dupNamespace false

/-! ### §1 定义 -/

/-- 通用误差判据：误差 $\varepsilon$ 与噪声尺度 $\sigma$ 同阶（依裁决 K）。 -/
def ErrorAcceptable (ε σ : ℝ) : Prop := σ / 2 ≤ ε ∧ ε ≤ 2 * σ

/-- 判据等价于落入闭区间 $[\sigma/2,\ 2\sigma]$。 -/
theorem errorAcceptable_iff_mem_Icc (ε σ : ℝ) :
    ErrorAcceptable ε σ ↔ ε ∈ Set.Icc (σ / 2) (2 * σ) :=
  Iff.rfl

/-- 判据的两个分量。 -/
theorem lower {ε σ : ℝ} (h : ErrorAcceptable ε σ) : σ / 2 ≤ ε := h.1

theorem upper {ε σ : ℝ} (h : ErrorAcceptable ε σ) : ε ≤ 2 * σ := h.2

/-! ### §2 单调性：$\varepsilon$ 越小越容易合格（在 $\varepsilon \le 2\sigma$ 范围内）

判据含**下界** $\sigma/2 \le \varepsilon$，故 $\varepsilon$ 变小并非全局更容易合格；
真正的单调性在**合格区间内**成立：低于 $\varepsilon$ 且仍在下界之上者必合格。
即合格集关于 $\varepsilon$ **向下闭**（downward closed）。 -/

/-- **单调性**：$\varepsilon$ 合格，且 $\sigma/2 \le \varepsilon' \le \varepsilon$，则 $\varepsilon'$ 合格。
换言之：在 $[\sigma/2, 2\sigma]$ 内，$\varepsilon$ 越小（越靠上界内侧）越容易合格。 -/
theorem mono_eps {ε ε' σ : ℝ} (h : ErrorAcceptable ε σ)
    (hlo : σ / 2 ≤ ε') (hhi : ε' ≤ ε) : ErrorAcceptable ε' σ :=
  ⟨hlo, le_trans hhi h.2⟩

/-- 单调性的**端点形式**：若 $\sigma/2 \le \varepsilon' \le \varepsilon$ 且 $\varepsilon \le 2\sigma$，
则 $\varepsilon'$ 合格（前提不要求 $\varepsilon$ 本身合格）。 -/
theorem mono_eps' {ε ε' σ : ℝ} (hlo : σ / 2 ≤ ε')
    (hhi : ε' ≤ ε) (h : ε ≤ 2 * σ) : ErrorAcceptable ε' σ :=
  ⟨hlo, le_trans hhi h⟩

/-- 合格集关于 $\varepsilon$ 的**向下闭性**（集合形式）。 -/
theorem downward_closed {σ : ℝ} :
    ∀ ε ε', ErrorAcceptable ε σ → σ / 2 ≤ ε' → ε' ≤ ε → ErrorAcceptable ε' σ :=
  fun _ _ h hlo hhi => mono_eps h hlo hhi

/-! ### §3 非空性：$\sigma > 0$ 时合格区间非空 -/

/-- $\sigma > 0$ 时合格区间非空（等价于 $\sigma/2 \le 2\sigma$）。 -/
theorem interval_nonempty {σ : ℝ} (hσ : 0 < σ) : (σ / 2 : ℝ) ≤ 2 * σ := by
  linarith

/-- 区间非空的**集合论**表述。 -/
theorem set_nonempty {σ : ℝ} (hσ : 0 < σ) :
    (Set.Icc (σ / 2) (2 * σ) : Set ℝ).Nonempty :=
  ⟨σ, by constructor <;> linarith⟩

/-- 显式见证：$\varepsilon = \sigma$ 总是合格的（当 $\sigma \ge 0$）。 -/
theorem self_acceptable {σ : ℝ} (hσ : 0 ≤ σ) : ErrorAcceptable σ σ :=
  ⟨by linarith, by linarith⟩

/-! ### §4 伸缩不变性：这是「同阶」的形式化

判据**不含绝对尺度**：把 $\varepsilon$ 与 $\sigma$ 同时放大/缩小 $c>0$ 倍，
合格性不变。这正是「$\varepsilon$ 与 $\sigma$ 同阶」的数学内容——
合格性只取决于**比值** $\varepsilon/\sigma \in [1/2, 2]$。 -/

/-- **伸缩不变性**：$c > 0$ 时 `ErrorAcceptable (c*ε) (c*σ) ↔ ErrorAcceptable ε σ`。 -/
theorem scale_invariant {c ε σ : ℝ} (hc : 0 < c) :
    ErrorAcceptable (c * ε) (c * σ) ↔ ErrorAcceptable ε σ := by
  have hc0 : (0 : ℝ) ≤ c := le_of_lt hc
  unfold ErrorAcceptable
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have h1' : c * (σ / 2) ≤ c * ε := by
        calc c * (σ / 2) = c * σ / 2 := by ring
          _ ≤ c * ε := h1
      exact le_of_mul_le_mul_left h1' hc
    · have h2' : c * ε ≤ c * (2 * σ) := by
        calc c * ε ≤ 2 * (c * σ) := h2
          _ = c * (2 * σ) := by ring
      exact le_of_mul_le_mul_left h2' hc
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have h1' : c * (σ / 2) ≤ c * ε := mul_le_mul_of_nonneg_left h1 hc0
      calc c * σ / 2 = c * (σ / 2) := by ring
        _ ≤ c * ε := h1'
    · calc c * ε ≤ c * (2 * σ) := mul_le_mul_of_nonneg_left h2 hc0
        _ = 2 * (c * σ) := by ring

/-- **比值刻画**：$\sigma > 0$ 时合格性等价于比值 $\varepsilon/\sigma$ 落在 $[1/2, 2]$。
这是伸缩不变性的直接推论，也是「同阶」最直观的表述。 -/
theorem iff_ratio {ε σ : ℝ} (hσ : 0 < σ) :
    ErrorAcceptable ε σ ↔ (1 / 2 : ℝ) ≤ ε / σ ∧ ε / σ ≤ 2 := by
  have hs : σ ≠ 0 := ne_of_gt hσ
  unfold ErrorAcceptable
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(le_div_iff₀ hσ).mpr (by linarith), (div_le_iff₀ hσ).mpr (by linarith)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by have := (le_div_iff₀ hσ).mp h1; linarith,
           by have := (div_le_iff₀ hσ).mp h2; linarith⟩

/-- 伸缩不变性的**推论**：合格性只依赖比值，$(\varepsilon,\sigma)$ 与 $(c\varepsilon, c\sigma)$ 同判。 -/
theorem same_ratio_same_verdict {c ε σ : ℝ} (hc : 0 < c) :
    ErrorAcceptable (c * ε) (c * σ) ↔ ErrorAcceptable ε σ :=
  scale_invariant hc

/-! ### §5 与既有 `Fate.AttrAcceptable` 一致

`Fate/AttrAcceptable.lean` 中的 `AttrAcceptable` 与本文件的 `ErrorAcceptable`
是**同一个谓词**。为使本文件可被**单文件验证**（不依赖外部 `.olean` 构建），
此处给出其定义的同构副本 `AttrAcceptableMirror`，并证明二者**外延相等**；
同时复述 `AttrAcceptable.lean` 中已证的 `example_interval` 并在此**独立重证**，
以保证「一致性」不是空口声称。 -/

/-- `Fate/AttrAcceptable.lean` 中 `AttrAcceptable` 的定义（同构副本）。 -/
def AttrAcceptableMirror (ε σ : ℝ) : Prop := σ / 2 ≤ ε ∧ ε ≤ 2 * σ

/-- 抽象判据与 `AttrAcceptable` 的定义相同：二者**互推**。 -/
theorem iff_attrAcceptable (ε σ : ℝ) :
    ErrorAcceptable ε σ ↔ AttrAcceptableMirror ε σ :=
  Iff.rfl

/-- 由抽象判据可得属性合格。 -/
theorem to_attrAcceptable {ε σ : ℝ} (h : ErrorAcceptable ε σ) :
    AttrAcceptableMirror ε σ :=
  h

/-- 由属性合格可得抽象判据。 -/
theorem of_attrAcceptable {ε σ : ℝ} (h : AttrAcceptableMirror ε σ) :
    ErrorAcceptable ε σ :=
  h

/-- 一致性也可表述为谓词的**外延相等**。 -/
theorem ext_eq_attrAcceptable : ErrorAcceptable = AttrAcceptableMirror :=
  rfl

/-- 一致性把 `AttrAcceptable` 已有的结论**继承**过来：
    $\sigma = 0.05$ 时合格区间为 $[0.025, 0.1]$（独立重证，不依赖外部模块）。 -/
theorem example_interval_transfer (ε : ℝ) :
    ErrorAcceptable ε 0.05 ↔ ε ∈ Set.Icc (0.025 : ℝ) 0.1 := by
  have h₁ : (0.05 : ℝ) / 2 = 0.025 := by norm_num
  have h₂ : 2 * (0.05 : ℝ) = 0.1 := by norm_num
  unfold ErrorAcceptable
  rw [h₁, h₂]
  rfl

/-! ### §6 推论：$\sigma$ 各类自定，判据不因 $\sigma$ 的绝对大小而变

同一「同阶」要求可以在任意尺度上表达：给一个 $\sigma$ 与任意缩放后的 $\sigma'=c\sigma$，
判据的形状完全相同，只是 $\varepsilon$ 相应缩放到 $c\varepsilon$。 -/

/-- **尺度无关的形状**：对任意 $c>0$，$\sigma$ 与 $c\sigma$ 上的判据由同一个不变式刻画。 -/
theorem shape_scale_free {c ε σ : ℝ} (hc : 0 < c) :
    ErrorAcceptable ε σ ↔ ErrorAcceptable (c * ε) (c * σ) :=
  (scale_invariant hc).symm

/-- **$\sigma$ 的自定性（已证部分）**：若 $\varepsilon$ 相对 $\sigma_1$ 合格，
则任何「同尺度重述」 $\sigma_2 = c\sigma_1$、$\varepsilon_2 = c\varepsilon$ 也合格。
即：判据对 $\sigma$ 的**取值**不敏感，只对 $\varepsilon/\sigma$ 敏感。 -/
theorem sigma_arbitrary {c ε σ : ℝ} (hc : 0 < c) (h : ErrorAcceptable ε σ) :
    ErrorAcceptable (c * ε) (c * σ) :=
  (scale_invariant hc).mpr h

/- 注（诚实标注，非已证命题）：
   「$\sigma$ 该取多少」——即哪一类问题该配哪个噪声尺度——属于**建模选择**，
   无法也不应在纯数学层证明。本文件所证的是：一旦 $\sigma$ 选定，
   判据的形式（§1）、单调性（§2）、非空性（§3）、伸缩不变性（§4）
   与既有判据的一致性（§5）全部成立且彼此协调。 -/

end ErrorCriterion

end Fate
