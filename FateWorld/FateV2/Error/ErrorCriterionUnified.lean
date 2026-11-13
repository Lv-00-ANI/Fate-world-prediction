import FateWorld.FateV2.Error.AttrAcceptable
import FateWorld.FateV2.Error.ErrorCriterion
import FateWorld.FateV2.Error.ScoreK
import FateWorld.FateV2.Error.FitBoundary
import FateWorld.FateV2.Error.ErrorDimUnified
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ErrorCriterionUnified.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 13 处，含 5 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Predict
open FateV2.Loop

/-
  判据的统一口径与桥接（对应论文 §8.2）

  带偏离判据「误差与噪声尺度同阶」在全库共有四处形态：三处是同一定义体的逐字重复

    AttrAcceptable ε σ      := σ/2 ≤ ε ∧ ε ≤ 2σ
    ErrorAcceptable ε σ     := σ/2 ≤ ε ∧ ε ≤ 2σ
    AttrAcceptableMirror ε σ := σ/2 ≤ ε ∧ ε ≤ 2σ

  第四处是 ℝ 值的带偏离损失 bandLoss σ ε := max 0 (max (σ/2 - ε) (ε - 2σ))。
  本模块以 ErrorAcceptable 为唯一权威口径（别名 Canonical），并把其余形态桥接到它：

    §1  三处 Prop 形态之间的桥接——因定义体逐字相同，这些桥是 Iff.rfl，属定义层面；
    §2  bandLoss 与区间判据的桥接。这里不是定义恒等（一个是 ℝ 值函数、一个是命题），
        需经 max 的极值刻画；结论同时去掉了 ScoreK 原定理的 0 < σ 前件；
    §2.4 乘性刻画：判据 ⟺ |log(ε/σ)| ≤ log 2，即「同阶」= 与 σ 的乘性距离不超过 2 倍；
    §3  判据（逐点谓词）与边界（剖面级极值谓词）的相互关系。二者互不蕴含，
        两个方向都有显式反例；唯一的正向联系是「边界点处判据必成立」，且它不是
        同义反复——需用 err ≥ 0 才能从 err γ = σ 得到 σ ≥ 0；
    §4  退化区：σ < 0 时判据与边界一致地空（故不是冲突，但此区判据毫无鉴别力，
        使用处必须显式要求 0 ≤ σ）；σ = 0 时判据退化为单点 ε = 0；
    §5  把上述结论汇编为一条可单点引用的合取定理。

  （下文 §n 指本文件内部分节，与论文节次无关。）

  注：§1 全部桥接是 Iff.rfl / rfl，属定义层面，不声称是数学贡献，只作口径统一的
     可引用入口；实质内容是 §2、§2.4、§3.2、§3.3 与 §4。本模块不改动既有模块。
     三处重复定义的真实病理不是语义分歧，而是重复定义加零下游引用。

  不取 `sorry` / `admit` / 自定义 `axiom`。
-/


namespace FateV2.Error

namespace ErrorCriterionUnified

noncomputable section

/-! ===========================================================================
  §1  唯一权威口径与 ①②③ 的桥接
  =========================================================================== -/

/-! ### §1.1 权威口径 -/

/-- **唯一权威口径**：别名指向 `FateV2.Error/ErrorCriterion.lean:51` 的 `ErrorAcceptable`。

`abbrev`（而非 `def`）⟹ `Canonical` 与 `ErrorAcceptable` 是**同一项**，
故本文件的一切 `Canonical` 结论对 `ErrorAcceptable` 直接可用，**无需转换**。

参数顺序：`(ε σ)` —— **误差在前、尺度在后**（与 ① ② ③ 一致，与 ④ 相反）。 -/
abbrev Canonical (ε σ : ℝ) : Prop := ErrorCriterion.ErrorAcceptable ε σ

/-- 权威口径的**展开**（与源文件 `FateV2.Error/ErrorCriterion.lean:51` 的定义体逐字一致）。 -/
theorem canonical_iff (ε σ : ℝ) : Canonical ε σ ↔ σ / 2 ≤ ε ∧ ε ≤ 2 * σ :=
  Iff.rfl

/-- 权威口径的区间刻画（与 `ErrorCriterion.errorAcceptable_iff_mem_Icc` 同陈述，
此处从权威别名再导出一次，以便只用 `Canonical` 的下游不必打开 `ErrorCriterion`）。 -/
theorem canonical_iff_mem_Icc (ε σ : ℝ) :
    Canonical ε σ ↔ ε ∈ Set.Icc (σ / 2) (2 * σ) :=
  Iff.rfl

/-! ### §1.2 ① 的桥接（`FateV2.Error/AttrAcceptable.lean:33`） -/

/-- **桥接 ① → 权威口径**：`AttrAcceptable ε σ ↔ Canonical ε σ`。

**⚠ 非实质**：二者定义体逐字相同，故为 `Iff.rfl`。（审计 B3 的第 1 处。） -/
theorem bridge_attrAcceptable (ε σ : ℝ) :
    AttrAcceptable.AttrAcceptable ε σ ↔ Canonical ε σ :=
  Iff.rfl

/-- 桥接 ① 的**外延相等**形式（比 `↔` 更强）：两个谓词是**同一函数**。 -/
theorem def_eq_attrAcceptable :
    AttrAcceptable.AttrAcceptable = (Canonical : ℝ → ℝ → Prop) :=
  rfl

/-! ### §1.3 ③ 的桥接（`FateV2.Error/ErrorCriterion.lean:158`） -/

/-- **桥接 ③ → 权威口径**：`AttrAcceptableMirror ε σ ↔ Canonical ε σ`。

**⚠ 非实质**：`Iff.rfl`。（审计 B3 的第 3 处。） -/
theorem bridge_attrAcceptableMirror (ε σ : ℝ) :
    ErrorCriterion.AttrAcceptableMirror ε σ ↔ Canonical ε σ :=
  Iff.rfl

/-- 桥接 ③ 的**外延相等**形式。 -/
theorem def_eq_attrAcceptableMirror :
    ErrorCriterion.AttrAcceptableMirror = (Canonical : ℝ → ℝ → Prop) :=
  rfl

/-! ### §1.4 为什么「三处互不相通」在语义上是**假问题**（登记为定理）

三处定义体逐字相同 ⟹ 它们之间**不存在强/弱关系可言**，
只有「谁被引用」的**工程问题**。下面把「不存在强弱关系」写成两条可检验的定理：
任一处成立 ⟺ 权威口径成立（不是单向蕴含）。 -/

/-- **三处判据两两之间也无强弱之分**（① ⟺ ③，均经权威口径）。

若有人主张「`AttrAcceptable` 比 `AttrAcceptableMirror` 强/弱」，此定理即为反驳：
二者互为充要，故**方向性不存在**。 -/
theorem attrAcceptable_iff_attrAcceptableMirror (ε σ : ℝ) :
    AttrAcceptable.AttrAcceptable ε σ ↔ ErrorCriterion.AttrAcceptableMirror ε σ :=
  Iff.rfl

/-- **权威性判据的「无偏向性」**：三处判据对 `(ε, σ)` 的真值函数完全相同。 -/
theorem three_definitions_agree :
    (∀ ε σ : ℝ, AttrAcceptable.AttrAcceptable ε σ ↔ Canonical ε σ) ∧
    (∀ ε σ : ℝ, ErrorCriterion.AttrAcceptableMirror ε σ ↔ Canonical ε σ) :=
  ⟨bridge_attrAcceptable, bridge_attrAcceptableMirror⟩

/-! ===========================================================================
  §2  ④ `ScoreK.bandLoss` 与权威口径的桥接（本文件最实质的部分）
  =========================================================================== -/

/-! ### §2.1 无条件桥接（去掉 `ScoreK` 原定理的 `0 < σ` 前件） -/

/-- **`bandLoss = 0` ⟺ 权威口径成立**，**对一切** σ, ε（无需 `0 < σ`）。

**⚠ 参数顺序**：`bandLoss` 是 `(σ, ε)`，`Canonical` 是 `(ε, σ)` —— 顺序相反。

**证明**（非平凡）：`max 0 X = 0 ↔ X ≤ 0`；再对 `max (σ/2 - ε) (ε - 2σ)` 用两次
`max_le_iff` 拆成两条不等式。

**⚠ 这加强** `FateV2.Error/ScoreK.lean` 的 `bandLoss_eq_zero_iff`（原定理要 `0 < σ`，
且其注释声称反向"需要 `0 < σ`"是错误的，见 §E 与 §2.2）。 -/
theorem bridge_bandLoss (σ ε : ℝ) :
    ScoreK.bandLoss σ ε = 0 ↔ Canonical ε σ := by
  unfold ScoreK.bandLoss
  constructor
  · intro h
    have h0 : max 0 (max (σ / 2 - ε) (ε - 2 * σ)) ≤ 0 := le_of_eq h
    have hm : max (σ / 2 - ε) (ε - 2 * σ) ≤ 0 := (max_le_iff.mp h0).2
    exact ⟨by linarith [(max_le_iff.mp hm).1], by linarith [(max_le_iff.mp hm).2]⟩
  · rintro ⟨h1, h2⟩
    exact max_eq_left (max_le (by linarith) (by linarith))

/-- **非负性**：`bandLoss` 恒非负（`max 0 _` 的左分量）。 -/
theorem bandLoss_nonneg (σ ε : ℝ) : 0 ≤ ScoreK.bandLoss σ ε :=
  le_max_left 0 _

/-- **二分法定理**：`bandLoss` 或为零（合格），或严格正（不合格）。 -/
theorem bandLoss_eq_zero_or_pos (σ ε : ℝ) :
    ScoreK.bandLoss σ ε = 0 ∨ 0 < ScoreK.bandLoss σ ε :=
  (eq_or_lt_of_le (bandLoss_nonneg σ ε)).elim (fun h => Or.inl h.symm) Or.inr

/-! ### §2.2 ⚠ 修正 `ScoreK` 注释的错误断言（σ = 0 时的真实行为） -/

/-- **σ = 0 时 `bandLoss` 就是绝对值**：`bandLoss 0 ε = |ε|`。

这**直接反驳** `FateV2.Error/ScoreK.lean:110-116` 注释中
「`σ = 0` 时 …… `bandLoss 0 0 = 0` 但 `ε ≠ 0` 也可能给出 `0`」的说法：
`|ε| = 0 ↔ ε = 0`，故截断**不会**误判。 -/
theorem bandLoss_zero_eq_abs (ε : ℝ) : ScoreK.bandLoss 0 ε = |ε| := by
  unfold ScoreK.bandLoss
  rw [show (0 : ℝ) / 2 - ε = -ε by ring, show ε - 2 * 0 = ε by ring]
  rcases le_total 0 ε with h | h
  · rw [abs_of_nonneg h, max_eq_right (by linarith : -ε ≤ ε), max_eq_right h]
  · rw [abs_of_nonpos h, max_eq_left (by linarith : ε ≤ -ε),
      max_eq_right (by linarith : (0 : ℝ) ≤ -ε)]

/-- **σ = 0 时无「截断误判」**：`bandLoss 0 ε = 0 ↔ ε = 0`（对照 §4.3 `canonical_zero_iff`）。 -/
theorem bandLoss_zero_eq_zero_iff (ε : ℝ) :
    ScoreK.bandLoss 0 ε = 0 ↔ ε = 0 := by
  rw [bandLoss_zero_eq_abs, abs_eq_zero]

/-! ### §2.3 `ScoreK` 原定理是本文件定理的特例（`0 < σ` 前件冗余） -/

/-- **`ScoreK.bandLoss_eq_zero_iff` 可由本文件的 `bridge_bandLoss` 导出**：
原定理的 `0 < σ` 前件**未被使用**。 -/
theorem bandLoss_eq_zero_iff_pos {σ : ℝ} (_hσ : 0 < σ) {ε : ℝ} :
    ScoreK.bandLoss σ ε = 0 ↔ σ / 2 ≤ ε ∧ ε ≤ 2 * σ :=
  (bridge_bandLoss σ ε).trans (canonical_iff ε σ)

/-- **`ErrorDimUnified.bandCriterion`（⑤）与权威口径一致**（同样无需 `0 < σ`）。 -/
theorem bridge_bandCriterion (σ ε : ℝ) :
    ErrorDimUnified.bandCriterion σ ε ↔ Canonical ε σ :=
  bridge_bandLoss σ ε

/-- `ErrorDimUnified.bandCriterion_iff`（带 `0 < σ`）是本桥的无条件特例。 -/
theorem bandCriterion_iff_pos {σ ε : ℝ} (_hσ : 0 < σ) :
    ErrorDimUnified.bandCriterion σ ε ↔ σ / 2 ≤ ε ∧ ε ≤ 2 * σ :=
  (bridge_bandCriterion σ ε).trans (canonical_iff ε σ)

/-! ### §2.4 新增刻画：判据 = 「与 σ 的**乘性距离**不超过 2 倍」

$\sigma/2 \le \varepsilon \le 2\sigma$ 在 $(\sigma,\varepsilon) > 0$ 上等价于
$\bigl|\log(\varepsilon/\sigma)\bigr| \le \log 2$ —— 即「$\varepsilon$ 与 $\sigma$
的比值落在 $[1/2, 2]$」，也就是**「同阶」的精确含义**。

这是与「双不等式」**形式完全不同**的刻画，故**不是同义反复**。 -/

/-- **对数刻画**：`0 < σ`、`0 < ε` 时，权威口径 ⟺ `|log(ε/σ)| ≤ log 2`。 -/
theorem canonical_iff_log {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    Canonical ε σ ↔ |Real.log (ε / σ)| ≤ Real.log 2 := by
  have hr : 0 < ε / σ := div_pos hε hσ
  have hexp1 : Real.exp (-Real.log 2) = (1 : ℝ) / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have hexp2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  have key1 : -Real.log 2 ≤ Real.log (ε / σ) ↔ σ / 2 ≤ ε := by
    rw [Real.le_log_iff_exp_le hr, hexp1]
    rw [le_div_iff₀ hσ]
    constructor
    · intro h; linarith
    · intro h; linarith
  have key2 : Real.log (ε / σ) ≤ Real.log 2 ↔ ε ≤ 2 * σ := by
    rw [Real.log_le_iff_le_exp hr, hexp2]
    rw [div_le_iff₀ hσ]
  have hab : (|Real.log (ε / σ)| ≤ Real.log 2) ↔
      (-Real.log 2 ≤ Real.log (ε / σ) ∧ Real.log (ε / σ) ≤ Real.log 2) := abs_le
  simp only [Canonical, ErrorCriterion.ErrorAcceptable]
  constructor
  · rintro ⟨a, b⟩; exact hab.mpr ⟨key1.mpr a, key2.mpr b⟩
  · intro h; exact ⟨key1.mp (hab.mp h).1, key2.mp (hab.mp h).2⟩

/-- **σ 是合格带的乘性中心**：`(σ/2)·(2σ) = σ²`，且 σ 自身合格（σ ≥ 0）。

⟹ 合格带是「以 σ 为**几何中心**、乘性半宽 2 倍」的对称带。 -/
theorem band_geometric_center {σ : ℝ} (hσ : 0 ≤ σ) :
    (σ / 2) * (2 * σ) = σ ^ 2 ∧ Canonical σ σ := by
  refine ⟨by ring, ?_⟩
  exact ErrorCriterion.self_acceptable hσ

/-! ===========================================================================
  §3  ⚠ 两判据的关系：逐点判据与 `IsFitBoundary`（剖面级极值）**互不蕴含**
  =========================================================================== -/

/-! ### §3.1 唯一的正向联系：**边界点处判据必成立**（真蕴含，非同义反复） -/

/-- **`IsFitBoundary` ⟹ 该点满足权威口径**。

前件是**剖面级极值断言**（`err γ = σ` 且 σ 是全局下界），
结论是**逐点不等式对**。**必须**用 `ErrProfileWeak.err_nonneg` 才能从
`err γ = σ` 得到 `σ ≥ 0`（否则 `σ/2 ≤ σ` 不成立）⟹ **非同义反复**。 -/
theorem isFitBoundary_implies_canonical {W : Core.ErrProfileWeak} {σ γ : ℝ}
    (h : Core.IsFitBoundary W σ γ) : Canonical (W.err γ) σ := by
  obtain ⟨h1, h2⟩ := h
  have hnn := Core.ErrProfileWeak.err_nonneg W γ
  rw [h1] at hnn
  simp only [Canonical, ErrorCriterion.ErrorAcceptable]
  rw [h1]
  constructor <;> linarith

/-- **边界的 σ 必非负**（`err ≥ 0` 的推论；与 §4.1 的退化区相接）。 -/
theorem sigma_nonneg_of_isFitBoundary {W : Core.ErrProfileWeak} {σ γ : ℝ}
    (h : Core.IsFitBoundary W σ γ) : 0 ≤ σ := by
  have hnn := Core.ErrProfileWeak.err_nonneg W γ
  rw [h.1] at hnn
  exact hnn

/-- **边界存在 ⟹ 存在满足判据的点**（存在形式）。 -/
theorem exists_canonical_of_hasFitBoundary {W : Core.ErrProfileWeak} {σ : ℝ}
    (h : Core.HasFitBoundary W σ) : ∃ γ, Canonical (W.err γ) σ := by
  obtain ⟨γ, hγ⟩ := h
  exact ⟨γ, isFitBoundary_implies_canonical hγ⟩

/-! ### §3.2 ⚠ 反例一：**边界存在，但判据并非在全体 γ 成立**

剖面 `profSqPlusOne`：`err γ = γ² + 1`，σ = 1。
* γ = 0 是边界点（`err 0 = 1`，且 `1 ≤ γ² + 1` 恒成立）；
* 但 γ = 2 处 `err = 5 > 2·1` ⟹ 判据**失败**。

⟹ `HasFitBoundary` **不蕴含**「判据在一切 γ 成立」。 -/

/-- 剖面 ①：`err γ = γ² + 1`（`bias = γ²`，`var = 1`）。 -/
def profSqPlusOne : Core.ErrProfileWeak where
  bias := fun γ => γ ^ 2
  var := fun _ => 1
  bias_nonneg := fun γ => sq_nonneg γ
  var_nonneg := fun _ => by norm_num

/-- `profSqPlusOne` 的误差展开。 -/
theorem profSqPlusOne_err (γ : ℝ) : profSqPlusOne.err γ = γ ^ 2 + 1 := by
  simp [Core.ErrProfileWeak.err, profSqPlusOne]

/-- `γ = 0` 是 `profSqPlusOne` 在 σ = 1 下的**边界点**。 -/
theorem profSqPlusOne_isFitBoundary : Core.IsFitBoundary profSqPlusOne 1 0 := by
  refine ⟨?_, ?_⟩
  · rw [profSqPlusOne_err]; norm_num
  · intro γ'
    rw [profSqPlusOne_err]
    nlinarith [sq_nonneg γ']

/-- `profSqPlusOne` 在 σ = 1 下**有边界**。 -/
theorem profSqPlusOne_hasBoundary : Core.HasFitBoundary profSqPlusOne 1 :=
  ⟨0, profSqPlusOne_isFitBoundary⟩

/-- **反例一定理**：`profSqPlusOne` 在 γ = 2 处**不满足**判据
（`err 2 = 5`，而合格带上界为 `2·1 = 2`）。 -/
theorem profSqPlusOne_canonical_fails : ¬ Canonical (profSqPlusOne.err 2) 1 := by
  rw [profSqPlusOne_err]
  norm_num [ErrorCriterion.ErrorAcceptable]

/-- **`HasFitBoundary` ⇏ 判据在全体 γ 成立**（反例封装）。 -/
theorem boundary_does_not_imply_criterion_uniform :
    ∃ (W : Core.ErrProfileWeak) (σ : ℝ),
      Core.HasFitBoundary W σ ∧ ∃ γ, ¬ Canonical (W.err γ) σ :=
  ⟨profSqPlusOne, 1, profSqPlusOne_hasBoundary, 2, profSqPlusOne_canonical_fails⟩

/-! ### §3.3 ⚠ 反例二：**判据在全体 γ 成立，但不存在边界**

剖面 `profThreeHalves`：`err ≡ 3/2`，σ = 1。
`3/2 ∈ [1/2, 2]` 对**每个** γ 成立（判据处处成立），
但没有任何 γ 使 `err γ = 1`（`3/2 ≠ 1`）⟹ 无边界。

⟹ 「判据处处成立」**不蕴含** `HasFitBoundary`。 -/

/-- 剖面 ②：`err ≡ 3/2`（`bias ≡ 3/2`，`var ≡ 0`）。 -/
def profThreeHalves : Core.ErrProfileWeak where
  bias := fun _ => 3 / 2
  var := fun _ => 0
  bias_nonneg := fun _ => by norm_num
  var_nonneg := fun _ => le_refl 0

/-- `profThreeHalves` 的误差恒为 `3/2`。 -/
theorem profThreeHalves_err (γ : ℝ) : profThreeHalves.err γ = 3 / 2 := by
  simp [Core.ErrProfileWeak.err, profThreeHalves]

/-- **判据在 `profThreeHalves` 上处处成立**（σ = 1）。 -/
theorem profThreeHalves_canonical_uniform (γ : ℝ) :
    Canonical (profThreeHalves.err γ) 1 := by
  rw [profThreeHalves_err]
  norm_num [ErrorCriterion.ErrorAcceptable]

/-- **`profThreeHalves` 在 σ = 1 下无边界**（因 `err ≡ 3/2 ≠ 1`，σ 从未被达到）。 -/
theorem profThreeHalves_noBoundary : ¬ Core.HasFitBoundary profThreeHalves 1 := by
  rintro ⟨γ, h1, _h2⟩
  rw [profThreeHalves_err] at h1
  norm_num at h1

/-- **判据处处成立 ⇏ 边界存在**（反例封装）。 -/
theorem criterion_uniform_does_not_imply_boundary :
    ∃ (W : Core.ErrProfileWeak) (σ : ℝ),
      (∀ γ, Canonical (W.err γ) σ) ∧ ¬ Core.HasFitBoundary W σ :=
  ⟨profThreeHalves, 1, profThreeHalves_canonical_uniform, profThreeHalves_noBoundary⟩

/-! ===========================================================================
  §4  ⚠ 退化区登记（σ < 0 与 σ = 0）
  =========================================================================== -/

/-! ### §4.1 σ < 0：判据**恒假** -/

/-- ⚠ **σ < 0 时判据无鉴别力**：对一切 ε，判据不成立
（合格区间 `[σ/2, 2σ]` 下界大于上界，为空集）。 -/
theorem canonical_false_of_neg {σ : ℝ} (hσ : σ < 0) (ε : ℝ) :
    ¬ Canonical ε σ := by
  simp only [Canonical, ErrorCriterion.ErrorAcceptable]
  rintro ⟨h1, h2⟩
  linarith

/-- ⚠ **σ < 0 时合格集为空**。 -/
theorem canonical_set_empty_of_neg {σ : ℝ} (hσ : σ < 0) :
    {ε : ℝ | Canonical ε σ} = ∅ := by
  ext ε
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact canonical_false_of_neg hσ ε

/-! ### §4.2 σ < 0：边界**必然不存在** -/

/-- ⚠ **σ < 0 时不存在边界**（`err ≥ 0` 与 `err γ = σ < 0` 矛盾）。 -/
theorem not_hasFitBoundary_of_neg {W : Core.ErrProfileWeak} {σ : ℝ} (hσ : σ < 0) :
    ¬ Core.HasFitBoundary W σ := by
  rintro ⟨γ, h1, _h2⟩
  have hnn := Core.ErrProfileWeak.err_nonneg W γ
  linarith

/-- **退化区一致性**（D.2 的定理形式）：σ < 0 时判据与边界**同时为空**。

⟹ 二者**不冲突**（一致地空），但**共同的盲区**须由使用处 `0 ≤ σ` 挡掉。 -/
theorem degeneracy_neg_consistent {W : Core.ErrProfileWeak} {σ : ℝ} (hσ : σ < 0) :
    (∀ ε, ¬ Canonical ε σ) ∧ ¬ Core.HasFitBoundary W σ :=
  ⟨canonical_false_of_neg hσ, not_hasFitBoundary_of_neg hσ⟩

/-! ### §4.3 σ = 0：判据退化为单点 `ε = 0` -/

/-- ⚠ **σ = 0 时判据 ⟺ `ε = 0`**（带退化为单点 `[0, 0]`）。 -/
theorem canonical_zero_iff {ε : ℝ} : Canonical ε 0 ↔ ε = 0 := by
  simp only [Canonical, ErrorCriterion.ErrorAcceptable]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; subst h; norm_num

/-- ⚠ **σ = 0 处判据与 `bandLoss` 完全一致**（`bandLoss 0 ε = |ε|` 故二者同判）。 -/
theorem canonical_zero_iff_bandLoss {ε : ℝ} :
    Canonical ε 0 ↔ ScoreK.bandLoss 0 ε = 0 :=
  (bridge_bandLoss 0 ε).symm

/-! ===========================================================================
  §5  汇编：**单点可引用结论**
  =========================================================================== -/

/-- **判据统一的合取汇编**（供下游单点引用）：

1. **三处判据（①②③）与权威口径互相充要**（实际上是同一谓词）；
2. **`bandLoss = 0` 无条件等价于权威口径**（`ScoreK` 的 `0 < σ` 前件冗余）；
3. **`bandCriterion`（⑤）与权威口径无条件等价**；
4. **σ < 0 时判据恒假**，故权威口径的**有效域须 `0 ≤ σ`**；
5. **边界点处判据必成立**（唯一的正向联系），但
   **`HasFitBoundary` 与「判据处处成立」互不蕴含**（两个反例见 §3）。

**⚠ 本定理是汇编，不是新数学**：它把上面已证的 ①②③④⑤ 打包，
使「判据已统一」这件事有一个**类型可检查**的凭证。 -/
theorem criterion_unified :
    -- ①②③ 互相充要（⟹ 不存在强弱之分，只是重复定义）
    (∀ ε σ : ℝ, AttrAcceptable.AttrAcceptable ε σ ↔ Canonical ε σ) ∧
    (∀ ε σ : ℝ, ErrorCriterion.AttrAcceptableMirror ε σ ↔ Canonical ε σ) ∧
    -- ④ 无条件等价（0<σ 前件冗余）
    (∀ σ ε : ℝ, ScoreK.bandLoss σ ε = 0 ↔ Canonical ε σ) ∧
    -- ⑤ 无条件等价
    (∀ σ ε : ℝ, ErrorDimUnified.bandCriterion σ ε ↔ Canonical ε σ) ∧
    -- 退化区：σ<0 判据恒假
    (∀ {σ : ℝ}, σ < 0 → ∀ ε : ℝ, ¬ Canonical ε σ) ∧
    -- 唯一的正向联系：边界点处判据必成立
    (∀ {W : Core.ErrProfileWeak} {σ γ : ℝ},
      Core.IsFitBoundary W σ γ → Canonical (W.err γ) σ) :=
  ⟨bridge_attrAcceptable, bridge_attrAcceptableMirror, bridge_bandLoss,
    bridge_bandCriterion, fun hσ ε => canonical_false_of_neg hσ ε,
    fun h => isFitBoundary_implies_canonical h⟩

/-- **B3 的「唯一权威口径」的最终表述**：权威口径就是 `σ/2 ≤ ε ≤ 2σ`，
且它就是 `bandLoss = 0`，也是（在 σ>0, ε>0 上）`|log(ε/σ)| ≤ log 2`。 -/
theorem canonical_three_faces (ε σ : ℝ) :
    (Canonical ε σ ↔ σ / 2 ≤ ε ∧ ε ≤ 2 * σ) ∧
    (Canonical ε σ ↔ ScoreK.bandLoss σ ε = 0) ∧
    (0 < σ → 0 < ε → (Canonical ε σ ↔ |Real.log (ε / σ)| ≤ Real.log 2)) :=
  ⟨canonical_iff ε σ, (bridge_bandLoss σ ε).symm,
    fun hσ hε => canonical_iff_log hσ hε⟩

end

end ErrorCriterionUnified

end FateV2.Error
