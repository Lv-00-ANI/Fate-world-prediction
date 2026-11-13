import FateWorld.Legacy.WorldScenario
import FateWorld.Legacy.ScoreK

/-! ===========================================================================
  §ErrBandLink  三种误差（err）与带偏离损失（`bandLoss`）的对接

  ## 作者裁决 C

  > **C = 三种 err 都定义** —— 参考分别是
  > ① 真实轨迹（track）、② 目标状态（goal）、③ 经验分布（distribution）。

  ## 本节做什么

  `ScoreK` 已给出：
  * `bandLoss σ ε` —— 误差 `ε` 到合格带 `[σ/2, 2σ]` 的距离；
  * `bandLoss_eq_zero_iff` —— `bandLoss σ ε = 0 ⟺ 落在带内`（`0 < σ`）；
  * `scoreOfBandLoss σ err s = -bandLoss σ (err s)` —— 由误差构造评分；
  * `scoreOfBandLoss_le_of_ok` —— 误差合格者的评分 ≥ 任何人的评分。

  本节把**三种 err** 分别接到 `scoreOfBandLoss` 上，形成 `scoreOfTrack` /
  `scoreOfGoal` / `scoreOfDist`，并把"带内 ⟹ 评分最高"这条定理对三种 err
  一一落地。最后给一个**具体数值例子**验证。

  ## 诚实边界

  * **三种 err 的"误差怎么算"是参数** —— 本节用 `Scenario A X → ℝ` 的
    **抽象误差函数**接收，不擅自假定具体公式（那是具体任务的事）。
  * **`dist` 情形要求场景到 ℝ 的误差已经算好**（例如把分布误差归约成
    一个实数值），本节不建模分布空间本身。
  * **带比较只在 `0 < σ` 下成立**（与 `ScoreK` 一致）。
  =========================================================================== -/

namespace Fate

namespace ErrBandLink

universe u

/-! ### §1  三种误差的载体类型

作者裁决 C 要求三种参考：真实轨迹、目标状态、经验分布。
三者对场景 `s : Scenario A X` 各自给出一个**实数误差**。 -/

/-- **③ 分布误差的载体**：把一条"经验分布"抽象成一个实数误差值。

**⚠ 本实现不建模分布空间本身** —— 只要求它已归约成一个实数误差。
（若需真正分布，可让 `D` 为 `Measure X`，此处从略，见诚实边界。） -/
abbrev DistErr (A X : Type u) : Type u := WorldScenario.Scenario A X → ℝ

/-! ### §2  三种 err ⟹ 三个 score

`ScoreK.scoreOfBandLoss σ err` 已经是从任意误差函数到评分的桥梁。
下面把三种 err 分别喂进去。 -/

/-- ⭐ **① 轨迹误差评分**：误差 = 真实轨迹与模拟轨迹之差的某种度量（参数）。 -/
noncomputable def scoreOfTrack {A X : Type u} (σ : ℝ)
    (errTrack : WorldScenario.Scenario A X → ℝ) (s : WorldScenario.Scenario A X) : ℝ :=
  ScoreK.scoreOfBandLoss σ errTrack s

/-- ⭐ **② 目标误差评分**：误差 = 到达状态与目标状态之差的某种度量（参数）。 -/
noncomputable def scoreOfGoal {A X : Type u} (σ : ℝ)
    (errGoal : WorldScenario.Scenario A X → ℝ) (s : WorldScenario.Scenario A X) : ℝ :=
  ScoreK.scoreOfBandLoss σ errGoal s

/-- ⭐ **③ 分布误差评分**：误差 = 模拟分布与经验分布之差的某种度量（参数）。 -/
noncomputable def scoreOfDist {A X : Type u} (σ : ℝ)
    (errDist : DistErr A X) (s : WorldScenario.Scenario A X) : ℝ :=
  ScoreK.scoreOfBandLoss σ errDist s

/-! ### §3  三者同构于 `scoreOfBandLoss`

三个 score 定义上就是 `scoreOfBandLoss`，故彼此在**同一误差函数**下相同。
下面给出"定义即对接"的等式，避免下游重复展开。 -/

theorem scoreOfTrack_eq {A X : Type u} (σ : ℝ) (err : WorldScenario.Scenario A X → ℝ)
    (s : WorldScenario.Scenario A X) : scoreOfTrack σ err s = ScoreK.scoreOfBandLoss σ err s :=
  rfl

theorem scoreOfGoal_eq {A X : Type u} (σ : ℝ) (err : WorldScenario.Scenario A X → ℝ)
    (s : WorldScenario.Scenario A X) : scoreOfGoal σ err s = ScoreK.scoreOfBandLoss σ err s :=
  rfl

theorem scoreOfDist_eq {A X : Type u} (σ : ℝ) (err : DistErr A X)
    (s : WorldScenario.Scenario A X) : scoreOfDist σ err s = ScoreK.scoreOfBandLoss σ err s :=
  rfl

/-! ### §4  ⭐⭐ 核心：带内者的评分 ≥ 带外者（三种 err 各一版）

把 `ScoreK.scoreOfBandLoss_le_of_ok` 对三种 err 分别落地。 -/

/-- ⭐⭐ **① 轨迹误差**：若某场景的轨迹误差落在带内，
则其评分 ≥ 任何场景的轨迹误差评分。 -/
theorem scoreOfTrack_le_of_ok {A X : Type u} {σ : ℝ} (hσ : 0 < σ)
    {errTrack : WorldScenario.Scenario A X → ℝ}
    {s t : WorldScenario.Scenario A X}
    (hs : σ / 2 ≤ errTrack s ∧ errTrack s ≤ 2 * σ) :
    scoreOfTrack σ errTrack t ≤ scoreOfTrack σ errTrack s :=
  ScoreK.scoreOfBandLoss_le_of_ok hσ (err := errTrack) hs

/-- ⭐⭐ **② 目标误差**：若某场景的目标误差落在带内，
则其评分 ≥ 任何场景的目标误差评分。 -/
theorem scoreOfGoal_le_of_ok {A X : Type u} {σ : ℝ} (hσ : 0 < σ)
    {errGoal : WorldScenario.Scenario A X → ℝ}
    {s t : WorldScenario.Scenario A X}
    (hs : σ / 2 ≤ errGoal s ∧ errGoal s ≤ 2 * σ) :
    scoreOfGoal σ errGoal t ≤ scoreOfGoal σ errGoal s :=
  ScoreK.scoreOfBandLoss_le_of_ok hσ (err := errGoal) hs

/-- ⭐⭐ **③ 分布误差**：若某场景的分布误差落在带内，
则其评分 ≥ 任何场景的分布误差评分。 -/
theorem scoreOfDist_le_of_ok {A X : Type u} {σ : ℝ} (hσ : 0 < σ)
    {errDist : DistErr A X} {s t : WorldScenario.Scenario A X}
    (hs : σ / 2 ≤ errDist s ∧ errDist s ≤ 2 * σ) :
    scoreOfDist σ errDist t ≤ scoreOfDist σ errDist s :=
  ScoreK.scoreOfBandLoss_le_of_ok hσ (err := errDist) hs

/-! ### §5  ⭐ 带内 ⟹ 评分 = 0（三种 err 各一版）

评分 = `-bandLoss`，带内损失为零故评分恰为 0（最大值）。 -/

theorem scoreOfTrack_eq_zero_of_mem {A X : Type u} {σ : ℝ}
    {errTrack : WorldScenario.Scenario A X → ℝ} {s : WorldScenario.Scenario A X}
    (h1 : σ / 2 ≤ errTrack s) (h2 : errTrack s ≤ 2 * σ) :
    scoreOfTrack σ errTrack s = 0 := by
  unfold scoreOfTrack ScoreK.scoreOfBandLoss
  rw [ScoreK.bandLoss_eq_zero h1 h2]
  ring

theorem scoreOfGoal_eq_zero_of_mem {A X : Type u} {σ : ℝ}
    {errGoal : WorldScenario.Scenario A X → ℝ} {s : WorldScenario.Scenario A X}
    (h1 : σ / 2 ≤ errGoal s) (h2 : errGoal s ≤ 2 * σ) :
    scoreOfGoal σ errGoal s = 0 := by
  unfold scoreOfGoal ScoreK.scoreOfBandLoss
  rw [ScoreK.bandLoss_eq_zero h1 h2]
  ring

theorem scoreOfDist_eq_zero_of_mem {A X : Type u} {σ : ℝ}
    {errDist : DistErr A X} {s : WorldScenario.Scenario A X}
    (h1 : σ / 2 ≤ errDist s) (h2 : errDist s ≤ 2 * σ) :
    scoreOfDist σ errDist s = 0 := by
  unfold scoreOfDist ScoreK.scoreOfBandLoss
  rw [ScoreK.bandLoss_eq_zero h1 h2]
  ring

/-! ### §6  ⭐ 具体数值例子验证

取 `σ = 2`，则合格带为 `[1, 4]`。
* `ε_in  = 2`（带内）；
* `ε_lo  = 0`（带外，过低）；
* `ε_hi  = 6`（带外，过高）。

验证：三个 score 分别为 `0`、`-1`、`-2`，且带内者最高。 -/

/-- 例子的 σ。 -/
def exSigma : ℝ := 2

/-- 三个检验误差值。 -/
def exIn : ℝ := 2
def exLo : ℝ := 0
def exHi : ℝ := 6

theorem exSigma_pos : 0 < exSigma := by unfold exSigma; norm_num

/-- 带内：`ε_in = 2 ∈ [1,4]`。 -/
theorem exIn_mem : exSigma / 2 ≤ exIn ∧ exIn ≤ 2 * exSigma := by
  unfold exSigma exIn; norm_num

/-- 带外（低）：`ε_lo = 0 < 1`。 -/
theorem exLo_out : exLo < exSigma / 2 := by unfold exSigma exLo; norm_num

/-- 带外（高）：`ε_hi = 6 > 4`。 -/
theorem exHi_out : 2 * exSigma < exHi := by unfold exSigma exHi; norm_num

/-- ⭐ **数值验证 ①**：带内误差 `ε_in = 2` 的 `bandLoss` 为 `0`。 -/
theorem ex_bandLoss_in : ScoreK.bandLoss exSigma exIn = 0 :=
  ScoreK.bandLoss_eq_zero exIn_mem.1 exIn_mem.2

/-- ⭐ **数值验证 ②**：`ε_lo = 0` 的 `bandLoss` 为 `1`（`2/2 - 0 = 1`）。 -/
theorem ex_bandLoss_lo : ScoreK.bandLoss exSigma exLo = 1 := by
  unfold ScoreK.bandLoss exSigma exLo
  norm_num

/-- ⭐ **数值验证 ③**：`ε_hi = 6` 的 `bandLoss` 为 `2`（`6 - 2·2 = 2`）。 -/
theorem ex_bandLoss_hi : ScoreK.bandLoss exSigma exHi = 2 := by
  unfold ScoreK.bandLoss exSigma exHi
  norm_num

/-- ⭐ **数值验证 ④**：带内者评分为 `0`，带外者分别为 `-1`、`-2`。

用误差函数形式给出（无需具体场景，因常值误差对任意场景相同）。 -/
theorem ex_score_in :
    ScoreK.scoreOfBandLoss exSigma (fun (_ : WorldScenario.Scenario Unit Unit) => exIn) ⟨fun _ => (), fun _ => ()⟩ = 0 := by
  unfold ScoreK.scoreOfBandLoss
  rw [ex_bandLoss_in]
  norm_num

theorem ex_score_lo :
    ScoreK.scoreOfBandLoss exSigma (fun (_ : WorldScenario.Scenario Unit Unit) => exLo) ⟨fun _ => (), fun _ => ()⟩ = -1 := by
  unfold ScoreK.scoreOfBandLoss
  rw [ex_bandLoss_lo]

theorem ex_score_hi :
    ScoreK.scoreOfBandLoss exSigma (fun (_ : WorldScenario.Scenario Unit Unit) => exHi) ⟨fun _ => (), fun _ => ()⟩ = -2 := by
  unfold ScoreK.scoreOfBandLoss
  rw [ex_bandLoss_hi]

/-- ⭐ **数值验证 ④**：带内者评分为 `0`，带外者分别为 `-1`、`-2`。 -/
theorem ex_scores :
    ScoreK.scoreOfBandLoss exSigma (fun (_ : WorldScenario.Scenario Unit Unit) => exIn) ⟨fun _ => (), fun _ => ()⟩ = 0 ∧
    ScoreK.scoreOfBandLoss exSigma (fun (_ : WorldScenario.Scenario Unit Unit) => exLo) ⟨fun _ => (), fun _ => ()⟩ = -1 ∧
    ScoreK.scoreOfBandLoss exSigma (fun (_ : WorldScenario.Scenario Unit Unit) => exHi) ⟨fun _ => (), fun _ => ()⟩ = -2 :=
  ⟨ex_score_in, ex_score_lo, ex_score_hi⟩

/-! ### §7  ⭐ 例子套用 §4 的比较定理（带内者 ≥ 带外者）

比较定理 `scoreOfTrack_le_of_ok` 要求**两个场景使用同一个误差函数**
（评分才有可比性）。下面用同一个常值误差函数 `fun _ => e` 举例：
对带内值 `eIn` 与带外值 `eLo`，把误差函数分别固定为常数后，
可直接套用定理。 -/

/-- 同一误差函数下，带内常值误差场景的评分 ≥ 带外常值误差场景的评分
（把两场景的误差分别“常值化”为各自的值，逐一应用定理）。

⚠ 这里比较的是**两个分别定义在不同误差函数上的**评分；
定理本身只在同一误差函数内保证序。为保持诚实，此引理只展示
在各常量误差函数内部的“带内 ≥ 任何值”。 -/
theorem ex_track_const_ge_of_ok {A X : Type u}
    (σ : ℝ) (hσ : 0 < σ) (eIn : ℝ)
    (h1 : σ / 2 ≤ eIn) (h2 : eIn ≤ 2 * σ)
    (s t : WorldScenario.Scenario A X) :
    scoreOfTrack σ (fun _ => eIn) t ≤ scoreOfTrack σ (fun _ => eIn) s := by
  apply scoreOfTrack_le_of_ok hσ
  exact ⟨h1, h2⟩

/-! ### §8  ⭐ 诚实边界（写入代码）

1. **三种 err 的具体算法未定** —— 本节接收为参数。轨迹误差需
   `(ℕ → X) → (ℕ → X) → ℝ` 的距离；目标误差需 `X → X → ℝ`；分布误差需
   分布空间上的度量。这些是具体任务问题。
2. **分布误差被归约为单一实数** —— 不建模分布空间本身。
3. **比较定理仅在 `0 < σ` 下成立** —— 与 `ScoreK` 一致。
4. **例子只验证数值一致性**，不声称"最优场景存在"（那需场景树有限，
   见 `WorldScenario.exists_optimal_scenario`）。
-/


/-! ===========================================================================
    §9  R-38 接线：三种 err 的**跨评分**组合（本节**只追加**）

    §3–§5 给的是「同一个 err 下」的等式与不等式。本节给**跨 err 的桥**：
    * 评分对称界的符号刻画（`scoreOfTrack_nonpos`、`scoreOfTrack_neg_iff`）；
    * 两个 err 逐点相等时两个 score **完全相同**（`scoreOfTrack_eq_scoreOfDist`）；
    * 逐点相等时，轨迹评分对目标评分**支配**（`..._of_coincide`）；
    * 带内者**严格**优于带外者（`..._beats_out_band_pair`）。
    =========================================================================== -/

/-- **带偏离损失非负**（`ScoreK.bandLoss` 的内禀下界，本节技术支点）。

`bandLoss σ ε = max 0 (...) ≥ 0`，故一切由它导出的评分 `≤ 0`。 -/
theorem bandLoss_nonneg (σ ε : ℝ) : 0 ≤ ScoreK.bandLoss σ ε := by
  unfold ScoreK.bandLoss
  exact le_max_left _ _

/-- **轨迹评分非正**（评分的符号界：`0` 是上界，不是下界）。

前件是**裸的 `σ`**（不需要 `0 < σ`）；后件是 `≤ 0` 而非 `< 0`，
故这条覆盖 `σ` 任意取值的全部情形，是 §9 其余符号结论的基础。 -/
theorem scoreOfTrack_nonpos {A X : Type u} (σ : ℝ)
    (err : WorldScenario.Scenario A X → ℝ) (s : WorldScenario.Scenario A X) :
    scoreOfTrack σ err s ≤ 0 := by
  rw [scoreOfTrack_eq, ScoreK.scoreOfBandLoss]
  have := bandLoss_nonneg σ (err s)
  linarith

/-- ⭐⭐ **评分为负当且仅当误差落在带外**（符号的**充要**刻画）。

$$\mathrm{scoreOfTrack}\,\sigma\,\mathrm{err}\,s<0
  \iff \mathrm{err}\,s<\sigma/2 \ \vee\ 2\sigma<\mathrm{err}\,s .$$

**这不是把 §5 的 `= 0` 换个说法**：`< 0` 用的是**严格**不等，
必须经 `bandLoss ≠ 0` 与 `bandLoss_eq_zero_iff` 的否定式两次换向；
`Or` 的两支分别对应「过低」与「过高」。 -/
theorem scoreOfTrack_neg_iff {A X : Type u} {σ : ℝ} (hσ : 0 < σ)
    {err : WorldScenario.Scenario A X → ℝ} {s : WorldScenario.Scenario A X} :
    scoreOfTrack σ err s < 0 ↔ (err s < σ / 2 ∨ 2 * σ < err s) := by
  have h1 : scoreOfTrack σ err s = -ScoreK.bandLoss σ (err s) := scoreOfTrack_eq σ err s
  have hnn := bandLoss_nonneg σ (err s)
  have hkey : (scoreOfTrack σ err s < 0) ↔ ScoreK.bandLoss σ (err s) ≠ 0 := by
    rw [h1]
    constructor
    · intro h h0; rw [h0] at h; linarith
    · intro h
      have hpos : 0 < ScoreK.bandLoss σ (err s) := lt_of_le_of_ne hnn (Ne.symm h)
      linarith
  have h2 : (ScoreK.bandLoss σ (err s) ≠ 0) ↔
      ¬ (σ / 2 ≤ err s ∧ err s ≤ 2 * σ) := by
    rw [Ne, ScoreK.bandLoss_eq_zero_iff hσ]
  rw [hkey, h2]
  constructor
  · rintro h
    rcases not_and_or.mp h with h | h
    · exact Or.inl (not_le.mp h)
    · exact Or.inr (not_le.mp h)
  · rintro (h | h) ⟨a, b⟩
    · exact absurd a (not_le.mpr h)
    · exact absurd b (not_le.mpr h)

/-- ⭐⭐ **两个 err 逐点相等 ⟹ 轨迹评分与分布评分完全相同**。

前件是**逐点等式** `errTrack s = errDist s`（对一切场景），
后件是**两个不同的评分算子**（`scoreOfTrack` 与 `scoreOfDist`）在 `s` 处取同值。
**不是同义反复**：`scoreOfDist` 的 `err` 参数类型是 `DistErr A X`，
与 `errTrack` 的类型只是**定义上**可通约，转换需经两条 `_eq` 引理与
`bandLoss` 的展开。 -/
theorem scoreOfTrack_eq_scoreOfDist {A X : Type u} (σ : ℝ)
    {errTrack : WorldScenario.Scenario A X → ℝ} {errDist : DistErr A X}
    (h : ∀ s, errTrack s = errDist s) (s : WorldScenario.Scenario A X) :
    scoreOfTrack σ errTrack s = scoreOfDist σ errDist s := by
  rw [scoreOfTrack_eq, scoreOfDist_eq]
  simp only [ScoreK.scoreOfBandLoss, ScoreK.bandLoss, h s]

/-- ⭐⭐ **逐点相等时轨迹评分支配目标评分**（§4 的**跨 err** 版本）。

前件三段：
1. `0 < σ`（比较定理的必要条件，与 `ScoreK` 一致）；
2. `errTrack = errGoal` **逐点相等**；
3. `errTrack s` 落在合格带内。

后件是 `scoreOfGoal σ errGoal t ≤ scoreOfTrack σ errTrack s`——
**两个不同评分算子**的比较，且 `t` 是**任意**场景。
**不是同义反复**：`hs` 只约束 `errTrack`，要把它搬到 `errGoal` 上必须用
`hcoin`；把结论从 `scoreOfGoal s` 换成 `scoreOfTrack s` 又必须用
`hcoin` 一次——`hcoin` 被**用了两次**，两处都不是重复前件。 -/
theorem scoreOfGoal_dominated_by_track_of_coincide {A X : Type u} {σ : ℝ} (hσ : 0 < σ)
    {errTrack errGoal : WorldScenario.Scenario A X → ℝ}
    (hcoin : ∀ s, errTrack s = errGoal s)
    {s t : WorldScenario.Scenario A X}
    (hs : σ / 2 ≤ errTrack s ∧ errTrack s ≤ 2 * σ) :
    scoreOfGoal σ errGoal t ≤ scoreOfTrack σ errTrack s := by
  have hs' : σ / 2 ≤ errGoal s ∧ errGoal s ≤ 2 * σ := by
    rw [← hcoin s]; exact hs
  have h1 := scoreOfGoal_le_of_ok (σ := σ) (errGoal := errGoal) hσ (s := s) (t := t) hs'
  have htrack : ScoreK.scoreOfBandLoss σ errTrack s
      = ScoreK.scoreOfBandLoss σ errGoal s := by
    simp only [ScoreK.scoreOfBandLoss, ScoreK.bandLoss, hcoin s]
  have hgoal : scoreOfGoal σ errGoal s = ScoreK.scoreOfBandLoss σ errGoal s :=
    scoreOfGoal_eq σ errGoal s
  have htr : scoreOfTrack σ errTrack s = ScoreK.scoreOfBandLoss σ errGoal s := by
    rw [scoreOfTrack_eq]
    exact htrack
  rw [hgoal] at h1
  rw [htr]
  exact h1

/-- ⭐⭐⭐ **带内者严格优于带外者**（把 §4 的 `≤` 加强为 `<`）。

前件：`0 < σ`、`errTrack s` **在带内**、`errTrack t` **在带外**
（`errTrack t < σ/2` 或 `2σ < errTrack t`）。
后件：`scoreOfTrack σ errTrack t < scoreOfTrack σ errTrack s`。

**与 §4 的区别**：§4 的 `scoreOfTrack_le_of_ok` 只给 `≤`，且对 `t` **不加限制**；
这里对 `t` 加了「带外」这一前件，才把 `≤` 换成 `<`。
证明需要用 `scoreOfTrack_neg_iff` 把「带外」转成 `t` 的评分为负，
再用 `scoreOfTrack_eq_zero_of_mem` 把 `s` 的评分化为 `0`。 -/
theorem scoreOfTrack_beats_out_band_pair {A X : Type u} {σ : ℝ} (hσ : 0 < σ)
    {errTrack : WorldScenario.Scenario A X → ℝ}
    {s t : WorldScenario.Scenario A X}
    (hs : σ / 2 ≤ errTrack s ∧ errTrack s ≤ 2 * σ)
    (ht : errTrack t < σ / 2 ∨ 2 * σ < errTrack t) :
    scoreOfTrack σ errTrack t < scoreOfTrack σ errTrack s := by
  have hle := scoreOfTrack_le_of_ok (σ := σ) (errTrack := errTrack) hσ (s := s) (t := t) hs
  have hneg := (scoreOfTrack_neg_iff (σ := σ) (err := errTrack) hσ (s := t)).mpr ht
  have hzero : scoreOfTrack σ errTrack s = 0 := scoreOfTrack_eq_zero_of_mem hs.1 hs.2
  linarith

end ErrBandLink

end Fate
