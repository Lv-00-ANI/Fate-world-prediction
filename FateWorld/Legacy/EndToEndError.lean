import FateWorld.Legacy.ScoreK
import FateWorld.Legacy.WorldScenario

/-! ===========================================================================
  §EndToEndError  端到端误差 + 逐层诊断误差：形式化「两者都报、不相加」

  ## 作者裁决 E（再述）

  > **误差量纲不需要统一，因为统一不可能（不同空间无自然嵌入）。**
  > **但「组合误差」要算 —— 方法是：端到端直接测 + 逐层各自算（用于诊断），
  > 两者都报、不相加。**
  > 这绕开了跨层相加的量纲问题。

  ## 本文件的内容（与任务书逐条对应）

  ### ① 端到端误差 `EndToEndError`
  `e2e : Data → ℝ` —— **从输入数据到最终预测**的总体误差，
  **直接测量**，**不经过任何中间层求和**。
  （`WorldScenario.Scenario` 的轨迹 `traj` 就是「最终预测」的载体，
  故 `e2e` 是 `Scenario A X → ℝ`，直接读轨迹 / 参考量，不读 `plan`。）

  ### ② 逐层诊断误差 `LayerErr ι`
  每条误差项带**自己的尺度** `σ i`：
  ```lean
  structure LayerErr (ι : Type u) where
    err : ι → ℝ      -- 逐层误差读数
    σ   : ι → ℝ      -- 逐层噪声尺度（各自量纲）
  ```
  因为「不同空间无自然嵌入」，`err i` 与 `err j` **不可相加**（见 `ErrorDimUnified`
  的 `crossTier_incomparable`：各档合格不推出和合格）。

  ### ③ ⭐ 关键：**没有通用传播律**
  形式化：把一个「有端到端误差 + 有逐层剖面」的系统记为 `LayeredSystem ι D`。
  若存在**一个**把逐层剖面映到端到端误差的函数 `f`（跨系统、跨数据统一），
  那就是一条「通用传播律」：
  ```lean
  def HasPropagationLaw (ι D : Type u) : Prop :=
    ∃ f : LayerErr ι → ℝ, ∀ (sys : LayeredSystem ι D) (d : D), sys.e2e d = f (sys.layer d)
  ```
  **本节证明**：

  * `hasPropagationLaw_iff_determined` —— **等价刻画**：
    存在传播律 ⟺ 逐层剖面**唯一决定**端到端误差（「决定」即 `Determined`）。
    **⟹ 于是「无传播律」与「存在同剖面不同 e2e 的反例」是同一件事。**
  * `same_layer_diff_e2e` / `not_determined` / `no_propagation_law` ——
    **显式反例**：两个系统逐层剖面**完全相同**（`err ≡ 1, σ ≡ 1`），
    但端到端误差分别为 `0` 与 `5`。
    **⟹ 这既是否定命题 `¬ HasPropagationLaw`，也是任务书要求的「反例」退路，
    二者在此被证为等价（`no_law_iff_counterexample`）。**

  ### ④ 双指标（门槛 `σ₂` / 最优 `σ₁`）用于端到端误差
  * `IsGateOk σ₂ e2e` —— **门槛指标**：端到端误差落在 `[σ₂/2, 2σ₂]`（裁决 K 的带）；
    `gateOk_iff_bandLoss` 证明它**精确等于** `ScoreK.bandLoss σ₂ e2e = 0`。
  * `IsOptimalGap σ₁ e2e e2eBest` —— **最优差距指标**：所选系统端到端误差
    距**最优可达** `e2eBest` 不超过 `σ₁`。

  ## 诚实边界（写入代码）

  * **`e2e` 的具体公式是参数**（由具体任务给出）—— 本文件给的是**结构**与**不可组合性**，
    不虚构具体误差数值。
  * **反例取自抽象系统空间** —— 它说明「逐层剖面 → 端到端误差」不是单值的，
    故任何「把逐层误差加起来当端到端误差」的做法在**一般情形**下都不成立。
    它**不**排除在某些**受限**情形下存在传播律（例如所有系统共享同一 `f` 的特例，
    见 `hasPropagationLaw_of_const`）；那正是「两者都报」而非「证其相等」的理由。
  * **`σ₂` / `σ₁` 的取值**属于建模选择，本文件只给判据的**形式**与其**性质**。
  * **零 `sorry` / 零 `admit` / 零 `axiom`；不改 `Fate/`。**
  =========================================================================== -/

namespace Fate

namespace EndToEndError

universe u

/-! ### §1 ⭐ 逐层诊断误差（每层带自己的尺度） -/

/-- ⭐ **逐层误差剖面**：一个指标族 `ι`，每项一个误差读数 `err i` 与一个尺度 `σ i`。

**⚠ 关键**：`σ i` 是**逐项的** —— 不同层可能处不同量纲的空间，**不可跨层相加**。 -/
structure LayerErr (ι : Type u) where
  /-- 逐层误差读数。 -/
  err : ι → ℝ
  /-- 逐层噪声尺度（各自量纲）。 -/
  σ : ι → ℝ

/-- ⭐ **逐层合格**：第 `i` 层在自己的尺度 `σ i` 下进带。

⟹ 这里**只做逐层判定**，**不做跨层求和** —— 正是裁决 E 的「逐层各自算」。 -/
def LayerOk (L : LayerErr ι) (i : ι) : Prop :=
  L.σ i / 2 ≤ L.err i ∧ L.err i ≤ 2 * L.σ i

/-- ⭐ **逐层合格 ⟺ 该层带偏离损失为零**（`0 < σ i`）。

⟹ 逐层诊断与 `ScoreK.bandLoss` 对接，且**每一层尺度独立**。 -/
theorem layerOk_iff_bandLoss {L : LayerErr ι} {i : ι} (hσ : 0 < L.σ i) :
    (L.σ i / 2 ≤ L.err i ∧ L.err i ≤ 2 * L.σ i) ↔
      ScoreK.bandLoss (L.σ i) (L.err i) = 0 :=
  (ScoreK.bandLoss_eq_zero_iff hσ).symm

/-! ### §2 ⭐ 端到端误差 + 分层系统

「端到端误差」`e2e : D → ℝ` 是**直接测量**，与逐层剖面并列存放，**互不派生**。 -/

/-- ⭐⭐ **分层系统**：同时携带
* `e2e : D → ℝ` —— **端到端误差**（直接测，不经中间层求和）；
* `layer : D → LayerErr ι` —— **逐层诊断误差**（每层自己尺度）。

**⟹ 两者并列，`e2e` 不由 `layer` 计算 —— 这是裁决 E 的「不相加」。** -/
structure LayeredSystem (ι : Type u) (D : Type u) where
  /-- 端到端误差：数据 `d` 上，从输入到最终预测的总体误差（直接测）。 -/
  e2e : D → ℝ
  /-- 逐层诊断误差：数据 `d` 上的逐层剖面（每层自己尺度）。 -/
  layer : D → LayerErr ι

/-! ### §3 ⭐⭐ 通用传播律及其「不存在」的等价刻画

**通用传播律**：存在**一个** `f : LayerErr ι → ℝ`，对**所有**系统 **与所有**数据，
把逐层剖面映成端到端误差。 -/

/-- ⭐⭐ **通用传播律**：存在单一 `f`，跨系统、跨数据把逐层剖面映成端到端误差。

$$\exists f,\ \forall sys\ d,\ \mathrm{e2e}(sys, d) = f(\mathrm{layer}(sys, d))$$ -/
def HasPropagationLaw (ι : Type u) (D : Type u) : Prop :=
  ∃ f : LayerErr ι → ℝ, ∀ (sys : LayeredSystem ι D) (d : D), sys.e2e d = f (sys.layer d)

/-- ⭐⭐ **「决定」性质**：逐层剖面相同的两个（系统, 数据）对，端到端误差必须相同。 -/
def Determined (ι : Type u) (D : Type u) : Prop :=
  ∀ (sys t : LayeredSystem ι D) (d e : D), sys.layer d = t.layer e → sys.e2e d = t.e2e e

/-- ⭐⭐⭐ **核心等价**：**存在传播律 ⟺ 逐层剖面唯一决定端到端误差。**

**⟹ 这是任务书第 3 条的关键结构定理**：
「无通用传播律」与「存在同剖面不同端到端的反例」**是同一件事**。 -/
theorem hasPropagationLaw_iff_determined : HasPropagationLaw ι D ↔ Determined ι D := by
  constructor
  · -- 传播律 ⟹ 决定：两边都用同一个 `f`。
    rintro ⟨f, hf⟩ sys t d e h
    rw [hf sys d, hf t e, h]
  · -- 决定 ⟹ 传播律：用选择函数取一个代表剖面来定义 `f`。
    intro hdet
    classical
    refine ⟨fun l => if hl : ∃ (p : LayeredSystem ι D × D), p.1.layer p.2 = l then
        (Classical.choose hl).1.e2e (Classical.choose hl).2 else 0, ?_⟩
    intro sys d
    have hmem : ∃ (p : LayeredSystem ι D × D), p.1.layer p.2 = sys.layer d :=
      ⟨⟨sys, d⟩, rfl⟩
    show sys.e2e d =
      (if hl : ∃ (p : LayeredSystem ι D × D), p.1.layer p.2 = sys.layer d then
        (Classical.choose hl).1.e2e (Classical.choose hl).2 else 0)
    rw [dif_pos hmem]
    exact hdet sys (Classical.choose hmem).1 d (Classical.choose hmem).2
      (Classical.choose_spec hmem).symm

/-! ### §4 ⭐⭐⭐ 反例：同逐层剖面，不同端到端误差

取 `ι = Unit`（一层）、`D = Unit`（一个数据点）。
两个系统 `sysA`（端到端 `0`）与 `sysB`（端到端 `5`），
**逐层剖面完全相同**（`err ≡ 1`、`σ ≡ 1`）。 -/

/-- 反例用系统 A：端到端 `0`，单层剖面 `err ≡ 1, σ ≡ 1`。 -/
def sysA : LayeredSystem Unit Unit :=
  { e2e := fun _ => 0, layer := fun _ => { err := fun _ => 1, σ := fun _ => 1 } }

/-- 反例用系统 B：端到端 `5`，单层剖面与 `sysA` **完全相同**。 -/
def sysB : LayeredSystem Unit Unit :=
  { e2e := fun _ => 5, layer := fun _ => { err := fun _ => 1, σ := fun _ => 1 } }

/-- ⭐⭐⭐ **反例主体**：逐层剖面相同，端到端误差不同。 -/
theorem same_layer_diff_e2e :
    sysA.layer () = sysB.layer () ∧ sysA.e2e () ≠ sysB.e2e () := by
  constructor
  · rfl
  · intro h
    norm_num [sysA, sysB] at h

/-- ⭐⭐ **决定性质不成立**（直接由反例得出）。 -/
theorem not_determined : ¬ Determined Unit Unit := by
  intro hdet
  have := hdet sysA sysB () () rfl
  exact same_layer_diff_e2e.2 this

/-- ⭐⭐⭐ **【关键】不存在通用传播律**：`¬ ∃ f, ∀ 情形, e2e = f(逐层误差)`。 -/
theorem no_propagation_law : ¬ HasPropagationLaw Unit Unit := by
  rw [hasPropagationLaw_iff_determined]
  exact not_determined

/-- ⭐⭐⭐ **【任务书要求的等价】「无传播律」⟺「存在同剖面不同端到端的反例」。**

⟹ 这两条路线（否定通用传播律 / 举反例）**在本形式化中是同一个命题**。 -/
theorem no_law_iff_counterexample :
    ¬ HasPropagationLaw Unit Unit ↔
      ∃ (sys t : LayeredSystem Unit Unit) (d e : Unit),
        sys.layer d = t.layer e ∧ sys.e2e d ≠ t.e2e e := by
  constructor
  · intro h
    exact ⟨sysA, sysB, (), (), same_layer_diff_e2e.1, same_layer_diff_e2e.2⟩
  · rintro ⟨sys, t, d, e, hl, he⟩ hlaw
    rw [hasPropagationLaw_iff_determined] at hlaw
    exact he (hlaw sys t d e hl)

/-! ### §5 边界：**受限**系统族下传播律可以存在（故只能「两者都报」）

上面的否定是针对 `HasPropagationLaw`（量化**所有** `LayeredSystem`）而言的「一般情形」。
若**限定**系统族到「由同一 `f` 生成」的子类 `FromLaw f`，则传播律**平凡存在**。
这说明本文件**不**主张「传播律永不成立」，而只主张「它在**全部系统上**不成立」——
这正是「两者都报」而非「证其相等」的根据。 -/

/-- ⭐ **由 `f` 生成的系统族**：`e2e` 恰为 `f` 作用于逐层剖面。

⟹ 这是「受限情形」，在其上传播律存在（见 `fromLaw_hasPropagationLaw`）。 -/
def FromLaw {ι : Type u} (f : LayerErr ι → ℝ) (D : Type u) :
    LayeredSystem ι D → Prop :=
  fun sys => ∀ d, sys.e2e d = f (sys.layer d)

/-- ⭐⭐ **边界定理**：若系统族被限定到 `FromLaw f`，则传播律存在。

⟹ 「无传播律」的否定**只对一般情形**成立；受限族中可以对齐 ——
故两个指标必须**都报**，不能用等式把逐层诊断替成端到端。 -/
theorem fromLaw_hasPropagationLaw {ι : Type u} (f : LayerErr ι → ℝ) (D : Type u)
    {sys : LayeredSystem ι D} (h : ∀ d, sys.e2e d = f (sys.layer d)) :
    ∃ g : LayerErr ι → ℝ, ∀ d : D, sys.e2e d = g (sys.layer d) :=
  ⟨f, h⟩

/-! ### §6 ⭐⭐ 双指标（门槛 `σ₂` / 最优 `σ₁`）用于端到端误差

裁决 K 的带判据在这里拆成两个**并列**指标，都作用在**端到端误差** `e2e` 上：

| 指标 | 定义 | 含义 |
|---|---|---|
| **门槛** `IsGateOk σ₂ e2e` | `σ₂/2 ≤ e2e ≤ 2σ₂` | 端到端误差是否「刚好处在拟合/过拟合边界」|
| **最优差距** `IsOptimalGap σ₁ e2e e2eBest` | `e2eBest ≤ e2e ∧ e2e - e2eBest ≤ σ₁` | 所选系统的端到端误差距**最优可达** `e2eBest` 不超过 `σ₁` |

**关键区别**：`σ₂` 判「相对于噪声尺度合不合格」；`σ₁` 判「相对于最优解差多少」。
两者尺度不同，**不相加**（这正是裁决 E）。 -/

/-- ⭐ **门槛指标**：端到端误差落在裁决 K 的带 `[σ₂/2, 2σ₂]`。 -/
def IsGateOk (σ₂ ε : ℝ) : Prop := σ₂ / 2 ≤ ε ∧ ε ≤ 2 * σ₂

/-- ⭐⭐ **门槛 ⟺ 带偏离损失为零**（`0 < σ₂`）—— 与 `ScoreK.bandLoss` 对接。 -/
theorem gateOk_iff_bandLoss {σ₂ : ℝ} (hσ₂ : 0 < σ₂) {ε : ℝ} :
    IsGateOk σ₂ ε ↔ ScoreK.bandLoss σ₂ ε = 0 :=
  (ScoreK.bandLoss_eq_zero_iff hσ₂).symm

/-- ⭐ **最优差距指标**：所选系统的端到端误差 `ε` 不低于最优 `εbest`（不可能低于最小值），
且距最优不超过 `σ₁`。 -/
def IsOptimalGap (σ₁ ε εbest : ℝ) : Prop := εbest ≤ ε ∧ ε - εbest ≤ σ₁

/-- ⭐ **最优差距给上界**：`ε ≤ εbest + σ₁`。 -/
theorem optimalGap_le {σ₁ ε εbest : ℝ} (h : IsOptimalGap σ₁ ε εbest) :
    ε ≤ εbest + σ₁ := by
  unfold IsOptimalGap at h
  linarith [h.2]

/-- ⭐ **最优差距非负**：`0 ≤ ε - εbest`。 -/
theorem optimalGap_nonneg {ε εbest : ℝ} (h : IsOptimalGap 0 ε εbest) :
    0 ≤ ε - εbest := by
  unfold IsOptimalGap at h
  linarith [h.1]

/-- ⭐⭐ **双指标同报（不相加）的形式接口**：对端到端误差 `ε`，
同时报其门槛判定与最优差距判定为一个 `Prop` **合取**（并列，**非求和**）。 -/
def DualReport (σ₂ σ₁ ε εbest : ℝ) : Prop :=
  IsGateOk σ₂ ε ∧ IsOptimalGap σ₁ ε εbest

/-- ⭐⭐ **双指标可同时成立**（一致性）：若 `εbest` 已在门槛带内，且 `ε` 距 `εbest` 不超过 `σ₁`，
并且这个差距不会把 `ε` 推出门槛带的上界（额外的可检条件 `εbest + σ₁ ≤ 2*σ₂`），
则 `ε` 的门槛与最优差距**可同时报**。

**⟹ 这是「两个都报」的最小可检验内容**：它们**不矛盾**，只是**不同尺度**的并列判定。
**⚠ 必须显式要求上界不被差距顶出** —— 否则 `σ₁` 很大时 `ε` 会溢出门槛带，
这正是「两指标不相加」的体现（不能假设两者自动兼容）。 -/
theorem dualReport_consistent {σ₂ σ₁ ε εbest : ℝ}
    (hgate : IsGateOk σ₂ εbest) (hgap : εbest ≤ ε) (hσ₁ : ε - εbest ≤ σ₁)
    (hbound : εbest + σ₁ ≤ 2 * σ₂) :
    DualReport σ₂ σ₁ ε εbest := by
  refine ⟨?_, hgap, hσ₁⟩
  unfold IsGateOk at hgate ⊢
  constructor <;> linarith [hgate.1, hgate.2]

/-- ⭐⭐ **针对端到端误差的双指标陈述（任务书第 4 条）**：
存在一个评分方式使「端到端误差合格者评分不低于任何不合格者」，
且该评分直接由 `ScoreK.scoreOfBandLoss` 施加于**端到端误差** `e2e` 得到。

⟹ 门槛指标 `σ₂` 直接接上 `Policy.score`；最优差距 `σ₁` 另作诊断。 -/
theorem gate_of_scoreOfBandLoss_le {A X : Type u} {σ₂ : ℝ} (hσ₂ : 0 < σ₂)
    {e2e : WorldScenario.Scenario A X → ℝ} {s t : WorldScenario.Scenario A X}
    (hs : IsGateOk σ₂ (e2e s)) :
    ScoreK.scoreOfBandLoss σ₂ e2e t ≤ ScoreK.scoreOfBandLoss σ₂ e2e s :=
  ScoreK.scoreOfBandLoss_le_of_ok hσ₂ ⟨hs.1, hs.2⟩

/-- ⭐⭐⭐ **总结（任务书四条）**：
1. **端到端误差**直接定义（`LayeredSystem.e2e`，不经中间层求和）；
2. **逐层诊断**是记录结构 `LayerErr`，每层带自己尺度 `σ i`；
3. **无通用传播律** `¬ HasPropagationLaw`（且等价于存在同剖面不同端到端的反例）；
4. **双指标**（门槛 `σ₂` / 最优 `σ₁`）作用于端到端误差，门槛精确等于 `bandLoss = 0`。 -/
theorem endToEnd_summary :
    (¬ HasPropagationLaw Unit Unit) ∧
    (¬ HasPropagationLaw Unit Unit ↔
      ∃ (sys t : LayeredSystem Unit Unit) (d e : Unit),
        sys.layer d = t.layer e ∧ sys.e2e d ≠ t.e2e e) ∧
    (∀ {σ₂ : ℝ}, 0 < σ₂ → ∀ {ε : ℝ}, IsGateOk σ₂ ε ↔ ScoreK.bandLoss σ₂ ε = 0) :=
  ⟨no_propagation_law, no_law_iff_counterexample,
   fun hσ₂ => gateOk_iff_bandLoss hσ₂⟩

end EndToEndError

end Fate
