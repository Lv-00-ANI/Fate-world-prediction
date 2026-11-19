import FateWorld.FateV2.Rules.StatAlpha
/-!
  # Rules · StatAlphaConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/StatAlphaConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：StatAlpha
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §Stat α 的**统计版**接入 `LawRule` 主链（消费模块）

  ## 被消费的模块

  `StatAlpha`（见其文件头）：经验条件核 + 置信带 α，主判据
  `isPoint_iff_all_zero_radius`、`diracRule_iff_zero_and_pure`。
  其 §6 明确登记一**缺口**：`freqToMeasure` 的**单射性未证**，
  「频率层 `IsPointFreq` 与 `LawRule.IsPoint` 的等价」属未闭合项。

  ## 本文件做什么

  1. `freqToMeasure_singleton`（**技术核心**）：有限 $Y$ + `MeasurableSingletonClass` 下
     $$\left(\textstyle\sum_y f(y)\delta_y\right)(\{y_0\})=\mathrm{ofReal}(f\,y_0).$$
  2. `freqToMeasure_injOn`：**概率向量上 `freqToMeasure` 单射** ——
     即 `StatAlpha` §6 登记缺口的**闭合**（在 `0 ≤ f` 前提下）。
  3. `statLawRule`：把带宽球经 `freqToMeasure` **推前**成真正的 `LawRule`。
  4. `statLawRule_isPoint_of_zero_radius`：零半径 ⟹ `LawRule.IsPoint`
     （**不需要单射**，是「像集」方向的直接推理）。
  5. `statLawRule_isPoint_iff`：`LawRule.IsPoint` ⟺ `IsPointFreq`
     （**用 2 的单射**，闭合 §6 缺口）。
  6. `statLawRule_deterministic_iff`：与 `LawRule.Deterministic` 对齐。
  7. `statLawRule_not_deterministic_of_pos_radius`：正半径、$|Y|\ge2$ ⟹
     推前的规律**不是**确定性规律（统计版的**可证伪性**）。

  ## 诚实边界

  * `MeasurableSingletonClass Y` 是**必需**的（`dirac_apply'` 要 `MeasurableSet {y₀}`），
    非本文件可省。`StatAlpha` 原文只要求 `[Fintype Y]`。
  * 单射性只在 `0 ≤ f`（**概率向量**）上成立；一般 $Y\to\mathbb R$ 上
    `ofReal` 把负数压成 $0$，故**不单射**（本文件未证该反例，仅登记）。
  * 本文件**不声称**任何统计前提（`ρ` 覆盖真核的概率断言），
    与 `StatAlpha` 诚实边界 1 一致。
  =========================================================================== -/

namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
namespace StatAlpha

open Finset

variable {C X Y : Type*} [DecidableEq C] [DecidableEq X] [DecidableEq Y] [Fintype Y]

/-! ===========================================================================
    §1  技术核心：单点求值
    =========================================================================== -/

/-- ⭐ **单点求值**：$\left(\sum_y f(y)\,\delta_y\right)(\{y_0\})=\mathrm{ofReal}(f\,y_0)$。

这是 §6 缺口的**唯一技术障碍**：一旦能在单点上求值，系数即可逐个还原。 -/
theorem freqToMeasure_singleton [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (f : Y → ℝ) (y₀ : Y) :
    freqToMeasure (Y := Y) f ({y₀} : Set Y) = ENNReal.ofReal (f y₀) := by
  rw [freqToMeasure, MeasureTheory.Measure.finsetSum_apply]
  have hstep : ∀ y ∈ (Finset.univ : Finset Y),
      (ENNReal.ofReal (f y) • (MeasureTheory.Measure.dirac y : MeasureTheory.Measure Y))
      ({y₀} : Set Y) = if y = y₀ then ENNReal.ofReal (f y) else 0 := by
    intro y _
    rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.dirac_apply' y
      (measurableSet_singleton y₀), smul_eq_mul]
    by_cases h : y = y₀
    · subst h; simp
    · simp [h]
  rw [Finset.sum_congr rfl hstep]
  simp

/-! ===========================================================================
    §2  ⭐ `freqToMeasure` 在概率向量上单射（**闭合 `StatAlpha` §6 登记的缺口**）
    =========================================================================== -/

/-- ⭐⭐ **概率向量上 `freqToMeasure` 单射**。

`StatAlpha` 文件头诚实边界 3 / §6 把「`freqToMeasure` 的单射性」登记为**未证缺口**；
本定理在 `0 ≤ f`、`0 ≤ g` 前提下**闭合**该缺口
（一般 `Y → ℝ` 上 `ofReal` 把负数压为 $0$，**不**单射）。 -/
theorem freqToMeasure_injOn [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (f g : Y → ℝ) (hf : ∀ y, 0 ≤ f y) (hg : ∀ y, 0 ≤ g y)
    (h : freqToMeasure (Y := Y) f = freqToMeasure (Y := Y) g) : f = g := by
  funext y
  have hcongr := congrArg (fun μ : MeasureTheory.Measure Y => μ ({y} : Set Y)) h
  rw [freqToMeasure_singleton, freqToMeasure_singleton] at hcongr
  exact (ENNReal.ofReal_eq_ofReal_iff (hf y) (hg y)).mp hcongr

/-! ===========================================================================
    §3  把带宽球推前成真 `LawRule`
    =========================================================================== -/

variable {CX : CtxSpace} {SX : StateSpace} {OY : OutSpace}
variable [DecidableEq CX.Carrier] [DecidableEq SX.Carrier] [DecidableEq OY.Carrier]
variable [Fintype OY.Carrier]

/-- ⭐ **统计版规则**（真 `LawRule`）：把带宽球经 `freqToMeasure` 推前。

即 $\alpha_{\text{stat}}$ 的**规则层像**：
$\text{Rule}(c,x)=\{\,\text{freqToMeasure}(f)\mid f\in\mathrm{Band}_{c,x}\,\}$。

外层类型用 `Y.Carrier` 作 `CtxSpace`/`StateSpace` 的载体，使构造与
`StatAlpha.Data` 的三元组 $(c,x,y)$ 直接对齐。 -/
noncomputable def statLawRule [MeasurableSpace OY.Carrier]
    (D : StatAlpha.Data CX.Carrier SX.Carrier OY.Carrier) (ρ : StatAlpha.Radius CX.Carrier SX.Carrier) :
    LawRule.LawRule CX SX OY :=
  fun c x => freqToMeasure (Y := OY.Carrier) '' (StatAlpha.StatRule D ρ c x)

/-- 推前规则的成员判定（定义展开，便于下游）。 -/
theorem mem_statLawRule [MeasurableSpace OY.Carrier] {D : StatAlpha.Data CX.Carrier SX.Carrier OY.Carrier}
    {ρ : StatAlpha.Radius CX.Carrier SX.Carrier} {c : CX.Carrier} {x : SX.Carrier}
    {μ : MeasureTheory.Measure OY.Carrier} :
    μ ∈ statLawRule D ρ c x ↔
      ∃ f ∈ StatAlpha.StatRule D ρ c x, freqToMeasure (Y := OY.Carrier) f = μ :=
  Iff.rfl

/-! ===========================================================================
    §4  ⭐ 接入 `LawRule.IsPoint` 主链
    =========================================================================== -/

/-- ⭐⭐ **零半径 ⟹ `LawRule.IsPoint`**（**不需要单射**）。

「像集」保持单点：带宽球 $=\{\bar p\}$ ⟹ 推前集 $=\{\text{freqToMeasure}(\bar p)\}$。
这是 `StatAlpha.band_isPoint_of_zero_radius` 在 `LawRule` 层的直接消费。 -/
theorem statLawRule_isPoint_of_zero_radius [MeasurableSpace OY.Carrier]
    (D : StatAlpha.Data CX.Carrier SX.Carrier OY.Carrier) (ρ : StatAlpha.Radius CX.Carrier SX.Carrier)
    (hlayer : ∀ c x, StatAlpha.layerCount D c x ≠ 0)
    (hρ : StatAlpha.RadiusAllZero ρ) :
    LawRule.IsPoint (statLawRule D ρ) := by
  intro c x
  refine ⟨freqToMeasure (Y := OY.Carrier) (StatAlpha.empFreq D c x), ?_⟩
  unfold statLawRule
  rw [StatAlpha.band_isPoint_of_zero_radius D ρ c x (hlayer c x) (hρ c x)]
  exact Set.image_singleton

/-- ⭐⭐⭐ **`LawRule.IsPoint` ⟺ `IsPointFreq`**（**闭合 `StatAlpha` §6 缺口**）。

`StatAlpha` 文件头说：「频率层 `IsPointFreq` 与 `LawRule.IsPoint` 的等价是**未闭合项**」。
本定理在前件（每层非空 ⟹ 频率层元素都是概率向量，故 `0 ≤ ·`）
与前向（上面 `statLawRule_isPoint_of_zero_radius`）+ 反向（用 `freqToMeasure_injOn`）双向下闭合。

**反向**的要点：若推前集是单点 $\{\mu\}$，则由单射性
$f_1=f_2$，故带宽球本身单点。 -/
theorem statLawRule_isPoint_iff [MeasurableSpace OY.Carrier] [MeasurableSingletonClass OY.Carrier]
    (D : StatAlpha.Data CX.Carrier SX.Carrier OY.Carrier) (ρ : StatAlpha.Radius CX.Carrier SX.Carrier) :
    LawRule.IsPoint (statLawRule D ρ) ↔ StatAlpha.IsPointFreq (StatAlpha.StatRule D ρ) := by
  constructor
  · intro h c x
    obtain ⟨μ, hμ⟩ := h c x
    -- 推前集非空 ⟹ 带宽球中至少有一个 `f₀`
    have hne : (statLawRule D ρ c x).Nonempty := by rw [hμ]; exact ⟨μ, rfl⟩
    obtain ⟨ν, hν⟩ := hne
    obtain ⟨f₀, hf₀, _⟩ := hν
    refine ⟨f₀, ?_⟩
    ext f
    constructor
    · intro hf
      rw [Set.mem_singleton_iff]
      -- `f` 与 `f₀` 的像同在单点集 `{μ}`，由单射性得 `f = f₀`
      have hf_img : freqToMeasure (Y := OY.Carrier) f ∈ statLawRule D ρ c x := ⟨f, hf, rfl⟩
      have hf₀_img : freqToMeasure (Y := OY.Carrier) f₀ ∈ statLawRule D ρ c x := ⟨f₀, hf₀, rfl⟩
      rw [hμ, Set.mem_singleton_iff] at hf_img hf₀_img
      exact freqToMeasure_injOn f f₀ hf.2.1 hf₀.2.1 (by rw [hf_img, hf₀_img])
    · intro hf
      rw [Set.mem_singleton_iff.mp hf]
      exact hf₀
  · intro h c x
    obtain ⟨f, hf⟩ := h c x
    exact ⟨freqToMeasure (Y := OY.Carrier) f, by
      unfold statLawRule
      rw [hf, Set.image_singleton]⟩

/-! ===========================================================================
    §5  与 `LawRule.Deterministic` 对齐 + 正半径的**可证伪性**
    =========================================================================== -/

/-- ⭐⭐ **统计版 α 是确定性规律 ⟺ 半径处处为零**（层非空、$|Y|\ge2$）。

用 `StatAlpha.isPoint_iff_all_zero_radius`（主判据）+
`LawRule.isPoint_iff_deterministic` + 本文件 `statLawRule_isPoint_iff`（§6 缺口闭合）
三段拼成。**这是 §5 主判据在 `LawRule` 层的完整形态。** -/
theorem statLawRule_deterministic_iff [MeasurableSpace OY.Carrier] [MeasurableSingletonClass OY.Carrier]
    [Nonempty OY.Carrier]
    (D : StatAlpha.Data CX.Carrier SX.Carrier OY.Carrier) (ρ : StatAlpha.Radius CX.Carrier SX.Carrier)
    (hY : ∃ a b : OY.Carrier, a ≠ b)
    (hlayer : ∀ c x, StatAlpha.layerCount D c x ≠ 0) :
    LawRule.Deterministic (statLawRule D ρ) ↔ StatAlpha.RadiusAllZero ρ := by
  constructor
  · intro hdet
    have hpt : LawRule.IsPoint (statLawRule D ρ) := by
      -- 每层非空（带宽球非空 ⟹ 推前集非空）
      refine LawRule.isPoint_of_deterministic _ (fun c x => ?_) hdet
      obtain ⟨f, hf⟩ := StatAlpha.band_nonempty D ρ c x (hlayer c x)
      exact ⟨freqToMeasure (Y := OY.Carrier) f, f, hf, rfl⟩
    exact (StatAlpha.isPoint_iff_all_zero_radius D ρ hY hlayer).mp
      ((statLawRule_isPoint_iff D ρ).mp hpt)
  · intro hρ
    have hpt : LawRule.IsPoint (statLawRule D ρ) :=
      statLawRule_isPoint_of_zero_radius D ρ hlayer hρ
    exact LawRule.IsPoint.deterministic _ hpt

/-- ⭐⭐⭐ **正半径 ⟹ 推前规律不是确定性规律**（统计版 α 的**可证伪性**）。

若某层 $\rho.r\,c\,x>0$ 且 $|Y|\ge2$、层非空，则带宽球至少含两点
（`StatAlpha.band_not_singleton_of_pos_radius`），由单射性
→ 推前集至少含两个不同测度 → 违反 `Deterministic`。

**这是本文件的「反面消费」**：不只把零半径条件用在正面，
还用正半径证明「统计版 α 无法充当确定性世界模型」。 -/
theorem statLawRule_not_deterministic_of_pos_radius
    [MeasurableSpace OY.Carrier] [MeasurableSingletonClass OY.Carrier] [Nonempty OY.Carrier]
    (D : StatAlpha.Data CX.Carrier SX.Carrier OY.Carrier) (ρ : StatAlpha.Radius CX.Carrier SX.Carrier)
    (hY : ∃ a b : OY.Carrier, a ≠ b)
    (hlayer : ∀ c x, StatAlpha.layerCount D c x ≠ 0)
    (c : CX.Carrier) (x : SX.Carrier) (hpos : 0 < ρ.r c x) :
    ¬ LawRule.Deterministic (statLawRule D ρ) := by
  intro hdet
  -- `hdet` 与零半径等价（上一节），但此处直接走构造
  obtain ⟨f₁, f₂, hne, h1, h2⟩ :=
    StatAlpha.band_not_singleton_of_pos_radius D ρ c x hY
      (StatAlpha.empFreq_sum D c x (hlayer c x)) hpos
  have hμ1 : freqToMeasure (Y := OY.Carrier) f₁ ∈ statLawRule D ρ c x := ⟨f₁, h1, rfl⟩
  have hμ2 : freqToMeasure (Y := OY.Carrier) f₂ ∈ statLawRule D ρ c x := ⟨f₂, h2, rfl⟩
  have heq := hdet c x _ _ hμ1 hμ2
  exact hne (freqToMeasure_injOn f₁ f₂ h1.2.1 h2.2.1 heq)

/-- ⭐⭐ **主判据的 `LawRule` 形态（充要）**：推前规律单点 ⟺ 半径处处为零。

`StatAlpha.isPoint_iff_all_zero_radius` 在 `LawRule` 层的完整消费：
把「统计单点」与「规则单点」**双向**接通（前向不需单射，反向需 §6 缺口已闭合）。 -/
theorem statLawRule_isPoint_iff_zero_radius
    [MeasurableSpace OY.Carrier] [MeasurableSingletonClass OY.Carrier] [Nonempty OY.Carrier]
    (D : StatAlpha.Data CX.Carrier SX.Carrier OY.Carrier) (ρ : StatAlpha.Radius CX.Carrier SX.Carrier)
    (hY : ∃ a b : OY.Carrier, a ≠ b)
    (hlayer : ∀ c x, StatAlpha.layerCount D c x ≠ 0) :
    LawRule.IsPoint (statLawRule D ρ) ↔ StatAlpha.RadiusAllZero ρ :=
  (statLawRule_isPoint_iff D ρ).trans
    (StatAlpha.isPoint_iff_all_zero_radius D ρ hY hlayer)

end StatAlpha

end FateV2.Rules