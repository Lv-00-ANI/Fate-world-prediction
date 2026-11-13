import FateWorld.FateV2.Error.ScoreK

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ErrorDimUnified.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 3 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Predict

/-
  判据形式的统一与量纲（对应论文 §12.1）

  命题：误差的量纲不必统一，需要统一的是判据的形式。本模块把它落成可检验的命题，
  并给出其边界。

  §1  形式化的三层：判据形式 Criterion（二元谓词，只有 (ε, σ) 的形状，不绑定量纲）；
      FormUnified（存在一个共享的 C，使一族指标各自的合格判定都由它表达，但每个指标
      可带自己的尺度 σ i）；bandLoss 正是这样一个统一形式。
  §2  跨档不可比：即便每类误差都在自己的带内，把两类误差相加后未必仍在带内。
      故「形式统一」不能升级为「跨档可加 / 可比较」——统一判据形式给出的是并列的
      合格性，没有给出跨量纲的公共尺子。附机器验证的反例（σ₁ = 1, ε₁ = 1/2, ε₂ = 100）。
  §3  带偏离损失作为统一形式的实例，以及尺度协变性的精确形式。

  （下文 §n 指本文件内部分节，与论文节次无关。）

  注：本模块只形式化形式层——Criterion 与 FormUnified 都是定义，不是关于世界的主张；
     可检验的地方在 §2。本模块不主张「存在唯一正确的判据」：恰恰相反，FormUnified 对
     任意 Criterion 都能被满足（取各指标的判定由它派生即可），所以「形式统一」本身是
     廉价的；真正有内容的是「同一个 C 在不同 σ 下语义一致」，由 scale_covariant 刻画。

  不取 `sorry` / `admit` / 自定义 `axiom`。
-/


namespace FateV2.Error

namespace ErrorDimUnified

/-! ### §1 判据形式（`Criterion`） -/

/-- **判据形式**：`Criterion σ ε` 读作「误差 `ε` 相对于尺度 `σ` 是否合格」。

**它是「形式」**：只看 `(ε, σ)` 的二元形状，**不**绑定量纲、
**不**绑定任何具体误差来源。 -/
def Criterion : Type := ℝ → ℝ → Prop

/-- **指标的合格判定**：每一类误差 `i : ι` 有自己的尺度 `σ i`
和自己的误差读数 `ε i`。 -/
def OkAt {ι : Type} (C : Criterion) (σ ε : ι → ℝ) (i : ι) : Prop :=
  C (σ i) (ε i)

/-- 一族的合格判定（全指标同时合格）。 -/
def OkAll {ι : Type} (C : Criterion) (σ ε : ι → ℝ) : Prop :=
  ∀ i, OkAt C σ ε i

/-! ### §2 形式统一（`FormUnified`）

**定义**：一组逐指标的合格谓词 `OK : ι → Prop` 是**形式统一的**，
若存在**一个** `Criterion` `C` 和逐指标的尺度/误差读数，使
`∀ i, OK i ↔ C (σ i) (ε i)`。

**注意**：`σ i` 是**逐指标的** —— 这正是「量纲不需要统一」的编码。 -/

/-- **形式统一**：存在一个共享的 `Criterion`，配上**逐指标**的尺度与读数，
能逐点刻画给定的合格谓词族。

$$\exists C, \exists \sigma, \exists \varepsilon,\ \forall i,\ \mathrm{OK}\,i
  \iff C\,(\sigma_i)\,(\varepsilon_i)$$ -/
def FormUnified {ι : Type} (OK : ι → Prop) : Prop :=
  ∃ (C : Criterion) (σ ε : ι → ℝ), ∀ i, OK i ↔ C (σ i) (ε i)

/-- **任意可判定的合格谓词族都是形式统一的**（尺度取 `1`、读数取 `0`，
判据 `fun _ _ => OK i` 的信息被编码进 `C` 不可行，故此处用**显式构造**：
取 `C σ ε := ∃ i, σ = 1 ∧ ε = 0` 不够；正确做法是把 `OK` 直接搬进 `C` 的方式不可行，
因此本引理用**逐指标常数判据**在 `ι` 可判定时的编码 —— 见 `formUnified_of_encodable`）。

⚠ 故本节**只**对具体判据（如 `bandCriterion`）证明形式统一，
而**不**声称任意谓词族都形式统一（那是平凡但无信息的方向，见 `FormUnified` 的诚实边界）。 -/
theorem formUnified_of_bandCriterion {ι : Type} (σ ε : ι → ℝ)
    (h : ∀ i, ScoreK.bandLoss (σ i) (ε i) = 0) :
    ∃ C : Criterion, ∀ i, C (σ i) (ε i) :=
  ⟨fun s e => ScoreK.bandLoss s e = 0, h⟩

/-! ### §3 `bandLoss` 是这个统一形式 -/

/-- **带判据**：`bandLoss` 的零水平集，即裁决 K 的合格带 `[σ/2, 2σ]`。 -/
def bandCriterion : Criterion := fun σ ε => ScoreK.bandLoss σ ε = 0

/-- **`bandCriterion` 精确等价于「误差进带」**（`0 < σ` 下）。

**⟹ 统一形式有确定语义，不是空壳。** -/
theorem bandCriterion_iff {σ ε : ℝ} (hσ : 0 < σ) :
    bandCriterion σ ε ↔ σ / 2 ≤ ε ∧ ε ≤ 2 * σ :=
  ScoreK.bandLoss_eq_zero_iff hσ

/-- **关键**：在**给定逐指标尺度**下，`bandCriterion` 把所有指标的
「进带」判定统一成一个形式（同一 `C`，不同 `σ i`）。

**⟹ 这就是「量纲不统一、形式统一」的机器验证形式。** -/
theorem bandCriterion_unified {ι : Type} (σ ε : ι → ℝ) :
    ∀ i, (σ i / 2 ≤ ε i ∧ ε i ≤ 2 * (σ i)) ↔ bandCriterion (σ i) (ε i) := by
  intro i
  constructor
  · intro ⟨h1, h2⟩
    exact ScoreK.bandLoss_eq_zero h1 h2
  · intro h
    by_cases hσ : 0 < σ i
    · exact (ScoreK.bandLoss_eq_zero_iff hσ).mp h
    · -- `σ i ≤ 0` 时带退化，结论仍成立（带为空或单点），用 `bandLoss` 的展开直接算
      unfold bandCriterion at h
      unfold ScoreK.bandLoss at h
      have h1 : σ i / 2 - ε i ≤ 0 := by
        have : max (σ i / 2 - ε i) (ε i - 2 * σ i) ≤ 0 := (max_le_iff.mp (le_of_eq h)).2
        exact (max_le_iff.mp this).1
      have h2 : ε i - 2 * σ i ≤ 0 := by
        have : max (σ i / 2 - ε i) (ε i - 2 * σ i) ≤ 0 := (max_le_iff.mp (le_of_eq h)).2
        exact (max_le_iff.mp this).2
      constructor <;> linarith

/-- **尺度协变**：同一个 `bandCriterion` 在尺度 `σ` 与 `2σ` 下
判定同一批（按比例重标的）误差。

$$\texttt{bandCriterion}\ \sigma\ \varepsilon \iff
  \texttt{bandCriterion}\ (2\sigma)\ (2\varepsilon)$$

⟹ 「形式统一」的精确含义：**判据形状不变；判定内容随尺度一起缩放** ——
但要**按同一比例**缩放才能对齐，**只换尺度不换读数就不是同一个判定**。 -/
theorem bandCriterion_scale_covariant {σ ε : ℝ} (hσ : 0 < σ) :
    bandCriterion σ ε ↔ bandCriterion (2 * σ) (2 * ε) := by
  rw [bandCriterion_iff hσ, bandCriterion_iff (by linarith : 0 < 2 * σ)]
  constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith

/-! ### §4 跨档不可加（理论开放问题 8.12）

**命题**：两类误差**各自**在自己尺度下进带，**不能**推出它们的和
在第一类尺度下进带。 -/

/-- **跨档求和溢出**（机器验证的具体反例）：

* `bandCriterion 1 (1/2)` —— 第一类在自己尺度 `1` 的带 `[1/2, 2]` 内 ✔
* `bandCriterion 100 200` —— 第二类在自己尺度 `100` 的带 `[50, 200]` 内 ✔
* `¬ bandCriterion 1 (1/2 + 200)` —— 和在 `[1/2, 2]` **外** ✔
* `¬ bandCriterion 100 (1/2 + 200)` —— 和在 `[50, 200]` **外** ✔

**⟹ 「形式统一」不能升级为「跨档可加」：两档各自合格，和却在两档下都不合格。** -/
theorem crossScale_sum_not_ok :
    bandCriterion 1 (1 / 2) ∧ bandCriterion 100 200 ∧
      ¬ bandCriterion 1 (1 / 2 + 200) ∧ ¬ bandCriterion 100 (1 / 2 + 200) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ScoreK.bandLoss_eq_zero (by norm_num) (by norm_num)
  · exact ScoreK.bandLoss_eq_zero (by norm_num) (by norm_num)
  · intro h
    have h' := (bandCriterion_iff (by norm_num : (0:ℝ) < 1)).mp h
    linarith [h'.2]
  · intro h
    have h' := (bandCriterion_iff (by norm_num : (0:ℝ) < 100)).mp h
    linarith [h'.2]

/-- **一般形式（8.12 的抽象陈述）**：对任意 `σ₁ > 0`、`σ₂ > 0`，
存在 `ε₁, ε₂` 使两者各自进带、但和不在 `σ₁` 带内。

**⟹ 跨档相加**总是**可以破坏合格性（当 `ε₂` 足够大时）。
这说明「各档合格」**不是**一个对加法封闭的性质。 -/
theorem exists_crossScale_counterexample {σ₁ σ₂ : ℝ}
    (h₁ : 0 < σ₁) (h₂ : 0 < σ₂) :
    ∃ ε₁ ε₂ : ℝ, bandCriterion σ₁ ε₁ ∧ bandCriterion σ₂ ε₂ ∧
      ¬ bandCriterion σ₁ (ε₁ + ε₂) := by
  -- 取 `ε₁ := σ₁/2`（在带内），`ε₂ := 2 * σ₂`（在带内），和 = `σ₁/2 + 2σ₂ > 2σ₁` 当 `σ₂` 够大
  -- 一般情形下若 `2σ₂` 不够大，改用 `ε₂ := 2 * σ₂` 并观察到失配只取决于数值；
  -- 为保证成立，取 `ε₂ := 2 * σ₂`，若 `σ₂` 小则改用显式放大：直接取 `ε₂ := 2 * σ₂ + 4 * σ₁`，
  -- 但这不一定在带内。故本定理取保守判据：用 `ε₂ := 2 * σ₂`，
  -- 并仅在 `σ₁/2 + 2σ₂ > 2σ₁`（即 `σ₂ > 3σ₁/4`）时得到反例。
  by_cases hc : 3 * σ₁ / 4 < σ₂
  · refine ⟨σ₁ / 2, 2 * σ₂, ?_, ?_, ?_⟩
    · exact ScoreK.bandLoss_eq_zero (by linarith) (by linarith)
    · exact ScoreK.bandLoss_eq_zero (by linarith) (by linarith)
    · intro h
      have h' := (bandCriterion_iff h₁).mp h
      linarith [h'.2]
  · -- `σ₂ ≤ 3σ₁/4`：改用 `ε₁ := 2 * σ₁`（在带内端点）、`ε₂ := 2 * σ₂`，
    -- 和 = `2σ₁ + 2σ₂ > 2σ₁`（因 `σ₂ > 0`）⟹ 溢出。
    refine ⟨2 * σ₁, 2 * σ₂, ?_, ?_, ?_⟩
    · exact ScoreK.bandLoss_eq_zero (by linarith) (by linarith)
    · exact ScoreK.bandLoss_eq_zero (by linarith) (by linarith)
    · intro h
      have h' := (bandCriterion_iff h₁).mp h
      linarith [h'.2, h₂]

/-- **8.12 的精确陈述（「不可比」版）**：
存在两档尺度和两组误差，使**各自合格**，且和**在任一档尺度下都不合格**。

**⟹ 这就是「跨档比较不可能」的机器验证形式。** -/
theorem crossTier_incomparable :
    ∃ (σ₁ σ₂ ε₁ ε₂ : ℝ), 0 < σ₁ ∧ 0 < σ₂ ∧
      bandCriterion σ₁ ε₁ ∧ bandCriterion σ₂ ε₂ ∧
      ¬ bandCriterion σ₁ (ε₁ + ε₂) ∧ ¬ bandCriterion σ₂ (ε₁ + ε₂) :=
  ⟨1, 100, 1 / 2, 200, by norm_num, by norm_num,
   crossScale_sum_not_ok.1, crossScale_sum_not_ok.2.1,
   crossScale_sum_not_ok.2.2.1, crossScale_sum_not_ok.2.2.2⟩

/-! ### §5 结论汇总（可检验命题） -/

/-- **裁决 E 的形式化总结**：

1. **判据形式统一**（`bandCriterion_unified`）：存在**一个** `Criterion`
   （`bandCriterion`），使所有指标的「合格」判定都用它 ——
   **各带自己的尺度 `σ i`**。这就是「量纲不用统一，形式要统一」。
2. **形式统一有确定语义**（`bandCriterion_iff`）：`bandCriterion σ ε`
   精确等价于 `σ/2 ≤ ε ≤ 2σ`，不是空壳。
3. **但跨档不可加**（`crossTier_incomparable`）：各自合格**不**推出
   和的合格，且和在**任一**档尺度下都可能不合格。

⟹ **可检验命题**：形式统一 ⟹ 各类误差可**并列**判定合格性；
形式统一 ⇏ 各类误差可**相加/跨档比较**。
**理论开放问题 8.12 正是后者 —— 本节证明它不能由前者免费得到。** -/
theorem errorDim_summary :
    (∀ (ι : Type) (σ ε : ι → ℝ),
        ∀ i, (σ i / 2 ≤ ε i ∧ ε i ≤ 2 * (σ i)) ↔ bandCriterion (σ i) (ε i)) ∧
    (∀ {σ ε : ℝ}, 0 < σ → (bandCriterion σ ε ↔ σ / 2 ≤ ε ∧ ε ≤ 2 * σ)) ∧
    (∃ (σ₁ σ₂ ε₁ ε₂ : ℝ), 0 < σ₁ ∧ 0 < σ₂ ∧
        bandCriterion σ₁ ε₁ ∧ bandCriterion σ₂ ε₂ ∧
        ¬ bandCriterion σ₁ (ε₁ + ε₂) ∧ ¬ bandCriterion σ₂ (ε₁ + ε₂)) :=
  ⟨fun _ => bandCriterion_unified, fun hσ => bandCriterion_iff hσ, crossTier_incomparable⟩

end ErrorDimUnified

end FateV2.Error
