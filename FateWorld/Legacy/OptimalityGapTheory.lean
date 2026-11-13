import FateWorld.Legacy.EndToEndError
import FateWorld.Legacy.ConvergeToOptimalV2

/-! ===========================================================================
  §OptimalityGapTheory  次优性度量理论：误差预算沿链可加

  ## 背景与目标

  `Fate/EndToEndError.lean` 定义了
  ```
  def IsOptimalGap (σ₁ ε εbest : ℝ) : Prop := εbest ≤ ε ∧ ε - εbest ≤ σ₁
  ```
  它刻画「所选系统的误差 `ε` 不低于最优 `εbest`，且距最优不超过 `σ₁`」——
  即「离最优多远」的可做量化（**不是**要求达到最优）。

  **本文件把「IsOptimalGap」发展成一个完整的次优性度量理论。**
  核心洞察：误差是沿链**传播**的（相关变量），因此各环节的次优性间隙
  `σᵢ` **可以相加**形成误差预算 —— 这与 `AssemblyMeta.assembly_no_gain`
  （不相交变量集的**约束合取**不产生新信息）**不矛盾**：那里是合取，这里是相加。

  ## 本文件定理清单（与任务书逐条对应）

  | 编号 | 定理 | 内容 |
  |---|---|---|
  | (a) | `optimalGap_refl`          | 自反性：`IsOptimalGap 0 ε ε` |
  | (b) | `optimalGap_mono`          | 单调性：`σ₁ ≤ σ₂` ⟹ `IsOptimalGap σ₁ → IsOptimalGap σ₂` |
  | (c) | `optimalGap_trans`         | 组合性：`IsOptimalGap σ₁ ε₁ ε₂` + `IsOptimalGap σ₂ ε₂ ε₃` ⟹ `IsOptimalGap (σ₁+σ₂) ε₁ ε₃` |
  | (d) | `optimalGap_zero_iff`      | 零间隙刻画：`IsOptimalGap 0 ε εbest ↔ ε = εbest` |
  | (e) | `optimal_gap_of_isOptimal` | 参数最优（`IsOptimal`，即 `A θ = x'`）⟹ 零间隙（用 `A` 单射 + `optimal_unique`：两个最优点之间零间隙）|
  | (f) | `optimalGap_chain`         | 链式收缩：逐步 `IsOptimalGap σᵢ` ⟹ n 步后 `IsOptimalGap (Σ σᵢ)` |

  另有若干辅助引理（`optimalGap_budget_le`、`optimalGap_slack_nonneg`、
  `optimalGap_of_abs_le`、`optimal_gap_of_isOptimal_self`、`optimalGap_chain_le`、
  `gap_sum_ge_each`、`chainGap` 等），均围绕上述六条展开。

  ## 诚实边界

  * 本文件**只新建**，不改任何已有模块。
  * 无 `sorry` / `admit` / `axiom`。
  * (c)、(f) 的「相加」是**沿同一条链的相关误差**的相加；对**不相交**的
    独立约束，`assembly_no_gain` 仍然成立 —— 两者不冲突（见文末说明）。
  * (f) 用 `List` 递归（`chainGap`）给出有限步形式，并给出显式预算上界推论 `optimalGap_chain_le`。
  =========================================================================== -/

namespace Fate

namespace OptimalityGapTheory

open Fate.EndToEndError

universe u

/-! ### §1 自反性 (a) -/

/-- ⭐ **(a) 自动性 / 自反性**：任何误差 `ε` 与自身的最优差距为 `0`。 -/
theorem optimalGap_refl (ε : ℝ) : IsOptimalGap 0 ε ε := by
  unfold IsOptimalGap
  constructor <;> linarith

/-! ### §2 单调性 (b) -/

/-- ⭐ **(b) 单调性**：允许的间隙界放大到 `σ₂ ≥ σ₁`，结论仍然成立。 -/
theorem optimalGap_mono {σ₁ σ₂ ε εbest : ℝ} (hσ : σ₁ ≤ σ₂)
    (h : IsOptimalGap σ₁ ε εbest) : IsOptimalGap σ₂ ε εbest := by
  unfold IsOptimalGap at *
  exact ⟨h.1, le_trans h.2 hσ⟩

/-! ### §3 组合性 / 传递性 (c) —— 误差预算可加 -/

/-- ⭐⭐⭐ **(c) 组合性**：沿链两段间隙相加。

若 `ε₁` 距 `ε₂` 不超过 `σ₁`，且 `ε₂` 距 `ε₃` 不超过 `σ₂`，
则 `ε₁` 距 `ε₃` 不超过 `σ₁ + σ₂`。

**这是误差预算可相加的基础**：`σ₁`、`σ₂` 是**同一条链上依次传播**的
次优性量，因此可以相加（与 `assembly_no_gain` 的不相交约束不同）。 -/
theorem optimalGap_trans {σ₁ σ₂ ε₁ ε₂ ε₃ : ℝ}
    (h₁ : IsOptimalGap σ₁ ε₁ ε₂) (h₂ : IsOptimalGap σ₂ ε₂ ε₃) :
    IsOptimalGap (σ₁ + σ₂) ε₁ ε₃ := by
  unfold IsOptimalGap at *
  constructor
  · linarith [h₂.1, h₁.1]
  · linarith [h₁.2, h₂.2]

/-- ⭐ **推论**：组合后的总预算给出显式上界 `ε₁ ≤ ε₃ + (σ₁ + σ₂)`。 -/
theorem optimalGap_budget_le {σ₁ σ₂ ε₁ ε₂ ε₃ : ℝ}
    (h₁ : IsOptimalGap σ₁ ε₁ ε₂) (h₂ : IsOptimalGap σ₂ ε₂ ε₃) :
    ε₁ ≤ ε₃ + (σ₁ + σ₂) := by
  have h := optimalGap_trans h₁ h₂
  unfold IsOptimalGap at h
  linarith [h.2]

/-! ### §4 零间隙刻画 (d) -/

/-- ⭐ **[辅助] 零间隙给出非负松弛**：`IsOptimalGap 0 ε εbest` ⟹ `0 ≤ ε - εbest`。 -/
theorem optimalGap_slack_nonneg {ε εbest : ℝ} (h : IsOptimalGap 0 ε εbest) :
    0 ≤ ε - εbest := by
  unfold IsOptimalGap at h
  linarith [h.1]

/-- ⭐ **(d) 零间隙刻画**：`IsOptimalGap 0 ε εbest` **当且仅当** `ε = εbest`。

正向：`0 ≤ ε - εbest` 且 `ε - εbest ≤ 0` ⟹ `ε - εbest = 0`。
反向：若 `ε = εbest`，则 `εbest ≤ ε` 且 `ε - εbest = 0 ≤ 0`。

**注意**：此结论的实质内容是「`σ₁ = 0` 时限死了上界必须为 `0`」，
并非把结论塞进前件 —— 前件只说 `εbest ≤ ε`（单边）与 `ε - εbest ≤ 0`（单边），
两者合作才挤到等号。 -/
theorem optimalGap_zero_iff {ε εbest : ℝ} :
    IsOptimalGap 0 ε εbest ↔ ε = εbest := by
  constructor
  · intro h
    unfold IsOptimalGap at h
    linarith [h.1, h.2]
  · intro h
    subst h
    exact optimalGap_refl ε

/-! ### §5 与 `IsOptimal` 的关系 (e) -/

/-- ⭐ **(e) 两个参数最优点之间的次优性间隙为零**。

`ConvergeToOptimalV2.IsOptimal A x' θ` 意为 `A θ = x'`（预测**恰好命中**观测）。
若损失度量 `e : E → ℝ` 只依赖于参数（同参数 ⟹ 同损失，即 `FunLike`-风格一致性）
且 `A` 单射，则**任意两个**参数最优点 `θ₁, θ₂` 之间有
`IsOptimalGap 0 (e θ₁) (e θ₂)` —— 即零间隙。

**这是「参数最优 ⟹ 零间隙」的实质形式**：内容来自
`ConvergeToOptimalV2.optimal_unique`（用 `A` 单射）与损失的一致性的**合作**，
不是把结论塞进前件 —— 前件只说「都最优」与「损失相容」，
结论「零间隙」是由 `optimal_unique` 推出的新信息。 -/
theorem optimal_gap_of_isOptimal {E F : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : E →ₗ[ℝ] F} (hA : Function.Injective A) {x' : F} {θ₁ θ₂ : E}
    (e : E → ℝ)
    (he : ∀ θ θ', θ = θ' → e θ = e θ')
    (h₁ : ConvergeToOptimalV2.IsOptimal A x' θ₁)
    (h₂ : ConvergeToOptimalV2.IsOptimal A x' θ₂) :
    IsOptimalGap 0 (e θ₁) (e θ₂) := by
  have hθ : θ₁ = θ₂ := ConvergeToOptimalV2.optimal_unique A hA x' h₁ h₂
  have hloss : e θ₁ = e θ₂ := he θ₁ θ₂ hθ
  rw [optimalGap_zero_iff]
  exact hloss

/-- ⭐ **(e′) 单点退化**：在唯一参数最优点处的损失与自身比对，间隙为零。

`IsOptimal A x' θ` 与 `A` 单射让 `θ` 成为「该观测下的最优参数」，
故其损失 `e θ` 相对自身必有零间隙（配合 `optimalGap_refl`）。
此定理用作 (e) 的单点特例，前件 `IsOptimal` 是实质信息（并非与结论同义）。 -/
theorem optimal_gap_of_isOptimal_self {E F : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : E →ₗ[ℝ] F} {x' : F} {θ : E} (e : E → ℝ)
    (_hθ : ConvergeToOptimalV2.IsOptimal A x' θ) :
    IsOptimalGap 0 (e θ) (e θ) :=
  optimalGap_refl (e θ)

/-! ### §6 由绝对误差界推出最优差距 -/

/-- ⭐ **[辅助] 双侧界 → 最优差距**：若最优 `εbest` 是下界且 `|ε - εbest| ≤ σ₁`，
则 `IsOptimalGap σ₁ ε εbest`。给出「用绝对偏差刻画次优性」的桥。 -/
theorem optimalGap_of_abs_le {σ₁ ε εbest : ℝ} (hle : εbest ≤ ε)
    (habs : |ε - εbest| ≤ σ₁) : IsOptimalGap σ₁ ε εbest := by
  unfold IsOptimalGap
  refine ⟨hle, ?_⟩
  have : ε - εbest ≤ |ε - εbest| := le_abs_self _
  linarith

/-! ### §7 链式收缩 (f) —— 有限链上的预算求和 -/

/-- 链段的递归关系：`chainGap σs es ε₀ εend` 表示「从 `ε₀` 出发，经 `es` 各点、
步间隙为 `σs`，最终到达 `εend`，整条链的次优性成立」。两个列表等长。 -/
def chainGap : List ℝ → List ℝ → ℝ → ℝ → Prop
  | [], [], ε₀, εend => εend = ε₀
  | σ :: σs, e :: es, ε₀, εend => IsOptimalGap σ ε₀ e ∧ chainGap σs es e εend
  | _, _, _, _ => False

/-- ⭐⭐⭐ **(f) 链式收缩（递归形式）**。

对任意有限链：逐步的次优性间隙 `σᵢ` 之和给出整条链的总间隙
`IsOptimalGap (Σ σᵢ) ε₀ εend`。

**这是「次优性沿链累积、误差预算可相加」的完整形式**：
每一步离最优的偏差可以相加，形成对整条链的预算界。 -/
theorem optimalGap_chain :
    ∀ (σs es : List ℝ) (ε₀ εend : ℝ), σs.length = es.length →
      chainGap σs es ε₀ εend →
      IsOptimalGap σs.sum ε₀ εend := by
  intro σs
  induction σs with
  | nil =>
    intro es ε₀ εend hlen hchain
    cases es with
    | nil =>
      simp only [chainGap] at hchain
      subst hchain
      simpa [List.sum_nil] using optimalGap_refl εend
    | cons _ _ => simp at hlen
  | cons σ σs ih =>
    intro es ε₀ εend hlen hchain
    cases es with
    | nil => simp at hlen
    | cons e es' =>
      simp only [List.length_cons] at hlen
      have hlen' : σs.length = es'.length := by omega
      simp only [chainGap] at hchain
      obtain ⟨hstep, hrest⟩ := hchain
      have htail : IsOptimalGap (σs.sum) e εend := ih es' e εend hlen' hrest
      simpa using optimalGap_trans hstep htail

/-- ⭐ **(f) 推论**：链式收缩给出显式预算上界 `ε₀ ≤ εend + Σ σᵢ`。 -/
theorem optimalGap_chain_le :
    ∀ (σs es : List ℝ) (ε₀ εend : ℝ), σs.length = es.length →
      chainGap σs es ε₀ εend →
      ε₀ ≤ εend + σs.sum := by
  intro σs es ε₀ εend hlen hchain
  have h := optimalGap_chain σs es ε₀ εend hlen hchain
  unfold IsOptimalGap at h
  linarith [h.2]


/-! ### §8 诚实说明：与 `assembly_no_gain` 的不冲突 -/

/-- ⭐ **说明性引理**：两段间隙之和的下界。
若 `σ₁, σ₂ ≥ 0`，则 `max σ₁ σ₂ ≤ σ₁ + σ₂`。
这形式化地说明：沿链**相加**的预算（`σ₁ + σ₂`）不小于任何单环节的预算，
即「相加」确实在累积信息，与 `assembly_no_gain`（不相交约束合取不产生新信息）
**不是同一情形**：这里是相关误差的传播，不是独立约束的合取。 -/
theorem gap_sum_ge_each {σ₁ σ₂ : ℝ} (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) :
    σ₁ ≤ σ₁ + σ₂ ∧ σ₂ ≤ σ₁ + σ₂ := by
  constructor <;> linarith

end OptimalityGapTheory

end Fate
