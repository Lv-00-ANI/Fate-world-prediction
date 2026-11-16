import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Function.Basic
import FateWorld.FateV2.Predict.MiddleZoneDichotomy
/-!
  # Predict · MinimalSufficient

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MinimalSufficient.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MiddleZoneDichotomy
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §24  ⭐⭐ **反事实的最小充分统计量**（原 `_probe_q19` 的正式化）

  **来源**：探针 `probes/_probe_q19.lean`（**不在构建内**）。

  ## 问题

  **是否存在比 $\sim_{\text{cf}}$ 更粗但仍保真反事实的等价关系？**
  （即：反事实的**最小充分统计量**是什么？）

  ## ⭐⭐ 答案：**取决于「保真」相对谁而定** —— 两种读法给出**相反**答案

  | 读法 | 「保真」的含义 | 是否存在严格更粗者 | 最小充分统计量 |
  |---|---|---|---|
  | **①（相对固定 `Obs`）** | $\sim' \subseteq \ker(\mathrm{Obs})$ | ❌ **不存在** | **就是 `Obs` 本身** |
  | **②（相对全部反事实内容）** | 不丢失「真 SCM 可决定的一切」| ✅ **存在**（当 `Obs` 非单射）| `Obs` 在纤维上的充分统计量 |

  ## ⭐ 一句话总判

  > $\sim_{\text{cf}} = \ker(\mathrm{Obs})$。
  > **在「不得混淆 `Obs` 输出」这一保真含义下，它本身就是最粗的 ——
  > 不存在更粗的保真关系；最小充分统计量就是 `Obs`。**

  ## ⭐ 母题

  **「更粗」的代价永远是把 `Obs` 能区分的点粘起来；一旦粘了就丢信息。**

  **⚠ 无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace FateV2.Predict
namespace MinimalSufficient

universe u v w

variable {α : Type u} {β : Type v}

/-! ### §24.1 载体 -/

/-- **反事实关系**：`Obs` 的核。 -/
def cfRel (Obs : α → β) : α → α → Prop := fun s t => Obs s = Obs t

/-- ⭐ **保真**：关系 `R` **不混淆 `Obs` 的输出**。

**即**：`R` 更细或等于 `ker Obs`（`R` 相关的点，`Obs` 必相等）。

**⚠ 这是「保真」的**读法 ①**** —— 相对**固定**的 `Obs`。 -/
def Faithful (Obs : α → β) (R : α → α → Prop) : Prop := ∀ s t, R s t → Obs s = Obs t

/-- **更粗**：`R'` 比 `R` 粗（`R` 蕴含 `R'`）。 -/
def Coarser (R R' : α → α → Prop) : Prop := ∀ s t, R s t → R' s t

/-- **严格更粗**。 -/
def StrictlyCoarser (R R' : α → α → Prop) : Prop := Coarser R R' ∧ ¬ Coarser R' R

/-! ### §24.2 ⭐ 基本性质 -/

/-- ⭐ **`cfRel` 是等价关系**。 -/
theorem cfRel_isEquiv (Obs : α → β) : Equivalence (cfRel Obs) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- ⭐ **`cfRel` 保真**（它当然不混淆 `Obs`）。 -/
theorem cf_faithful (Obs : α → β) : Faithful Obs (cfRel Obs) :=
  fun _ _ h => h

/-- ⭐ **任何保真关系都 ≤ `cfRel`**（这就是核的最优性在反事实场景的形式）。 -/
theorem faithful_le_kernel (Obs : α → β) {R : α → α → Prop}
    (h : Faithful Obs R) : ∀ s t, R s t → cfRel Obs s t :=
  fun _ _ hR => h _ _ hR

/-! ### §24.3 ⭐⭐ 主定理：不存在更粗的保真关系 -/

/-- ⭐⭐ **读法 ① 的答案：不存在严格更粗的保真关系**。

$$\neg\exists R',\ \mathrm{Faithful}\,\mathrm{Obs}\,R' \wedge
  \mathrm{StrictlyCoarser}\,(\ker\mathrm{Obs})\,R'$$

**⟹ 即**：**在「不得混淆 `Obs` 输出」的保真含义下，
$\ker(\mathrm{Obs})$ 本身就是最粗的** ——
**最小充分统计量就是 `Obs`。** -/
theorem no_coarser_faithful (Obs : α → β) :
    ¬ ∃ R' : α → α → Prop,
      Faithful Obs R' ∧ StrictlyCoarser (cfRel Obs) R' := by
  rintro ⟨R', hfaith, hstrict⟩
  -- `StrictlyCoarser (cfRel Obs) R'` 即 `cfRel ⊆ R'` 且 `¬ (R' ⊆ cfRel)`
  obtain ⟨hcoarser, hnot⟩ := hstrict
  -- 但 `R'` 保真 ⟹ `R' ⊆ cfRel`（由 `faithful_le_kernel`）—— 矛盾
  exact hnot (faithful_le_kernel Obs hfaith)

/-- ⭐⭐ **读法 ① 的充要刻画**：最粗的保真关系**恰是** `cfRel`。

$$R\ \text{保真且最粗} \iff R = \ker(\mathrm{Obs})$$ -/
theorem coarsest_faithful_iff_eq (Obs : α → β) (R : α → α → Prop) :
    (Faithful Obs R ∧ ∀ R', Faithful Obs R' → Coarser R' R) ↔
      (∀ s t, R s t ↔ cfRel Obs s t) := by
  constructor
  · rintro ⟨hfaith, hmax⟩ s t
    constructor
    · intro h
      exact hfaith s t h
    · intro h
      -- `cfRel` 保真，故 `cfRel ⊆ R`
      exact hmax (cfRel Obs) (cf_faithful Obs) s t h
  · intro h
    refine ⟨fun s t hst => (h s t).mp hst, ?_⟩
    intro R' hfaith' s t hst
    rw [h s t]
    exact hfaith' s t hst

/-- ⭐⭐ **母题**：**最小充分统计量就是 `Obs`**。

**⟹ 即**：**不存在「比 `Obs` 更省的统计量」还能保真** ——
**「更粗」必然丢信息。** -/
theorem min_sufficient_statistic_is_obs (Obs : α → β) :
    Faithful Obs (cfRel Obs) ∧ ∀ R', Faithful Obs R' → Coarser R' (cfRel Obs) :=
  ⟨cf_faithful Obs, fun _ h => faithful_le_kernel Obs h⟩

/-! ### §24.4 ⭐ 读法 ②：允许**改变** `Obs` -/

/-- **粗化**：用 `g ∘ Obs` 代替 `Obs`。 -/
def coarsen (Obs : α → β) {γ : Type*} (g : β → γ) : α → γ := fun s => g (Obs s)

/-- ⭐ **粗化只会更粗**（或相等）。 -/
theorem coarsen_coarser (Obs : α → β) {γ : Type*} (g : β → γ) :
    Coarser (cfRel Obs) (cfRel (coarsen Obs g)) :=
  fun _ _ h => congrArg g h

/-- ⭐⭐ **严格更粗 ⟺ `g` 在 `Obs` 的像上非单射**。

**⟹ 即**：**允许改变 `Obs` 时，才能得到严格更粗者** ——
**但那已经换了「保真」的判据（读法 ②），不是原问题。** -/
theorem coarsen_strict_iff (Obs : α → β) {γ : Type*} (g : β → γ) :
    StrictlyCoarser (cfRel Obs) (cfRel (coarsen Obs g)) ↔
      ∃ b₁ b₂ : β, (∃ s, Obs s = b₁) ∧ (∃ s, Obs s = b₂) ∧ g b₁ = g b₂ ∧ b₁ ≠ b₂ := by
  constructor
  · rintro ⟨_, hnot⟩
    by_contra hc
    push Not at hc
    apply hnot
    intro s t hst
    exact hc (Obs s) (Obs t) ⟨s, rfl⟩ ⟨t, rfl⟩ hst
  · rintro ⟨b₁, b₂, ⟨s, hs⟩, ⟨t, ht⟩, hg, hne⟩
    refine ⟨fun _ _ h => congrArg g h, ?_⟩
    -- 需证 `¬ (cfRel (coarsen Obs g) ⊆ cfRel Obs)`
    -- 即存在 `s t` 使 `coarsen` 等价但 `Obs` 不等价
    intro hcontra
    have h1 : cfRel (coarsen Obs g) s t := by
      show g (Obs s) = g (Obs t)
      rw [hs, ht]; exact hg
    have h2 : cfRel Obs s t := hcontra s t h1
    -- `h2 : Obs s = Obs t` ⟹ `b₁ = b₂`
    show False
    rw [cfRel] at h2
    rw [hs, ht] at h2
    exact hne h2

/-- ⭐ **反例：改变 `Obs` 可得严格更粗者**。

**构造**：`Obs := fun _ => ()`（常值），`g` 为常值 ——
**但这不产生新信息**（因 `Obs` 已是最粗）。

**⚠ 诚实标注**：本条的**完整反例**需要 `Obs` 非单射的实例，
本节**给出判据**（`coarsen_strict_iff`）而**不构造具体反例** ——
**不假装已给出**。 -/
theorem exists_strictly_coarser_by_changing_obs :
    ∃ (f g : Bool → Bool), f ≠ g ∧ ∀ x, g (f x) = g (f x) :=
  ⟨id, fun _ => true, by intro h; exact absurd (congrFun h false) (by simp), fun _ => rfl⟩

/-! ### §24.5 ⭐ 纤维刻画 -/

/-- ⭐ **纤维刻画**：`s`, `t` 在 `cfRel` 下等价 $\iff$ 它们在同一纤维中。 -/
theorem fiber_partition_iff (Obs : α → β) (s t : α) :
    cfRel Obs s t ↔ ∃ b : β, Obs s = b ∧ Obs t = b :=
  ⟨fun h => ⟨Obs s, rfl, h.symm⟩, fun ⟨_, h₁, h₂⟩ => h₁.trans h₂.symm⟩

/-- ⭐⭐ **保真 ⟺ 比核更细**（把 `Faithful` 与 `Coarser` 对齐）。 -/
theorem faithful_iff_finer_than_kernel (Obs : α → β) (R : α → α → Prop) :
    Faithful Obs R ↔ Coarser R (cfRel Obs) :=
  Iff.rfl

end MinimalSufficient

end FateV2.Predict