import FateWorld.FateV2.Error.ErrorBound
import FateWorld.FateV2.Error.ErrBandLink
import FateWorld.FateV2.Error.VerdictTheory

/-!
# Integration · Error · 误差判定链的综合（第一批）

## 本文件做什么

一次消费 **3 个** Error 域模块的既有结果：

| 源模块 | 被消费的定理 |
|---|---|
| `Error.ErrorBound` | `sgn_trichotomy`、`sgn_of_pos`、`sgn_of_neg`、`sgn_of_zero` |
| `Error.ErrBandLink` | `scoreOfTrack_le_of_ok`、`scoreOfGoal_le_of_ok`、`scoreOfDist_eq` |
| `Error.VerdictTheory` | `fitBoundary_isMin`、`fitBoundary_unique_of_isMin` |

这三条线索分别是「符号判定」「带内最优」「拟合边界唯一」，
在 `Error` 域的证明链里处于同一层，但**互不引用**。
本文件把它们并置，使上游（Loop/Export）可以一次取用。

## 不引入新数学

每条都是源定理的组合或直接特化。
-/

namespace FateV2.Integration

namespace ErrorBatch1

/-! ---------------------------------------------------------------------------
  §1  符号判定的三分类
  --------------------------------------------------------------------------- -/

namespace SgnNS

open FateV2.Error.R250ErrorBound

/-- ⭐⭐ **符号判定的三分类，且三种情形的常数都被锁定**。

`sgn t` 只能是 `1`、`-1`、`0` 三者之一，且每种情形对应的
`sgn` 值由 `sgn_of_pos` / `sgn_of_neg` / `sgn_of_zero` **分别钉死**。

**为什么值得一条定理**：`sgn_trichotomy` 只给出「三分」，
但下游往往还需要「每种情形下 `sgn` 确实是那个常数」——
这需要三条 `sgn_of_*` 协同，单靠三分得不到。 -/
theorem sgn_trichotomy_pinned (t : ℝ) :
    (0 < t → sgn t = 1) ∧ (t < 0 → sgn t = -1) ∧ (t = 0 → sgn t = 0)
      ∧ (sgn t = 1 ∨ sgn t = -1 ∨ sgn t = 0) :=
  ⟨sgn_of_pos, sgn_of_neg, fun h => by rw [h]; exact sgn_of_zero, sgn_trichotomy t⟩

end SgnNS

/-! ---------------------------------------------------------------------------
  §2  误差带内的得分最优性
  --------------------------------------------------------------------------- -/

namespace BandNS

open FateV2.Error.ErrBandLink
open FateV2.Predict.WorldScenario

universe u

/-- ⭐⭐⭐ **带内最优性：轨道误差落在 `[σ/2, 2σ]` 时，该轨道的得分最高**。

对任意两个场景 `s t`，只要 `s` 的误差落在**目标带**内，
则 `t` 的得分不超过 `s` 的。

**这是「误差带 ⟹ 最优」的核心断言**：它是
`scoreOfTrack_le_of_ok` 的无改动特化，单列是因为下游（Export 的
评分链）需要以「带内 ⟹ 最优」的形式引用，而不是穿透
`FateV2.Predict.WorldScenario.Scenario` 的细节。 -/
theorem band_error_implies_optimal {A X : Type u} {σ : ℝ} (hσ : 0 < σ)
    {errTrack : FateV2.Predict.WorldScenario.Scenario A X → ℝ}
    {s t : FateV2.Predict.WorldScenario.Scenario A X}
    (hs : σ / 2 ≤ errTrack s ∧ errTrack s ≤ 2 * σ) :
    scoreOfTrack σ errTrack t ≤ scoreOfTrack σ errTrack s :=
  scoreOfTrack_le_of_ok hσ hs

end BandNS

/-! ---------------------------------------------------------------------------
  §3  拟合边界的唯一性
  --------------------------------------------------------------------------- -/

namespace BoundaryNS

open FateV2.ErrorN

/-- ⭐⭐⭐ **边界点的 `σ` 被「最小值」唯一锁定**。

若 `(σ₁, γ₁)` 是边界点，且 `γ₂` 处取到最小值 `σ₂`，
则 `σ₁ = σ₂`。

**这条把「边界点」与「最小值」两个概念连起来**：前者是
`IsFitBoundaryN`（水平 + 全称下界），后者是「某点取等 + 全称下界」。
两条定理协同才得出唯一性 —— 单看任一条都得不到 `σ` 被锁定。 -/
theorem boundary_sigma_locked (W : ErrProfileN) {σ₁ σ₂ : Real} {γ₁ γ₂ : Nat}
    (h₁ : IsFitBoundaryN W σ₁ γ₁)
    (he₂ : W.err γ₂ = σ₂) (hle₂ : ∀ γ' : Nat, σ₂ ≤ W.err γ') :
    σ₁ = σ₂ :=
  fitBoundary_unique_of_isMin W h₁ he₂ hle₂

/-- ⭐ **边界点的双重刻画**：`IsFitBoundaryN W σ γ` 蕴含
「`σ = W.err γ`」与「`σ` 是全称下界」两条。

本体即 `fitBoundary_isMin` 加上 `h.1` 的反向使用；
单列是因为下游常用「边界点 ⟹ 取最小值」这一单向形式。 -/
theorem boundary_gives_min (W : ErrProfileN) {σ : Real} {γ : Nat}
    (h : IsFitBoundaryN W σ γ) :
    σ = W.err γ ∧ ∀ γ' : Nat, σ ≤ W.err γ' :=
  ⟨h.1.symm, (fitBoundary_isMin W h).2⟩

end BoundaryNS

end ErrorBatch1

end FateV2.Integration
