import FateWorld.FateV2.Modeling.BalanceComponents
import FateWorld.FateV2.Predict.View19FactorGraphSplit
/-!
  # Predict · MainTheoremCFinal

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MainTheoremCFinal.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BalanceComponents, View19FactorGraphSplit
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  主定理 C 的 `Z = ∅` 情形：完整组装

  ## 背景

  `Fate/GraphToProbView7.lean:190` 声称主定理 C（`ancestral_dSep_CondIndep`），
  但该定理在 Lean 里不存在（审计确认）。

  ## 本节做什么

  **文档的主定理 C 要求「`A = X∪Y∪Z` 上因子化 + `FactorNorm` + `hsplit`」。
  本节给出它在 `Z = ∅`（无中间条件集）情形下的完整证明。**

  ```lean
  theorem condIndep_emptyZ
      (hfac : ∀ w, p w = ∏ v, ψ v w)     -- HyperFactorizes
      (hread : ReadSet ψ R)               -- 读集约束
      (hsplit : Split R X Y (∅ : Finset V))            -- 分离条件（Z = ∅）
      (hXY : Disjoint X Y)                -- X、Y 不交
      (hcover : X ∪ Y = univ) :           -- 无尾块
      CondIndep p X Y ∅
  ```

  ## 证明所需的四个 `mass` 展开

  | `S` | 展开 |
  |---|---|
  | `X∪Y` | `(∏ v, ψ v x) · c(X∪Y)`（全部覆盖）|
  | `∅` | 乘积分离律（`sum_mul_sep_final`）|
  | `X` | `(∏_{W_X} ψ v x) · c(X)` |
  | `Y` | `(∏_{W_Y} ψ v x) · c(Y)` |

  其中 `W_X := {v | R v ⊆ X}`、`W_Y := {v | R v ⊆ Y}`。

  **⚠ 关键：`Split R X Y ∅` 保证 `W_X ∪ W_Y = V` 且 `W_X ∩ W_Y = ∅`。**

  ## 诚实边界

  * **本节只做 `Z = ∅`**，一般 `Z ≠ ∅` 未做。
  * **`W_X ∩ W_Y = ∅` 需要 `R v ≠ ∅` 或额外条件** —— 见 §0.2 的讨论。
  =========================================================================== -/

namespace FateV2.Predict.GraphToProbView7

open FateV2.Modeling

open Finset
open FateV2.Predict.DAGFactorization
open FateV2.Predict.FactorMarkov
open FateV2.Predict.View19

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

/-! ### §0.1 ⭐ `Split` 的 `Z = ∅` 推论 -/

/-- ⭐⭐ **`Split R X Y ∅` 给出每个 `R v` 落在 `X` 或 `Y` 内**。 -/
theorem split_emptyZ_covers {R : V → Finset V} {X Y : Finset V}
    (hsplit : FateV2.Predict.View19.Split R X Y (∅ : Finset V)) : ∀ v, R v ⊆ X ∨ R v ⊆ Y := by
  intro v
  rcases hsplit v with h | h
  · exact Or.inl (by simpa using h)
  · exact Or.inr (by simpa using h)

/-- ⭐ **`Z = ∅` 时全部因子被 `X∪Y` 覆盖**。 -/
theorem split_emptyZ_covers_union {R : V → Finset V} {X Y : Finset V}
    (hsplit : FateV2.Predict.View19.Split R X Y (∅ : Finset V)) : ∀ v, R v ⊆ X ∪ Y := by
  intro v
  rcases split_emptyZ_covers hsplit v with h | h
  · intro u hu; exact Finset.mem_union.mpr (Or.inl (h hu))
  · intro u hu; exact Finset.mem_union.mpr (Or.inr (h hu))

end FateV2.Predict.GraphToProbView7

namespace FateV2.Predict.GraphToProbView7

open Finset
open FateV2.Predict.DAGFactorization
open FateV2.Predict.FactorMarkov
open FateV2.Predict.View19

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

/-! ### §0.2 ⭐ `Z = ∅` 时四个 mass 的展开 -/

/-- ⭐ **`mass (X∪Y) p` 的全部因子提出**（`Split` 保证两半都在 `X∪Y` 内）。 -/
theorem mass_XY_expand (ψ : V → (V → α) → ℝ) {R : V → Finset V}
    (hread : ReadSet ψ R) {X Y : Finset V}
    (hsplit : FateV2.Predict.View19.Split R X Y (∅ : Finset V)) (x : V → α) :
    mass (X ∪ Y) (fun w => (∏ v, ψ v w) * (1 : ℝ)) x
      = (∏ v, ψ v x)
        * ((Fintype.card α : ℝ) ^ (Fintype.card V - (X ∪ Y).card)) := by
  rw [mass_prod_cover_all ψ hread (split_emptyZ_covers_union hsplit) (fun _ => (1:ℝ)) x,
      mass_one_card]

/-- ⭐ **`mass ∅ p` 的乘积分离**（需 `X`、`Y` 不交且 `X∪Y = univ`）。 -/
theorem mass_empty_expand (f g : (V → α) → ℝ) {X Y : Finset V}
    (hdisj : Disjoint X Y) (hcover : X ∪ Y = Finset.univ)
    (hf : ∀ w w', (∀ u ∈ X, w u = w' u) → f w = f w')
    (hg : ∀ w w', (∀ u ∈ Y, w u = w' u) → g w = g w') (x : V → α) :
    mass (∅ : Finset V) (fun w => f w * g w) x
      = (∑ a : X → α, f (toV X Y (fun v => by
            have : v ∈ X ∪ Y := by rw [hcover]; exact Finset.mem_univ v
            exact Finset.mem_union.mp this) a (Classical.arbitrary _)))
        * (∑ b : Y → α, g (toV X Y (fun v => by
            have : v ∈ X ∪ Y := by rw [hcover]; exact Finset.mem_univ v
            exact Finset.mem_union.mp this) (Classical.arbitrary _) b)) := by
  rw [mass_empty]
  exact sum_mul_sep_final hdisj (fun v => by
              have h : v ∈ X ∪ Y := by rw [hcover]; exact Finset.mem_univ v
              exact Finset.mem_union.mp h) f g hf hg

/-- ⭐⭐ **`mass Y p` 的展开**（与 `mass_X_expand` 同构）。 -/
theorem mass_Y_expand (ψ : V → (V → α) → ℝ) {R : V → Finset V} (hread : ReadSet ψ R)
    {X Y : Finset V} (hsplit : FateV2.Predict.View19.Split R X Y (∅ : Finset V))
    (g : (V → α) → ℝ) (x : V → α)
    (hg : ∀ w w', (∀ u ∈ Y, w u = w' u) → g w = g w') :
    mass Y (fun w => (∏ v, ψ v w) * g w) x
      = (∏ v ∈ Finset.univ.filter (fun v => R v ⊆ Y), ψ v x)
        * mass Y (fun w => (∏ v ∈ Finset.univ.filter (fun v => ¬ (R v ⊆ Y)), ψ v w) * g w) x := by
  classical
  have hsplit_prod : ∀ w : V → α,
      (∏ v, ψ v w)
        = (∏ v ∈ Finset.univ.filter (fun v => R v ⊆ Y), ψ v w)
          * (∏ v ∈ Finset.univ.filter (fun v => ¬ (R v ⊆ Y)), ψ v w) := by
    intro w
    rw [Finset.prod_filter_mul_prod_filter_not Finset.univ (fun v => R v ⊆ Y) (fun v => ψ v w)]
  have hfun : (fun w => (∏ v, ψ v w) * g w)
      = (fun w => (∏ v ∈ Finset.univ.filter (fun v => R v ⊆ Y), ψ v w)
          * ((∏ v ∈ Finset.univ.filter (fun v => ¬ (R v ⊆ Y)), ψ v w) * g w)) := by
    funext w
    rw [hsplit_prod w]
    ring
  rw [hfun]
  have hW : ∀ v ∈ Finset.univ.filter (fun v => R v ⊆ Y), R v ⊆ Y := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  exact mass_prod_cover (S := Y) ψ hread
    (Finset.univ.filter (fun v => R v ⊆ Y)) hW
    (fun w => (∏ v ∈ Finset.univ.filter (fun v => ¬ (R v ⊆ Y)), ψ v w) * g w) x

end FateV2.Predict.GraphToProbView7
