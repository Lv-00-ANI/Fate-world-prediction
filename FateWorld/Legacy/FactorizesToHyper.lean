/-
  Fate_agent_staging/FactorizesToHyper.lean

  缺口 B：`Factorizes ⟹ HyperFactorizes` + `ReadSet`

  ## 内容

  | # | 名称 | 陈述 |
  |---|---|---|
  | 1 | `readSetOf G v` | `insert v (G.parents v)` —— 因子 `v` 的局部域 |
  | 2 | `localTo_iff_readSet` | `LocalTo G f ↔ ReadSet f (readSetOf G)` |
  | 3 | `readSetOf_nonempty` | `∀ v, (readSetOf G v).Nonempty` |
  | 4 | `factorizes_to_hyper` | `Factorizes p G ⟹ ∃ f, ReadSet f (readSetOf G) ∧ HyperFactorizes f p` |
  | 5 | `condIndep_of_factorizes` | 与 `condIndep_emptyZ` 串联：`Factorizes p G` + `Split (readSetOf G) X Y ∅` + … ⟹ `CondIndep p X Y ∅` |

  ## 依赖

  * `Fate.FactorMarkov.LocalTo` / `Factorizes` / `CondIndep` —— `Fate/FactorMarkov.lean`
  * `Fate.View19.ReadSet` / `HyperFactorizes` / `Split` —— `Fate/View19FactorGraphSplit.lean`
  * `Fate.GraphToProbView7.condIndep_emptyZ` —— `Fate/CondIndepEmptyZ.lean`
  * `Causalean.Graph.DAG.parents` / `mem_parents` —— `CausDAG.lean`

  ## 诚实边界

  * **`hne` 不再需要作为假设**：`readSetOf G v = insert v (G.parents v)` 天然非空，
    故 `condIndep_of_factorizes` 从 `condIndep_emptyZ` 的 `hne` 前提中解放出来
    （见 `readSetOf_nonempty`）。
  * `condIndep_of_factorizes` 需要 `[Nonempty α]`，这是 `condIndep_emptyZ`
    底层基础设施（`toV` / `mass_one_card`）的要求，**不削弱结论**
    （若 `α` 空而 `V` 非空则 `V → α` 为空，`CondIndep` 空洞为真）。
  * **零 `sorry` / `admit` / `axiom`**；不修改任何既有模块。
-/

import FateWorld.Legacy.CondIndepEmptyZ
import Mathlib.Tactic.Ring

namespace Fate

namespace FactorizesToHyper

open Finset
open Causalean.Graph

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false

/-! ===========================================================================
  §1  定义：因子的局部域
  =========================================================================== -/

/-- ⭐⭐ **因子 `v` 的局部域**：`{v} ∪ pa_G(v)`。

**⟹ 这就是 `LocalTo G f` 在 `ReadSet` 口径下要用的读集。** -/
def readSetOf (G : DAG V) (v : V) : Finset V := insert v (G.parents v)

/-- 局部域的成员判定（展开用）。 -/
theorem mem_readSetOf {G : DAG V} {v u : V} :
    u ∈ readSetOf G v ↔ u = v ∨ u ∈ G.parents v := by
  unfold readSetOf
  exact Finset.mem_insert

/-- ⭐⭐ **局部域非空**：总含 `v` 本身。 -/
theorem readSetOf_nonempty (G : DAG V) (v : V) : (readSetOf G v).Nonempty :=
  ⟨v, (mem_readSetOf).mpr (Or.inl rfl)⟩

/-! ===========================================================================
  §2  `LocalTo ↔ ReadSet`
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **`LocalTo G f` 与 `ReadSet f (readSetOf G)` 是同一命题**。

两者的前提**逐字相同**（`∀ u ∈ {v}∪pa v, x u = y u`），
区别仅在于 `LocalTo` 把集合写开、`ReadSet` 用 `Finset` 成员。 -/
theorem localTo_iff_readSet (G : DAG V) (f : V → (V → α) → ℝ) :
    Fate.FactorMarkov.LocalTo G f ↔ Fate.View19.ReadSet f (readSetOf G) := by
  constructor
  · intro h v x y hxy
    exact h v x y (fun u hu => hxy u ((mem_readSetOf).mpr hu))
  · intro h v x y hxy
    exact h v x y (fun u hu => hxy u ((mem_readSetOf).mp hu))

/-- `LocalTo` 版本（便于直接消费）。 -/
theorem readSet_of_localTo {G : DAG V} {f : V → (V → α) → ℝ}
    (h : Fate.FactorMarkov.LocalTo G f) : Fate.View19.ReadSet f (readSetOf G) :=
  (localTo_iff_readSet G f).mp h

/-- `ReadSet` 版本（便于直接消费）。 -/
theorem localTo_of_readSet {G : DAG V} {f : V → (V → α) → ℝ}
    (h : Fate.View19.ReadSet f (readSetOf G)) : Fate.FactorMarkov.LocalTo G f :=
  (localTo_iff_readSet G f).mpr h

/-! ===========================================================================
  §3  `Factorizes ⟹ HyperFactorizes`（带读集）
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **主命题**：`Factorizes p G` 给出**同族因子** `f`，
它既满足读集约束 `ReadSet f (readSetOf G)`，又满足 `HyperFactorizes f p`。 -/
theorem factorizes_to_hyper (p : Fate.FactorMarkov.Joint V α) (G : DAG V)
    (h : Fate.FactorMarkov.Factorizes p G) :
    ∃ f : V → (V → α) → ℝ,
      Fate.View19.ReadSet f (readSetOf G) ∧ Fate.View19.HyperFactorizes f p := by
  obtain ⟨f, hloc, hfac⟩ := h
  exact ⟨f, readSet_of_localTo hloc, hfac⟩

/-- 只取 `HyperFactorizes` 部分的便利形式。 -/
theorem factorizes_to_hyperFactorizes (p : Fate.FactorMarkov.Joint V α) (G : DAG V)
    (h : Fate.FactorMarkov.Factorizes p G) :
    ∃ f : V → (V → α) → ℝ, Fate.View19.HyperFactorizes f p :=
  let ⟨f, _, hf⟩ := factorizes_to_hyper p G h
  ⟨f, hf⟩

/-! ===========================================================================
  §4  与 `condIndep_emptyZ` 串联
  =========================================================================== -/

section Chain

variable [Nonempty α]

/-- ⭐⭐⭐⭐⭐ **`Factorizes` ⟹ 条件独立**（`Z = ∅` 情形）。

把 §3 的 `factorizes_to_hyper` 直接喂给 `condIndep_emptyZ`；
唯一的额外工作是 `hne : ∀ v, (readSetOf G v).Nonempty`，
它由 `readSetOf_nonempty` 免费得到。 -/
theorem condIndep_of_factorizes (p : Fate.FactorMarkov.Joint V α) (G : DAG V)
    (hfac : Fate.FactorMarkov.Factorizes p G)
    {X Y : Finset V}
    (hsplit : Fate.View19.Split (readSetOf G) X Y (∅ : Finset V))
    (hXY : Disjoint X Y)
    (hcover : X ∪ Y = univ) :
    Fate.FactorMarkov.CondIndep p X Y ∅ := by
  obtain ⟨f, hread, hhyper⟩ := factorizes_to_hyper p G hfac
  exact Fate.GraphToProbView7.condIndep_emptyZ f p hhyper hread
    (readSetOf_nonempty G) hsplit hXY hcover

end Chain

end FactorizesToHyper

end Fate
