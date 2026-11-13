import FateWorld.Legacy.InterventionSup

/-! ===========================================================================
  §D1  `InterventionSup` 的**消费者**（G46 真消费）

  ## 背景

  审计 R950：

  > `InterventionSup`（11 定理）与 `FitBoundaryLowerBound`（14 定理）双双 0 消费者。

  `Fate/InterventionSup.lean` 用 `Finset.sup'` 重新定义最优值 `bestScoreSup`，
  使紧性定理依赖 Mathlib 的真实定理（`Finset.exists_mem_eq_sup'`、
  `Finset.le_sup'`、`Finset.sup'_le`、`Finset.lt_sup'_iff`），
  而**不是**由 `Classical.choose` 的定义展开直接搬运结论。

  本文件是它的消费者：把「树上的上确界」搬进**干预场景选型**的语境，
  给出可以直接被下游使用的推论。

  ## 消费清单（每条定理体都直接出现 `InterventionSup.<名字>`）

  | 本文件定理 | 消费的上游定理 |
  |---|---|
  | `score_le_bestScoreSup`              | `le_bestScoreSup` |
  | `bestScoreSup_isAttained`            | `bestScoreSup_mem_image` |
  | `bestScoreSup_isGreatest`            | `bestScoreSup_isGreatest` |
  | `bestScoreSup_lub_iff`               | `bestScoreSup_isLUB` |
  | `exists_score_near_bestScoreSup`     | `bestScoreSup_sharp` |
  | `bestScoreSup_le_uniform_bound`      | `bestScoreSup_le` |
  | `bestScoreSup_le_bestScore`          | `bestScoreSup_le_bestScore` |
  | `optimal_iff_score_eq_bestScoreSup`  | `le_bestScoreSup`, `bestScoreSup_le` |
  | `exists_scenario_isGreatest_score`   | `bestScoreSup_mem_image`, `le_bestScoreSup` |

  ## 诚实边界

  1. **只覆盖有限树** —— 论域是 `Finset`；无限树的 `sup` 未必被达到。
  2. **`score` 仍是参数** —— 「最优」相对于给定 `score`；本文件不填 `score`。
  3. **零 `sorry` / 零 `axiom` / 零 `native_decide`**。
  4. 本文件**不修改**任何已有模块。
  =========================================================================== -/

namespace Fate

namespace WorldScenario

namespace InterventionSupConsumer

open InterventionSup

universe u

/-! ### §D1.1 上界：任一场景不超过上确界 -/

/-- ⭐⭐ **【上界：任意场景得分不超过上确界】**（真消费 `le_bestScoreSup`）

干预选型的第一个基本事实：树中任何候选场景的得分都不会超过最优值。 -/
theorem score_le_bestScoreSup {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    (s : Scenario A X) (hs : s ∈ tree) :
    P.score s ≤ bestScoreSup P tree hne :=
  InterventionSup.le_bestScoreSup P tree hne s hs

/-! ### §D1.2 紧性：上确界被某个场景达到 -/

/-- ⭐⭐⭐ **【紧性：上确界被达到，以存在形式给出】**（真消费 `bestScoreSup_mem_image`）

把 `bestScoreSup ∈ P.score '' tree` 展开为显式的「存在一个场景取到最优值」，
这是干预选型可直接使用的形式：**最优干预方案存在**。 -/
theorem bestScoreSup_isAttained {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    ∃ s ∈ tree, P.score s = bestScoreSup P tree hne := by
  have hmem := InterventionSup.bestScoreSup_mem_image P tree hne
  obtain ⟨s, hs, hEq⟩ := hmem
  exact ⟨s, by simpa using hs, hEq⟩

/-- ⭐⭐ **【同一事实的最大元形式】**（真消费 `bestScoreSup_isGreatest`） -/
theorem bestScoreSup_isGreatest {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    IsGreatest (P.score '' (tree : Set (Scenario A X))) (bestScoreSup P tree hne) :=
  InterventionSup.bestScoreSup_isGreatest P tree hne

/-! ### §D1.3 最小上界刻画 -/

/-- ⭐⭐⭐ **【最小上界：`beta` 是上界 `↔` `bestScoreSup ≤ beta`】**（真消费 `bestScoreSup_isLUB`）

干预选型的告警阈值判定：验证 `beta` 是安全阈值，等价于验证
最优值不超过 `beta`，**无需遍历树**。 -/
theorem bestScoreSup_lub_iff {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    (beta : ℝ) :
    (∀ s ∈ tree, P.score s ≤ beta) ↔ bestScoreSup P tree hne ≤ beta :=
  InterventionSup.bestScoreSup_isLUB P tree hne beta

/-- ⭐⭐ **【安全阈值的充分条件】**（真消费 `bestScoreSup_le`）

若能直接算出上确界的界 `a`，则它是安全阈值。 -/
theorem bestScoreSup_le_uniform_bound {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    {a : ℝ} (ha : ∀ s ∈ tree, P.score s ≤ a) :
    bestScoreSup P tree hne ≤ a :=
  InterventionSup.bestScoreSup_le P tree hne ha

/-! ### §D1.4 锐利性：下调不再是上界 -/

/-- ⭐⭐⭐ **【锐利性：任何下调都失效】**（真消费 `bestScoreSup_sharp`）

最优值不可改进：对任意 `eps > 0`，都存在场景得分超过 `bestScoreSup - eps`。
这是「干预选型已最优、无法再压」的定量表述。 -/
theorem exists_score_near_bestScoreSup {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ s ∈ tree, bestScoreSup P tree hne - eps < P.score s :=
  InterventionSup.bestScoreSup_sharp P tree hne heps

/-! ### §D1.5 与旧 `bestScore` 的关系 -/

/-- ⭐⭐ **【真上确界不超过旧最优值】**（真消费 `bestScoreSup_le_bestScore`）

旧 `bestScore`（基于 `chooseOptimal`）总是真上确界的一个上界。 -/
theorem bestScoreSup_le_bestScore {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    bestScoreSup P tree hne ≤ Tight.bestScore P tree hne :=
  InterventionSup.bestScoreSup_le_bestScore P tree hne

/-! ### §D1.6 综合：最优场景的判据 -/

/-- ⭐⭐⭐ **【最优场景的等价刻画】**（真消费 `le_bestScoreSup` 与 `bestScoreSup_le`）

树中场景 `s` 达到最优值，当且仅当它的得分等于上确界。

这是干预选型的**收尾判据**：无需计算 `chooseOptimal`，
直接比较得分与 `bestScoreSup` 即可判定最优性。 -/
theorem optimal_iff_score_eq_bestScoreSup {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    (s : Scenario A X) (hs : s ∈ tree) :
    (∀ t ∈ tree, P.score t ≤ P.score s) ↔
      P.score s = bestScoreSup P tree hne := by
  constructor
  · intro hmax
    apply le_antisymm
    · exact InterventionSup.le_bestScoreSup P tree hne s hs
    · exact InterventionSup.bestScoreSup_le P tree hne
        (fun t ht => hmax t ht)
  · rintro hEq t ht
    rw [hEq]
    exact InterventionSup.le_bestScoreSup P tree hne t ht

/-- ⭐⭐ **【最优场景存在，且是最优】—— 合取形式**（真消费两条）

把紧性与上界合成一句话：存在一个场景，其得分恰为最优值，
且树中其余场景都不超过它。这是本消费文件的**主结论**。 -/
theorem exists_scenario_isGreatest_score {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    ∃ s ∈ tree, P.score s = bestScoreSup P tree hne ∧
      ∀ t ∈ tree, P.score t ≤ P.score s := by
  obtain ⟨s, hs, hEq⟩ := bestScoreSup_isAttained P tree hne
  refine ⟨s, hs, hEq, ?_⟩
  intro t ht
  rw [hEq]
  exact InterventionSup.le_bestScoreSup P tree hne t ht

end InterventionSupConsumer

end WorldScenario

end Fate
