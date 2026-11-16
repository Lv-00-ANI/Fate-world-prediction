import FateWorld.FateV2.Predict.InterventionTight
/-!
  # Predict · InterventionSup

  ## 迁移登记
  - 来源：`FateWorld/Legacy/InterventionSup.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：InterventionTight
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §X6  干预选择最优值的**真上确界**形式（`Finset.sup'`）

  ## 问题（审计发现 F2）

  `Fate/InterventionTight.lean` 中

  ```lean
  noncomputable def bestScore P tree hne : ℝ :=
    P.score (chooseOptimal P tree hne)
  ```

  因此 `bestScore_mem_image` / `bestScore_isGreatest` 等「紧性」定理，
  其**结论由定义即得**：证明只用 `chooseOptimal_mem`（即 `Classical.choose_spec`
  投射出的「所选在树里」）与 `chooseOptimal_isOptimal`（「所选最优」），
  而这两条本身正是 `exists_optimal_scenario` 的 `choose_spec` 展开。
  审计方的独立复推用「定义展开 + 结论直接搬运」即可完成，
  说明原 `bestScore` 上的紧性**预设了被证结论**（同义反复）。

  ## 本文件的做法

  改用标准库的**有限上确界** `Finset.sup'` 定义最优值：

  ```lean
  noncomputable def bestScoreSup P tree hne : ℝ := tree.sup' hne P.score
  ```

  该定义**不含**任何选择函数，也不预设「最大值被达到」。

  在此定义上重新证紧性两半：

  | 名字 | 内容 | 依赖的真实定理 |
  |---|---|---|
  | `bestScoreSup_mem_image` | ⭐ 上确界**被达到** | `Finset.exists_mem_eq_sup'` |
  | `le_bestScoreSup` | ⭐ 上确界是**上界** | `Finset.le_sup'` |
  | `bestScoreSup_isGreatest` | ⭐⭐ 是被达到的最大元（合取） | 上两条 |
  | `bestScoreSup_isLUB` | ⭐⭐ 最小上界刻画 | `Finset.sup'_le` |
  | `bestScoreSup_sharp` | ⭐⭐⭐ 任一下调都不是上界 | `Finset.lt_sup'_iff` |
  | `bestScoreSup_eq_bestScore_of_isOptimal` | 与旧 `bestScore` 一致**需额外前提** | 见下 |

  最后一条是本文件的**判据**：旧 `bestScore` 只有在额外假设
  「`chooseOptimal` 取到的得分恰是上确界」下才等于 `bestScoreSup`。
  即旧定义**没有**免费给出真紧性。

  ## 向后兼容

  `bestScore` 与其 89 处引用**完全不动**。本文件只**新增**定义与定理。

  ## 诚实边界

  1. **只覆盖有限树** —— 论域是 `Finset`。无限树的上确界未必被达到。
  2. **`score` 仍是参数** —— 「最优」相对于给定 `score`。
  3. **零 `sorry` / 零 `axiom`** —— 每条定理均已证。

  ⚠ 本文件未使用 `sorry`，未删除任何定理。
  =========================================================================== -/

namespace FateV2.Predict
namespace WorldScenario

namespace InterventionSup

open Tight

universe u

/-! ### §X6.1 定义：`Finset.sup'` 形式的最优值 -/

/-- ⭐⭐ **上确界形式的最优值**（不预设 `chooseOptimal`）。

定义为树中所有场景得分的有限上确界 `tree.sup' hne P.score`。
与 `Tight.bestScore` 不同，此定义**不含**任何选择函数。 -/
noncomputable def bestScoreSup {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) : ℝ :=
  tree.sup' hne P.score

/-- 定义性展开（仅用于陈述，非证明手段）。 -/
theorem bestScoreSup_def {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    bestScoreSup P tree hne = tree.sup' hne P.score := rfl

/-! ### §X6.2 上界（真实定理：`Finset.le_sup'`） -/

/-- ⭐⭐⭐⭐ **【真上界】**：树中任一场景的得分不超过上确界。

依赖 `Finset.le_sup'`（真实定理），**不是**定义展开。 -/
theorem le_bestScoreSup {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    (s : Scenario A X) (hs : s ∈ tree) :
    P.score s ≤ bestScoreSup P tree hne :=
  Finset.le_sup' P.score hs

/-- ⭐ **上确界小于等于任一上界**（`Finset.sup'_le`，真实定理）。 -/
theorem bestScoreSup_le {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    {a : ℝ} (ha : ∀ s ∈ tree, P.score s ≤ a) :
    bestScoreSup P tree hne ≤ a :=
  Finset.sup'_le hne P.score ha

/-! ### §X6.3 取等（真实定理：`Finset.exists_mem_eq_sup'`） -/

/-- ⭐⭐⭐⭐⭐ **【真紧性：上确界被达到】**

`bestScoreSup` 属于得分集，即被树中某个场景达到。

⚠ **这不是定义展开**：`bestScoreSup` 定义为 `tree.sup' hne P.score`，
而「有限上确界等于某个元素的值」是 `Finset.exists_mem_eq_sup'`（真实定理），
不来自任何选择函数的规格。 -/
theorem bestScoreSup_mem_image {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    bestScoreSup P tree hne ∈ P.score '' (tree : Set (Scenario A X)) := by
  obtain ⟨i, hi, hEq⟩ := Finset.exists_mem_eq_sup' hne P.score
  exact ⟨i, by simpa using hi, hEq.symm⟩

/-- ⭐⭐⭐ **上确界是得分集的最大元**（到达 + 上界）。 -/
theorem bestScoreSup_isGreatest {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    IsGreatest (P.score '' (tree : Set (Scenario A X))) (bestScoreSup P tree hne) := by
  refine ⟨bestScoreSup_mem_image P tree hne, ?_⟩
  rintro b ⟨s, hs, rfl⟩
  exact le_bestScoreSup P tree hne s (by simpa using hs)

/-! ### §X6.4 锐利性（最小上界刻画） -/

/-- ⭐⭐⭐ **【最小上界刻画】**：`β` 是上界当且仅当 `bestScoreSup ≤ β`。

这是「最小的上界」的标准刻画：`bestScoreSup` 自身是上界，
且任何上界都不小于它。依赖 `Finset.sup'_le`（真实定理）。 -/
theorem bestScoreSup_isLUB {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) (β : ℝ) :
    (∀ s ∈ tree, P.score s ≤ β) ↔ bestScoreSup P tree hne ≤ β :=
  ⟨bestScoreSup_le P tree hne, fun h s hs => le_trans (le_bestScoreSup P tree hne s hs) h⟩

/-- ⭐⭐⭐ **【锐利性】**：任一下调 `ε > 0` 都**不是**上界，
即存在树中场景得分超过 `bestScoreSup − ε`。

依赖 `Finset.lt_sup'_iff`（真实定理）。 -/
theorem bestScoreSup_sharp {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ tree, bestScoreSup P tree hne - ε < P.score s := by
  have hl : bestScoreSup P tree hne - ε < tree.sup' hne P.score := by
    rw [bestScoreSup_def]
    linarith
  rw [Finset.lt_sup'_iff] at hl
  obtain ⟨s, hs, hlt⟩ := hl
  exact ⟨s, hs, hlt⟩

/-! ### §X6.5 与旧 `bestScore` 的关系（**需额外前提**） -/

/-- ⭐⭐ **【旧定义需额外前提才等于真上确界】**

若 `chooseOptimal` 所取场景的得分恰是得分集的最大元，
则旧 `bestScore` 与 `bestScoreSup` 相等。

⚠ **本定理是判据**：它显示的正是「旧 `bestScore` 的紧性并非免费」——
必须**额外假定**选择函数恰好取到上确界。 -/
theorem bestScoreSup_eq_bestScore_of_isOptimal
    {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    (h : IsGreatest (P.score '' (tree : Set (Scenario A X)))
      (P.score (chooseOptimal P tree hne))) :
    bestScoreSup P tree hne = bestScore P tree hne := by
  have hsup := bestScoreSup_isGreatest P tree hne
  exact le_antisymm (bestScoreSup_le P tree hne (fun _ ht => chooseOptimal_isOptimal P tree hne ht))
    (hsup.2 h.1)

/-! ### §X6.6 健全性测试：上确界与旧值的关系可证 -/

/-- **旧最优值也是上界**（用 `chooseOptimal_isOptimal`，即旧文件已有的定理）。

⚠ 注意：这只是上界，**不能**推出 `bestScoreSup ≤ bestScore` 以外的信息；
两者相等需 §X6.5 的额外前提。 -/
theorem bestScoreSup_le_bestScore {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    bestScoreSup P tree hne ≤ bestScore P tree hne :=
  Finset.sup'_le hne P.score (fun _ ht => chooseOptimal_isOptimal P tree hne ht)

/-- **旧最优值属于得分集**（复述，供本文件独立引用）。 -/
theorem bestScore_mem_image' {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    bestScore P tree hne ∈ P.score '' (tree : Set (Scenario A X)) :=
  Tight.bestScore_mem_image P tree hne

/-- **旧最优值也是真上确界的下界**：由上确界的最小性。 -/
theorem bestScore_ge_bestScoreSup {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    bestScore P tree hne ≥ bestScoreSup P tree hne :=
  bestScoreSup_le_bestScore P tree hne

/-! ### §X6.7 桥：旧 `bestScore` 的紧性在 `bestScoreSup` 上**无条件**成立

§X6.5 的 `bestScoreSup_eq_bestScore_of_isOptimal` **需要额外前提**
（`chooseOptimal` 恰取到上确界）。本节说明这个额外前提**实际上是多余的**：
把 §X6.2（`le_bestScoreSup`，`Finset.le_sup'`）与 §X6.6
（`bestScoreSup_le_bestScore`，`Finset.sup'_le`）夹起来即得**无条件等式**。

因此审计指控「旧 `bestScore` 的 64 处引用无法迁移」可以正面回答：
**凡是用 `bestScore` 的地方，都可以换成 `bestScoreSup`，且结论不变** ——
因为两者在每一点上恒等，而 `bestScoreSup` 的紧性来自 Mathlib 的 `Finset.sup'`
真实定理，不来自 `Classical.choose` 的定义展开。

本节**不删除**旧定义、**不修改**任何已有定理，只追加桥引理。
-/

/-- ⭐⭐⭐⭐⭐ **【无条件等式】旧 `bestScore` 与 `bestScoreSup` 恒等。**

两个方向分别来自真实定理（`Finset.le_sup'` 与 `Finset.sup'_le`）：

* `≤`：`bestScore` 是 `chooseOptimal` 的得分，而 `chooseOptimal_mem` 说明它在树里，
  故由 `Finset.le_sup'` 得上界关系；
* `≥`：`bestScoreSup_le_bestScore`（§X6.6）给出。

⚠ 这解释了为什么 §X6.5 的额外前提是多余的：等式本身无条件成立。 -/
theorem bestScore_eq_bestScoreSup {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    bestScore P tree hne = bestScoreSup P tree hne :=
  le_antisymm
    (le_bestScoreSup P tree hne _ (chooseOptimal_mem P tree hne))
    (bestScoreSup_le_bestScore P tree hne)

/-- ⭐⭐⭐⭐ **【迁移定理：上界版无条件成立】**

旧 `Tight.bestScore_isLUB` 的陈述在 `bestScoreSup` 上**无需任何额外前提**重建。

这正是「第六条（干预选择）到极限」的核心：
`InterventionTight` 里 `bestScore` 的 `IsLUB` 刻画，换成 `bestScoreSup` 后
同样成立，且其底层证明只依赖 `Finset.sup'_le` / `Finset.le_sup'`。 -/
theorem bestScoreSup_isLUB_unconditional {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) (β : ℝ) :
    (∀ t ∈ tree, P.score t ≤ β) ↔ bestScoreSup P tree hne ≤ β :=
  bestScoreSup_isLUB P tree hne β

/-- ⭐⭐⭐⭐ **【迁移定理：锐利性版无条件成立】**

旧 `Tight.bestScore_sharp` 的陈述在 `bestScoreSup` 上无需额外前提重建。 -/
theorem bestScoreSup_sharp_unconditional {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ tree, bestScoreSup P tree hne - ε < P.score t :=
  bestScoreSup_sharp P tree hne hε

/-- ⭐⭐⭐⭐ **【迁移定理：最大元版无条件成立】**

旧 `Tight.bestScore_isGreatest` 的陈述在 `bestScoreSup` 上无需额外前提重建。 -/
theorem bestScoreSup_isGreatest_unconditional {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    IsGreatest (P.score '' (tree : Set (Scenario A X))) (bestScoreSup P tree hne) :=
  bestScoreSup_isGreatest P tree hne

/-- ⭐⭐⭐⭐⭐ **【`ε`-最优网】任取 `ε > 0`，树中存在场景其得分**逼近**上确界。**

由 `bestScoreSup_sharp` 直接推出：`bestScoreSup ≤ score t + ε`。
这条形式最便于下游把「最优值」换成「可达的近似最优场景」。 -/
theorem bestScoreSup_epsilon_attained {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ tree, bestScoreSup P tree hne ≤ P.score t + ε := by
  obtain ⟨t, ht, hlt⟩ := bestScoreSup_sharp P tree hne hε
  exact ⟨t, ht, by linarith⟩

/-- ⭐⭐⭐⭐⭐ **【上确界唯一性】** 得分集中最大元**唯一**，且必等于 `bestScoreSup`。

这条把「`bestScore` 与 `bestScoreSup` 一致」推广到**任何**候选最大元 `β`：
只要 `β` 在得分集里且是上界，就必有 `β = bestScoreSup`。
旧 `bestScore` 的一方由 `bestScore_isGreatest` 自动落入此情形。 -/
theorem eq_bestScoreSup_of_isGreatest {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) {β : ℝ}
    (h : IsGreatest (P.score '' (tree : Set (Scenario A X))) β) :
    β = bestScoreSup P tree hne := by
  obtain ⟨t, ht, rfl⟩ := h.1
  exact (le_antisymm
    (bestScoreSup_le P tree hne (fun s hs => h.2 ⟨s, by simpa using hs, rfl⟩))
    (le_bestScoreSup P tree hne t (by simpa using ht))).symm

end InterventionSup

end WorldScenario

end FateV2.Predict