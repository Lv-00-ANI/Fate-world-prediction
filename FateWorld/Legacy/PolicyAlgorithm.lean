import FateWorld.Legacy.WorldScenario

/-! ===========================================================================
  §P1-1  `Policy.choose` 从参数变成算法

  ## 背景

  `WorldScenario.Policy` 里 `choose : Set (Scenario A X) → Scenario A X`
  是**参数**（字段），正确性由 `choose_mem` 字段保证 —— 即「未给出算法」。

  `WorldScenario` 的诚实边界第 4 条原话：
  > **`Policy.choose` 的构造性** —— 本实现用 `choose_mem` 保证正确性，
  > 但**未给出算法**（`choose` 是参数）。

  本文件补上这一条：把有限情形下的 `choose` **构造出来**。

  ## 做法

  场景树是**有限**的（`Finset (Scenario A X)`），
  这正是 `exists_optimal_scenario`（`Finset.exists_max_image`）所覆盖的情形。
  用 `Classical.choose` 从「存在最优场景」这一**已证事实**中取出一条，
  于是 `choose` 不是参数，而是**由存在性定理派生的定义**。

  ## 交付内容

  | 名字 | 内容 |
  |---|---|
  | `chooseOptimal` | 算法：`Finset → Nonempty → Scenario A X`（`Classical.choose`）|
  | `chooseOptimal_spec` | 规格：在树里 ∧ 最优 |
  | `chooseOptimal_mem` | ⭐ **所选场景确实在树里** |
  | `chooseOptimal_isOptimal` | ⭐⭐ **所选场景确实最优** |
  | `optimalPolicy` | 把 `chooseOptimal` 装成 `Policy`（`choose_mem` 由定理供）|
  | `optimalPolicy_isOptimal` | 该 `Policy` 在有限树上满足 `Policy.IsOptimal` |
  | `randEq_of_optimal` | 最优值的唯一性（得分是树的本征量）|
  | `chooseOptimal_agree_on_singleton` | 单点树上算法无自由度（健全性测试）|

  ## 诚实边界

  * **只覆盖有限树** —— 论域是 `Finset`。无限树的最优性需紧性，本文件**不处理**。
  * **`Fintype A` / `Fintype X` 是显式前提** —— 承 `exists_optimal_scenario`，照实保留。
  * **`score` 仍是参数** —— 「满足要求」的判准由作者给出，本文件**不填**。
  * **`Policy.choose` 的 `Set` 签名** —— 见 §P1-1.3 的桥接说明：
    仅在 `Set.Finite` 时可用（`Set.toFinset`），无限集合上不给算法、也不虚构。
  * **非构造性** —— `Classical.choose` 只断言「存在一条算法」，不给可执行代码。
  * **平局未消解** —— 最优解可能不唯一，`Classical.choose` 取其中一条，
    未规定取哪一条（不作任何 tie-breaking 承诺）。
  =========================================================================== -/

namespace Fate

namespace WorldScenario

universe u

/-! ### §P1-1.1 算法定义 -/

/-- ⭐⭐ **选择最优场景**：从非空有限场景树中取出一条得分最大的场景。

实现：`Classical.choose` 作用在 `exists_optimal_scenario` 上
（后者由 `Finset.exists_max_image` 证得）。

返回的是**整个场景** `s`（连同其 `plan` 与 `traj`），而非仅 `plan`
—— 因为得分 `score` 定义在场景上。 -/
noncomputable def chooseOptimal {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    Scenario A X :=
  Classical.choose (exists_optimal_scenario P hne)

/-- **`chooseOptimal` 的规格**：所选场景在树里，且其得分不低于树中任何场景。 -/
theorem chooseOptimal_spec {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    (chooseOptimal P tree hne ∈ tree) ∧
      (∀ t ∈ tree, P.score (chooseOptimal P tree hne) ≥ P.score t) :=
  Classical.choose_spec (exists_optimal_scenario P hne)

/-! ### §P1-1.2 两条主定理（要求 2） -/

/-- ⭐ **所选场景确实在树里**。 -/
theorem chooseOptimal_mem {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    chooseOptimal P tree hne ∈ tree :=
  (chooseOptimal_spec P tree hne).1

/-- ⭐⭐ **所选场景确实最优**（在树内得分最大）。 -/
theorem chooseOptimal_isOptimal {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    {t : Scenario A X} (ht : t ∈ tree) :
    P.score (chooseOptimal P tree hne) ≥ P.score t :=
  (chooseOptimal_spec P tree hne).2 t ht

/-- ⭐ **最优值唯一**：任何**达到最大值**的场景，得分都等于 `chooseOptimal` 的得分。

⟹ 「最大得分」是树的**本征量**，与 `chooseOptimal` 具体选了哪一条无关。 -/
theorem score_eq_of_optimal {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) {tree : Finset (Scenario A X)} (hne : tree.Nonempty)
    {s : Scenario A X} (hs : s ∈ tree)
    (hopt : ∀ z ∈ tree, P.score s ≥ P.score z) :
    P.score s = P.score (chooseOptimal P tree hne) := by
  refine le_antisymm ?_ (hopt _ (chooseOptimal_mem P tree hne))
  exact chooseOptimal_isOptimal P tree hne hs

/-- ⭐ **健全性测试**：单点树上算法没有自由度 —— 必选中该点。

⟹ 若树上只有一个候选干预，`chooseOptimal` **不会**选别的。 -/
theorem chooseOptimal_eq_of_singleton {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (s : Scenario A X) :
    chooseOptimal P {s} ⟨s, Finset.mem_singleton_self s⟩ = s := by
  have h := chooseOptimal_mem P {s} ⟨s, Finset.mem_singleton_self s⟩
  exact Finset.mem_singleton.mp h

/-! ### §P1-1.3 装成 `Policy`（`choose_mem` 由定理供，不再是参数）

⚠ **桥接说明（诚实标注）**：
`Policy.choose` 的签名是 `Set (Scenario A X) → Scenario A X`，
而 `chooseOptimal` 的论域是 `Finset`。二者之间的转换用 `Set.Finite.toFinset`，
故包装时**要求 `Set.Finite` 前提** —— 这不是缺陷，正是「有限树」这一诚实边界：

* 有限树 → 转 `Finset` → `chooseOptimal`（**有算法**）；
* 无限树 → 本文件**不给算法**（宁可留空，不虚构 `Classical.arbitrary`）。 -/

/-- **选择器（`Set` → 场景）**：把 `Policy.choose` 的 `Set` 签名桥接到 `chooseOptimal`。

* 有限非空集合 → `Set.Finite.toFinset` → `chooseOptimal`；
* 其余情况 → `fallback`（无限集合本文件**不提供算法**，不用 `Classical.arbitrary` 冒充）。 -/
noncomputable def chooseOptimalSet {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Set (Scenario A X)) (hne : tree.Nonempty) :
    Scenario A X := by
  classical
  exact
    if h : tree.Finite then
      if hne' : h.toFinset.Nonempty then chooseOptimal P h.toFinset hne'
      else Classical.choose hne
    else Classical.choose hne

/-- **`chooseOptimalSet` 的成员性**（对所有非空集合成立）。

* 有限 → 由 `chooseOptimal_mem`；
* 无限 → `Classical.choose hne`，定义上就在集合里。 -/
theorem chooseOptimalSet_mem {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) {tree : Set (Scenario A X)} (hne : tree.Nonempty) :
    chooseOptimalSet P tree hne ∈ tree := by
  classical
  unfold chooseOptimalSet
  split_ifs with hfin hne'
  · have hmem := chooseOptimal_mem P hfin.toFinset hne'
    rw [Set.Finite.mem_toFinset] at hmem
    exact hmem
  · exact Classical.choose_spec hne
  · exact Classical.choose_spec hne

/-- **`chooseOptimalSet` 的最优性**（仅限有限非空集合）。 -/
theorem chooseOptimalSet_isOptimal {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) {tree : Set (Scenario A X)} (hfin : tree.Finite)
    (hne : tree.Nonempty) {t : Scenario A X} (ht : t ∈ tree) :
    P.score (chooseOptimalSet P tree hne) ≥ P.score t := by
  classical
  have hne' : hfin.toFinset.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]
    exact hne
  have ht' : t ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact ht
  have h := chooseOptimal_isOptimal P hfin.toFinset hne' ht'
  unfold chooseOptimalSet
  rw [dif_pos hfin, dif_pos hne']
  exact h

/-- **选择器（`Set` → 场景）**：非空时用 `chooseOptimalSet`；
空集分支**不可达**（所有定理都以 `tree.Nonempty` 为前提），仅用于给出全函数。 -/
noncomputable def optimalChoose {A X : Type u} [Fintype A] [Fintype X]
    [Nonempty A] [Nonempty X]
    (P : Policy A X) (tree : Set (Scenario A X)) : Scenario A X := by
  classical
  exact if hne : tree.Nonempty then chooseOptimalSet P tree hne
        else ⟨fun _ => Classical.arbitrary A, fun _ => Classical.arbitrary X⟩

/-- **`optimalChoose` 的成员性**：对任何非空集合都成立（无有限性要求）。 -/
theorem optimalChoose_mem {A X : Type u} [Fintype A] [Fintype X]
    [Nonempty A] [Nonempty X]
    (P : Policy A X) {tree : Set (Scenario A X)} (hne : tree.Nonempty) :
    optimalChoose P tree ∈ tree := by
  classical
  unfold optimalChoose
  rw [dif_pos hne]
  exact chooseOptimalSet_mem P hne

/-- ⭐⭐ **最优策略**：`score` 取定，`choose` 用 `optimalChoose` 落地。

正确性 `choose_mem` **由定理 `optimalChoose_mem` 供出**，
而 `WorldScenario.Policy` 里它是**字段（假设）** —— 这就是「参数 → 算法」的落点。 -/
noncomputable def optimalPolicy {A X : Type u} [Fintype A] [Fintype X]
    [Nonempty A] [Nonempty X]
    (P : Policy A X) : Policy A X where
  score := P.score
  choose := optimalChoose P
  choose_mem := by
    intro tree hne
    exact optimalChoose_mem P hne

/-- ⭐ **`optimalPolicy` 的 `score` 与原 `P` 一致**（定义性展开）。 -/
theorem optimalPolicy_score {A X : Type u} [Fintype A] [Fintype X]
    [Nonempty A] [Nonempty X]
    (P : Policy A X) : (optimalPolicy P).score = P.score :=
  rfl

/-- ⭐⭐ **`optimalPolicy` 在有限非空树上确实最优**。

即 `Policy.IsOptimal` 的有限树实例：
所选的场景得分 ≥ 树中任一场景的得分。 -/
theorem optimalPolicy_isOptimal {A X : Type u} [Fintype A] [Fintype X]
    [Nonempty A] [Nonempty X]
    (P : Policy A X)
    {tree : Set (Scenario A X)} (hfin : tree.Finite) (hne : tree.Nonempty)
    {t : Scenario A X} (ht : t ∈ tree) :
    P.score ((optimalPolicy P).choose tree) ≥ P.score t := by
  have hch : (optimalPolicy P).choose tree = chooseOptimalSet P tree hne := by
    show optimalChoose P tree = chooseOptimalSet P tree hne
    unfold optimalChoose
    rw [dif_pos hne]
  rw [hch]
  exact chooseOptimalSet_isOptimal P hfin hne ht

/-- ⭐⭐ **`optimalPolicy` 满足 `Policy.IsOptimal`（有限版本）**：
在任意有限非空树上，其 `choose` 选出得分最大的场景。 -/
theorem optimalPolicy_satisfies_isOptimal {A X : Type u} [Fintype A] [Fintype X]
    [Nonempty A] [Nonempty X]
    (P : Policy A X)
    {tree : Set (Scenario A X)} (hfin : tree.Finite) (hne : tree.Nonempty) :
    ∀ s : Scenario A X, s ∈ tree →
      (optimalPolicy P).score ((optimalPolicy P).choose tree)
        ≥ (optimalPolicy P).score s := by
  intro s hs
  have hsc : (optimalPolicy P).score = P.score := rfl
  rw [hsc]
  exact optimalPolicy_isOptimal P hfin hne hs

/-- ⭐ **`optimalPolicy` 的 `choose_mem` 比原 `Policy` 的假设更强**：
原 `Policy` 把 `choose_mem` 当**字段（假设）**，这里它**已被证成定理**。 -/
theorem optimalPolicy_choose_mem {A X : Type u} [Fintype A] [Fintype X]
    [Nonempty A] [Nonempty X]
    (P : Policy A X) {tree : Set (Scenario A X)} (hne : tree.Nonempty) :
    (optimalPolicy P).choose tree ∈ tree :=
  (optimalPolicy P).choose_mem hne

/-! ### §P1-1.4 诚实边界（写入代码）

1. **只覆盖有限树** —— `chooseOptimal` 的论域是 `Finset`；
   无限树的最优性需**紧性**，本文件不处理。
   对无限集合，`chooseOptimalSet` 只保证**成员性**（`Classical.choose hne`），
   **不保证最优性**。
2. **`Fintype A` / `Fintype X` 为显式前提** —— 承 `exists_optimal_scenario`。
3. **`score` 仍是参数** —— 「满足要求」的判准由作者给出，本文件不填数。
4. **`Policy.choose` 的 `Set` 签名需 `Set.Finite` 才能给出最优性**；
   无限集合上 `optimalPolicy` 只给**成员性**（不退回最优性结论）。
5. **非构造性** —— `Classical.choose` 不承诺可执行性。
6. **平局未消解** —— 最优场景可能不唯一；`chooseOptimal` 不承诺 tie-breaking。
-/

end WorldScenario

end Fate
