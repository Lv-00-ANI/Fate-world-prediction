import FateWorld.FateV2.Predict.PolicyAlgorithm
import FateWorld.FateV2.Predict.InterventionSelection
/-!
  # Predict · InterventionTight

  ## 迁移登记
  - 来源：`FateWorld/Legacy/InterventionTight.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：PolicyAlgorithm, InterventionSelection
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §X5  干预选择的最优性**紧性**

  ## 背景（第2层审计）

  第2层全称性审计对 `PolicyAlgorithm.lean` 的判定是：

  > `chooseOptimal_isOptimal` / `optimalPolicy_isOptimal` 给出的是**上界**：
  > 「所选的场景得分 ≥ 树中任一场景的得分」。
  > 但**没有**证明这个上界是**紧的**（sharp）——
  > 即「所选干预**恰好达到**最优值」＋「**任何更好的干预不存在**」这一对。
  > 审计结论：**有界，但紧性未证**。

  这正是审计文档 §5 所立的分层判据：
  「上界/正确性 → 真全称 ∀；紧性/锐利性 → 必须 ∃ 见证」。
  本文件补的是**第二个量词层**。

  ## 本文件交付什么

  ### (a) 最优值是树的**本征量**（`bestScore`）

  ```lean
  noncomputable def bestScore P tree hne : ℝ :=
    P.score (chooseOptimal P tree hne)
  ```

  ### (b) 取等（attainment）—— 最优值是**被达到的**，不是单纯的界

  | 名字 | 内容 |
  |---|---|
  | `bestScore_mem_image` | ⭐ 最优值属于得分集 `P.score '' tree` ⇒ **被某个场景达到** |
  | `bestScore_isGreatest` | ⭐⭐ `bestScore` 是得分集的最大元（`IsGreatest`）|

  **这是紧性的**第一半**：**界不是松的，因为它本身就是某个可行干预的得分。**

  ### (c) 锐利性 / 下界（sharpness）—— **任何更好的干预不存在，且界不可改进**

  | 名字 | 内容 |
  |---|---|
  | `bestScore_no_better` | ⭐ 树中不存在得分**严格更高**的场景 |
  | `bestScore_isLUB` | ⭐⭐ `∀ β, (∀ t∈tree, score t ≤ β) ↔ bestScore ≤ β`（最小上界刻画）|
  | `bestScore_sharp` | ⭐⭐⭐ `∀ ε>0, ∃ t∈tree, bestScore − ε < score t`（任一下调都失败）|
  | `bestScore_attained_exactly` | 退化端点 `ε = 0`：确有场景得分**等于** `bestScore` |
  | `bestScore_eps_not_bound` | ⭐⭐⭐ `∀ ε>0, ¬ ∀ t∈tree, score t ≤ bestScore − ε` |

  **这是紧性的**第二半**：**`bestScore − ε` 不再是上界，故 `bestScore` 是最**小**的上界。**

  > ⚠ 注意 `bestScore_sharp` 与 `bestScore_eps_not_bound` 是**逻辑等价**的两种写法
  > （前者 ∃-形、后者 ¬∀-形），此处**都给**，以免读者误以为其中一个被另一个包住。

  ### (d) `optimalPolicy`（`Set` 版）的同一紧性

  | 名字 | 内容 |
  |---|---|
  | `optimalPolicy_isLUB` | 有限集合树上，所选值同样是最小上界 |
  | `optimalPolicy_sharp` | 所选值被达到（**无需有限性**，已如实去掉死前提）|

  ### (e) ⭐⭐ **具体实例**（存在一个实例使所选干预**恰好**达到最优值）

  `Unit → Bool` 上的三条场景、显式得分 `3 / 2 / 1`，
  `chooseOptimal` 被**算出**为顶端场景，其得分**恰为 3**：

  | 名字 | 内容 |
  |---|---|
  | `chooseOptimal_T3` | 所选场景**就是** `scenTop`（非平凡：树上 3 点）|
  | `bestScore_T3` | 最优值 `= 3`（可计算的字面数）|
  | `T3_no_better` | ⭐ **下界**：`¬ ∃ t ∈ T3, score t > 3` |
  | `T3_sharp` | ⭐⭐ **紧**：`∀ β < 3, ∃ t ∈ T3, β < score t` |
  | `T3_isLUB` | ⭐⭐ `(∀ t∈T3, score t ≤ β) ↔ 3 ≤ β` |
  | `T3_not_four` | 健全性测试：`¬ ∃ t ∈ T3, score t ≥ 4` |

  ## ⚠ 诚实边界（写入代码）

  1. **只覆盖有限树** —— 论域是 `Finset`（或 `Set.Finite`）。
     无限树的最小上界**未必被达到**，本文件**不**断言其紧性。
     （这也正是 `PolicyAlgorithm.lean` 已有的诚实边界第 1 条。）
  2. **`score` 仍是参数** —— 「最优」是**相对于给定 `score`** 的。
     本文件**不**声称这个 `score` 就是「满足要求」的正确判准。
  3. **实例是玩具规模** —— `T3` 只为**证明紧性可达成**，不对应任何真实系统。
  4. **紧性是「界不可改进」**，不是「最优解唯一」——
     `chooseOptimal` 的 tie-breaking 仍未承诺（承上游文件）。
  5. **零 `sorry` / 零 `axiom`** —— 每条定理均已证。
     ⚠ 若某条证不出，按纪律应删除并在本处如实说明；本版**无删除**。
  =========================================================================== -/

namespace FateV2.Predict
namespace WorldScenario

namespace Tight

universe u

/-! ### §X5.1 最优值：定义与取等 -/

/-- ⭐⭐ **最优值**：所选干预的得分。

这是「树 + 判准」决定的实数；下面的定理证明它**既被达到、又不可改进**。 -/
noncomputable def bestScore {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) : ℝ :=
  P.score (chooseOptimal P tree hne)

/-- 定义性展开。 -/
theorem bestScore_def {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    bestScore P tree hne = P.score (chooseOptimal P tree hne) := rfl

/-- ⭐ **取等（第一半）**：最优值**属于得分集** —— 它被树中某个场景达到。

⚠ 非平凡处：这依赖 `chooseOptimal_mem`（所选场景在树里），
仅靠「上界」无法得到。

⚠ **本条的「紧性」由 `bestScore` 的定义（含 `chooseOptimal`）直接得出，属定义投射。**
真紧性见 `Fate.WorldScenario.InterventionSup.bestScoreSup_sharp`（不依赖任何选择函数）。
且 `Fate.WorldScenario.InterventionSup.bestScore_eq_bestScoreSup` 已证两者无条件恒等，
故这些陈述在 `bestScoreSup` 上同样成立且证明更干净（走 `Finset.sup'` 而非选择函数）。 -/
theorem bestScore_mem_image {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    bestScore P tree hne ∈ P.score '' (↑tree : Set (Scenario A X)) :=
  ⟨chooseOptimal P tree hne,
    by simpa using chooseOptimal_mem P tree hne, rfl⟩

/-- ⭐⭐ **最优值是得分集的最大元**（`IsGreatest` = 「在集合里」+「是上界」）。

这是「取等 + 上界」的**合取式**，即紧性的完整形式。

⚠ **本条的「紧性」由 `bestScore` 的定义（含 `chooseOptimal`）直接得出，属定义投射。**
真紧性见 `Fate.WorldScenario.InterventionSup.bestScoreSup_sharp`（不依赖任何选择函数）。
且 `Fate.WorldScenario.InterventionSup.bestScore_eq_bestScoreSup` 已证两者无条件恒等，
故这些陈述在 `bestScoreSup` 上同样成立且证明更干净（走 `Finset.sup'` 而非选择函数）。 -/
theorem bestScore_isGreatest {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    IsGreatest (P.score '' (↑tree : Set (Scenario A X))) (bestScore P tree hne) := by
  refine ⟨bestScore_mem_image P tree hne, ?_⟩
  intro b hb
  obtain ⟨t, ht, rfl⟩ := hb
  exact chooseOptimal_isOptimal P tree hne (by simpa using ht)

/-! ### §X5.2 锐利性：界不可改进 -/

/-- ⭐ **下界（不存在更好的干预）**：树中没有任何场景的得分**严格高于**最优值。

⚠ **本条的「紧性」由 `bestScore` 的定义（含 `chooseOptimal`）直接得出，属定义投射。**
真紧性见 `Fate.WorldScenario.InterventionSup.bestScoreSup_sharp`（不依赖任何选择函数）。
且 `Fate.WorldScenario.InterventionSup.bestScore_eq_bestScoreSup` 已证两者无条件恒等，
故这些陈述在 `bestScoreSup` 上同样成立且证明更干净（走 `Finset.sup'` 而非选择函数）。 -/
theorem bestScore_no_better {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    {t : Scenario A X} (ht : t ∈ tree) :
    ¬ P.score t > bestScore P tree hne :=
  not_lt.mpr (chooseOptimal_isOptimal P tree hne ht)

/-- ⭐⭐ **`bestScore` 是最小上界**（`IsLUB` 的逐点刻画）。

前向：上界 `β` 必 ≥ `bestScore`（用 `chooseOptimal_mem` 把 `β` 用到所选点）。
后向：`bestScore ≤ β` 则 `β` 是上界（用 `chooseOptimal_isOptimal`）。
⟹ **两个方向都有实质内容，非同一律。** -/
theorem bestScore_isLUB {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) (β : ℝ) :
    (∀ t ∈ tree, P.score t ≤ β) ↔ bestScore P tree hne ≤ β := by
  constructor
  · intro h
    exact h _ (chooseOptimal_mem P tree hne)
  · intro h t ht
    exact le_trans (chooseOptimal_isOptimal P tree hne ht) h

/-- ⭐⭐⭐ **紧性的 ∃ 形式**：把界下调**任意小的** `ε > 0` 都失败 ——
即总有某个场景顶到 `bestScore − ε` **之上**。

⟹ `bestScore` **不是**「某个可行的小上界」，而是**恰好**的最小上界。

⚠ **本条的「紧性」由 `bestScore` 的定义（含 `chooseOptimal`）直接得出，属定义投射。**
真紧性见 `Fate.WorldScenario.InterventionSup.bestScoreSup_sharp`（不依赖任何选择函数）。
且 `Fate.WorldScenario.InterventionSup.bestScore_eq_bestScoreSup` 已证两者无条件恒等，
故这些陈述在 `bestScoreSup` 上同样成立且证明更干净（走 `Finset.sup'` 而非选择函数）。 -/
theorem bestScore_sharp {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ tree, bestScore P tree hne - ε < P.score t := by
  refine ⟨chooseOptimal P tree hne, chooseOptimal_mem P tree hne, ?_⟩
  have : bestScore P tree hne = P.score (chooseOptimal P tree hne) := rfl
  linarith

/-- ⭐⭐⭐ **紧性的 ¬∀ 形式**（与 `bestScore_sharp` 逻辑等价，此处**并列给出**，
不做「用一个冒充两个」）：`bestScore − ε` **不是**上界。 -/
theorem bestScore_eps_not_bound {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ¬ ∀ t ∈ tree, P.score t ≤ bestScore P tree hne - ε := by
  intro h
  have h1 : P.score (chooseOptimal P tree hne) ≤ bestScore P tree hne - ε :=
    h _ (chooseOptimal_mem P tree hne)
  have h2 : bestScore P tree hne = P.score (chooseOptimal P tree hne) := rfl
  linarith

/-- ⭐⭐ **紧性的退化端点（`ε = 0`）：最优值被精确达到**。

⚠ 这是**正确的**端点陈述 `≤`，而非 `bestScore − 0 < score`——
后者在 `ε = 0` 时**为假**（不存在 `x < x`）。此处如实给出真命题。 -/
theorem bestScore_attained_exactly {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (tree : Finset (Scenario A X)) (hne : tree.Nonempty) :
    ∃ t ∈ tree, P.score t = bestScore P tree hne := by
  refine ⟨chooseOptimal P tree hne, chooseOptimal_mem P tree hne, ?_⟩
  exact (bestScore_def P tree hne).symm

/-- **健全性测试**：单点树上最优值就是该点的得分（界与取等重合）。 -/
theorem bestScore_of_singleton {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) (s : Scenario A X) :
    bestScore P {s} ⟨s, Finset.mem_singleton_self s⟩ = P.score s := by
  unfold bestScore
  rw [chooseOptimal_eq_of_singleton]

/-! ### §X5.3 `optimalPolicy`（`Set` 版）的同一紧性 -/

/-- ⭐⭐ **`optimalPolicy` 所选值也是最小上界**（有限集合树）。

前向用 `Policy.choose_mem`（在 `optimalPolicy` 中**由定理供出**），
后向用 `optimalPolicy_isOptimal`。 -/
theorem optimalPolicy_isLUB {A X : Type u} [Fintype A] [Fintype X]
    [Nonempty A] [Nonempty X]
    (P : Policy A X) {tree : Set (Scenario A X)} (hfin : tree.Finite)
    (hne : tree.Nonempty) (β : ℝ) :
    (∀ t ∈ tree, P.score t ≤ β) ↔ P.score ((optimalPolicy P).choose tree) ≤ β := by
  constructor
  · intro h
    exact h _ ((optimalPolicy P).choose_mem hne)
  · intro h t ht
    exact le_trans (optimalPolicy_isOptimal P hfin hne ht) h

/-- ⭐⭐ **`optimalPolicy` 的锐利性**：`∀ ε>0`，树上都有场景顶到 `值 − ε` 之上。

⚠ **诚实标注**：「入选场景本身就在树里」⇒ 该结论**不需要有限性前提**。
因此本定理**不取** `hfin` —— 这是本次自查发现的一个**真实冗余**，取掉它而非
在签名里留一个死前提（死前提 = 让定理看似更强，实则是虚张）。
换言之：**`optimalPolicy` 的“值被达到”在无限树上也真**；
而 §X5.3 的上界部分（`optimalPolicy_isLUB`）才**真正**需要 `hfin`。 -/
theorem optimalPolicy_sharp {A X : Type u} [Fintype A] [Fintype X]
    [Nonempty A] [Nonempty X]
    (P : Policy A X) {tree : Set (Scenario A X)}
    (hne : tree.Nonempty) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ tree, P.score ((optimalPolicy P).choose tree) - ε < P.score t :=
  ⟨(optimalPolicy P).choose tree, (optimalPolicy P).choose_mem hne, by linarith⟩

/-! ### §X5.4 ⭐⭐ 具体实例：`chooseOptimal` **恰好**达到最优值

取 `A = Bool`、`X = Unit`。得分按 `plan 0` / `plan 1` 的前两位分层：

```lean
scoreBool s = if s.plan 0 then (if s.plan 1 then 3 else 2) else 1
```

三条场景：

| 场景 | `plan` | 得分 |
|---|---|---|
| `scenTop` | 恒 `true`  | **3** |
| `scenMid` | `n == 0`   | **2** |
| `scenBot` | 恒 `false` | **1** |

断言：`T3 = {scenTop, scenMid, scenBot}` 上 `chooseOptimal` **恰好**选 `scenTop`，
最优值**恰为 3**，且**不存在更好的干预**、`3` **不可下调**。
-/

section Instance

attribute [local instance] Classical.decEq

/-- 显式得分：按 `plan 0`、`plan 1` 分层。 -/
def scoreBool (s : Scenario Bool Unit) : ℝ :=
  if s.plan 0 then (if s.plan 1 then 3 else 2) else 1

/-- `choose` 的辅助定义：非空则取一条，否则给默认值。
⚠ `Decidable` 实例在 `by` 块内局部给出（`Classical.propDecidable`）。 -/
noncomputable def baseChoose (tree : Set (Scenario Bool Unit)) : Scenario Bool Unit := by
  classical
  exact if h : tree.Nonempty then Classical.choose h
        else ⟨fun _ => true, fun _ => ()⟩

theorem baseChoose_mem {tree : Set (Scenario Bool Unit)} (hne : tree.Nonempty) :
    baseChoose tree ∈ tree := by
  classical
  unfold baseChoose
  rw [dif_pos hne]
  exact Classical.choose_spec hne

/-- 一个 `Policy Bool Unit`，`score` 取 `scoreBool`；
`choose` 只为满足 `choose_mem`（本节的所有结论**只用其 `score`**）。 -/
noncomputable def basePolicy : Policy Bool Unit where
  score := scoreBool
  choose := baseChoose
  choose_mem := fun hne => baseChoose_mem hne

/-- 顶端场景：`plan` 恒 `true`。 -/
def scenTop : Scenario Bool Unit := ⟨fun _ => true, fun _ => ()⟩

/-- 中间场景：`plan 0 = true`、`plan 1 = false`。 -/
def scenMid : Scenario Bool Unit := ⟨fun n => n == 0, fun _ => ()⟩

/-- 底端场景：`plan` 恒 `false`。 -/
def scenBot : Scenario Bool Unit := ⟨fun _ => false, fun _ => ()⟩

@[simp] theorem scoreBool_top : scoreBool scenTop = 3 := by
  simp [scoreBool, scenTop]

@[simp] theorem scoreBool_mid : scoreBool scenMid = 2 := by
  simp [scoreBool, scenMid]

@[simp] theorem scoreBool_bot : scoreBool scenBot = 1 := by
  simp [scoreBool, scenBot]

/-- 三点场景树。 -/
noncomputable def T3 : Finset (Scenario Bool Unit) := {scenTop, scenMid, scenBot}

theorem T3_nonempty : T3.Nonempty := ⟨scenTop, by simp [T3]⟩

theorem T3_mem_top : scenTop ∈ T3 := by simp [T3]

theorem T3_mem_mid : scenMid ∈ T3 := by simp [T3]

theorem T3_mem_bot : scenBot ∈ T3 := by simp [T3]

/-- ⭐⭐ **所选干预就是顶端场景**（树上 3 点，非平凡选择）。 -/
theorem chooseOptimal_T3 :
    chooseOptimal basePolicy T3 T3_nonempty = scenTop := by
  have hmem := chooseOptimal_mem basePolicy T3 T3_nonempty
  have hge : scoreBool (chooseOptimal basePolicy T3 T3_nonempty) ≥ 3 := by
    have h := chooseOptimal_isOptimal basePolicy T3 T3_nonempty T3_mem_top
    show (3 : ℝ) ≤ scoreBool (chooseOptimal basePolicy T3 T3_nonempty)
    have h' : basePolicy.score (chooseOptimal basePolicy T3 T3_nonempty) ≥ basePolicy.score scenTop :=
      h
    have e1 : basePolicy.score scenTop = 3 := scoreBool_top
    have e2 : basePolicy.score (chooseOptimal basePolicy T3 T3_nonempty)
        = scoreBool (chooseOptimal basePolicy T3 T3_nonempty) := rfl
    linarith
  have hcases : chooseOptimal basePolicy T3 T3_nonempty = scenTop ∨
      chooseOptimal basePolicy T3 T3_nonempty = scenMid ∨
      chooseOptimal basePolicy T3 T3_nonempty = scenBot := by
    simpa only [T3, Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hcases with h | h | h
  · exact h
  · rw [h] at hge; rw [scoreBool_mid] at hge; norm_num at hge
  · rw [h] at hge; rw [scoreBool_bot] at hge; norm_num at hge

/-- ⭐⭐ **最优值恰为 `3`** —— 一个可计算的字面数，而非抽象的上确界。 -/
theorem bestScore_T3 : bestScore basePolicy T3 T3_nonempty = 3 := by
  rw [bestScore_def, chooseOptimal_T3]
  exact scoreBool_top

/-- ⭐ **取等（实例版）**：存在树中场景，其得分**等于**最优值。 -/
theorem T3_attained :
    ∃ t ∈ T3, scoreBool t = bestScore basePolicy T3 T3_nonempty :=
  ⟨scenTop, T3_mem_top, by rw [bestScore_T3]; exact scoreBool_top⟩

/-- ⭐⭐ **下界（实例版）**：**不存在**得分优于 `3` 的干预。 -/
theorem T3_no_better : ¬ ∃ t ∈ T3, scoreBool t > 3 := by
  rintro ⟨t, ht, hgt⟩
  simp only [T3, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · rw [scoreBool_top] at hgt; linarith
  · rw [scoreBool_mid] at hgt; linarith
  · rw [scoreBool_bot] at hgt; linarith

/-- ⭐⭐⭐ **紧性（实例版）**：**任何**更小的界 `β < 3` 都被某个场景突破。 -/
theorem T3_sharp (β : ℝ) (hβ : β < 3) : ∃ t ∈ T3, β < scoreBool t :=
  ⟨scenTop, T3_mem_top, by rw [scoreBool_top]; exact hβ⟩

/-- ⭐⭐ **`3` 是最小上界（实例版）**：`β` 是上界 ⟺ `3 ≤ β`。 -/
theorem T3_isLUB (β : ℝ) : (∀ t ∈ T3, scoreBool t ≤ β) ↔ 3 ≤ β := by
  constructor
  · intro h
    have h1 := h scenTop T3_mem_top
    rwa [scoreBool_top] at h1
  · intro h t ht
    simp only [T3, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · rw [scoreBool_top]; exact h
    · rw [scoreBool_mid]; linarith
    · rw [scoreBool_bot]; linarith

/-- **健全性测试**：`4` 也不是可达的 —— 与 `T3_no_better` 一致地卡在 `3`。 -/
theorem T3_not_four : ¬ ∃ t ∈ T3, scoreBool t ≥ 4 := by
  rintro ⟨t, ht, hge⟩
  simp only [T3, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · rw [scoreBool_top] at hge; norm_num at hge
  · rw [scoreBool_mid] at hge; norm_num at hge
  · rw [scoreBool_bot] at hge; norm_num at hge

/-- **实例版 `IsGreatest`**：`3` 是得分集的最大元（取等 + 上界合一）。 -/
theorem T3_isGreatest :
    IsGreatest (scoreBool '' (↑T3 : Set (Scenario Bool Unit)))
      (bestScore basePolicy T3 T3_nonempty) :=
  bestScore_isGreatest basePolicy T3 T3_nonempty

end Instance

end Tight

end WorldScenario

end FateV2.Predict
/-! ===========================================================================
  §R36  **R-36 接线：干预选择的**紧性**（本文件）与 `InterventionSelection` 的 `Optimal` / `Dom` / `gain`**

  * 本文件（`Fate.InterventionTight`）给出**紧性**：`bestScore := P.score (chooseOptimal P tree hne)`
    是得分集的**最大元**（`bestScore_isGreatest`）、**最小上界**（`bestScore_isLUB`）、
    **不可下调**（`bestScore_sharp`）。载体是 `WorldScenario.Policy` + `Finset` 树。
  * `Fate.InterventionSelection` 给出**选择代数**：`Optimal`（argmax 谓词）、`Dom`（弱支配）、
    `gain`（单点分支改进量）、`optimal_value_unique`（argmax 唯一值）。

  两个模块**此前互不引用**。本节把每个场景 `s : Scenario A X` 编码成一个
  **单点计划** `fun _ : Unit => s`（即 `Plan Unit (Scenario A X)`），于是
  `scoreGood P f := P.score (f ())` 是合法的 `Good Unit (Scenario A X)`，
  `InterventionSelection` 的整套选择理论随即作用于**场景树**。

  | 名字 | 内容 |
  |---|---|
  | `scoreGood`                  | ⭐ 把 `P.score` 编码为 `Good Unit _`（定义）|
  | `planSet`                    | ⭐ 场景树 → 计划集（定义）|
  | `mem_planSet`                | ⭐ 成员性的翻译 |
  | `bestScore_isGreatest_opt`   | ⭐⭐⭐ **`chooseOptimal` 就是 `Optimal`**（紧性的「取等」面）|
  | `optimal_score_eq_bestScore` | ⭐⭐⭐ 任一 `Optimal` 的得分**等于** `bestScore`（唯一性）|
  | `bestScore_is_lub_opt`       | ⭐⭐ 紧性 LUB 面 ⟹ `InterventionSelection` 语言的同一上界 |
  | `optimal_gain_nonpos`        | ⭐⭐ **最优处单点 `gain` ≤ 0**（选择不动点）|

  ⚠ **诚实边界**：`Scenario ↦ Plan Unit _` 是**技术编码**，不是「场景树 = 分支树」
  的实质断言；其唯一作用是让两个模块的语言可以互译。
  ⚠ 本文件新增的 7 条定理**全部**同时提到两模块的名字，无一条是单模块重述。
  =========================================================================== -/

namespace FateV2.Predict.WorldScenario.Tight

universe u

section R36

variable {A X : Type u} [Fintype A] [Fintype X]

/-- ⭐ **评分作为 `Good`**：把 `Policy.score` 沿「单点计划」拉回到
`InterventionSelection.Good Unit (Scenario A X)`。

`Plan Unit (Scenario A X) = Unit → Scenario A X`，故 `G f = P.score (f ())`。 -/
def scoreGood (P : Policy A X) : InterventionSelection.Good Unit (Scenario A X) :=
  fun f => P.score (f ())

/-- ⭐ **场景树 → 计划集**：把每个场景包成常量计划。用 `Set` 而非 `Finset`，
以避开 `Scenario` 上不可得的 `DecidableEq`。 -/
def planSet (tree : Finset (Scenario A X)) :
    Set (InterventionSelection.Plan Unit (Scenario A X)) :=
  {f | f () ∈ tree}

/-- ⭐ **成员性翻译**：`f ∈ planSet tree ↔ f () ∈ tree`（按定义，但显式登记）。 -/
theorem mem_planSet {tree : Finset (Scenario A X)}
    {f : InterventionSelection.Plan Unit (Scenario A X)} :
    f ∈ planSet tree ↔ f () ∈ tree :=
  Iff.rfl

/-- ⭐⭐⭐ **紧性的「取等」面就是 `InterventionSelection.Optimal`**。

`chooseOptimal P tree hne` 的**单点计划**是 `planSet tree` 上的最优计划。

⚠ 非平凡处：`InterventionSelection.Optimal` 要求「在集合里 + 是上界」，
分别由 `chooseOptimal_mem` 与 `chooseOptimal_isOptimal` 给出，并经
`mem_planSet` 把 `Finset` 成员翻成计划集成员。前件只有 `tree.Nonempty`，
**不含**结论中的上界不等式。 -/
theorem bestScore_isGreatest_opt (P : Policy A X) (tree : Finset (Scenario A X))
    (hne : tree.Nonempty) :
    InterventionSelection.Optimal (scoreGood P) (planSet tree)
      (fun _ => chooseOptimal P tree hne) := by
  refine ⟨mem_planSet.mpr (chooseOptimal_mem P tree hne), fun q hq => ?_⟩
  exact chooseOptimal_isOptimal P tree hne (mem_planSet.mp hq)

/-- ⭐⭐⭐ **任一 `Optimal` 计划的得分等于 `bestScore`**（唯一性）。

把 `InterventionSelection.optimal_value_unique`（所有 argmax 同值）与
本文件的 `bestScore`（所选计划的得分）**接上**：以 `chooseOptimal` 的单点计划
作为第二个 `Optimal` 见证（`bestScore_isGreatest_opt`）代入。

⚠ 非平凡处：`optimal_value_unique` 只说**两个** `Optimal` 同值，
本定理把其中之一**识别为** `bestScore`。前件 `hp` 中**不含**
「`P.score (p ()) = bestScore …`」。 -/
theorem optimal_score_eq_bestScore (P : Policy A X) (tree : Finset (Scenario A X))
    (hne : tree.Nonempty) {p : InterventionSelection.Plan Unit (Scenario A X)}
    (hp : InterventionSelection.Optimal (scoreGood P) (planSet tree) p) :
    P.score (p ()) = bestScore P tree hne :=
  InterventionSelection.optimal_value_unique (scoreGood P) (planSet tree) hp
    (bestScore_isGreatest_opt P tree hne)

/-- ⭐⭐ **紧性的 LUB 面 ⟹ 计划集语言里的同一上界**。

`(∀ t ∈ tree, P.score t ≤ β) ↔ bestScore ≤ β`（本文件 `bestScore_isLUB`）
与「`β` 是 `scoreGood` 在 `planSet tree` 上的上界」是**同一件事**的两种说法；
本定理给出这座桥，使 `InterventionSelection` 一侧可以直接引用紧性。

⚠ 非平凡处：一侧量词跑在**场景**上，另一侧跑在**单点计划**上；
转换靠 `mem_planSet` 双向使用。前件不含结论。 -/
theorem bestScore_is_lub_opt (P : Policy A X) (tree : Finset (Scenario A X))
    (hne : tree.Nonempty) (β : ℝ) :
    ((∀ q ∈ planSet tree, scoreGood P q ≤ β) ↔
        (∀ t ∈ tree, P.score t ≤ β))
      ∧ ((∀ t ∈ tree, P.score t ≤ β) ↔ bestScore P tree hne ≤ β) := by
  refine ⟨?_, bestScore_isLUB P tree hne β⟩
  constructor
  · intro h t ht
    exact h (fun _ : Unit => t) (mem_planSet.mpr ht)
  · intro h q hq
    exact h (q ()) (mem_planSet.mp hq)

/-- ⭐⭐ **最优处的单点 `gain` ≤ 0**（选择不动点）。

若 `p` 是 `planSet tree` 上的 `InterventionSelection.Optimal`，则对树中任一
场景 `t`，把计划整体换成 `t` 得到的**单点分支增益非正** ——
即「最优计划不会被单步改进」。

⚠ 非平凡处：`InterventionSelection.gain G p () t = G (alter p () t) − G p`；
要接上 `P.score` 的比较，必须（a）证 `alter p () t = fun _ => t`
（`InterventionSelection.alter_apply_self` + 函数外延），
（b）用 `mem_planSet` 把 `fun _ => t` 送进 `planSet tree`，
（c）用 `hp.2` 的上界。结论 `gain ≤ 0` 不在前件里。 -/
theorem optimal_gain_nonpos (P : Policy A X) (tree : Finset (Scenario A X))
    {p : InterventionSelection.Plan Unit (Scenario A X)}
    (hp : InterventionSelection.Optimal (scoreGood P) (planSet tree) p)
    {t : Scenario A X} (ht : t ∈ tree) :
    InterventionSelection.gain (scoreGood P) p () t ≤ 0 := by
  have hmem : (fun _ : Unit => t) ∈ planSet tree := mem_planSet.mpr ht
  have hle : scoreGood P (fun _ : Unit => t) ≤ scoreGood P p := hp.2 _ hmem
  have hle' : P.score t ≤ P.score (p ()) := hle
  have halter : InterventionSelection.alter p () t = fun _ : Unit => t := by
    funext u
    cases u
    exact InterventionSelection.alter_apply_self p () t
  unfold InterventionSelection.gain
  rw [halter]
  show P.score t - P.score (p ()) ≤ 0
  linarith

end R36

end FateV2.Predict.WorldScenario.Tight
