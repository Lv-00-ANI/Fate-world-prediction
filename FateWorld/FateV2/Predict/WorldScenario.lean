import Mathlib

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/WorldScenario.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-009 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Predict（正文 2 处，含 0 条 import）；其余正文未改
  - 状态：已编译未验证
-/

/-! ===========================================================================
  §0  世界模型的两个缺失结构：场景树 + 干预选择

  ## 作者的三能力要求（原话）

  > **「后面还是需要大规模的模拟的，就是信息不断的注入，而且同时模拟不同的分支，
  > 然后挑出满足要求的一种干预 —— 世界模型吗」**

  | 能力 | 现状 |
  |---|---|
  | **① 信息不断注入** | ✅ `RuleActivation` + `refine`（收窄）|
  | **② 同时模拟不同分支** | 🔴 **缺 `ScenarioTree`** |
  | **③ 挑出满足要求的干预** | 🔴 **缺 `Policy`** |

  ## 本节补什么（作者裁决「建构的建构」）

  ### ① `ScenarioTree`：多分支模拟

  **关键设计：分支不是「不同轨迹」，而是「不同干预方案」。**

  ```lean
  structure Scenario where
    plan : ℕ → A            -- 一条干预方案（每个时刻一个动作）
    traj : ℕ → X            -- 该方案下的轨迹
  ```

  **而场景树是场景的集合：**

  ```lean
  def ScenarioTree (f) (x₀) (u) (e) (plans : Set (ℕ → A)) : Set (Scenario ...)
  ```

  **⟹ 「同时模拟不同分支」= 对每个候选干预方案，各跑一条轨迹。**

  **⚠ 这与「反事实」的区别**：反事实要求**同一外生 `u`** 下换干预；
  而场景树**只需同一 `u` 与 `e`**（本实现正是如此），故**它就是反事实的**。

  ### ② `Policy`：干预选择

  ```lean
  structure Policy where
    choose : ScenarioTree ... → ℕ → A     -- 从场景树选一个方案
    score  : Scenario ... → ℝ             -- 评分
    optimal : ∀ s ∈ tree, score (choose tree) ≥ score s   -- 最优性
  ```

  **⚠ 「满足要求」需要准则** —— 本实现把它做成参数（`score`），不擅自假定。

  ## 诚实边界

  * **`score` 的内容（「满足要求」的判准）由作者给出，本节不填。**
  * **场景树是**集合**而非真树** —— 因为本实现中不同方案共享同一 `u, e`，
    故没有「不确定性分叉」，只有「干预选择的分叉」。
  * **未处理「分支内的进一步分支」**（如方案本身随观测调整）。
  =========================================================================== -/

namespace FateV2.Predict

namespace WorldScenario

universe u

/-! ### §0.1 场景（一条干预方案 + 其轨迹） -/

/-- **场景**：一条干预方案，及该方案下的轨迹。 -/
structure Scenario (A X : Type u) where
  /-- 干预方案：每个时刻一个动作。 -/
  plan : ℕ → A
  /-- 该方案下的轨迹。 -/
  traj : ℕ → X

/-- **场景的轨迹由 `simulate` 给出**（构造）。 -/
def Scenario.ofSim {A X U N : Type u} (f : X → U → N → A → X) (x₀ : X)
    (u : ℕ → U) (e : ℕ → N) (plan : ℕ → A) : Scenario A X :=
  { plan := plan
    traj := fun n => Nat.rec x₀ (fun k xk => f xk (u k) (e k) (plan k)) n }

/-! ### §0.2 场景树（多分支） -/

/-- **场景树**：对一族候选干预方案，各生成一个场景。

**⚠ 这不是真树** —— 因为所有方案共享同一 `u, e`，没有不确定性分叉。 -/
def ScenarioTree {A X U N : Type u} (f : X → U → N → A → X) (x₀ : X)
    (u : ℕ → U) (e : ℕ → N) (plans : Set (ℕ → A)) : Set (Scenario A X) :=
  { s | s.plan ∈ plans ∧ s.traj = (Scenario.ofSim f x₀ u e s.plan).traj }

/-- **场景树的成员性刻画**。 -/
theorem mem_scenarioTree {A X U N : Type u} {f : X → U → N → A → X} {x₀ : X}
    {u : ℕ → U} {e : ℕ → N} {plans : Set (ℕ → A)} {s : Scenario A X} :
    s ∈ ScenarioTree f x₀ u e plans ↔
      s.plan ∈ plans ∧ s.traj = (Scenario.ofSim f x₀ u e s.plan).traj :=
  Iff.rfl

/-- **同一方案的场景唯一确定轨迹**（模拟是确定的）。 -/
theorem scenario_traj_determined {A X U N : Type u} {f : X → U → N → A → X}
    {x₀ : X} {u : ℕ → U} {e : ℕ → N} {plans : Set (ℕ → A)}
    {s t : Scenario A X} (hs : s ∈ ScenarioTree f x₀ u e plans)
    (ht : t ∈ ScenarioTree f x₀ u e plans) (hp : s.plan = t.plan) :
    s.traj = t.traj := by
  obtain ⟨_, hs'⟩ := (mem_scenarioTree.mp hs)
  obtain ⟨_, ht'⟩ := (mem_scenarioTree.mp ht)
  rw [hs', ht', hp]

/-! ### §0.3 干预选择（Policy） -/

/-- **策略**：从场景树中选一个场景，并声称它最优。

**⚠ `score` 是「满足要求」的判准** —— 由作者给出，本节不填。 -/
structure Policy (A X : Type u) where
  /-- 评分函数（准则）：越大越好。 -/
  score : Scenario A X → ℝ
  /-- 选择函数：从场景树中选一个。 -/
  choose : Set (Scenario A X) → Scenario A X
  /-- **正确性**：所选的场景确实来自给定的树。 -/
  choose_mem : ∀ {tree : Set (Scenario A X)}, tree.Nonempty → choose tree ∈ tree

/-- **最优性**（作为额外条件，不内建）。 -/
def Policy.IsOptimal (P : Policy A X) : Prop :=
  ∀ (tree : Set (Scenario A X)) (h : tree.Nonempty) (s : Scenario A X),
    s ∈ tree → P.score (P.choose tree) ≥ P.score s

/-- **若树有限且非空，则存在最优场景**（有限情形的最优性）。

**⚠ 需 `Fintype`** —— 无限树的最优性需要紧性，本节不处理。 -/
theorem exists_optimal_scenario [Fintype A] [Fintype X]
    (P : Policy A X) {tree : Finset (Scenario A X)} (hne : tree.Nonempty) :
    ∃ s ∈ tree, ∀ t ∈ tree, P.score s ≥ P.score t := by
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image tree P.score hne
  exact ⟨s, hs, fun t ht => hmax t ht⟩

/-! ### §0.4 ⚠ 诚实边界（写入代码）

**本节未解决的问题**：

1. **`score` 的内容（「满足要求」的判准）** —— 由作者给出，本节只把它做成参数。
2. **无限场景树的最优性** —— 需紧性，未处理。
3. **场景树不是真树** —— 本实现中所有方案共享 `u, e`，故没有不确定性分叉。
   若需「不确定性分叉」（同一干预下的多种可能），需把 `e` 也做成集合。
4. **`Policy.choose` 的构造性** —— 本实现用 `choose_mem` 保证正确性，
   但**未给出算法**（`choose` 是参数）。
-/

end WorldScenario

end FateV2.Predict
