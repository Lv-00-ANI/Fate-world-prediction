import FateWorld.FateV2.Loop.ScenarioBranchLimit
import Mathlib.Tactic

/-!
  # Predict · Scenario — 场景树与择优

  ## 迁移登记
  - 来源：新写（原为空壳占位）
  - 动作：C 重写
  - 对应环节：主链第 3 段 · 决策支
  - 依赖裁决：**D-009**（可逆建模与多模态预测）、**D-014**（模型 = SCM）
  - 改动：从空壳补成实现。给出场景、场景树、评分与择优的**结构**，
          并把 `Loop/ScenarioBranchLimit` 已证的**已知退化**接进来。
  - 状态：已编译

  ## 两个已知限制（09-总设计 §7.4 原文）

  > ⚠ **两个已知限制**（实测）：
  > - `Scenario` **无概率字段**，`ScenarioTree` 是 `Set (Scenario)` 而非真树
  > - 闭环树上**换 plan 轨迹不变**（`branch_traj_indep_of_plan`）⟹ 分支模拟退化

  **本模块不假装这两个限制不存在。** 它做的三件事：

  1. 把「场景树」定义成**真的树**（带分支），而不是 `Set`
  2. **保留概率字段的位置**（`prob`），但如实标注为「未实现」
  3. **显式引用** `ScenarioBranchLimit.branch_traj_indep_of_plan`，
     让任何用到择优的人都能看见这个限制

  ## 为什么还要写

  因为**择优逻辑本身是可用的**——退化的是「分支是否真的分叉」，
  不是「给定一组场景怎么选最好」。把两者分开，前者能用就用。

  **诚实边界**：`ScenarioTree.choose` 只做「在已给定场景集上评优」，
  **不**声称这些场景真的覆盖了不同 plan 的未来。
-/

namespace FateV2.Predict

universe u

/-! ## §1 · 场景 -/

/-- **一个场景**：某个 plan 下的一条预测轨迹，附带一个评分。

    ⚠ `prob` 字段是**占位**：`09-总设计` §7.4 指出原 `Scenario` 无概率字段，
    这是「场景树概率化」被列为架构级未决（A3）的原因。
    这里留出位置但**不给值**，等待 A3 裁决。 -/
structure Scenario (State : Type u) where
  /-- 该场景对应的干预方案 -/
  plan  : String
  /-- 预测出的状态轨迹 -/
  traj  : List State
  /-- 评分（越大越好） -/
  score : ℝ
  /-- **未实现的概率字段**（A3 未决，故为 `none`） -/
  prob  : Option ℝ

namespace Scenario

variable {State : Type u}

/-- **场景的概率已实现吗**：`prob` 非 `none`。 -/
def HasProb (s : Scenario State) : Prop := s.prob.isSome

/-- **当前所有场景都没有概率**（A3 未定的直接后果）。 -/
theorem no_prob_currently (s : Scenario State) (h : s.prob = none) : ¬ s.HasProb := by
  intro hp
  unfold HasProb at hp
  rw [h] at hp
  exact absurd hp (by simp)

end Scenario

/-! ## §2 · 场景树（真树，不是 Set） -/

/-- **场景树**：树根 + 分支。

    `09-总设计` §7.4 批评原实现「`ScenarioTree` 是 `Set (Scenario)` 而非真树」，
    本定义改成**递归结构**，分支是 `List`：

    * 空分支 = 叶子
    * 非空 = 内部节点 -/
inductive Tree (State : Type u) : Type u where
  /-- 叶子：一个终局场景 -/
  | leaf (s : Scenario State)
  /-- 内部节点：当前场景 + 若干分支 -/
  | node (s : Scenario State) (branches : List (Tree State))

namespace Tree

variable {State : Type u}

/-- **树的所有场景**（展平）。 -/
def scenarios : Tree State → List (Scenario State)
  | .leaf s => [s]
  | .node s bs => s :: bs.flatMap scenarios

/-- **树是真树判据**：有超过一个分支。 -/
def IsBranching : Tree State → Prop
  | .leaf _ => False
  | .node _ bs => 1 < bs.length

/-- **叶子树的场景数恰为 1**。 -/
theorem leaf_scenarios (s : Scenario State) : (Tree.leaf s).scenarios.length = 1 := by
  simp [Tree.scenarios]

/-- **场景数 ∈ 场景列表**。 -/
theorem mem_scenarios_self (t : Tree State) (s : Scenario State)
    (h : t = .leaf s) : s ∈ Tree.scenarios t := by
  subst h; simp [Tree.scenarios]

/-- **择优**：在树上所有场景里取评分最高的。

    这是「给定场景集，怎么选最好」的实现——**与分支是否真分叉无关**。 -/
noncomputable def choose (t : Tree State) : Option (Scenario State) :=
  match t.scenarios with
  | [] => none
  | s :: rest => some (rest.foldl (fun acc x => if acc.score ≤ x.score then x else acc) s)

end Tree

/-! ## §3 · 择优与分支退化的接线 -/

section Degeneracy

variable {State : Type u}

/-- **择优只依赖场景集，不依赖树形**：

    两棵场景集相同的树，`choose` 给出相同结果。

    这条把「择优逻辑」与「树形」解耦——**是 §2 能用的理由**。 -/
theorem choose_depends_only_on_scenarios (t₁ t₂ : Tree State)
    (h : t₁.scenarios = t₂.scenarios) : t₁.choose = t₂.choose := by
  unfold Tree.choose
  rw [h]

/-- **已知退化（引用上游定理）**：闭环树上换 `plan` 轨迹不变。

    本模块**不重新证明**它，只把它**指出来**——
    因为 `09-总设计` §7.4 明确要求：用到场景树的地方必须知道这个限制。

    上游：`FateV2.Loop.ScenarioBranchLimit.branch_traj_indep_of_plan`。 -/
theorem known_degeneracy_reference : True := trivial

end Degeneracy

/-! ## §4 · 评分的单调性 -/

section Score

variable {State : Type u}

/-- **评分的传播**：`choose` 在非空场景列表上，返回的评分不低于列表头的评分。

    用 `foldl` 的直接刻画表述——这是 `choose` 语义的唯一必要性质。 -/
theorem foldl_score_ge_head (s : Scenario State) (rest : List (Scenario State)) :
    s.score ≤ (rest.foldl (fun acc x => if acc.score ≤ x.score then x else acc) s).score := by
  induction rest generalizing s with
  | nil => exact le_refl s.score
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    by_cases hc : s.score ≤ hd.score
    · rw [if_pos hc]
      exact le_trans hc (ih hd)
    · rw [if_neg hc]
      -- 此时取 acc = s，目标是 s.score ≤ (foldl ... s tl).score，正是 ih
      exact ih s

end Score

end FateV2.Predict
