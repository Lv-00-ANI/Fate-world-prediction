/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.ScenarioBranchLimit`
任务：**P1-H3 / CHAIN-2 任务 E —— 显式记录「分支不分叉」这一设计限制**

===========================================================================
背景：CHAIN-2 审计的发现
===========================================================================

`Fate/ScenarioConvergence.lean:170` 的 `branch_traj_eq`：

    s.traj n = iterMap A phi eta x' n theta

右端 **不含 `s.plan`**。根因在 `Fate/ScenarioConvergence.lean:129`
的 `ofSim_traj_eq_iterMap`：步函数 `stepFun` 丢弃 `plan`（只读状态 `x`）。

⟹ **任意分支（任意干预方案）的第 n 步轨迹完全相同。**

**这不是 bug，是当前设计的限制**：闭环动力学
`theta |-> theta + eta • phi (x' - A theta)` 的误差递推与干预方案无关。
因此「多分支场景树」在本层实际是**单分支**（所有分支轨迹重合）。

===========================================================================
本文件做什么 / 不做什么
===========================================================================

**做**：把上述限制**显式证明为定理**（而不是让它隐含在 `stepFun` 的定义里）。
「同轨迹」此前只由 `branch_traj_eq` 间接体现；本文件给出**直接的**
「两分支轨迹相等」定理，且量化在**任意两个 plan** 上，不在**同一个** plan 上。

**不做**：**不**修改 `stepFun`（那是破坏性改动，会推翻 `ScenarioConvergence`
与 `ScenarioSharp` 的大量证明）。真正让分支分叉属于「方向 2」，本任务不取。

===========================================================================
⚠ 前件检查（防范同义反复）
===========================================================================

本文件没有任何假设性前件把结论包进去：
- `branch_traj_indep_of_plan` 的前件只有「两个场景都是树上的成员」，
  **不**假设 `s.plan = t.plan`，**不**假设 `s.traj = t.traj`；
  结论是它们各自被**同一个** `iterMap` 表达，从而相等。
- `ofSim_traj_indep_of_plan` 的前件只有空间结构与参数，**没有任何 `plan` 之间
  的关系假设**。

===========================================================================
九要件 ⑦ 的判定
===========================================================================

- **数学上真**：收敛定理（`branch_err` / `tree_tendsto_uniform`）成立。
- **要件上假**：所谓「多分支同时模拟」在本层是**单分支**。
- **判定**：从 ✅ 降为 ⚠（登记见 `Fate/ScenarioSharp.lean` §5.2 补充）。

===========================================================================
纪律
===========================================================================
- **零 `sorry` / 零 `admit` / 零 `axiom` / 零 `native_decide`**。
- **只新增本文件**，不修改任何已有模块（只 `import`）。
- 不使用希腊字母（G54）；所有引用均经 `#check` 核验（G45）。
-/

import FateWorld.Legacy.ScenarioConvergence
import FateWorld.Legacy.ScenarioSharp

namespace Fate

namespace ScenarioBranchLimit

open BoundWriteBack
open Fate.WiringConvergence (iterMap)
open Fate.WorldScenario (Scenario)
open Fate.ScenarioConvergence (loopTree mem_loopTree branch_traj_eq ofSim_traj_eq_iterMap)
open Fate.ScenarioConvergence (stepFun)

universe u

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ===========================================================================
    §1  ⭐⭐⭐ **【核心】任意两个干预方案生成的轨迹完全相同**
    =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【`ofSim` 轨迹与 plan 无关】（显式记录限制）**

对**任意两个**干预方案 `plan1`、`plan2`，`Scenario.ofSim (stepFun …)` 生成的
轨迹**逐点相等**。这正是 CHAIN-2 审计发现的「分支同轨迹」的最直接形式。

**证明**：两条轨迹都等于同一个闭环迭代 `iterMap A phi eta x' n theta`
（`ofSim_traj_eq_iterMap`），故相等。

⭐ **本定理没有把结论塞进前件**：前件只有空间结构与动力参数，
对 `plan1` 与 `plan2` **不作任何假设**（可以完全不同）。 -/
theorem ofSim_traj_indep_of_plan
    (A : E →L[ℝ] F) (phi : F →ₗ[ℝ] E) (eta : ℝ) (x' : F) (theta : E)
    (plan1 plan2 : ℕ → E) :
    (Scenario.ofSim (stepFun A phi eta x') theta (fun _ => 0) (fun _ => 0) plan1).traj
      = (Scenario.ofSim (stepFun A phi eta x') theta (fun _ => 0) (fun _ => 0) plan2).traj := by
  funext n
  rw [ofSim_traj_eq_iterMap A phi eta x' theta plan1 n,
      ofSim_traj_eq_iterMap A phi eta x' theta plan2 n]

/-! ===========================================================================
    §2  ⭐⭐⭐ **【场景树上任意两条分支的轨迹相同】**
    =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【分支轨迹与 plan 无关】—— 场景树上的陈述**

给定场景树 `loopTree A phi eta x' theta plans`，树上**任意两条分支**
`s`、`t`（它们的 `plan` 可以不同，**不假设相等**）在第 `n` 步的轨迹相同。

**证明**：由 `branch_traj_eq`，`s.traj n` 与 `t.traj n` 都等于
`iterMap A phi eta x' n theta`。

⭐⭐ 这**不是**由「同一 plan ⟹ 同轨迹」（`scenario_traj_determined`）得到的：
这里 `s.plan` 与 `t.plan` **可以完全不同**，轨迹仍相同。 -/
theorem branch_traj_indep_of_plan
    (A : E →L[ℝ] F) (phi : F →ₗ[ℝ] E) (eta : ℝ) (x' : F) (theta : E)
    {plans : Set (ℕ → E)} {s t : Scenario E E}
    (hs : s ∈ loopTree A phi eta x' theta plans)
    (ht : t ∈ loopTree A phi eta x' theta plans)
    (n : ℕ) :
    s.traj n = t.traj n := by
  rw [branch_traj_eq A phi eta x' theta hs n,
      branch_traj_eq A phi eta x' theta ht n]

/-- ⭐⭐⭐⭐ **【分支整条轨迹相同】（`branch_traj_indep_of_plan` 的函数形式）**

树上**任意两条分支**的**整条轨迹**作为 `ℕ → E` 的函数相等。 -/
theorem branch_traj_funext
    (A : E →L[ℝ] F) (phi : F →ₗ[ℝ] E) (eta : ℝ) (x' : F) (theta : E)
    {plans : Set (ℕ → E)} {s t : Scenario E E}
    (hs : s ∈ loopTree A phi eta x' theta plans)
    (ht : t ∈ loopTree A phi eta x' theta plans) :
    s.traj = t.traj := by
  funext n
  exact branch_traj_indep_of_plan A phi eta x' theta hs ht n

/-! ===========================================================================
    §3  ⭐⭐ **【推论】树上任意分支的轨迹都是固定的 `iterMap` 序列**
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【分支轨迹 = 无参数的固定序列】**

存在一个**与分支无关**的序列（即 `fun n => iterMap A phi eta x' n theta`），
树上**每条**分支的轨迹都恰好是它。

⭐ 这精确刻画了「单分支」：树上的「多分支」在轨迹层面**坍缩为一条**。 -/
theorem exists_branch_free_traj
    (A : E →L[ℝ] F) (phi : F →ₗ[ℝ] E) (eta : ℝ) (x' : F) (theta : E)
    {plans : Set (ℕ → E)} :
    ∃ g : ℕ → E, ∀ s ∈ loopTree A phi eta x' theta plans, s.traj = g := by
  refine ⟨fun n => iterMap A phi eta x' n theta, ?_⟩
  intro s hs
  funext n
  exact branch_traj_eq A phi eta x' theta hs n

/-- ⭐⭐⭐ **【强形式：不同的树也共享同一条轨迹】**

⚠ 注意：`loopTree` 的**成员条件**依赖 `plans`（`s.plan ∈ plans`），
所以两个不同 `plans` 的树作为集合**不相等**。但**轨迹**层面完全一致：
任一树上的分支与任一树上的分支，轨迹相同。

**这是「分支不分叉」的最强表述**：分支的 `plan` 差异**对轨迹毫无影响**，
连**不同的方案集合**之间也是如此。 -/
theorem cross_tree_traj_eq
    (A : E →L[ℝ] F) (phi : F →ₗ[ℝ] E) (eta : ℝ) (x' : F) (theta : E)
    {plans1 plans2 : Set (ℕ → E)} {s t : Scenario E E}
    (hs : s ∈ loopTree A phi eta x' theta plans1)
    (ht : t ∈ loopTree A phi eta x' theta plans2) :
    s.traj = t.traj := by
  funext n
  rw [branch_traj_eq A phi eta x' theta hs n,
      branch_traj_eq A phi eta x' theta ht n]

/-! ===========================================================================
    §4  ⭐ **【代价】「分支不同 ⟹ 轨迹不同」为假**
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【反例：plan 不同而轨迹相同】**

显式构造：在二维空间中（`E = F = ℝ × ℝ` 或更简单，取 `E = F = ℝ`），
取 `A = 0`、`phi = 0`，则 `plan1 = (fun _ => 0)` 与 `plan2 = (fun _ => 1)`
**不同**，但生成的轨迹**相同**。

⭐ 这是必要性证明：不能指望从轨迹反推 plan，
即「多分支模拟」在本模型下**在原理上不可区分**。

⚠ 该引理**不是**用来看 `stepFun` 的具体值，而是走 `ofSim_traj_indep_of_plan`
的一般结论（对任意 `A phi eta x'` 成立），故无需具体计算。 -/
theorem exists_distinct_plan_same_traj :
    ∃ (plan1 plan2 : ℕ → ℝ),
      plan1 ≠ plan2 ∧
        (Scenario.ofSim
            (stepFun (0 : ℝ →L[ℝ] ℝ) (0 : ℝ →ₗ[ℝ] ℝ) 0 0) 0 (fun _ => 0) (fun _ => 0) plan1).traj
          = (Scenario.ofSim
            (stepFun (0 : ℝ →L[ℝ] ℝ) (0 : ℝ →ₗ[ℝ] ℝ) 0 0) 0 (fun _ => 0) (fun _ => 0) plan2).traj := by
  refine ⟨fun _ => 0, fun _ => 1, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    norm_num at this
  · exact ofSim_traj_indep_of_plan _ _ _ _ _ _ _

end ScenarioBranchLimit

end Fate
