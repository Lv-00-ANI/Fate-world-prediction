/-
命运理论 · 干预选择的「次优差距下界」在具体实例上的接入
===============================================================================

模块：Fate.InterventionSharpWiring
上游：`Fate/InterventionSelection.lean`（`Plan`、`Good`）、
　　　`Fate/InterventionSharp.lean`（`loss`、`suboptimality_gap_lower_bound`）。

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
`Fate/InterventionSharp.lean` 里的 `suboptimality_gap_lower_bound` 此前**没有任何
消费者**（全库 `grep` 只在定义文件里出现）。本文件给它造一个**具体的可计算实例**
并**真的调用**该定理，使「干预选择的次优差距正下界」不再是孤立陈述。

具体实例（全部可计算，无 `Classical` 参与构造）：
* `WPlan := Plan Unit (Fin 3)`，即 `Unit → Fin 3` —— 单主体、三动作；
* `WGood p := ((p ()).val : ℝ)` —— 目标函数（动作编号越大越好）；
* `WSet := {p0, p1, p2}`，`p_i := fun _ => i`。

于是 `WGood p0 = 0`、`WGood p1 = 1`、`WGood p2 = 2`，`p2` 是 `WSet` 上**唯一**最优，
次优差距 `loss p1 − loss p2 = 1 > 0` 由 `suboptimality_gap_lower_bound` 直接给出。

---------------------------------------------------------------------------
⚠ 自查（纪律 7：前件是否已含结论）
---------------------------------------------------------------------------
本文件的三条前件 `w_opt` / `w_uniq` / `w_ne` **都不含** `δ`；
`δ` 只出现在 `w_suboptimality_gap` 的**结论**中。
且 `w_opt`、`w_uniq` 都是**在具体数字上算出来的**（`decide` 级），不是结论的重述。

---------------------------------------------------------------------------
诚实标注
---------------------------------------------------------------------------
* 「`Good` 该取什么」**不是**定理：`WGood` 是本文件**选定**的一个具体函数
  （对应 `InterventionSelection` 文件头「目标函数是前件，不能证」）。
* 本文件**只**把有限情形的正下界（`InterventionSharp` §2）落到一个具体例子上；
  **不**声称无限情形也成立（该情形需 `Isolated` 假设，见 `InterventionSharp` §5）。

零 `sorry` / 零 `axiom` / 零 `admit`。
-/

import FateWorld.Legacy.InterventionSelection
import FateWorld.Legacy.InterventionSharp

namespace Fate

open Fate.InterventionSelection

namespace InterventionSharpWiring

/-! ===========================================================================
    §1  具体实例
    =========================================================================== -/

/-- 具体候选集载体：单主体（`Unit`）上的三值动作（`Fin 3`）。 -/
abbrev WPlan : Type := Plan Unit (Fin 3)

/-- 恒取动作 `0` 的计划。 -/
def p0 : WPlan := fun _ => 0

/-- 恒取动作 `1` 的计划。 -/
def p1 : WPlan := fun _ => 1

/-- 恒取动作 `2` 的计划。 -/
def p2 : WPlan := fun _ => 2

/-- 目标函数：动作编号越大越好（值域 `ℝ`）。〔用户选择的约定，非定理〕 -/
def WGood : Good Unit (Fin 3) := fun p => ((p ()).val : ℝ)

/-- 候选集：三个具体计划。 -/
def WSet : Finset WPlan := {p0, p1, p2}

@[simp] theorem WGood_p0 : WGood p0 = 0 := by simp [WGood, p0]
@[simp] theorem WGood_p1 : WGood p1 = 1 := by simp [WGood, p1]
@[simp] theorem WGood_p2 : WGood p2 = 2 := by simp [WGood, p2]

/-- 三个计划互不相同（在 `Unit` 上按取值区分）。 -/
theorem p0_ne_p1 : p0 ≠ p1 := by
  intro h
  have := congrFun h ()
  simp [p0, p1] at this

theorem p0_ne_p2 : p0 ≠ p2 := by
  intro h
  have := congrFun h ()
  simp [p0, p2] at this

theorem p1_ne_p2 : p1 ≠ p2 := by
  intro h
  have := congrFun h ()
  simp [p1, p2] at this

/-! ===========================================================================
    §2  前件在具体数字上成立（`decide` 级，不含 `δ`）
    =========================================================================== -/

/-- `p2` 在候选集里。 -/
theorem w_mem : p2 ∈ WSet := by simp [WSet]

/-- `p2` 是候选集上的（弱）最优：其余候选的值 `0, 1` 都 `≤ 2`。 -/
theorem w_opt : ∀ q ∈ WSet, WGood q ≤ WGood p2 := by
  intro q hq
  fin_cases hq <;> simp

/-- `p2` 是候选集上的**唯一**最优：若 `WGood p2 ≤ WGood q` 则 `q = p2`。 -/
theorem w_uniq : ∀ q ∈ WSet, WGood p2 ≤ WGood q → q = p2 := by
  intro q hq hle
  fin_cases hq
  · simp only [WGood_p0, WGood_p2] at hle; exact absurd hle (by norm_num)
  · simp only [WGood_p1, WGood_p2] at hle; exact absurd hle (by norm_num)
  · rfl

/-- 候选集去掉 `p2` 后非空（还有 `p0`）。 -/
theorem w_ne : (WSet.erase p2).Nonempty := by
  refine ⟨p0, ?_⟩
  simp [WSet, p0_ne_p2]

/-! ===========================================================================
    §3  ⭐ 真调用 `suboptimality_gap_lower_bound`
    =========================================================================== -/

/-- ⭐⭐⭐ **【接入：次优差距正下界，具体实例版】**

存在 `δ > 0`，使候选集内任何非最优计划 `q ≠ p2` 都比 `p2` 至少差 `δ`。

证明直接调用 `Fate.InterventionSharp.suboptimality_gap_lower_bound`。
这里 `δ` **只出现在结论**；前件 `w_opt` / `w_uniq` / `w_ne` 中**没有** `δ`。 -/
theorem w_suboptimality_gap :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ q ∈ WSet, q ≠ p2 →
        δ ≤ InterventionSharp.loss WGood q - InterventionSharp.loss WGood p2 :=
  InterventionSharp.suboptimality_gap_lower_bound WGood WSet p2 w_mem w_opt w_uniq w_ne

/-- **同一条接入的显式数值版**：`δ = 1` 可行（次优者 `p1` 恰好差 `1`）。

⟹ 说明上条的 `δ` 不是空话：`loss p1 − loss p2 = 1`，故 `δ` 至多取到 `1`。 -/
theorem w_suboptimality_gap_one :
    ∀ q ∈ WSet, q ≠ p2 →
      (1 : ℝ) ≤ InterventionSharp.loss WGood q - InterventionSharp.loss WGood p2 := by
  intro q hq hne
  fin_cases hq
  · -- `q = p0`：`loss p0 − loss p2 = 2`
    simp only [InterventionSharp.loss, WGood_p0, WGood_p2]
    norm_num
  · -- `q = p1`：`loss p1 − loss p2 = 1`
    simp only [InterventionSharp.loss, WGood_p1, WGood_p2]
    norm_num
  · exact absurd rfl hne

/-! ===========================================================================
    §4  ⭐ 真调用 `gap_iff_strictly_better`（§4 的等价刻画）
    =========================================================================== -/

/-- ⭐ **【接入：正下界 ⟺ 严格优于其它候选】**（具体实例版）

在 `WSet` 上，「存在正下界」与「`p2` 严格优于所有其它候选」等价。

证明直接调用 `Fate.InterventionSharp.gap_iff_strictly_better`。 -/
theorem w_gap_iff :
    (∃ δ : ℝ, 0 < δ ∧
      ∀ q ∈ WSet, q ≠ p2 →
        δ ≤ InterventionSharp.loss WGood q - InterventionSharp.loss WGood p2)
      ↔ (∀ q ∈ WSet, q ≠ p2 → WGood q < WGood p2) :=
  InterventionSharp.gap_iff_strictly_better WGood WSet p2 w_mem

/-- 该等价刻画的**右侧**在具体实例上成立（`0 < 2` 与 `1 < 2`），故**左侧**成立。 -/
theorem w_strictly_better : ∀ q ∈ WSet, q ≠ p2 → WGood q < WGood p2 := by
  intro q hq hne
  simp only [WSet, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · simp only [WGood_p0, WGood_p2]; norm_num
  · simp only [WGood_p1, WGood_p2]; norm_num
  · exact absurd rfl hne

/-- 由上两条，正下界再次独立得到（经 §4 的等价刻画，而非经 §2）。 -/
theorem w_suboptimality_gap' :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ q ∈ WSet, q ≠ p2 →
        δ ≤ InterventionSharp.loss WGood q - InterventionSharp.loss WGood p2 :=
  w_gap_iff.mpr w_strictly_better

end InterventionSharpWiring

end Fate
