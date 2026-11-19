/-
  `Fate/NonemptyFree` —— **DOWN-1 A 类实测：去掉可去的 `[Nonempty]` 假设**

  ## 本文件做什么

  DOWN-1 报告称库内 `[Nonempty]` 出现 467 次、判为「主要 A 类（可去）」。
  **本文件只对下面 3 条具体定理做实测**，给出各自的**无 `[Nonempty]` 版本**。
  **不声称**「`[Nonempty]` 已全部去掉」——见文末「诚实边界」。

  | # | 原定理（**未改动**） | 所在模块 | 结论 |
  |---|---|---|---|
  | 1 | `FateV2.Predict.NonemptyFree.CondMulSeparable.condMul_implies_separable` | `CondMulSeparable` | ✅ 可去 |
  | 2 | `FateV2.Predict.MarkovBridgeTheorem.cond_mul_implies_separable_chain` | `MarkovBridgeTheorem` | ✅ 可去 |
  | 3 | `WorldScenario.optimalChoose_mem` | `PolicyAlgorithm` | ✅ 可去（实例降为显式参数）|

  ## 逐条理由（为什么是 A 类）

  **1. `condMul_implies_separable`**：
  原证的 `[Nonempty α]`/`[Nonempty β]` **只**用于 `obtain ⟨x₀⟩` / `obtain ⟨y₀⟩`
  —— 目的是用 `Finset.sum_pos` 见证 `0 < margZ p z`。
  **`α` 或 `β` 为空时**：`margZ p z = ∑ x, ∑ y, p((x,y),z) = 0`（空和），
  故 `hpos x y z` 的量化域为空（空真）；结论是
  `∃ f g, ∀ x y z, p ((x,y),z) = f x z * g y z`，其量化域
  `α × β` 也为空 ⟹ **空真**。取 `f := fun _ _ => 0`、`g := fun _ _ => 1` 即满足。
  ⟹ **结论与前件都不需要 `Nonempty`**，只是原证取了一条便利路径。

  **2. `cond_mul_implies_separable_chain`**：
  它是 (1) 的**逐字转调**（`exact condMul_implies_separable p h hpos`），
  故 (1) 可去 ⟹ (2) 可去。

  **3. `optimalChoose_mem`**：
  `[Nonempty A]`/`[Nonempty X]` 在 `optimalChoose` 的**定义**里只被
  **else 分支**（`⟨fun _ => Classical.arbitrary A, fun _ => Classical.arbitrary X⟩`）
  用到；而该分支**在 `optimalChoose_mem` 里不可达**
  （前提 `hne : tree.Nonempty` 使 `dif_pos hne` 生效）。
  底层 `chooseOptimalSet P tree hne` **本就不要求任何 `Nonempty` 实例**
  （其签名只有 `[Fintype A] [Fintype X]`）。
  ⟹ 把 `hne` 留在显式参数位、绕开 `optimalChoose` 的 else 分支即可，
  **不需要** `[Nonempty A] [Nonempty X]`。

  ## ⚠ 不变式

  **本文件不修改任何已有模块**（原定理原样保留），只**新增**定理。
  零 `sorry` / `admit` / `axiom` / `native_decide`。

  ## ⚠ 反向记录（**不可去**的候选，见文末 §4）
-/

import FateWorld.FateV2.Predict.CondMulSeparable
import FateWorld.FateV2.Predict.MarkovBridgeTheorem
import FateWorld.FateV2.Predict.PolicyAlgorithm
namespace FateV2.Predict.NonemptyFree

open FateV2.Modeling

/-!
  # Predict · NonemptyFree

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NonemptyFree.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：CondMulSeparable, MarkovBridgeTheorem, PolicyAlgorithm
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  `condMul_implies_separable` 的无 `[Nonempty]` 版本
  =========================================================================== -/

namespace CondMulSeparable

open FateV2.Predict.FinCondIndep

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- ⭐ **【无 `[Nonempty]` 版】**：`FateV2.Predict.NonemptyFree.CondMulSeparable.condMul_implies_separable`
去掉 `[Nonempty α] [Nonempty β]` 后**仍然成立**。

**证明策略**：对 `Nonempty α ∧ Nonempty β` 分支**复用原证**（原定理可直接调用）；
空分支给出**显式见证** `f ≡ 0`、`g ≡ 1`（此时 `α × β` 为空，等式空真）。 -/
theorem condMul_implies_separable_noNonempty (p : FinJoint α β γ)
    (h : CondMul p) (hpos : ∀ x y z, 0 < p ((x, y), z)) :
    ∃ (f : α → γ → ℝ) (g : β → γ → ℝ),
      ∀ x y z, p ((x, y), z) = f x z * g y z := by
  classical
  by_cases hα : Nonempty α
  · by_cases hβ : Nonempty β
    · exact FateV2.Predict.NonemptyFree.CondMulSeparable.condMul_implies_separable p h hpos
    · -- `β` 为空 ⟹ 量化域 `α × β` 为空 ⟹ 结论空真，显式见证即可
      exact ⟨fun _ _ => 0, fun _ _ => 0, fun x y _ => absurd ⟨y⟩ hβ⟩
  · -- `α` 为空 ⟹ 同样空真
    exact ⟨fun _ _ => 0, fun _ _ => 0, fun x _ _ => absurd ⟨x⟩ hα⟩

end CondMulSeparable

/-! ===========================================================================
  §2  `cond_mul_implies_separable_chain` 的无 `[Nonempty]` 版本
  =========================================================================== -/

namespace MarkovBridgeTheorem

open FateV2.Predict.FinCondIndep

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]

/-- ⭐ **【无 `[Nonempty]` 版】**：`FateV2.Predict.MarkovBridgeTheorem.cond_mul_implies_separable_chain`
去掉 `[Nonempty α] [Nonempty β]` 后**仍然成立**。

原定理是 §1 的逐字转调，故直接转调 §1 的无 `Nonempty` 版本。 -/
theorem cond_mul_implies_separable_chain_noNonempty
    (p : FinJoint α β γ)
    (h : CondMul p) (hpos : ∀ x y z, 0 < p ((x, y), z)) :
    ∃ (f : α → γ → ℝ) (g : β → γ → ℝ),
      ∀ x y z, p ((x, y), z) = f x z * g y z :=
  FateV2.Predict.NonemptyFree.CondMulSeparable.condMul_implies_separable_noNonempty p h hpos

end MarkovBridgeTheorem

/-! ===========================================================================
  §3  `optimalChoose_mem` 的无 `[Nonempty]` 版本
  =========================================================================== -/

namespace WorldScenario

open FateV2.Predict.WorldScenario

universe u

/-- ⭐ **【无 `[Nonempty]` 版】**：`WorldScenario.optimalChoose_mem`
去掉 `[Nonempty A] [Nonempty X]` 后**仍然成立**。

**做法**：用底层 `chooseOptimalSet P tree hne`（签名**不含**任何 `Nonempty` 实例），
其成员性正是 `chooseOptimalSet_mem`。
这与 `optimalChoose P tree` 在 `hne` 下的取值**定义上相同**
（`optimalChoose` 里的 `dif_pos hne` 分支），故这就是同一命题的无实例形式。 -/
theorem optimalChoose_mem_noNonempty {A X : Type u} [Fintype A] [Fintype X]
    (P : Policy A X) {tree : Set (Scenario A X)} (hne : tree.Nonempty) :
    chooseOptimalSet P tree hne ∈ tree :=
  chooseOptimalSet_mem P hne

/-- ⭐⭐ **一致性**：在 `[Nonempty]` 可用时，无实例版与 `optimalChoose` **取同值**
（`optimalChoose` 定义里的 `dif_pos hne` 分支就是 `chooseOptimalSet`）。

⟹ 上一条**不是**「换了一个函数」，而是**同一个函数**在不需实例的签名下的陈述。 -/
theorem optimalChoose_eq_chooseOptimalSet {A X : Type u} [Fintype A] [Fintype X]
    [Nonempty A] [Nonempty X]
    (P : Policy A X) {tree : Set (Scenario A X)} (hne : tree.Nonempty) :
    optimalChoose P tree = chooseOptimalSet P tree hne := by
  classical
  unfold optimalChoose
  rw [dif_pos hne]

end WorldScenario

/-! ===========================================================================
  §4  ⚠ **诚实边界 / 不可去候选的反向记录**
  ===========================================================================

  **本节是「不可去」的实测记录，不写定理，只写结论与理由。**

  1. `FateV2.Modeling.sum_pos_univ`（`[Nonempty σ]`）—— **不可去**。
     `σ` 为空时 `∑ x, f x = 0`，`h : ∀ x, 0 < f x` 空真，
     **结论 `0 < 0` 为假** ⟹ 在 `[Fintype σ]` 下**没有**无 `Nonempty` 形式。

  2. `SCMWorldModel.scmWorldModel_*`（`[Nonempty Y]`）—— **不可去**。
     构造 `WorldModel` 的 `cur := Classical.choice ‹Nonempty Y›` / `initial.val`：
     空类型 `Y` 上 `WorldState.cur : Y` **无法给出取值**。这是**结构需要**，
     与本任务要找的「只作默认值、结论不读它」的 A 类**不同**（此处结论依赖 `W.x` 的存在）。

  3. `LawRule.isPoint_genRule_iff`（`[Nonempty C.Carrier] [Nonempty X.Carrier]`）
     —— **实测不可去**（与 DOWN-1 的 A 类判定**相反**，如实记录）。
     原证用 `Classical.arbitrary C.Carrier` / `X.Carrier` 从 `hp : ∀ c x, ...` 取一点。
     若 `C.Carrier` 为空：`IsPoint (genRule G g)` **空真**，
     而右侧 `∃ i₀ ∈ G, (∃ μ, g i₀ = {μ}) ∧ g i₀ = ⋃ i ∈ G, g i`
     **与 `C`/`X` 无关**，取 `G = ∅` 时它**为假** ⟹ 双向不成立。
     ⟹ 该 `[Nonempty]` **承载真实内容**，原判「A 类」有误。

  4. `CondMI` §2 的 `[Nonempty α] [Nonempty β] [Nonempty γ]` —— **不可去**，
     且**模块已自行记录**（`Fate/CondMI.lean:326` 原话：
     「`∀ x y z, 0 < p` 在空类型上会**空真**，故这里显式排除」）。
     这是**正确的断言**：正性假设需要非空域才有信息。

  **⟹ 结论**：`[Nonempty]` **并非**「主要 A 类」。
  本轮实测的 4 个「看似可去」的候选中，**只有 3 条真的可去**，
  另 1 条（`isPoint_genRule_iff`）**不可去**，且其 `[Nonempty]` 不可省。
-/

end FateV2.Predict.NonemptyFree
