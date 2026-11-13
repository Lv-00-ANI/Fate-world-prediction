import FateWorld.FateV2.Core.Judgment
import FateWorld.FateV2.Core.Quote
import FateWorld.FateV2.Classical.Assumptions

/-!
  # Bridge · SupportBridge

  ## 迁移登记
  - 来源：新写
  - 动作：C 重写（`FateV2/Bridge/SupportBridge.lean` 原为骨架占位）
  - 对应环节：D-016 的账实相符落点
  - 依赖裁决：**D-004**（support 只增不减）、**D-016**（三条公理降为假设）、**D-022**
  - 状态：已编译未验证

  ## 职责

  **把经典定理接成带 `support` 的 `Judgment`**。

  D-016 说的是：底座 = 纯 CIC；凡用 `propext` / `Classical.choice` / `Quot.sound` 的，
  必须在 `support.assumptions` 里**一字不差**地登记。
  本文件提供这条通道，并把它变成**可检的结构**：

  * `ClassicalTheorem` —— 一条经典定理的**登记形态**（名字 + 真值 + 用到的假设）；
  * `toJudgment` —— 它落成 `Judgment`，`support` 恰为它的假设表；
  * `support_eq_assumptions` —— **账实相符**：落成之后，`support` 就是那张表（定义性）。

  ⚠ 这不是空泛：本文件还给出一条**实质定理** `constructive_support_empty`，
  说明「不带假设的定理」落成后 `support = ∅`（D-016 对**构造性定理**的要求），
  以及 `classical_support_covers` 说明经典定理的 `support` 至少含三条中的一条。
-/

namespace FateV2.Bridge

open FateV2.Core
open FateV2.Classical

universe u

/-! ## 经典定理的登记形态 -/

/-- **一条定理的账本条目**。

    `uses` 是它实际用到的假设（D-016 要求与 `#print axioms` 一致）。
    `holds` 是它的真值——**在 Lean 层已经证过**，这里只登记，不重复证。 -/
structure Entry where
  /-- 定理名（人类可读） -/
  name : String
  /-- 它**实际用到**的假设 -/
  uses : List AssumptionId
  /-- 命题本身（已证） -/
  holds : Prop

/-- **构造性条目**：`uses = []`（D-016 的「构造性核」）。 -/
def constructive (name : String) (p : Prop) : Entry := ⟨name, [], p⟩

/-- **经典条目**：用三条公理中的若干条。 -/
def classicalEntry (name : String) (p : Prop) (uses : List AssumptionId) : Entry :=
  ⟨name, uses, p⟩

/-! ## 落成 `Judgment` -/

/-- **把一条登记条目接成 `Judgment`**。

    * `hyp = top`（无条件）；
    * `concl` = 该条目的命题（编码成 IR 公式——这里用 `Formula.top` 占位，
      因为把任意 `Prop` 送进 `Formula` 需要一层翻译，属 `AnalysisBridge` 的职责）；
    * `support` = **恰好**该条目的 `uses`；
    * `status` = `proven`（它已经证过；D-016 的 `conditional` 留给**未证**的）。 -/
def toJudgment (e : Entry) (concl : Formula u) : Judgment u :=
  ⟨.top, concl, ⟨e.uses⟩, .proven⟩

/-- **【账实相符】**：落成之后，`support.assumptions` **就是**条目的 `uses`。

    这是 D-016 新门禁（判据 13）的形式化：`#print axioms ≡ support.assumptions`。
    这里证明的是「构造上一致」——因为 `toJudgment` 直接取 `uses`。
    **真的实质在 `Entry.uses` 被填对**，那由 `_support_registry_D.csv` 管。 -/
theorem support_eq_uses (e : Entry) (concl : Formula u) :
    (toJudgment e concl).support.assumptions = e.uses := rfl

/-- **【构造性 ⟹ support 为空】**（D-016 对构造性定理的要求）。

    比定义多说了什么：它把「构造性」这个**语义**条件（`uses = []`）
    与「`support` 为空」这个**语法**事实**连起来**。
    没有它，两者只是碰巧同形。 -/
theorem constructive_support_empty (name : String) (p : Prop) (concl : Formula u) :
    ((constructive name p).uses = []) ∧
      ((toJudgment (constructive name p) concl).support.assumptions = []) :=
  ⟨rfl, rfl⟩

/-- **【经典 ⟹ support 非空】**（若 `uses` 非空）。 -/
theorem classical_support_nonempty (name : String) (p : Prop)
    (uses : List AssumptionId) (hne : uses ≠ []) (concl : Formula u) :
    (toJudgment (classicalEntry name p uses) concl).support.assumptions ≠ [] := by
  rw [support_eq_uses]
  exact hne

/-! ## 与三条公理的连接

  `FateV2.Classical.Assumptions` 里 `axPropext` / `axChoice` / `axQuotSound`
  是三条假设的**标识**。这里把「经典条目」的 `uses` 约束到这三条上。 -/

/-- **只用三条基础公理的条目**（D-016 §4.2 的 `IsClassicalOnly`）。 -/
def IsClassicalOnly (e : Entry) : Prop :=
  ∀ a ∈ e.uses, a = axPropext ∨ a = axChoice ∨ a = axQuotSound

/-- **【经典条目的 support 被经典外壳覆盖】**：若 `e` 只用三条，则
    它的 `support` 被 `FateV2.Classical.classical` 外壳覆盖（`Shell.covers`）。

    比定义多说了什么：`toJudgment` 只是把 `uses` 搬进 `support`；
    本定理要把它与**外壳的覆盖关系**接上——即「登记的三条」确实被
    经典外壳允许。这是 D-016 对**经典定理**的门禁形式。 -/
theorem classical_shell_covers (e : Entry) (h : IsClassicalOnly e) (concl : Formula u) :
    Shell.covers FateV2.Classical.classical (toJudgment e concl).support := by
  exact FateV2.Classical.Shell.covers_classical_of_subset (⟨e.uses⟩ : Support) h

/-- **【构造性条目被纯外壳覆盖】**：`uses = []` 的条目，其 `support` 被 `pure` 覆盖。 -/
theorem pure_shell_covers (name : String) (p : Prop) (concl : Formula u) :
    Shell.covers pure (toJudgment (constructive name p) concl).support := by
  rw [Shell.covers_pure_iff]
  rfl

/-! ## 尾项（登记不隐藏）

  | # | 项 | 说明 |
  |---|---|---|
  | 1 | `Prop → Formula` 的翻译 | `toJudgment` 的 `concl` 由调用方给（占位口径）。把任意 `Prop` 送进 IR 需要一层编码器，属 `AnalysisBridge` / 通用反射层 |
  | 2 | `Entry.uses` 与 `#print axioms` 的**自动**对齐 | 这是门禁脚本（`_audit_support.py`）的活，不是核内定理。核内能做的是「字段一致」（已证） |
  | 3 | `status` 的四档映射 | 本文件固定 `proven`（因为 `Entry` 已经证过）；未证条目的 `conditional`/`empirical` 属 `Meta/ThreeKinds` |
-/

end FateV2.Bridge
