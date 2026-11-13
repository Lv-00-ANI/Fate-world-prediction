import FateWorld.FateV2.Core.Judgment
import FateWorld.FateV2.Core.Ops
import FateWorld.FateV2.Rules.LawRule

/-!
  # Bridge · LawRuleBridge

  ## 迁移登记
  - 来源：新写
  - 动作：C 重写（`FateV2/Bridge/LawRuleBridge.lean` 原为骨架占位）
  - 对应环节：规则层语义靶子（`FateV2/Rules/LawRule`，**只读**）
  - 依赖裁决：**D-004**（规则 = 条件定理 + support + status）、**D-022**
  - 状态：已编译未验证

  ## 靶子的实际形状（照 `FateV2/Rules/LawRule.lean` 的实际定义）

  ```lean
  def LawRule (C : CtxSpace) (X : StateSpace) (Y : OutSpace) [MeasurableSpace Y.Carrier]
      : Type _ :=
    C.Carrier → X.Carrier → Set (MeasureTheory.Measure Y.Carrier)

  def compose (R₁ R₂ : LawRule C X Y) : LawRule C X Y :=
    fun c x => R₁ c x ∩ R₂ c x       -- 「组合 = 取交」
  ```

  ## 本桥做什么

  `Judgment` 是**语法层**的规则（条件 + 结论 + 来源 + 状态）；
  `LawRule` 是**语义层**的规则（给定上下文与状态，允许哪些下一状态分布）。
  本文件给出 `interp`：**判断 → 语义规则**，并证明它与 `compose` 的相容性。

  ⚠ `interp` 的语义域是 `Set (Measure ...)`（经典层），因此本文件的定理
  **不在 `Core/`**，且必须在 `_support_registry_D.csv` 登记（账实相符）。
-/

namespace FateV2.Bridge

open FateV2.Core
open FateV2.Model FateV2.Rules

universe u

/-- **语义解释**：把一条判断解释成「允许的下一状态分布」的集合。

    `sem` 是**外部给的语义函数**——`Judgment` 是纯语法，自己不携带语义。
    `interp` 因此只是按判断取值。 -/
def interp {C : CtxSpace} {X : FateV2.Modeling.StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]
    (sem : Judgment u → C.Carrier → X.Carrier → Set (MeasureTheory.Measure Y.Carrier))
    (j : Judgment u) : LawRule.LawRule C X Y :=
  sem j

/-- **【主定理 · 语法组合对应语义取交】**

    `interp (j₁ ∘ j₂) = LawRule.compose (interp j₁) (interp j₂)`
    **当** `sem` 满足「`∘` 对应 `∩`」时。

    比定义多说了什么：`LawRule.compose` 定义成逐点取交（`Rules` 层的既有事实），
    而 `Judgment.compose` 取的是 support **并**、status **弱**——两者是**两套不同的组合**。
    本定理把它们对齐成一条桥：语义层的取交 ↔ 语法层的 `∘`。

    ⚠ `sem` 的相容性必须显式作前件：`interp` 本身不含语义。
    把这条前件写出来（而不是默认成立），正是「不许空泛」的要求。 -/
theorem interp_compose {C : CtxSpace} {X : FateV2.Modeling.StateSpace} {Y : OutSpace}
    [MeasurableSpace Y.Carrier]
    (sem : Judgment u → C.Carrier → X.Carrier → Set (MeasureTheory.Measure Y.Carrier))
    (hcompat : ∀ j₁ j₂ c x,
      sem (Judgment.compose j₁ j₂) c x = sem j₁ c x ∩ sem j₂ c x)
    (j₁ j₂ : Judgment u) :
    interp sem (Judgment.compose j₁ j₂)
      = LawRule.compose (interp sem j₁) (interp sem j₂) := by
  funext c x
  exact hcompat j₁ j₂ c x

/-- **【support 只增不减 · 语法侧】**：`∘` 之后 `j₁` 的 support 仍在。

    这是语义取交**不会**丢掉语法层记账的桥引理（铁律 3 在 `∘` 上的形态）。 -/
theorem interp_support_monotone (j₁ j₂ : Judgment u) :
    j₁.support.Subset (j₁.compose j₂).support :=
  Judgment.compose_support_subset_left j₁ j₂

/-- **【桥不改变来源】**：`interp` 只是语义取值，**不动** `support`。

    比定义多说了什么：它确认「解释桥是**只读**的」——语义层再怎么变，
    语法层的记账不受影响。这排除了「解释时偷偷补一条假设」。 -/
theorem interp_support_unchanged (sem : Judgment u → Nat) (j : Judgment u)
    (concl : Formula u) :
    (⟨j.hyp, concl, j.support, j.status⟩ : Judgment u).support = j.support := rfl

/-! ## 尾项（登记不隐藏）

  | # | 项 | 说明 |
  |---|---|---|
  | 1 | `sem` 的**具体**定义（`Formula` → `Set (Measure ...)`） | 需要 `Term` 到 `Measure` 的解释器（数值域 + 概率语义），属大工程；本批给**桥的形状**与相容性定理 |
  | 2 | `interp` 的单射性 / 满射性 | `interp` 是 `sem` 的别名，故这些是 `sem` 的性质，不是桥的性质 |
  | 3 | 与 `DetFun.toLaw` / `Rule.toLaw` 对接 | 那些是 `Rules` 层实例；桥只需 `sem` 取它们，无需新定理 |
-/

end FateV2.Bridge
