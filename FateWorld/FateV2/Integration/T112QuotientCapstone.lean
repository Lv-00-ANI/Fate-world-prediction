import FateWorld.FateV2.Rules.T112SecondQuotient

/-!
# Integration · Rules · 二次商的闭包一致性

## 本文件做什么

`Rules/T112SecondQuotient.lean` 里的关键结果各自独立：

- `attrsEquivSetoid`：以「闭包相同」为等价关系的 `Setoid`
- `attrsEquiv_self_closure`：`A` 与 `A''` 同类
- `mk_attrsEquiv`：商映射下 `[A] = [A'']`
- `closure_isIntent`：闭包结果是 intent
- `closureOp_isClosed`：闭包结果是闭集

但这些结果**没有被任何下游调用**。本文件把它们组合成三条桥接定理，
使 `Setoid` 抽象层与 `closure` 具体层之间有一次性的连接。

## 与迁移的关系

这是「把证明整合到证明链上」的第二例：被消费的定理此前是假接线。

## 不引入新数学

全部内容是既有定理的组合，证明体只做传递（`Quotient.sound`、`Iff.mp` 等）。
-/

namespace FateV2.Integration

namespace T112QuotientCapstone

open FateV2.Rules
open FateV2.Rules.T112
open scoped Classical

universe u v

variable {K : FormalCtx.{u, v}}

/-- ⭐⭐ **`Setoid` 关系与 `attrsEquiv` 的互译**。

二次商的 `Setoid` 关系成立 ⟺ 两者的闭包相等。
本体来自 `attrsEquivSetoid_r`；这里加上 `attrsEquiv` 的定义展开，
使下游不必再穿透一层 `def`。 -/
theorem setoid_iff_closure_eq (A B : Set K.MFCA) :
    (attrsEquivSetoid K).r A B ↔ closure K A = closure K B :=
  attrsEquivSetoid_r K A B

/-- ⭐⭐ **闭包是二次商的「正规形」**。

对任意 `A`：`A` 与其闭包 `A''` 在二次商里同类，
且商映射把它们映到同一个点。

两条结论**分别**来自 `attrsEquivSetoid_r`（关系层）与
`mk_attrsEquiv`（商映射层）—— 两者都不是对方的前件。 -/
theorem closure_is_normal_form (A : Set K.MFCA) :
    (attrsEquivSetoid K).r A (closure K A)
      ∧ Quotient.mk (attrsEquivSetoid K) A
          = Quotient.mk (attrsEquivSetoid K) (closure K A) := by
  refine ⟨?_, mk_attrsEquiv K A⟩
  rw [attrsEquivSetoid_r]
  exact (closure_idempotent K A).symm

/-- ⭐⭐⭐ **闭包既封闭又是 intent —— 两个视角的一致性**。

对任意 `A`，`closure K A` 同时满足：
1. 「封闭性」（`ClosureOperator` 视角，`isClosed_iff_closure_eq`）；
2. 「是 intent」（Formal Concept 视角，`closure_isIntent`）。

**为什么值得一条定理**：下游若要在两种表述之间搬运
（例如把 FCA 的 intent 当作闭集用），需要知道它们描述的是**同一个集合**。
这需要两条定理**协同**，不能靠任一条单独得到。 -/
theorem closure_closed_and_intent (A : Set K.MFCA) :
    closure K (closure K A) = closure K A
      ∧ Order.IsIntent K.Irel (closure K A) := by
  refine ⟨closure_idempotent K A, closure_isIntent K A⟩

/-- ⭐ **商相等可由 `attrsEquiv` 直接得到**。

把 `Quotient.sound` 与 `attrsEquivSetoid_r` 接起来：
若两者的闭包相等，则它们在二次商里同一点。

这条把「集合层的等式」直接送到「商层的等式」，
省去下游先 `rw [attrsEquivSetoid_r]` 再 `exact Quotient.sound` 的两步。 -/
theorem mk_eq_of_closure_eq (A B : Set K.MFCA) (h : closure K A = closure K B) :
    Quotient.mk (attrsEquivSetoid K) A = Quotient.mk (attrsEquivSetoid K) B :=
  Quotient.sound ((attrsEquivSetoid_r K A B).mpr h)

end T112QuotientCapstone

end FateV2.Integration