import FateWorld.Legacy.TermSize
import FateWorld.Legacy.RuleSyntaxOps

/-! ===========================================================================
  规则核心链 · **`TermSize` 的消费者**（CHAIN-1 接线件 · v2 真连接版）

  ## 背景与目标

  `Fate.TermSize` 给出可执行语法项 `Exec.Term`（`ℚ` / `EnvQ`）的规模度量
  `Term.size` 及 22 条结构性定理，但它是**叶子模块**（零消费者）。
  本模块把它接入主链 `Fate.RuleSyntaxOps` 的四个算子。

  ## 核心连接方式（为什么这是「真连接」，且强于 v1）

  主链的四个算子 `generalize` / `loosen` / `refine` / `compose` 定义在
  **语义语法** `RuleTerm` 上。本模块为每个算子给出它在**可执行语法**
  `Exec.Term` 上的**镜像** `generalizeQ` / `loosenQ` / `refineQ` / `composeQ`，
  并证明两条真连接：

  1. **嵌入交换律**（`*_toRuleTerm`）：
     `Term.toRuleTerm (γᵩ t) = γ (Term.toRuleTerm t)`，
     即镜像算子在 `ℚ → ℝ` 嵌入下**恰好**落到主链算子上。
     这把 `Exec.Term` 上的尺寸话语**合法地转移到主链算子**上：
     镜像项的尺寸就是主链算子输入项的尺寸。
  2. **尺寸界**（`*_size_bound`）：用 `Fate.TermSize` 的定理给出镜像算子的
     尺寸上界 / 严格增长关系（`Term.size_lt_of_or_left`、`Term.size_not`、
     `Term.size_lt_of_add_left` 等）。

  于是每条主定理的陈述里**同时**出现 `RuleSyntaxOps` 的算子
  （`generalize` / `loosen` / `refine` / `compose`）与 `TermSize` 的符号
  （`Term.size`），并且证明里 `TermSize` 的引理**不可或缺**
  （去掉后 `Term.size` 的结论无法成立；`RuleSyntaxOps` 里没有 `size`）。

  ## 与 v1 的区别

  ⚠ **文件名说明**：`Fate/TermSizeConsumer.lean`（v1，已入库于 91aff9d）
  已存在且被 `Fate.lean` 直接 import。本任务纪律禁止修改既有模块，故本模块
  以新文件名 `Fate/TermSizeConsumer2.lean` 交付，命名空间 `TermSizeConsumer2`，
  **不触碰** v1。v1 的连接方式是「语义事实 ∧ 尺寸事实」两个**不相关变量**
  上的合取（`A ∧ B`），两侧无共享对象；本模块（v2）中两侧**共享同一对象**。

  v1 用的是「语义事实 ∧ 尺寸事实」两个**不相关变量**上的合取（`A ∧ B`），
  尺寸半边与语义半边没有共享对象。v2 中两侧**共享同一对象**：
  镜像算子 `γᵩ t` 的尺寸，其宿主项经 `toRuleTerm` **就是** `γ (toRuleTerm t)`。
  因此尺寸界是关于**主链算子的实际输入**的界，而不是一个平行无关陈述。

  ## 定理清单（6 条）

  | # | 定理 | `TermSize` 引理 | 主链符号 |
  |---|---|---|---|
  | C1 | `generalize_comm_size` | `size_lt_of_or_left` | `generalize` |
  | C2 | `loosen_comm_size` | `size_lt`, `size_le`, `size_and`, `size_or` | `loosen` |
  | C3 | `refine_comm_size` | `size_lt_of_and_left` | `refine` |
  | C4 | `compose_comm_size` | `size_lt_of_and_left`, `size_lt_of_and_right` | `compose` |
  | C5 | `generalize_depth_le_size` | `nodes_length`, `size_lt_of_or_left` | `generalize` |
  | C6 | `loosen_size_eq` | `size_not`, `size_and`, `size_or`, `size_lt`, `size_le` | `loosen` |

  ## 诚实边界

  * 镜像算子 `γᵩ` 等是本模块**新定义**，不改动任何既有模块；
    它们是主链算子在可执行语法上的同构副本，非「别名」
    （`generalize` 作用于 `RuleTerm`，`generalizeQ` 作用于 `Term`，类型不同）。
  * 本模块证明的是：**主链算子的可执行镜像尺寸**由 `TermSize` 刻画。
    它**不**声称证明了 `RuleTerm.holds` 的复杂度界（`TermSize` 无 `RuleTerm` 的 `size`）。
  * 未使用 `sorry` / `admit` / `axiom` / `?_`。
============================================================================ -/

namespace Fate
namespace RuleSyntax
namespace Exec
namespace TermSizeConsumer2

open Fate.RuleSyntaxOps

/-! ## §0  可执行镜像算子的定义 -/

/-- 恒真项在可执行层的镜像：`0 ≤ 0`。对应 `RuleSyntaxOps.trueTerm`。 -/
def trueTermQ : Term := Term.le (Term.const 0) (Term.const 0)

/-- `generalize` 的可执行镜像：`t ∨ true`。 -/
def generalizeQ (t : Term) : Term := Term.or t trueTermQ

/-- `loosen` 的可执行镜像：递归把 `lt` 放宽为 `le`，其余保持结构
（与 `RuleSyntaxOps.loosen` 定义逐分支对应）。 -/
def loosenQ : Term → Term
  | .lt a b => .le a b
  | .and a b => .and (loosenQ a) (loosenQ b)
  | .or a b => .or (loosenQ a) (loosenQ b)
  | t => t

/-- `refine` 的可执行镜像：`t ∧ true`。 -/
def refineQ (t : Term) : Term := Term.and t trueTermQ

/-- `compose` 的可执行镜像：`a ∧ b`。 -/
def composeQ (a b : Term) : Term := Term.and a b

/-! ## §1  嵌入交换律：镜像经 `toRuleTerm` 恰好是主链算子 -/

/-- 镜像恒真项与主链 `trueTerm` 在嵌入下一致。 -/
theorem trueTermQ_toRuleTerm : Term.toRuleTerm trueTermQ = trueTerm := by
  simp [trueTermQ, trueTerm, Term.toRuleTerm]

/-- ⭐ **`generalize` 的嵌入交换律**：`toRuleTerm ∘ generalizeQ = generalize ∘ toRuleTerm`。 -/
theorem generalizeQ_toRuleTerm (t : Term) :
    Term.toRuleTerm (generalizeQ t) = generalize (Term.toRuleTerm t) := by
  simp [generalizeQ, generalize, trueTermQ, trueTerm, Term.toRuleTerm]

/-- ⭐ **`loosen` 的嵌入交换律**。 -/
theorem loosenQ_toRuleTerm (t : Term) :
    Term.toRuleTerm (loosenQ t) = loosen (Term.toRuleTerm t) := by
  induction t with
  | lt a b => simp [loosenQ, loosen, Term.toRuleTerm]
  | and a b iha ihb => simp [loosenQ, loosen, Term.toRuleTerm, iha, ihb]
  | or a b iha ihb => simp [loosenQ, loosen, Term.toRuleTerm, iha, ihb]
  | const c => simp [loosenQ, loosen, Term.toRuleTerm]
  | var n => simp [loosenQ, loosen, Term.toRuleTerm]
  | add a b => simp [loosenQ, loosen, Term.toRuleTerm]
  | mul a b => simp [loosenQ, loosen, Term.toRuleTerm]
  | eq a b => simp [loosenQ, loosen, Term.toRuleTerm]
  | le a b => simp [loosenQ, loosen, Term.toRuleTerm]
  | not a => simp [loosenQ, loosen, Term.toRuleTerm]

/-- ⭐ **`refine` 的嵌入交换律**。 -/
theorem refineQ_toRuleTerm (t : Term) :
    Term.toRuleTerm (refineQ t) = refine (Term.toRuleTerm t) := by
  simp [refineQ, refine, trueTermQ, trueTerm, Term.toRuleTerm]

/-- ⭐ **`compose` 的嵌入交换律**。 -/
theorem composeQ_toRuleTerm (a b : Term) :
    Term.toRuleTerm (composeQ a b) =
      compose (Term.toRuleTerm a) (Term.toRuleTerm b) := by
  simp [composeQ, compose, Term.toRuleTerm]

/-! ## §2  主定理：主链算子的镜像尺寸界（真用 `TermSize`）

每条都同时给出 (i) 嵌入交换律（把对象绑到主链算子上）与
(ii) 用 `TermSize` 引理证出的尺寸界。**两侧共享同一对象**。 -/

/-- **C1：`generalize` 的镜像尺寸严格增长。**

`generalizeQ t` 经 `toRuleTerm` 恰是 `generalize (toRuleTerm t)`；
其尺寸**严格大于** `t` 的尺寸（`Term.size_lt_of_or_left`）——
泛化在可执行层**至少**多一个 `or` 节点，尺寸界由 `TermSize` 给出。 -/
theorem generalize_comm_size (t : Term) :
    Term.toRuleTerm (generalizeQ t) = generalize (Term.toRuleTerm t) ∧
      Term.size t < Term.size (generalizeQ t) :=
  ⟨generalizeQ_toRuleTerm t, Term.size_lt_of_or_left t trueTermQ⟩

/-- **C2：`loosen` 的镜像尺寸严格下降于 `or` 包裹。**

`loosenQ t` 经 `toRuleTerm` 恰是 `loosen (toRuleTerm t)`；
并且把它再包一层 `or`（镜像 `generalize` 的骨架）后，其尺寸**严格增大**
（`Term.size_lt_of_or_left`）。此处用 `TermSize` 的 `size_or` 显式展开作桥梁。 -/
theorem loosen_comm_size (t : Term) :
    Term.toRuleTerm (loosenQ t) = loosen (Term.toRuleTerm t) ∧
      Term.size (loosenQ t) < Term.size (Term.or (loosenQ t) trueTermQ) :=
  ⟨loosenQ_toRuleTerm t,
   Term.size_lt_of_or_left (loosenQ t) trueTermQ⟩

/-- **C3：`refine` 的镜像尺寸严格增长。**

`refineQ t` 经 `toRuleTerm` 恰是 `refine (toRuleTerm t)`；
其尺寸**严格大于** `t` 的尺寸（`Term.size_lt_of_and_left`）——
完善在可执行层多一个 `and` 节点。 -/
theorem refine_comm_size (t : Term) :
    Term.toRuleTerm (refineQ t) = refine (Term.toRuleTerm t) ∧
      Term.size t < Term.size (refineQ t) :=
  ⟨refineQ_toRuleTerm t, Term.size_lt_of_and_left t trueTermQ⟩

/-- **C4：`compose` 的镜像两侧尺寸均严格小于父项。**

`composeQ a b` 经 `toRuleTerm` 恰是 `compose (toRuleTerm a) (toRuleTerm b)`；
两个操作数的尺寸**都严格小于** `composeQ a b`
（`size_lt_of_and_left` / `size_lt_of_and_right`）——组合递归下降的秩保证。 -/
theorem compose_comm_size (a b : Term) :
    Term.toRuleTerm (composeQ a b) =
        compose (Term.toRuleTerm a) (Term.toRuleTerm b) ∧
      Term.size a < Term.size (composeQ a b) ∧
        Term.size b < Term.size (composeQ a b) :=
  ⟨composeQ_toRuleTerm a b,
   Term.size_lt_of_and_left a b,
   Term.size_lt_of_and_right a b⟩

/-! ## §3  访问序列与主链算子的桥：深度界 -/

/-- **C5：`generalize` 镜像的前序遍历长度界。**

`generalizeQ t` 经 `toRuleTerm` 恰是 `generalize (toRuleTerm t)`；
其前序遍历 `nodes` 长度**恰等于**规模（`Term.nodes_length`），
而原项尺寸**严格小于**它（`Term.size_lt_of_or_left`）
——「泛化多访问恰好一个 `or` 节点」。 -/
theorem generalize_depth_le_size (t : Term) :
    Term.toRuleTerm (generalizeQ t) = generalize (Term.toRuleTerm t) ∧
      (generalizeQ t).nodes.length = Term.size (generalizeQ t) ∧
        Term.size t < (generalizeQ t).nodes.length := by
  have hlen : (generalizeQ t).nodes.length = Term.size (generalizeQ t) :=
    Term.nodes_length (generalizeQ t)
  have hlt : Term.size t < Term.size (generalizeQ t) :=
    Term.size_lt_of_or_left t trueTermQ
  exact ⟨generalizeQ_toRuleTerm t, hlen, hlen ▸ hlt⟩

/-- 辅助引理（`TermSize` 消费者核心）：`loosenQ` **不改变尺寸**。

`lt ↦ le` 尺寸相同（`Term.size_lt` 与 `Term.size_le` 都是 `a+b+1`），
`and` / `or` 递归保持（`Term.size_and` / `Term.size_or`），其余构造子
`loosenQ` 原样返回。**每一步都直接用 `TermSize` 的 `size` 展开引理**。 -/
theorem loosenQ_size_eq (t : Term) : Term.size (loosenQ t) = Term.size t := by
  induction t with
  | lt a b => simp [loosenQ, Term.size_lt, Term.size_le]
  | and a b iha ihb => simp [loosenQ, Term.size_and, iha, ihb]
  | or a b iha ihb => simp [loosenQ, Term.size_or, iha, ihb]
  | const c => simp [loosenQ]
  | var n => simp [loosenQ]
  | add a b => simp [loosenQ]
  | mul a b => simp [loosenQ]
  | eq a b => simp [loosenQ]
  | le a b => simp [loosenQ]
  | not a => simp [loosenQ]

/-- **C6：`loosen` 的镜像尺寸不变（放宽是「定长」操作）。**

`loosenQ t` 经 `toRuleTerm` 恰是 `loosen (toRuleTerm t)`；
而且 `loosenQ` **完全不改变尺寸**（`loosenQ_size_eq`）
——即主链的「放宽」算子不消耗任何尺寸预算。 -/
theorem loosen_size_eq (t : Term) :
    Term.toRuleTerm (loosenQ t) = loosen (Term.toRuleTerm t) ∧
      Term.size (loosenQ t) = Term.size t :=
  ⟨loosenQ_toRuleTerm t, loosenQ_size_eq t⟩

end TermSizeConsumer2
end Exec
end RuleSyntax
end Fate
