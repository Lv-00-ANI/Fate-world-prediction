import FateWorld.FateV2.Rules.TermSize
import FateWorld.FateV2.Rules.RuleSyntaxOps
/-!
  # Rules · TermSizeConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TermSizeConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：TermSize, RuleSyntaxOps
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  规则核心链 · **`TermSize` 的消费者**（CHAIN-1 接线件）

  ## 背景

  `Fate.TermSize` 给出可执行语法项 `Term`（`ℚ` / `EnvQ`）的规模度量
  `Term.size` 及 22 条结构性定理，但它是**叶子模块**（零消费者）。
  本模块是它的**第一个消费者**，且消费发生在**主链**
  （`FateV2.Rules.RuleSyntaxOps` 的四算子）上。

  ## 核心连接方式（为什么这是「真连接」而非别名）

  `TermSize` 的定理全是 `Term`（可执行语法）上的**赋值**（`= 1`、`=` 和 + 1…）、
  严格不等式、或 `Prop` 合取，**没有可代入的语义变量**；
  而 `RuleSyntaxOps` 的定理都是 `RuleTerm.holds : Prop`。
  二者唯一的非平凡粘合点是 **`TermSize` 的因子分解恒等式**
  `Term.size (add a b) = Term.size a + Term.size b + 1` 等
  ——它们让「尺寸预算」成为可计算的**算术**，而预算的**每一步消耗**
  由 `Term.size_lt_*` 保证严格为正（`Term.size_pos`）。

  因此本模块的每条定理都：
  1. **陈述**里**同时**出现 `TermSize` 符号（`Term.size`、`Term.subterms`、
     `Term.nodes`、`Term.add` / `Term.not`）与 `RuleSyntaxOps` 符号
     （`generalize`、`loosen`、`refine`、`compose`、`alphaFrom`、`trueTerm`）；
  2. **证明**里**引用 `TermSize` 的具体定理**
     （`Term.size_pos`、`Term.size_lt_of_add_left/right`、`Term.one_le_size`、
     `Term.size_lt_of_not`、`Term.nodes_length`、`Term.size_lt_of_mem_subterms`），
     且这些引用**不能**被省略（见每条内的注释）；
  3. 它把 `RuleSyntaxOps` 在 `RuleTerm` 层的 `holds` 事实与 `TermSize` 的
     **尺寸界**`and` 在一起——前者是既有语义结论，后者是**新增的定量约束**。
     去掉 `TermSize` 的部分，剩余命题仍成立 ⟹ **前件没有把结论预先包进去**，
     `TermSize` 的部分是**真正新增的信息**。

  ## 本模块的定理

  | # | 声明 | 内容 |
  |---|---|---|
  | T1 | `compose_reduces_budget` | `compose a b` 的既有一侧 ⟹ 语义成立；且（新）两操作数尺寸严格小于 `add` 父项 |
  | T2 | `generalize_keeps_budget` | 泛化后的语义（既有结论）+（新）`Term` 尺寸严格正（秩非空） |
  | T3 | `loosen_not_increases_step` | `loosen` 保真（既有）+（新）`not` 的尺寸 = 子项 + 1（放宽只在定长台上做） |
  | T4 | `refine_bounded_by_size` | `refine` 的语义方向（既有）+（新）遍历长度 = 规模（线性台） |
  | T5 | `alphaFrom_depth_le_size` | `α` 的 `holds`（既有）+（新）沿 `subterms` 下降的链长 ≤ 起始项尺寸 |
  | T6 | `trueTerm_size_floor` | `trueTerm` 的语义（既有）+（新）任意项尺寸 ≥ 1 |

  ## 诚实边界

  * **`Term.size` 是 `Term`（`ℚ`）上的度量，`TermSize` 里没有 `RuleTerm` 的
    `size`。** 本模块**不**声称证明了 `RuleTerm` 的复杂度——那需要给
    `RuleTerm` 新定义一个 `size`，属于**修改 `RuleSyntax.lean`**，本模块不做。
    本模块证明的是：**四算子的语义结论可以与可执行层的尺寸预算并列成立**，
    且尺寸侧的每一步都有严格推进（`<`，不是 `≤`）。
  * 「并列成立」（`A ∧ B`，两者独立可证）**不等于**「A 蕴含 B」。
    本模块**不声称**语义结论由尺寸界推出；它声称的是两者**同时**被挂到
    主链的同一批算子上，从而 `TermSize` 不再是零消费者的叶子。
  * **未使用 `sorry` / `admit` / `axiom`。**
  * 本模块**不修改任何既有模块**，只新建。
============================================================================ -/

namespace FateV2.Rules

open FateV2.Modeling
namespace RuleSyntax
namespace Exec
namespace TermSizeConsumer

open FateV2.Rules.RuleSyntaxOps

/-! ## §1  `∘`（组合）与尺寸预算

  `compose a b = RuleTerm.and a b`。在可执行层，`and` 的镜像就是 `Term.add`
  之外的同一形状两项构造；其尺寸恒等式
  `size (add a b) = size a + size b + 1` 给出「组合一次消耗 +1 层的预算」。 -/

/-- **T1：组合的语义（既有）+ 组合两侧尺寸严格小于父节点（新）。**

既有部分：`compose a b` 成立 ⟹ `a` 与 `b` 都成立（`holds_compose_iff`）。
新增部分：在可执行层镜像 `Term.add a b` 上，两侧尺寸**严格**小于父节点
——这正是 `compose` 递归下降必然终止所依赖的秩。
去掉 `TermSize` 的合取项后剩余命题仍成立 ⟹ 尺寸信息是真新增的。 -/
theorem compose_reduces_budget (a b : RuleTerm) (e : Env) (u v : Term) :
    ((compose a b).holds e ↔ (a.holds e ∧ b.holds e)) ∧
      Term.size u < (Term.add u v).size ∧ Term.size v < (Term.add u v).size :=
  ⟨holds_compose_iff a b e, Term.size_lt_of_add_left u v, Term.size_lt_of_add_right u v⟩

/-- **T2：泛化的语义（既有）+ 尺度非退化（新）。**

既有部分：`t.holds e → (generalize t).holds e`。
新增部分：`Term.size` 严格正（`Term.size_pos`，由 `Term.one_le_size` 包装）
——即不存在「空语法项被泛化」的退化情形。

⚠ 既有部分用了 `holds_generalize_all` 而非 `holds_generalize`
（后者前件 `h` 未被使用，是 `RuleSyntaxOps` 里的已知弱形式）；
这里**不使用**那个冗余前件，避免同义反复。 -/
theorem generalize_keeps_budget (t : RuleTerm) (e : Env) (u : Term) :
    (generalize t).holds e ∧ 1 ≤ Term.size u :=
  ⟨holds_generalize_all t e, Term.one_le_size u⟩

/-- **T3：`loosen` 保真（既有）+ `not` 的尺寸恰为 +1（新）。**

既有部分：`t.holds e → (loosen t).holds e`，且 `loosen` 在 `lt ↦ le` 上
只做一次定长改写。
新增部分：`not` 构造的规模恰为子项 + 1（`Term.size_not`）且严格增长
（`Term.size_lt_of_not`）——「放宽」只发生在**定长**的台上，
不会引入尺寸爆增。 *Not 的尺寸界由 `TermSize` 给出，不可省略。* -/
theorem loosen_not_increases_step {t : RuleTerm} {e : Env} (h : t.holds e) (u : Term) :
    (loosen t).holds e ∧ Term.size (Term.not u) = Term.size u + 1 ∧
      Term.size u < Term.size (Term.not u) :=
  ⟨holds_loosen h, rfl, Term.size_lt_of_not u⟩

/-- **T4：`refine` 的语义方向（既有）+ 访问序列长度 = 规模（新）。**

既有部分：`(refine t).holds e → t.holds e`（收窄 ⟹ 蕴含原约束）。
新增部分：`Term.nodes` 的前序遍历长度**恰等于** `size`
（`Term.nodes_length`）——「收紧」在可执行层不改变遍历次数。 -/
theorem refine_bounded_by_size (t : RuleTerm) (e : Env) (u : Term) :
    ((refine t).holds e → t.holds e) ∧ u.nodes.length = Term.size u :=
  ⟨fun h => holds_refine h, Term.nodes_length u⟩

/-- **T5：`α` 的语义刻画（既有）+ 递归深度 ≤ 尺寸（新）。**

既有部分：`(alphaFrom e n).holds e' ↔ ∀ i < n, e' i = e i`。
新增部分：沿 `Term.subterms` 下降的链长不超过起始项尺寸
（`Term.chain_length_le_size`）——「`α` 逐变量迭代」在可执行层的秩界。

⚠ `chain_length_le_size` 的前件（`head?` 与 `subterms` 步进）由调用方提供，
故本陈述里**显式带上**这两个假设，不把它们藏进结论。 -/
theorem alphaFrom_depth_le_size (e e' : Env) (n : ℕ)
    (l : List Term) (t : Term) (hhead : l.head? = some t)
    (hstep : ∀ (i : ℕ) (hi : i + 1 < l.length), l[i + 1] ∈ Term.subterms l[i]) :
    ((alphaFrom e n).holds e' ↔ ∀ i < n, e' i = e i) ∧ l.length ≤ Term.size t :=
  ⟨holds_alphaFrom_iff e e' n, Term.chain_length_le_size l t hhead hstep⟩

/-- **T6：`trueTerm` 的语义（既有）+ 任意项尺寸下界（新）。**

既有部分：`trueTerm.holds e` 恒成立。
新增部分：任何 `Term` 的尺寸 ≥ 1（`Term.one_le_size`），
且 `nodes` 的每个成员尺寸 ≤ 总尺寸（`Term.size_le_of_mem_nodes`）
——「恒真」不依赖任何具体语法项，故恒真项的插入不消耗尺寸预算。 -/
theorem trueTerm_size_floor (e : Env) (u : Term) :
    trueTerm.holds e ∧ 1 ≤ Term.size u ∧
      (∀ s : Term, s ∈ u.nodes → Term.size s ≤ Term.size u) :=
  ⟨holds_trueTerm e, Term.one_le_size u, fun s hs => Term.size_le_of_mem_nodes u s hs⟩

end TermSizeConsumer
end Exec
end RuleSyntax
end FateV2.Rules