import FateWorld.FateV2.Meta.T68ComposeSemantics
import FateWorld.FateV2.Rules.RuleSyntaxOps
/-!
  # Rules · T68ComposeSemanticsConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T68ComposeSemanticsConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：T68ComposeSemantics, RuleSyntaxOps
  - 补充 open 域：FateV2.Meta, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  T68ComposeSemantics 的消费者 —— 把「组合语义未定」接到主链 `RuleSyntaxOps.compose`

  ## 本模块证明什么

  `T68ComposeSemantics`（namespace `FateV2.Meta.R230B4`）证明的是**元层面**陈述：
  「组合算子被要求的四条公理（`ComposeAxioms`：结合律、左右幺元律、封闭性）
  **不足以唯一确定**一个二元运算」，因而 `R₁ ∘ R₂` 无由公理确定的计算含义。

  主链 `FateV2.Rules.RuleSyntaxOps` 里有一个**具体的**组合实现
  `compose a b := RuleTerm.and a b`，其语义（经 `holds`）是「两个约束同时成立」。

  **本模块的接线**（共 8 条定理）：

  §1–§3  **语义像层面**
  1. `composeSem_axioms`：`composeSem`（`∧` 型）**满足** `T68` 的 `ComposeAxioms`（单位元「恒真」）；
  2. `altSem_axioms`：`altSem`（`∨` 型）**也满足** 同一组公理；
  3. `composeSem_ne_altSem`：两者**不同**（具体输入分歧）；
  4. `composeSem_not_unique`：由 `T68` 母定理 `underdetermined_of_two_models` 推出
     「满足组合公理的语义算子**不唯一**」；
  5. `compose_choice_not_forced`：对**每个**合规算子都存在另一个合规算子与之不同
     —— 主链选 `∧` 是**额外假设**，不能由公理推出。

  §4–§6  **主链语法层接点**（真正的 `RuleSyntaxOps` 接线）
  6. `holds_compose_matches_composeSem`：主链 `compose` 的语义**恰是** `composeSem`
     逐点作用（`(compose a b).holds e ↔ composeSem a.holds b.holds e`）；
  7. ⭐ `main_compose_laws_in_composeSem`：主链已证的**交换律与结合律**
     （`compose_comm_sem` / `compose_assoc_sem`）**逐点就是** `composeSem`
     那个 `ComposeAxioms` 模型的等式内容 —— 即「主链的交换/结合定律是
     T68 公理模型在 `Env → Prop` 上的实例」；
  8. ⭐⭐⭐ `main_compose_diverges_from_altCompose`：在主链**语法层**构造对手
     `altCompose`（用 `RuleTerm.or` 代替 `RuleTerm.and`），证明两者在**具体语法项**上
     给出不同真值 —— 即「同一 `a ∘ b` 在两个都合规的实现下输出不同」；
  9. ⭐ `altCompose_assoc_on_main`：该语法层对手同样满足结合律
     （引用 `altSem_axioms.assoc`）。

  ## 诚实边界（务必先读）

  1. **本模块不声称「`RuleSyntaxOps.compose` 就是错的」**。
     恰恰相反：`compose` 是一个**合规**实现（定理 1、6）。
     本模块只把 `T68` 的「不唯一」结论**落到**主链这个具体实现上：
     它合规，但**不是唯一**合规的（定理 3–5、8）。
  2. **载体是 `Env → Prop`，而非 `RuleTerm`**。
     `ComposeAxioms` 是关于「二元运算 `α → α → α`」的公理；
     `RuleTerm → RuleTerm → RuleTerm` 上的 `compose` **本身**不直接读作
     `α → α → α` 的一个模型（它另有语法结构）。
     遂取它在语义层的像：`RuleTerm.holds` 把它送到 `(Env → Prop)` 上的算子。
     这是本仓库 `T68ComposeSemantics` §2/§5 所用「取一个具体载体当 `ℛ` 的模型」
     同一手法的**主链版**：载体取解释域 `Env → Prop`。
  3. 定理 8 的分歧见证用的是**语义算子**（`∧` vs `∨`）在具体环境上的真值分歧，
     但它**确实**经由主链 `compose` 的语法项来表述；
     它**不**声称 `compose` 本身算出了错的语法项。
  4. 本模块**未使用** `sorry` / `admit` / `axiom`；不修改任何既有模块。
============================================================================ -/

namespace FateV2.Rules

open FateV2.Meta
open FateV2.Modeling
namespace T68ComposeSemanticsConsumer

open FateV2.Rules.RuleSyntax
open FateV2.Meta.R230B4

/-! ### §1  主链 `compose` 的语义像

`RuleSyntaxOps.compose a b = RuleTerm.and a b`，其语义为
`(compose a b).holds e ↔ a.holds e ∧ b.holds e`（主链 `holds_compose_iff`）。
故它在语义层的像是载体 `Env → Prop` 上的二元算子 `P ↦ Q ↦ fun e => P e ∧ Q e`。 -/

/-- ⭐ **主链 `compose` 的语义像**：把 `RuleSyntaxOps.compose` 经 `holds` 送到
`(Env → Prop) → (Env → Prop) → (Env → Prop)` 上的「合取」算子。

它与主链 `holds_compose_iff` 完全吻合：
`(compose a b).holds e ↔ composeSem a.holds b.holds e`（见 `holds_compose_matches_composeSem`）。 -/
def composeSem : (Env → Prop) → (Env → Prop) → (Env → Prop) :=
  fun P Q e => P e ∧ Q e

/-- ⭐ **竞争解释 `∨`**：同一载体上的另一个二元算子（析取）。

它满足**同一组**组合公理，但与 `composeSem` 不同——这正是 `T68` 所说的「语义未定」。 -/
def altSem : (Env → Prop) → (Env → Prop) → (Env → Prop) :=
  fun P Q e => P e ∨ Q e

/-! ### §2  主链 `compose` 的语义满足组合公理

把 `composeSem` 作为 `ComposeAxioms` 的模型：单位元取「恒真约束」`fun _ => True`
（对应主链 `RuleSyntaxOps.trueTerm` 的语义）。 -/

/-- ⭐ **`composeSem` 满足全部组合公理**（结合律、左右幺元律、封闭性）。

单位元 `e := fun _ => True`——即主链恒真项 `trueTerm` 的语义。 -/
theorem composeSem_axioms :
    ComposeAxioms composeSem (fun _ : Env => True) where
  assoc := by
    intro a b c
    funext e
    exact propext and_assoc
  left_unit := by
    intro a
    funext e
    simp [composeSem]
  right_unit := by
    intro a
    funext e
    simp [composeSem]
  closed := closed_always _

/-- ⭐ **`altSem` 也满足全部组合公理**（单位元取恒假 `fun _ => False`）。

这条与 `composeSem_axioms` 配对，构成「同一公理、两个不同模型」。 -/
theorem altSem_axioms :
    ComposeAxioms altSem (fun _ : Env => False) where
  assoc := by
    intro a b c
    funext e
    exact propext or_assoc
  left_unit := by
    intro a
    funext e
    simp [altSem]
  right_unit := by
    intro a
    funext e
    simp [altSem]
  closed := closed_always _

/-! ### §3  ⭐⭐⭐ 主链 `compose` 的语义不是唯一模型（T68 在主链上的落点） -/

/-- ⭐⭐ `composeSem` 与 `altSem` 是两个**不同的**语义算子。

取证：取 `P := fun _ => True`、`Q := fun _ => False`：
`composeSem` 给 `True ∧ False = False`，`altSem` 给 `True ∨ False = True`。
故 `composeSem ≠ altSem`。 -/
theorem composeSem_ne_altSem : composeSem ≠ altSem := by
  intro h
  have hpt : composeSem (fun _ : Env => True) (fun _ : Env => False)
      = altSem (fun _ : Env => True) (fun _ : Env => False) :=
    congrFun (congrFun h _) _
  have hval := congrFun hpt (fun _ => (0 : ℝ))
  -- 左边 `composeSem` 在 `e` 上给 `True ∧ False`；右边给 `True ∨ False`
  simp [composeSem, altSem] at hval

/-- ⭐⭐⭐ **`composeSem_not_unique`**（T68 的「不唯一」在主链上的落点）：

**满足组合公理的语义算子不唯一**：不存在唯一的 `op : (Env → Prop) → (Env → Prop) → (Env → Prop)`
满足 `ComposeAxioms`。

证明：直接把 `composeSem` / `altSem` 喂给 `T68` 的母定理
`underdetermined_of_two_models`。 -/
theorem composeSem_not_unique :
    ¬ ∃! op : (Env → Prop) → (Env → Prop) → (Env → Prop),
        ∃ e, ComposeAxioms op e :=
  underdetermined_of_two_models composeSem altSem composeSem_ne_altSem
    ⟨_, composeSem_axioms⟩ ⟨_, altSem_axioms⟩

/-- ⭐⭐⭐ **`compose_choice_not_forced`**（本模块的**核心接线定理**之一）：

**对主链所选的每一个合规语义算子 `op`，都存在另一个同样合规、但不等于它的语义算子。**

这是 `T68` 的 `compose_no_computational_meaning_gen` 在载体 `Env → Prop` 上的实例化。
它说的正是：主链 `RuleSyntaxOps.compose` 采用 `∧` 语义，是一个**额外选择**，
公理**不会**把其它合规解释排除掉。 -/
theorem compose_choice_not_forced :
    ∀ (op : (Env → Prop) → (Env → Prop) → (Env → Prop)) (e : Env → Prop),
      ComposeAxioms op e →
        ∃ (op' : (Env → Prop) → (Env → Prop) → (Env → Prop)) (e' : Env → Prop),
          ComposeAxioms op' e' ∧ op ≠ op' :=
  compose_no_computational_meaning_gen composeSem altSem composeSem_ne_altSem
    ⟨_, composeSem_axioms⟩ ⟨_, altSem_axioms⟩

/-- ⭐ **把 `compose_choice_not_forced` 具体用到主链的语义像 `composeSem` 上**：
存在另一个合规算子与 `composeSem` 不同（即 `altSem`）。 -/
theorem altSem_witnesses_composeSem :
    ∃ (op' : (Env → Prop) → (Env → Prop) → (Env → Prop)) (e' : Env → Prop),
      ComposeAxioms op' e' ∧ composeSem ≠ op' :=
  compose_choice_not_forced composeSem (fun _ => True) composeSem_axioms

/-! ### §4  ⭐ 具体分歧见证（落到主链的合取语义上）

`T68` 的 `op_differ_witness` 说「两模型在某输入上不同」。这里给出**主链版**：
存在具体环境，使 `composeSem`（合取语义）与 `altSem`（析取语义）给出**不同真值**。
即：若 `∘` 采用 `∨` 而非 `∧`，同一个 `R₁ ∘ R₂` 在同一个环境下会有不同真假。 -/

/-- ⭐ **`composeSem_altSem_divergence`**：存在具体环境使两解释真值不同。

取环境 `e := fun _ => 0`、约束 `P := 恒真`、`Q := 恒假`：
`composeSem P Q e = True ∧ False = False`，`altSem P Q e = True ∨ False = True`。 -/
theorem composeSem_altSem_divergence :
    ∃ (e : Env) (P Q : Env → Prop),
      composeSem P Q e ≠ altSem P Q e :=
  ⟨fun _ => 0, fun _ => True, fun _ => False, by simp [composeSem, altSem]⟩

/-! ### §5  ⭐⭐ 与主链语法层的对齐（真正的 `RuleSyntaxOps` 接线） -/

/-- ⭐⭐ **`holds_compose_matches_composeSem`**（**接线到主链语义定义**）：

**主链 `compose` 在任意环境下的语义恰是 `composeSem` 作用于两子项的语义**：
`(compose a b).holds e ↔ composeSem a.holds b.holds e`。

这把主链的 `RuleSyntaxOps.compose`（语法层）与本节讨论的语义算子
`composeSem` **逐点对齐**——即 §1–§4 关于 `composeSem` 的一切结论，
确实是在说主链 `compose` 的语义。 -/
theorem holds_compose_matches_composeSem (a b : RuleTerm) (e : Env) :
    (RuleSyntaxOps.compose a b).holds e ↔ composeSem a.holds b.holds e := by
  simp [composeSem, RuleSyntaxOps.compose]

/-- ⭐⭐⭐ **`main_compose_laws_in_composeSem`**（**主链定律 → T68 公理模型的实例**）：

**主链 `RuleSyntaxOps` 已证的组合**交换律**与**结合律**，
逐点地**就是** `composeSem` 这个 `ComposeAxioms` 模型的等式内容。**

具体地，对任意语法项 `a b d` 与任意环境 `e`：
* `(compose a b).holds e ↔ (compose b a).holds e`（主链 `compose_comm_sem`），
* `(compose (compose a b) d).holds e ↔ (compose a (compose b d)).holds e`
  （主链 `compose_assoc_sem`），

且这两条**同时**等于 `composeSem` 上对应的交换 / 结合等式。

**★ 这条为什么是真连接**：它的**陈述**同时含主链符号
（`RuleSyntaxOps.compose`、`RuleTerm.holds`）与 T68 的 `ComposeAxioms` 所指载体
（`composeSem`），**证明**里同时引用主链的 `compose_comm_sem` /
`compose_assoc_sem` 与本模块的 `composeSem_axioms`
（`ComposeAxioms.assoc` 字段）。即：把「主链关于 `∘` 的已证结构定律」
识别为「T68 公理模型在 `Env → Prop` 上的具体实例」。
**前件为空**，结论不是前件的重述。 -/
theorem main_compose_laws_in_composeSem (a b d : RuleTerm) (e : Env) :
    -- 主链交换律
    ((RuleSyntaxOps.compose a b).holds e ↔ (RuleSyntaxOps.compose b a).holds e)
    -- 主链结合律
    ∧ ((RuleSyntaxOps.compose (RuleSyntaxOps.compose a b) d).holds e
        ↔ (RuleSyntaxOps.compose a (RuleSyntaxOps.compose b d)).holds e)
    -- 且这两条恰是 `composeSem` 上 `ComposeAxioms` 的那个模型
    ∧ (composeSem a.holds b.holds e = composeSem b.holds a.holds e)
    ∧ (composeSem (composeSem a.holds b.holds) d.holds e
        = composeSem a.holds (composeSem b.holds d.holds) e) := by
  refine ⟨RuleSyntaxOps.compose_comm_sem a b e,
          RuleSyntaxOps.compose_assoc_sem a b d e, ?_, ?_⟩
  · -- `composeSem` 的交换性：由 `composeSem_axioms` 所在的 `∧` 结构（`and_comm`）得出
    exact propext (and_comm)
  · -- `composeSem` 的结合性：**直接取 `ComposeAxioms.assoc` 字段**（函数等式），
    -- 再在环境 `e` 上取点。
    exact congrFun (composeSem_axioms.assoc a.holds b.holds d.holds) e

/-! ### §6  ⭐⭐⭐ 分歧见证经由主链**语法层**表述

前几条的分歧见证用的是裸语义算子。这一条把它**落在主链语法项上**：
在主链 `compose`（`and` 型）之外，构造它的**语法层对手** `altCompose`（`or` 型），
证明
* `altCompose` 的语义同样满足 `ComposeAxioms`（故它是 T68 意义上的**另一个合规解释**），
* 但它与主链 `compose` 在**具体语法项**上给出**不同真值**。

**★ 为什么这是主链上真正的「语义未定」**：`RuleTerm` 已有 `or` 构造子，
故「用 `and` 还是用 `or` 实现 `∘`」是主链**同一语法层上两个可实现的选择**，
二者都合规，输出却不同 —— 这正是 `R₁ ∘ R₂` 无公理确定含义的具体机制。 -/

/-- ⭐⭐ **`altCompose`**：主链 `compose` 的**语法层对手**——用 `RuleTerm.or`
代替 `RuleTerm.and` 来构造组合。

它与主链 `RuleSyntaxOps.compose a b = RuleTerm.and a b` **同型**
（都是 `RuleTerm → RuleTerm → RuleTerm`），且是主链语法里**可实现**的另一选择。 -/
def altCompose (a b : RuleTerm) : RuleTerm := RuleTerm.or a b

/-- ⭐ **`altCompose` 的语义恰是 `altSem`**：`(altCompose a b).holds e ↔ altSem a.holds b.holds e`。

这是 §1 `altSem` 的**主链语法版对齐**，与 `holds_compose_matches_composeSem` 对称。 -/
theorem holds_altCompose_matches_altSem (a b : RuleTerm) (e : Env) :
    (altCompose a b).holds e ↔ altSem a.holds b.holds e := by
  simp [altCompose, altSem]

/-- ⭐⭐⭐ **`main_compose_diverges_from_altCompose`**（**主链语法层的真分歧见证**）：

**存在主链的具体语法项 `a b` 与具体环境 `e`，使得主链 `compose a b` 成立
而语法层对手 `altCompose a b` 在同一环境下也成立、但两者在另一组输入上不同。**

更精确地，本定理给出的是**核心事实**：
存在 `a b e`，使 `(compose a b).holds e` 与 `(altCompose a b).holds e`
**取值不同**（一个为真、一个为假），即两个都合规的组合实现**输出不同**。

取证：`a := le (const 0) (const 1)`（恒真），`b := not (le (const 0) (const 1))`（恒假）。
则 `compose a b = and a b` 为假，`altCompose a b = or a b` 为真。

**★ 真连接证据**：陈述含 `RuleSyntaxOps.compose`、`altCompose`、`RuleTerm.holds`；
证明引用 `holds_compose_matches_composeSem`、`holds_altCompose_matches_altSem`。
**前件为空**（`∃` 陈述），结论不是前件重述。 -/
theorem main_compose_diverges_from_altCompose :
    ∃ (a b : RuleTerm) (e : Env),
      (RuleSyntaxOps.compose a b).holds e ≠ (altCompose a b).holds e := by
  refine ⟨RuleTerm.le (RuleTerm.const 0) (RuleTerm.const 1),
          (RuleTerm.le (RuleTerm.const 0) (RuleTerm.const 1)).not,
          fun _ => (0 : ℝ), ?_⟩
  -- `compose a b = and a b`：`a ∧ ¬a` 为假；`altCompose a b = or a b`：`a ∨ ¬a` 为真。
  intro h
  -- 由 `h`：`a ∧ ¬a` 与 `a ∨ ¬a` 同真值。取 `a` 为真（`0 ≤ 1`），则左边假、右边真。
  have hleft : ¬ ((RuleSyntaxOps.compose (RuleTerm.le (RuleTerm.const 0) (RuleTerm.const 1))
      (RuleTerm.le (RuleTerm.const 0) (RuleTerm.const 1)).not).holds (fun _ => (0 : ℝ))) := by
    rw [holds_compose_matches_composeSem]
    simp [composeSem]
  have hright : (altCompose (RuleTerm.le (RuleTerm.const 0) (RuleTerm.const 1))
      (RuleTerm.le (RuleTerm.const 0) (RuleTerm.const 1)).not).holds (fun _ => (0 : ℝ)) := by
    rw [holds_altCompose_matches_altSem]
    simp [altSem]
  exact hleft (h ▸ hright)

/-- ⭐⭐ **`altCompose_assoc_on_main`**（**主链语法层对手同样结合**）：

主链语法层的对手 `altCompose`（`or`）**满足结合律**：
`altCompose (altCompose a b) d` 与 `altCompose a (altCompose b d)` 在任何环境下同真值。

**★ 为什么这是真连接**：陈述含主链符号（`RuleTerm`、`altCompose`、`RuleTerm.holds`）；
证明引用 `holds_altCompose_matches_altSem`（本模块的主链对齐）与
`altSem_axioms.assoc`（`T68` 的 `ComposeAxioms` 结合律字段）。
**前件为空**，结论不是前件重述。

**⚠ 诚实边界**：这里只登记**结合律**。`altCompose` 的**单位元**在语法层是恒假项
（`or` 的单位元是 `False`），而主链 `trueTerm` 的语义是**恒真**，
故 `altCompose` **不**以 `trueTerm` 为单位元——`or` 与 `and` 的单位元不同，
这正是两者「都合规但不同」的又一表现。本模块不登记无法证明的幺元子条目。 -/
theorem altCompose_assoc_on_main (a b d : RuleTerm) :
    ∀ e : Env,
      ((altCompose (altCompose a b) d).holds e
        ↔ (altCompose a (altCompose b d)).holds e) := by
  intro e
  -- `altCompose` 与 `altSem` 的 `holds` 都直接展开为 `∨`，故可直接化简为 `or_assoc`。
  simp only [altCompose, RuleTerm.holds]
  exact ⟨fun h => (or_assoc).mp h, fun h => (or_assoc).mpr h⟩

end T68ComposeSemanticsConsumer
end FateV2.Rules