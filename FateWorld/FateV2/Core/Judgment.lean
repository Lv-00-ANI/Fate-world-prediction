import FateWorld.FateV2.Core.Syntax

/-!
  # Core · 判断（规则）

  ## 迁移登记
  - 来源：新写
  - 动作：C 重写
  - 对应环节：F3-14（规则载体）、F3-17（规则集）、F3-18（规则状态）
  - 依赖裁决：**D-004**（规则单位 = 条件定理 + support + status）、
              **D-016**（纯 CIC）、**D-019**（自由度最大化）
  - 改动：旧代码把规则写成 `RuleTerm` 的集合，无来源、无状态。
          此处建立 `Judgment = hyp ⊢ concl + support + status`。
  - 状态：已编译未验证

  ## 为什么 `support` 里没有数据字段
  D-005/D-006：数据可**消融**——能形式化的转成具体定理（`support = ∅`），
  不能形式化的转成**经验假设**。数据本身归档，不进定理。
  因此 `Support` 只装**未证前件**，不装数据引用。

  ## 反射（J₁ 能否在 IR 内谈论判断）
  `quoteJudgment` 把判断编码成公式/项，于是 J₁ 层的公式可以指向具体判断。
  **完整的解码保真（`decode (encode j) = j`）不在本批**——见文件末「尾项」。
-/


namespace FateV2.Core

universe u

/-! ## 假设标识与来源 -/

/-- 假设标识。

    包含三类来源（D-016 之后它们**没有特殊地位**，都是 `support` 里的一行）：
    * 三条基础公理：`"propext"` / `"Classical.choice"` / `"Quot.sound"`
    * 理论假设：`"A1"` … `"A34"`
    * 建模假设与数据消融产生的经验假设 -/
abbrev AssumptionId : Type := String

/-- **来源**：这条判断靠哪些**未证前件**成立。

    ⚠ 不含数据（D-005/D-006：数据不进定理）。 -/
structure Support where
  assumptions : List AssumptionId
  deriving DecidableEq, Repr

namespace Support

/-- 空来源：无未证前件（即可视为「已证」的来源）。 -/
def empty : Support := ⟨[]⟩

/-- 合并来源。**这是 `∘` 组合用的运算**（D-004 §4.3：support 取并）。 -/
def union (a b : Support) : Support := ⟨a.assumptions ++ b.assumptions⟩

/-- 包含关系：`a ⊆ b` 表示 `b` 至少承了 `a` 的全部前件。 -/
def Subset (a b : Support) : Prop := ∀ x ∈ a.assumptions, x ∈ b.assumptions

/-- 合并后仍包含左边——**「没有算子能减少 support」的左半边**。 -/
theorem subset_union_left (a b : Support) : a.Subset (a.union b) := by
  intro x hx
  unfold union
  exact List.mem_append_left _ hx

/-- 合并后仍包含右边——右半边。 -/
theorem subset_union_right (a b : Support) : a.Subset (b.union a) := by
  intro x hx
  unfold union
  exact List.mem_append_right _ hx

/-- 来源包含是自反的。 -/
theorem subset_refl (a : Support) : a.Subset a := fun _ hx => hx

/-- 来源包含是传递的。 -/
theorem subset_trans {a b c : Support} (hab : a.Subset b) (hbc : b.Subset c) : a.Subset c :=
  fun x hx => hbc x (hab x hx)

end Support

/-! ## 状态 -/

/-- 判断的四档状态（D-004 §2.4）。 -/
inductive Status : Type where
  /-- 框架内已证（无未证前件） -/
  | proven
  /-- 条件定理（前件未证，但推导链完整） -/
  | conditional
  /-- 经验陈述（无法证明，只能登记） -/
  | empirical
  /-- 已被反驳 -/
  | refuted
  deriving DecidableEq, Repr

namespace Status

/-- 状态序：越靠前越强。用于 `∘` 组合时「取较弱」。 -/
def strength : Status → Nat
  | .proven      => 3
  | .conditional => 2
  | .empirical   => 1
  | .refuted     => 0

/-- 取两者中较弱的状态（`∘` 组合用，D-004 §4.3）。 -/
def weaker (a b : Status) : Status :=
  if a.strength ≤ b.strength then a else b

/-- 若两方都 `proven`，合并仍 `proven`。 -/
theorem weaker_proven_proven : weaker .proven .proven = .proven := by
  unfold weaker; decide

end Status

/-! ## 判断 = 规则 -/

/-- **条件定理 = 规则**。IR 的基本单位。 -/
structure Judgment (L : Type u) where
  /-- 前件（可为 `.top`，表示无条件） -/
  hyp     : Formula L
  /-- 结论 -/
  concl   : Formula L
  /-- 来源（铁律 3：不可丢弃） -/
  support : Support
  /-- 状态 -/
  status  : Status

namespace Judgment

variable {L : Type u}

/-- 无条件判断：`hyp = top`。 -/
def mkUncond (concl : Formula L) (support : Support) (status : Status) : Judgment L :=
  ⟨.top, concl, support, status⟩

/-- **`∘` 组合**：`j₂ ∘ j₁` 取 `j₁` 的前件与 `j₂` 的结论，
    来源取**并**，状态取**较弱**（D-004 §4.3）。

    注：真正的合法性（`j₁.concl` 能推出 `j₂.hyp`）需要一条桥，见 B3。
    这里只给**来源与状态的传播**，它是「脏会传播」的形式化。 -/
def compose (j₁ j₂ : Judgment L) : Judgment L :=
  ⟨j₁.hyp, j₂.concl, j₁.support.union j₂.support, j₁.status.weaker j₂.status⟩

/-- **「`∘` 不减少来源」的左半边**（J₁ 层可证）。 -/
theorem compose_support_subset_left (j₁ j₂ : Judgment L) :
    j₁.support.Subset (j₁.compose j₂).support := by
  unfold compose
  exact Support.subset_union_left _ _

/-- **「`∘` 不减少来源」的右半边**。 -/
theorem compose_support_subset_right (j₁ j₂ : Judgment L) :
    j₂.support.Subset (j₁.compose j₂).support := by
  unfold compose
  exact Support.subset_union_right _ _

end Judgment

/-! ## 反射：把判断编码进 IR

  J₁ 层要能谈论 J₀ 的判断，就必须把判断**编码**成项/公式。
  这里给**规范编码**，并用一个 `Codec` 结构留出替换空间（D-019：不写死）。 -/

/-- 把公式编成项（`Data.logic` 的用法）。 -/
def quoteFormula {L : Type u} (f : Formula L) : Term L := .lit (.logic f)

/-- 规范编码用的谓词名。 -/
def judgmentPredName : PredId := "Judgment"

/-- 把来源编成项（每条假设一个 `ent`）。 -/
def quoteSupport {L : Type u} (s : Support) : Term L :=
  .lit (.vec (s.assumptions.map (fun a => Data.ent a)))

/-- 把判断编成**公式**：`Judgment(hyp, concl)`。

    `support` 与 `status` 是**元数据**，不进入编码后的核心公式；
    需要谈论它们时，用 `quoteSupport` 单独编项。 -/
def quoteJudgment {L : Type u} (j : Judgment L) : Formula L :=
  .ext judgmentPredName [quoteFormula j.hyp, quoteFormula j.concl]

/-- 把判断编成**项**（可直接当数据嵌入）。 -/
def quoteJudgmentTerm {L : Type u} (j : Judgment L) : Term L :=
  .lit (.logic (quoteJudgment j))

/-- **判断的编码方式**（D-019：不写死编码，可替换）。

    默认用 `quoteJudgment`，但允许换别的编码（如带 `support`/`status` 的完整编码）。 -/
structure JudgmentCodec (L : Type u) where
  /-- 把判断编成公式 -/
  encode : Judgment L → Formula L

/-- 规范编码的实例。 -/
def canonicalCodec (L : Type u) : JudgmentCodec L := ⟨quoteJudgment⟩

/-! ## 尾项（本批未做，登记不隐藏）

  | # | 项 | 为什么难 | 归属 |
  |---|---|---|---|
  | 1 | `decode : Formula L → Option (Judgment L)` 与 `decode_encode` 保真 | `support`/`status` 无法从公式结构还原（它们不是语法） | B2 尾 |
  | 2 | 编码**单射性**（不同判断编码不同） | 需要 `String` 判等与 `ext` 的注入性，且 `Formula` 无 `DecidableEq` | B2 尾 |
  | 3 | `Support` 的「去重/规范化」 | 现用 `List`，重复假设会累积；是否需要 `Nodup` 待定（D-019：先不写死） | B2 尾 |

  这些都不阻断 B3（四算子的来源传播只用到 `subset_union_*` 与 `weaker`）。
-/

end FateV2.Core
