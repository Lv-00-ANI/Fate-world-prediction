import FateWorld.FateV2.Core.Judgment
import Mathlib.Tactic

/-!
  # Rules · RuleSet — 规则集与应用

  ## 迁移登记
  - 来源：新写（原为空壳占位）
  - 动作：C 重写
  - 对应环节：F3-17（规则集）、F3-18（规则状态）
  - 依赖裁决：**D-002**（载体 = IR）、**D-003**（完备性）、**D-004**（单位 = 条件定理）、
              **D-006**（数据三层）
  - 改动：从空壳补成实现。旧代码把规则集当 `Set RuleTerm`，无来源、无状态。
          此处建立 `RuleSet` = 带来源账目的规则集合。
  - 状态：已编译

  ## 核心问题：规则集自己也有「来源」

  `D-004` 铁律：**来源不可丢弃**。这条不只约束单条规则，
  也约束**整个规则集**——一个规则集承了哪些未证前件？

  答案：**它的每一条规则所承前件的并**。

  这带来一个非平凡的性质：**规则集变大，来源只增不减**
  （`support_mono`）。即：**加规则不可能让系统变干净**。
  这条是「不能靠堆规则绕过假设」的形式化。
-/

namespace FateV2.Rules

open FateV2.Core

universe u

/-! ## §1 · 规则集 -/

/-- **规则集**：一束判断（每条判断 = 一条条件定理 = 一条规则）。

    用 `List` 而非 `Set`：条数与顺序都可能有意义（D-019 自由度最大化），
    且 `List` 保持可计算。去重由使用方决定，不在此硬编码。 -/
structure RuleSet (L : Type u) where
  /-- 规则表 -/
  rules : List (Judgment L)

namespace RuleSet

variable {L : Type u}

/-- 空规则集。 -/
def empty : RuleSet L := ⟨[]⟩

/-- **整个规则集的来源**：所有规则来源的并集。

    这是 `D-004` 铁律在**集合层**的推广：
    引用一个规则集时，要承的正是它全部规则的前件。 -/
def support (R : RuleSet L) : Support :=
  ⟨R.rules.flatMap (fun j => j.support.assumptions)⟩

/-- **整个规则集的状态**：取所有规则中最弱的。

    为什么取最弱：一条链的强度由最弱环节决定（`∘` 组合律的归纳推广）。 -/
def status (R : RuleSet L) : Status :=
  R.rules.foldr (fun j acc => j.status.weaker acc) .proven

/-- 单条规则加入规则集。 -/
def insert (j : Judgment L) (R : RuleSet L) : RuleSet L := ⟨j :: R.rules⟩

/-- 两个规则集拼接。 -/
def append (R₁ R₂ : RuleSet L) : RuleSet L := ⟨R₁.rules ++ R₂.rules⟩

/-! ### 来源的单调性 -/

/-- **加入规则只会增加来源**：`R.support ⊆ (insert j R).support`。

    这是「不能靠堆规则绕过假设」的第一半：**新规则的来源进来了**。 -/
theorem support_subset_insert (j : Judgment L) (R : RuleSet L) :
    R.support.Subset (insert j R).support := by
  intro x hx
  unfold support
  simp only [insert, List.flatMap_cons]
  exact List.mem_append_right _ hx

/-- **加入规则不会丢掉原有来源**。 -/
theorem insert_support_subset (j : Judgment L) (R : RuleSet L) :
    j.support.Subset (insert j R).support := by
  intro x hx
  unfold support
  simp only [insert, List.flatMap_cons]
  exact List.mem_append_left _ hx

/-- **拼接后来源 ⊇ 左**。 -/
theorem support_subset_append_left (R₁ R₂ : RuleSet L) :
    R₁.support.Subset (R₁.append R₂).support := by
  intro x hx
  unfold support at *
  simp only [append, List.flatMap_append]
  exact List.mem_append_left _ hx

/-- **拼接后来源 ⊇ 右**。 -/
theorem support_subset_append_right (R₁ R₂ : RuleSet L) :
    R₂.support.Subset (R₁.append R₂).support := by
  intro x hx
  unfold support at *
  simp only [append, List.flatMap_append]
  exact List.mem_append_right _ hx

/-- **单调性的总结**：空集的来源包含于任何规则集的来源。

    ⟹ 从空规则集出发，无论怎么加规则，来源**只会变大**。 -/
theorem empty_support_subset (R : RuleSet L) : (empty : RuleSet L).support.Subset R.support := by
  intro x hx
  simp [empty, support, Support.empty] at hx

/-! ### 状态 -/

/-- **空规则集的状态是 `proven`**（空条件恒真，无未证前件）。 -/
theorem status_empty : (empty : RuleSet L).status = .proven := by
  simp [status, empty]

end RuleSet

/-! ## §2 · 应用：从规则集推导结论 -/

section Apply

variable {L : Type u}

/-- **应用**：给定规则集、一条目标公式，与一个**可判定的结论相等性**，
    返回结论匹配该目标的规则。

    ⚠ `Formula` 本身没有 `DecidableEq`（它是互递归的，无法自动导出），
    所以相等性**必须由调用方提供**。这不是偷懒——
    不同的语义层可能想要不同的"相等"（语法相等 / 判定同值），
    把它做成参数符合 `D-019` 自由度最大化。

    本定义**只做匹配的形状**，不做合一求解（那属 `Core.Formula` 的语义层）。 -/
def RuleSet.applies (R : RuleSet L) (goal : Formula L)
    (dec : ∀ j : Judgment L, Decidable (j.concl = goal)) : List (Judgment L) :=
  R.rules.filter (fun j => j.concl = goal)

/-- **应用结果里的每一条规则，其来源都在原规则集的来源里**。

    这是 `D-004`「来源不可丢弃」在「应用」这个动作上的体现：
    **取用规则不会丢失它承的前件**。 -/
theorem RuleSet.applies_support_subset (R : RuleSet L) (goal : Formula L)
    (dec : ∀ j : Judgment L, Decidable (j.concl = goal)) :
    ∀ j ∈ R.applies goal dec, j.support.Subset R.support := by
  intro j hj
  simp only [RuleSet.applies, List.mem_filter] at hj
  intro x hx
  exact List.mem_flatMap.mpr ⟨j, hj.1, hx⟩

end Apply

end FateV2.Rules
