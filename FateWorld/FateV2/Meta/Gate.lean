import FateWorld.FateV2.Meta.Ledger
import FateWorld.FateV2.Meta.ThreeKinds
import Mathlib.Tactic

/-!
  # Meta · Gate — 验收闸门

  ## 迁移登记
  - 来源：新写（原为空壳占位）
  - 动作：C 重写
  - 对应环节：元层 · 验收闸门
  - 依赖裁决：**D-001**（判据变更权归作者）、**D-016**（账实相符）、**D-022**（反空泛）
  - 改动：从空壳补成实现。把 `_gate.ps1` 里那 11 道门禁的**判据形状**形式化，
          并证明它们之间的**依赖关系**（有些门禁成立蕴含另一些成立）。
  - 状态：已编译

  ## 为什么要形式化门禁

  `_gate.ps1` 是脚本——它只能告诉你「这一批通过了」，
  不能告诉你「**为什么**这批复用之前的结论是安全的」。

  形式化的价值在于三条**蕴含关系**：

  | 若成立 | 则蕴含 | 为什么 |
  |---|---|---|
  | G4（核内零公理） | G5（账实相符）在 `pure` 外壳上成立 | 零公理 ⟹ 来源为空 |
  | G5 成立 | 定理可被它声称的外壳覆盖 | 登记即授权 |
  | D-001 前件必要性 | 结论有内容 | 两条必须同时满足 |

  ## 诚实边界

  本模块**不检查真实代码**（那是脚本的活：解析 `.lean`、跑 `#print axioms`）。
  它只给**判据的形式**与**判据间的逻辑关系**。
  把形式化的 `Gate.Verdict` 接上真实检查，是 `_gate.ps1` 的任务。
-/

namespace FateV2.Meta

open FateV2.Core

universe u

/-! ## §1 · 闸门的判据形状 -/

/-- **一道闸门**：一个判据 + 一句说明。

    判据用 `Prop` 表示——具体检查什么由调用方决定
    （脚本传「文件里有没有 sorry」这类可判定的命题）。 -/
structure Gate where
  /-- 闸门编号（`"G1"` … `"G11"`） -/
  id    : String
  /-- 判据 -/
  holds : Prop
  /-- 说明 -/
  desc  : String

/-- **一组闸门全过**：所有判据同时成立。 -/
def AllPass (gs : List Gate) : Prop := ∀ g ∈ gs, g.holds

namespace AllPass

/-- 空闸门集恒过。 -/
theorem nil : AllPass [] := by
  intro g hg
  exact absurd hg (by simp)

/-- 全过则每条都过。 -/
theorem elim {gs : List Gate} (h : AllPass gs) {g : Gate} (hg : g ∈ gs) : g.holds :=
  h g hg

/-- **单调性**：若一组闸门全过，其子集也全过。 -/
theorem subset {gs₁ gs₂ : List Gate} (h : AllPass gs₁)
    (hsub : ∀ g ∈ gs₂, g ∈ gs₁) : AllPass gs₂ :=
  fun g hg => h g (hsub g hg)

/-- **添加闸门后不自动全过**：`AllPass gs` 不蕴含 `AllPass (g :: gs)`，
    除非 `g` 本身成立。这条防止「加一道永远过的闸门来凑数」。 -/
theorem cons_intro {gs : List Gate} {g : Gate} (hg : g.holds) (h : AllPass gs) :
    AllPass (g :: gs) := by
  intro g' hg'
  rcases List.mem_cons.mp hg' with rfl | hmem
  · exact hg
  · exact h g' hmem

end AllPass

/-! ## §2 · 账实相符的两个方向（G5） -/

section AccountMatch

variable {L : Type u}

/-- **账实相符**：定理的真实公理依赖**等于**它登记的来源。

    这是 `D-016` 的核心判据，也是 G5 的形式。 -/
def AccountMatches (axs : List AssumptionId) (sup : Support) : Prop :=
  axs = sup.assumptions

/-- **零公理 ⟹ 空来源**（G4 ⟹ G5 的一半）：核内定理的公理依赖为空，
    则它的登记来源也必须为空。 -/
theorem zero_axioms_implies_empty_support {axs : List AssumptionId} {sup : Support}
    (h : axs = []) (hm : AccountMatches axs sup) : sup.assumptions = [] := by
  unfold AccountMatches at hm
  rw [← hm, h]

/-- **账实相符是对称的**：登记了什么，就应该是什么。

    这条看起来平凡，但它是「不能只报喜不报忧」的形式：
    若真实依赖是三条公理而登记为空，`AccountMatches` 直接为假。 -/
theorem account_match_symm {axs : List AssumptionId} {sup : Support}
    (h : AccountMatches axs sup) : AccountMatches sup.assumptions ⟨axs⟩ := by
  unfold AccountMatches at *
  simp [h]

/-- **账实相符蕴含可被外壳覆盖**：登记的来源就是真实用到的，
    因此只要外壳允许这些假设，定理就是合法的。

    这把 G5 与 `Classical.Shell.covers` 接上了。 -/
theorem account_match_covers {axs : List AssumptionId} {sup : Support}
    {s : FateV2.Classical.Shell}
    (hm : AccountMatches axs sup)
    (hcov : ∀ a ∈ axs, a ∈ s.assumptions) :
    s.covers sup :=
  fun a ha => hcov a (by rw [hm]; exact ha)

end AccountMatch

/-! ## §3 · 反空泛判据（D-022） -/

section NonVacuous

variable {L : Type u}

/-- **前件必要性**（D-001 双条件之一）：每条前件要么被证明必需，要么必须删除。

    「被证明必需」的形式：**删除它之后结论不再成立**。

    用参数 `needed : AssumptionId → Prop` 表示「该前件被证明必需」——
    具体怎么证，属实现层。 -/
def PremisesNecessary (sup : Support) (needed : AssumptionId → Prop) : Prop :=
  ∀ a ∈ sup.assumptions, needed a

/-- **结论有内容**（D-001 双条件之二，也是 D-022 的反空泛要求）：
    定理不是定义展开，即去掉定义后不能直接得到。

    `nonDefEq : L → Prop` 表示「该判断不是定义相等」——由实现层给出判据。 -/
def Contentful (j : Judgment L) (nonDefEq : Judgment L → Prop) : Prop := nonDefEq j

/-- **D-001 的验收判据**：两个条件**必须同时满足**。

    `_约束.md` §E 原文：
    > 「**必须同时满足，缺一不可**」 -/
def PassesAcceptance (j : Judgment L)
    (needed : AssumptionId → Prop) (nonDefEq : Judgment L → Prop) : Prop :=
  PremisesNecessary j.support needed ∧ Contentful j nonDefEq

/-- **只满足一条不算通过**：反例——前件都必需，但结论是定义展开。 -/
theorem one_condition_insufficient (j : Judgment L)
    (needed : AssumptionId → Prop) (nonDefEq : Judgment L → Prop)
    (hprem : PremisesNecessary j.support needed) (hnot : ¬ nonDefEq j) :
    ¬ PassesAcceptance j needed nonDefEq := by
  intro h
  exact hnot h.2

/-- **通过验收 ⟹ 前件必需**（取弱用）。 -/
theorem acceptance_implies_premises (j : Judgment L)
    (needed : AssumptionId → Prop) (nonDefEq : Judgment L → Prop)
    (h : PassesAcceptance j needed nonDefEq) : PremisesNecessary j.support needed := h.1

/-- **通过验收 ⟹ 结论有内容**。 -/
theorem acceptance_implies_content (j : Judgment L)
    (needed : AssumptionId → Prop) (nonDefEq : Judgment L → Prop)
    (h : PassesAcceptance j needed nonDefEq) : Contentful j nonDefEq := h.2

end NonVacuous

/-! ## §4 · 空来源的特殊地位 -/

section EmptySupport

variable {L : Type u}

/-- **空来源自动满足前件必要性**：没有前件，就没有「必需」要证。

    这解释了为什么构造性定理（`support = ∅`）在验收上最省事——
    不是豁免，而是条件空了（`∀ a ∈ [], ...` 恒真）。 -/
theorem empty_support_premises_necessary (needed : AssumptionId → Prop) :
    PremisesNecessary Support.empty needed := by
  intro a ha
  exact absurd ha (by simp [Support.empty])

/-- **但空来源不等于通过验收**：结论仍必须有内容。

    这是 D-001 双条件不可分裂的直接体现。 -/
theorem empty_support_still_needs_content (j : Judgment L)
    (needed : AssumptionId → Prop) (nonDefEq : Judgment L → Prop)
    (hnot : ¬ nonDefEq j) : ¬ PassesAcceptance j needed nonDefEq := by
  intro h
  exact hnot h.2

end EmptySupport

end FateV2.Meta
