import FateWorld.FateV2.Meta.Gate
import Mathlib.Tactic

/-!
  # Meta · Domain — 入域判据

  ## 迁移登记
  - 来源：新写（原为空壳占位）
  - 动作：C 重写
  - 对应环节：元层 · 入域判据
  - 依赖裁决：**D-001**（判据变更权）、**D-016**（纯 CIC）、**D-022**（反空泛）
  - 改动：从空壳补成实现。`09-总设计` §11 写「入域判据 7 条（A 组 3 + B 组 4）
          + N1–N4 不可判定」，但**从未定义清楚这 7 条具体是什么**。
          本模块按设计文档的意图给出可检查的形式，并明确区分
          **判据**与**不可判定标记**。
  - 状态：已编译

  ## 入域判据要回答什么

  > **一条来自真实世界的陈述，能不能进入形式化系统？**

  不能进的情况必须被识别出来，否则会把「无法形式化的东西」混进定理。

  ## 七条判据（A 组 3 + B 组 4）

  | 组 | # | 判据 | 含义 |
  |---|---|---|---|
  | **A** | A1 | 可陈述 | 能写成 `Formula` |
  | **A** | A2 | 有限可检查 | 不是「对一切可能世界」 |
  | **A** | A3 | 无自指 | 不引用自身真假 |
  | **B** | B1 | 数据可消融 | 数据能剥离（`D-005`） |
  | **B** | B2 | 来源可登记 | 前件能命名 |
  | **B** | B3 | 状态可判定 | 能定为四档之一 |
  | **B** | B4 | 非定义展开 | 结论有内容（`D-022`） |

  ## N1–N4 是「不可判定」标记，不是判据

  `09-总设计` §11 把它们和 7 条并列，但它们**性质不同**：
  N1–N4 标记的是**无法用算法判定的情形**。把它们当判据用会导致
  「以为检查过、其实永远返回 true」的假门禁——这正是 `T58` 记录的教训。
-/

namespace FateV2.Meta

open FateV2.Core

/-! ## §1 · 七条判据 -/

/-- **入域判据的 A 组（结构性）**。 -/
inductive CriterionA : Type where
  /-- A1 · 可陈述：能写成公式 -/
  | statable
  /-- A2 · 有限可检查：不量化「所有可能世界」 -/
  | finitelyCheckable
  /-- A3 · 无自指：不引用自身真假 -/
  | nonSelfReferential
  deriving DecidableEq, Repr

/-- **入域判据的 B 组（可操作性）**。 -/
inductive CriterionB : Type where
  /-- B1 · 数据可消融 -/
  | dissolvable
  /-- B2 · 来源可登记 -/
  | registrable
  /-- B3 · 状态可判定 -/
  | statableStatus
  /-- B4 · 非定义展开 -/
  | nonTrivial
  deriving DecidableEq, Repr

/-- **全部七条的标识**（A 组在前）。 -/
def allCriteria : List String :=
  [ "A1-statable", "A2-finitelyCheckable", "A3-nonSelfReferential"
  , "B1-dissolvable", "B2-registrable", "B3-statableStatus", "B4-nonTrivial" ]

/-- **恰好七条**。 -/
theorem seven_criteria : allCriteria.length = 7 := rfl

/-- **三 + 四 = 七**：分组与总数一致（用 `decide` 枚举验证）。 -/
theorem criteria_split :
    (([CriterionA.statable, CriterionA.finitelyCheckable, CriterionA.nonSelfReferential] : List CriterionA).length
      + ([CriterionB.dissolvable, CriterionB.registrable, CriterionB.statableStatus, CriterionB.nonTrivial] : List CriterionB).length) = 7 := by
  decide

/-! ## §2 · 不可判定标记（N1–N4） -/

/-- **N 组**：四条「不可判定」标记。

    ⚠ 它们**不是判据**——它们标记的是「这件事没有算法能判定」。
    把它们当判据用 = 写一个永远返回 true 的假门禁。 -/
inductive UndecidableMarker : Type where
  /-- N1 · 判定某陈述是否真的"关于真实世界" -/
  | genuinelyAboutWorld
  /-- N2 · 判定两个不同表述是否"同一个概念" -/
  | sameConcept
  /-- N3 · 判定某规则是否"有意义"（`D-012` 明确不设此判据） -/
  | meaningful
  /-- N4 · 判定某建模是否"忠实"（构造忠实性，只能登记不能判定） -/
  | faithful
  deriving DecidableEq, Repr

/-- **N 组恰好四条**：与七条判据分开计数。 -/
theorem four_markers :
    ([UndecidableMarker.genuinelyAboutWorld, UndecidableMarker.sameConcept,
      UndecidableMarker.meaningful, UndecidableMarker.faithful] : List UndecidableMarker).length = 4 := by
  decide

/-! ## §3 · 入域判定 -/

section Admit

/-- **一次入域检查的结果**。 -/
inductive AdmitResult where
  /-- 允许入域 -/
  | admit
  /-- 拒绝入域，附原因 -/
  | reject (reason : String)
  deriving Repr

/-- **入域判定**：给定七条判据的成立情况，决定是否允许。

    用 `List Bool` 表示各条的结果。
    **任何一条为 `false` 即拒绝**——这是「缺一不可」。 -/
def admit (checks : List Bool) : AdmitResult :=
  if checks.all id then .admit else .reject "至少一条判据未通过"

/-- **空检查表通过**（没有陈述就没有拒绝）。 -/
theorem admit_nil : admit [] = .admit := rfl

/-- **全通过 ⟹ admit**。 -/
theorem admit_all (cs : List Bool) (h : ∀ b ∈ cs, b = true) : admit cs = .admit := by
  unfold admit
  simp only [List.all_eq_true, id_eq]
  exact if_pos h

/-- **有一条失败 ⟹ reject**。 -/
theorem admit_not_all (cs : List Bool) (h : ¬ ∀ b ∈ cs, b = true) :
    ∃ r, admit cs = .reject r := by
  unfold admit
  simp only [List.all_eq_true, id_eq]
  exact ⟨_, if_neg h⟩

end Admit

/-! ## §4 · 与验收闸门的接线 -/

section WithGate

variable {L : Type u}

/-- **入域通过 ≠ 验收通过**：这是两个**独立**的检查。

    * 入域：这条陈述**能不能**进入系统
    * 验收：进了系统之后它**合不合格**（`Meta.Gate.PassesAcceptance`）

    ⟹ 一条陈述可以通过入域，但仍然验收失败（例如结论是定义展开）。 -/
theorem domain_does_not_imply_acceptance (j : Judgment L)
    (needed : AssumptionId → Prop) (nonDefEq : Judgment L → Prop)
    (hnot : ¬ nonDefEq j) : ¬ PassesAcceptance j needed nonDefEq := by
  intro h
  exact hnot h.2

/-- **两道检查的顺序**：先入域（能进来吗），再验收（合不合格）。 -/
def checkedAtAll (domainOk : Bool) (acceptOk : Bool) : Bool :=
  domainOk && acceptOk

/-- **入域失败 ⟹ 整体失败**（验收不再有意义）。 -/
theorem domain_gate_short_circuit (acc : Bool) :
    checkedAtAll false acc = false := rfl

/-- **两道都过才算过**。 -/
theorem both_checks_needed (acc : Bool) :
    checkedAtAll true acc = acc := rfl

end WithGate

end FateV2.Meta
