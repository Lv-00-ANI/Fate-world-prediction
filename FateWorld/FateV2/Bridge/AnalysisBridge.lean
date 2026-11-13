import FateWorld.FateV2.Core.Judgment
import FateWorld.FateV2.Core.Quote
import FateWorld.FateV2.Classical.Assumptions
import FateWorld.FateV2.Classical.Analysis

/-!
  # Bridge · AnalysisBridge

  ## 迁移登记
  - 来源：新写
  - 动作：C 重写（`FateV2/Bridge/AnalysisBridge.lean` 原为骨架占位）
  - 对应环节：实数 / 测度结论进入 IR 的**登记通道**
  - 依赖裁决：**D-016**（三条公理降为基础假设）、**D-018**（实数后补）、**D-022**
  - 状态：已编译未验证

  ## 职责（D-016 代价 1 的落点）

  D-016 明说：`ℝ` 与 `Measure` **在纯 CIC 下不可用**（Cauchy 完备化用 `Quotient`，
  序完备性用 `Classical.choice`）。⟹ 凡用它们的定理，必须：

  1. 放在 `FateV2/Classical/` 之下（**不在 `Core/`**）；
  2. `support.assumptions` 里**一字不差**地登记三条公理（用哪条记哪条）；
  3. `#print axioms` 与登记一致（G5 账实相符）。

  本文件提供**通道**：一个 `AnalysisClaim`（实数/测度层的结论）
  落成 `Judgment`，其 `support` 由**它实际依赖的假设**决定；
  并给出**至少一个可证性质**（见 `analysis_support_has_choice`）。

  ## ⚠ 本文件**不**包含任何 ℝ / Measure 的具体结论

  那是 `FateV2/Error/`、`FateV2/Loop/` 等层的活（它们已经存在且已在账本里）。
  本文件只保证「**结论怎么进来**」这一条通道的形状与性质——不多做，
  以免与其它层的登记重复（D-022：不做无内容的包装）。
-/

namespace FateV2.Bridge

open FateV2.Core
open FateV2.Classical

universe u

/-! ## 分析层结论的登记形态 -/

/-- **一条分析层结论**：它用了哪些基础假设。

    `name` 人类可读；`uses` 是**实际用到的**假设（由 `#print axioms` 决定，
    人工核对后填入 `_support_registry_D.csv`）。 -/
structure AnalysisClaim where
  /-- 结论名 -/
  name : String
  /-- 它**实际用到**的基础假设 -/
  uses : List AssumptionId

/-- **实数层结论**（默认登记 `Classical.choice` + `propext`）：
    `ℝ` 的存在性依赖 `Classical.choice`（序完备性）与 `Quotient`（Cauchy 完备化）。 -/
def realClaim (name : String) : AnalysisClaim :=
  ⟨name, [axPropext, axChoice, axQuotSound]⟩

/-- **测度层结论**（同上，另需 σ-代数与 Carathéodory 扩张，仍落在这三条内）。 -/
def measureClaim (name : String) : AnalysisClaim :=
  ⟨name, [axPropext, axChoice, axQuotSound]⟩

/-- **纯 `ℚ` 结论**（D-016 表：`Finset`/`List`/`ℚ` **不依赖**三条公理）。 -/
def rationalClaim (name : String) : AnalysisClaim :=
  ⟨name, []⟩

/-! ## 落成 `Judgment` -/

/-- **把一条分析层结论接成 `Judgment`**。 -/
def claimToJudgment (c : AnalysisClaim) (concl : Formula u) : Judgment u :=
  ⟨.top, concl, ⟨c.uses⟩, .proven⟩

/-- **【账实相符】**：落成后 `support` 就是登记表。 -/
theorem claimToJudgment_support (c : AnalysisClaim) (concl : Formula u) :
    (claimToJudgment c concl).support.assumptions = c.uses := rfl

/-! ## 至少一个**可证**性质（任务书要求）

  下面这些不是「接口说明」，而是**真的定理**：
  它们把 D-016 的两级分层（构造性核 / 经典外壳）在**账本层**上钉住。 -/

/-- **【性质 1 · 实数层结论必然带 `Classical.choice`】**

    `ℝ` 序完备性依赖 `Classical.choice`（D-016 §代价 1 的原话）。
    本定理说：`realClaim` 落成后的 `support` **含** `axChoice`。

    比定义多说了什么：它把「`realClaim` 的定义里写了三条」
    变成「`support` 里确实有 `Classical.choice`」这一条**成员性**事实——
    不是 `rfl`，是 `List.mem` 的构造。 -/
theorem real_support_has_choice (name : String) (concl : Formula u) :
    axChoice ∈ (claimToJudgment (realClaim name) concl).support.assumptions := by
  show axChoice ∈ ([axPropext, axChoice, axQuotSound] : List AssumptionId)
  exact List.mem_cons_of_mem _ List.mem_cons_self

/-- **【性质 2 · 纯 `ℚ` 结论的 support 为空】**（D-016：`ℚ` 不依赖三条公理）。

    这是**构造性核**与**经典外壳**的分界线：`rationalClaim` 在核内，
    `realClaim`/`measureClaim` 在外壳。 -/
theorem rational_support_empty (name : String) (concl : Formula u) :
    (claimToJudgment (rationalClaim name) concl).support.assumptions = [] := rfl

/-- **【性质 3 · 分析层结论被经典外壳覆盖】**

    `realClaim` / `measureClaim` 落成的 `support` 被 `Classical.classical` 覆盖
    （D-016 §4.2 的 `IsClassicalOnly` 在分析层的形态）。 -/
theorem real_support_covered (name : String) (concl : Formula u) :
    Shell.covers classical (claimToJudgment (realClaim name) concl).support := by
  exact Shell.covers_classical_of_subset _ (by
    intro a ha
    show a = axPropext ∨ a = axChoice ∨ a = axQuotSound
    exact List.mem_cons.mp ha |>.elim (fun h => Or.inl h)
      (fun h => List.mem_cons.mp h |>.elim (fun h2 => Or.inr (Or.inl h2))
        (fun h2 => List.mem_cons.mp h2 |>.elim (fun h3 => Or.inr (Or.inr h3))
          (fun h3 => absurd h3 (fun x => nomatch x)))))

/-- **【性质 4 · 纯外壳覆盖不了非空 support】**：若 `uses` 非空，
    则 `pure` 外壳**不**覆盖它——构造性外壳容不下任何假设。 -/
theorem pure_not_covers_of_nonempty (name : String) (concl : Formula u) :
    ¬ Shell.covers pure (claimToJudgment (realClaim name) concl).support := by
  intro h
  have hnil := (Shell.covers_pure_iff _).mp h
  rw [claimToJudgment_support] at hnil
  exact absurd hnil (fun he => by
    have hmem : axChoice ∈ ([] : List AssumptionId) := by
      rw [← he]; exact real_support_has_choice name concl
    nomatch hmem)

/-! ## 尾项（登记不隐藏）

  | # | 项 | 说明 |
  |---|---|---|
  | 1 | ℝ / Measure 的**具体**结论 | 本文件只做通道；具体结论在 `FateV2/Error/`、`FateV2/Loop/`（已存在，已在账本） |
  | 2 | `uses` 与 `#print axioms` 的**自动**对齐 | 门禁脚本 `_audit_support.py` 的活；核内能做的「字段一致」已证 |
  | 3 | `AnalysisClaim` 的实际命题内容 | 本文件只存 `name` + `uses`，不存命题（命题在 Lean 层已证，重复存会与 `_support_registry` 打架） |
-/

end FateV2.Bridge
