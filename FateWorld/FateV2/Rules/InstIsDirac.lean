import FateWorld.FateV2.Rules.LawRuleInstances
import FateWorld.FateV2.Rules.LawRuleToTraj

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/InstIsDirac.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-002 D-003
  - 改动：namespace/引用 ProperFit→FateV2.Rules（正文 6 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Rules
open FateV2.Model
open FateV2.Modeling

/-
===========================================================================
  实例层的 IsDirac 兑现（CHAIN-1 P0-F1）
===========================================================================

CHAIN-1 报告指出：`IsDirac` 的**构造性实例数 = 0**，而
`toDetFun` / `InstSpaceToLawRule.readDetFun` /
`lawDetToStepGen` 全部挂在这一个前件上 —— 于是整条链没有下游。

本模块给 `FateV2.Rules.LawRuleInstances` 的三个规则实例各补一条 `IsDirac`：

* `flipRule_isDirac`      —— **无条件**（有限状态、无待估参数）
* `linRegRule_isDirac`    —— 需数据兼容 `LinRegCorrect a D`
* `markovRule_isDirac`    —— 需数据兼容 `MarkovCorrect p D`

⚠ **为何后两条带前件（诚实说明，不是技术性规避）**：
`linRegRule` / `markovRule` 在数据**矛盾**时输出 `∅`（见
`linRegRule_of_wrong` / `markovRule_of_wrong`），而 `∅` 绝不是 `{δ_y}`。
故「无条件 `IsDirac`」在数学上**是假的**。前件 `LinRegCorrect a D`
是关于**数据 D 与参数 a** 的断言，与结论（规则值恰为 Dirac 单点集）
彼此独立 —— 见下文每个定理的「非循环性」注。

本模块**不修改**任何已有文件，只新增；`IsDirac` 的定义在
`FateV2.Rules/LawRuleToTraj.lean` §1，此处直接引用（G45：已 `#check`）。

零 `sorry` / `admit` / `axiom` / `?_` / `native_decide` / `maxHeartbeats`。
===========================================================================
-/


namespace FateV2.Rules

namespace LawRuleInstances

open MeasureTheory
open LawRule
open LawRuleToTraj

attribute [local instance] Classical.propDecidable

/-! ===========================================================================
   §1  实例 C：`flipRule` —— 无条件 Dirac
   =========================================================================== -/

/-- **实例 C 是 Dirac 档**（无条件）：见证函数就是 `flip2`。

`flipRule c i = {δ_{flip2 i}}` 是定义式，故 `IsDirac` 的见证 `fun _ i => flip2 i`
使等式成为 `rfl`。

**非循环性**：`flipRule` 的定义里**没有任何**一致性参数，
前件为空，结论 `IsDirac flipRule` 是实质断言（它说明 `flipRule` 落在
`DetFun.toLaw` 的像里，从而 `toDetFun flipRule h` 存在）。 -/
theorem flipRule_isDirac : IsDirac flipRule :=
  fun _ i => ⟨flip2 i, rfl⟩

/-- 契约检查：由上一条经 `LawRuleToTraj.IsDirac.isPoint` 应能重获 `flipRule_isPoint`
（两个文件中的同一命题，交叉验证 `IsDirac` 方向没接反）。 -/
theorem flipRule_isPoint_via_isDirac : IsPoint flipRule := flipRule_isDirac.isPoint

/-! ===========================================================================
   §2  实例 A：`linRegRule` —— 数据兼容时是 Dirac 档
   =========================================================================== -/

/-- **实例 A 在数据兼容时是 Dirac 档**：见证函数 `fun _ x => a * x`。

**非循环性**：前件 `LinRegCorrect a D` 只谈数据对 `(x, y) ∈ D` 满足 `a·x = y`，
**不**提及 `linRegRule` 的任何值形状；结论是「每点恰为 `{δ_{a·x}}`」。
二者独立 —— 若数据矛盾则结论为假（规则给出 `∅`），见 §4 的反向说明。 -/
theorem linRegRule_isDirac {a : ℝ} {D : List (ℝ × ℝ)} (h : LinRegCorrect a D) :
    IsDirac (linRegRule a D) :=
  fun _ x => ⟨a * x, linRegRule_of_correct h x⟩

/-- 契约检查：由上一条经 `IsDirac.isPoint` 重获 `linRegRule_isPoint`。 -/
theorem linRegRule_isPoint_via_isDirac {a : ℝ} {D : List (ℝ × ℝ)}
    (h : LinRegCorrect a D) : IsPoint (linRegRule a D) :=
  (linRegRule_isDirac h).isPoint

/-! ===========================================================================
   §3  实例 B：`markovRule` —— 数据兼容时是 Dirac 档
   =========================================================================== -/

/-- **实例 B 在数据兼容时是 Dirac 档**：见证函数 `fun _ i => i + 1`。

**非循环性**：前件 `MarkovCorrect p D` 只谈数据对满足 `q.2 = q.1 + 1`，
与结论「规则值恰为 `{δ_{i+1}}`」独立。 -/
theorem markovRule_isDirac {p : ℝ} {D : List (ℕ × ℕ)} (h : MarkovCorrect p D) :
    IsDirac (markovRule p D) :=
  fun _ i => ⟨i + 1, markovRule_of_correct h i⟩

/-- 契约检查：由上一条经 `IsDirac.isPoint` 重获 `markovRule_isPoint`。 -/
theorem markovRule_isPoint_via_isDirac {p : ℝ} {D : List (ℕ × ℕ)}
    (h : MarkovCorrect p D) : IsPoint (markovRule p D) :=
  (markovRule_isDirac h).isPoint

/-! ===========================================================================
   §4  下游兑现：`toDetFun` 在这三个实例上**真的**能抽出函数
   =========================================================================== -/

/-- **下游兑现（实例 C）**：`IsDirac` 档的抽出器 `toDetFun` 在 `flipRule` 上
给出一个函数，且满足 `toDetFun_spec`（规律被**精确复现**）。

这条把 CHAIN-1 说的「其余全部没有下游」**打通一格**：
`flipRule_isDirac` 是真前件，`toDetFun` 真能作用。 -/
theorem flipRule_toDetFun_spec (c : C₀.Carrier) (i : Fin 2) :
    flipRule c i
      = {Measure.dirac (toDetFun flipRule flipRule_isDirac c i)} :=
  toDetFun_spec flipRule flipRule_isDirac c i

/-- **下游兑现（实例 A）**。 -/
theorem linRegRule_toDetFun_spec {a : ℝ} {D : List (ℝ × ℝ)} (h : LinRegCorrect a D)
    (c : C₀.Carrier) (x : ℝ) :
    linRegRule a D c x
      = {Measure.dirac (toDetFun (linRegRule a D)
          (linRegRule_isDirac h) c x)} :=
  toDetFun_spec (linRegRule a D) (linRegRule_isDirac h) c x

/-- **下游兑现（实例 B）**。 -/
theorem markovRule_toDetFun_spec {p : ℝ} {D : List (ℕ × ℕ)} (h : MarkovCorrect p D)
    (c : C₀.Carrier) (i : ℕ) :
    markovRule p D c i
      = {Measure.dirac (toDetFun (markovRule p D)
          (markovRule_isDirac h) c i)} :=
  toDetFun_spec (markovRule p D) (markovRule_isDirac h) c i

/-! ===========================================================================
   §5  非平凡性见证：不兼容时 `IsDirac` **确实**失败
   =========================================================================== -/

/-- ⚠ **反向见证（实例 A）**：数据矛盾时 `linRegRule` **不是** Dirac 档。
end LawRuleInstances
这把 §2 的前件钉成**必要的**：`∅` 不等于任何 `{δ_y}`（因为 `δ_y univ = 1`，
而 `∅ univ = 0`）。故 §2 的 `h` 不可省，`linRegRule_isDirac` 不是空洞真理。 -/
theorem linRegRule_not_isDirac {a : ℝ} {D : List (ℝ × ℝ)}
    (h : ¬ LinRegCorrect a D) : ¬ IsDirac (linRegRule a D) := by
  intro hD
  obtain ⟨y, hy⟩ := hD PUnit.unit 0
  rw [linRegRule_of_wrong h] at hy
  have hmem : Measure.dirac y ∈ (∅ : Set (Measure ℝ)) := hy ▸ rfl
  exact Set.notMem_empty _ hmem

/-- ⚠ **反向见证（实例 B）**：数据矛盾时 `markovRule` **不是** Dirac 档。 -/
theorem markovRule_not_isDirac {p : ℝ} {D : List (ℕ × ℕ)}
    (h : ¬ MarkovCorrect p D) : ¬ IsDirac (markovRule p D) := by
  intro hD
  obtain ⟨y, hy⟩ := hD PUnit.unit 0
  rw [markovRule_of_wrong h] at hy
  have hmem : Measure.dirac y ∈ (∅ : Set (Measure ℕ)) := hy ▸ rfl
  exact Set.notMem_empty _ hmem

end LawRuleInstances

end FateV2.Rules
