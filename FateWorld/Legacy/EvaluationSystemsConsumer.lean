/-
命运理论 · **EvaluationSystems 的消费方**（EvaluationSystemsConsumer）
================================================================================
模块：`Fate.EvaluationSystemsConsumer`
依赖：`Fate.EvaluationSystems`
--------------------------------------------------------------------------------
(a) 本文件做什么
--------------------------------------------------------------------------------
`Fate/EvaluationSystems.lean` 提供了
  - `structure Dimensions`（8 个实值维度，纯参数）
  - `structure EvaluationSystem`（name / Eval / eval / le + 前序两律）
  - `EvaluationSystem.toRuleEvaluation`（structure → `RuleEval.RuleEvaluation` 实例的桥）
  - 三个具体体系 `popperSystem` / `occamSystem` / `lakatosSystem`
  - `systems_can_disagree`（费耶阿本德论纲，§5）
  - `MetaBetter` + `metaBetter_irrefl`（元评价，§6）

但**该文件内部**只证明了「各体系 `le` 方向相反」这一条**裸 `le` 形式**的结论，
**从未**把三个具体体系接到 `RuleEval.Better`（`Fate/RuleEvaluation.lean:155`）
这个**主链的严格序谓词**上，也**从未**用上 `lakatosSystem`
（该模块自己的文件头 §4 明说：「⚠ **本体系不被任何定理使用**」）。

⟹ 本文件补上这层**消费**，共 5 条定理（全部 `EXIT=0` 实测）：

1. `popperBetter_iff` —— 在 `popperSystem D` 上，主链 `Better` **恰等于**
   `D.falsifiability` 上的 `<`；即「波普尔体系」与 `RuleEval` 严格序**语义一致**；
2. `occamBetter_iff` —— 同上，对 `occamSystem D` / `D.simplicity`；
3. `lakatosBetter_iff` —— 同上，对 `lakatosSystem D`（`explanatory + novelty`）；
   **这是全项目第一条用到 `lakatosSystem` 的定理**；
4. `popperAndOccamBetter_conflict` —— 消费 `systems_can_disagree`：
   两条维度排序相反时，`popperSystem` 与 `occamSystem` 在**同一个 `Better`
   谓词**下给出**相反的严格判定**。这是把 §5 的裸 `le` 结论**升级**为
   「两体系的 `Better` 不能同时成立」；
5. `metaBetter_irrefl_popper` —— 消费 `metaBetter_irrefl`，把它实例化到
   具体体系 `popperSystem D` 上。

--------------------------------------------------------------------------------
(b) 前件是否把结论包进去？（本项目最高频问题 · 逐条自审）
--------------------------------------------------------------------------------
**1–3（`*Better_iff`）**：前件只有 `D : Dimensions C X Y` 与两条规则 `r₁ r₂`，
外加构造 `Rule` 必需的 `[MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]`。
结论是一个 **`↔`**，两边分别是
「桥注册后的 `RuleEval.Better`」与「`D.<维度>` 上的 `<`」。
⟹ 前件**不含** `<`、`≤`、`Better` 或任何数值假设。
⟹ 证明是**定义展开**（`eval := D.<维度>`，`le := (· ≤ ·)`，
再 `lt_iff_le_not_le`），故**不是同义反复**，但也**不深刻**：
它登记的是「桥接无隐藏的方向翻转」，不是关于科学的实质定理。

**4（`popperAndOccamBetter_conflict`）**：前件是**两条数值严格不等式**
（`D.falsifiability r₂ < D.falsifiability r₁` 与 `D.simplicity r₁ < D.simplicity r₂`），
结论是**两条 `RuleEval.Better`**（各自在不同体系下）。
`Better` 是 `le ∧ ¬ le` 的合取，**严格强于** `le`。
⟹ 前件是 `<`，结论含 `¬ ≤`，二者不同层级；**不是**同义反复。
⟹ **去掉前件结论可假**：取 `D.falsifiability` 常值（如 `dimsFirst` 的
`simplicity := fun _ => 0`），则 `Better` 的双边 `≤` 都成立，
`¬ le` 那一支失败，结论变假。

**5（`metaBetter_irrefl_popper`）**：前件只有 `D`。结论 `¬ MetaBetter S S` 由
`MetaBetter` 定义中的第 1 与第 3 合取支直接冲突得到；前件里**没有** `MetaBetter`。
⟹ **不是**同义反复（它很浅，这一点 `EvaluationSystems.lean` 自己已如实登记）。

--------------------------------------------------------------------------------
(c) 没做到什么（如实登记）
--------------------------------------------------------------------------------
1. **本文件不主张「8 个维度有科学定义」。** 它只把**已有的**三个体系接到
   `RuleEval.Better` 上；`Dimensions` 的 8 个字段仍是**任意实值函数**。
2. **`lakatosBetter_iff` 不背书 `explanatory + novelty` 的朴素加法。**
   `EvaluationSystems.lean` §4 已指出跨量纲相加「不可辩护」；
   本文件只登记「该体系作为值**能被消费**」，**不**声称这种加权科学上正确。
3. **不使用 `dimsFirst`。** `dimsFirst` 的 `simplicity` / `consistency` /
   `independence` / `novelty` / `robustness` 五个字段是 `fun _ => 0` 占位，
   在这些维度上 `RuleEval.Better` 恒假（双边 `≤` 都成立）。
   本文件因此**不**对 `dimsFirst` 声称任何排序结论；
   所有定理对**任意** `D : Dimensions C X Y` 成立。
4. **无 `sorry` / `admit` / `axiom` / `set_option`。**
-/

import FateWorld.Legacy.EvaluationSystems

namespace Fate

namespace EvaluationSystems

namespace Consumer

open RuleEval

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
  [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]

/-! ===========================================================================
  §1  ⭐⭐ **三个具体体系与主链 `RuleEval.Better` 的语义一致性**
  ===========================================================================

`EvaluationSystems.lean` §3 的 `toRuleEvaluation` 桥声称「任何体系都是
`RuleEvaluation` 实例」。本节把该桥**真的用上**：对三个具体体系逐一证明，
经桥注册后 `RuleEval.Better` **逐字**就是对应维度上的数学 `<`。
-/

/-- ⭐⭐ **【波普尔体系上的 `Better` 恰是 `falsifiability` 上的 `<`】**

**⚠ 前件与结论的关系**：前件只有 `D` 与 `r₁ r₂`，**不含** `<` / `≤` / `Better`。
结论是**定义展开**（`popperSystem` 的 `eval := D.falsifiability`、`le := (· ≤ ·)`，
再用 `lt_iff_le_not_le`）。⟹ **不是**同义反复，但**很浅**。

**⚠ 不声称**：本定理**不**说「可证伪性高 ⟹ 规则好」。它只说：
**若**你采用波普尔体系，**那么**主链的 `Better` 就是可证伪性的严格序。
价值判断不在本定理之内。 -/
theorem popperBetter_iff (D : Dimensions C X Y) (r₁ r₂ : Rule C X Y) :
    @RuleEval.Better C X Y _ _
      (EvaluationSystem.toRuleEvaluation (popperSystem D)) r₁ r₂
      ↔ D.falsifiability r₂ < D.falsifiability r₁ := by
  show D.falsifiability r₂ ≤ D.falsifiability r₁
        ∧ ¬ D.falsifiability r₁ ≤ D.falsifiability r₂
      ↔ D.falsifiability r₂ < D.falsifiability r₁
  exact (Std.LawfulOrderLT.lt_iff (D.falsifiability r₂) (D.falsifiability r₁)).symm

/-- ⭐⭐ **【奥卡姆体系上的 `Better` 恰是 `simplicity` 上的 `<`】**

**⚠ 前件与结论的关系**：同 `popperBetter_iff`，**不是**同义反复（定义展开）。
**⚠ 注意**：若 `D.simplicity` 是常值（如 `dimsFirst` 的 `fun _ => 0`），
则本定理的**右边恒假**，从而左边恒假——这正是「占位字段给出退化序」的
形式证据，本文件**不**借此声称任何真实排序。 -/
theorem occamBetter_iff (D : Dimensions C X Y) (r₁ r₂ : Rule C X Y) :
    @RuleEval.Better C X Y _ _
      (EvaluationSystem.toRuleEvaluation (occamSystem D)) r₁ r₂
      ↔ D.simplicity r₂ < D.simplicity r₁ := by
  show D.simplicity r₂ ≤ D.simplicity r₁
        ∧ ¬ D.simplicity r₁ ≤ D.simplicity r₂
      ↔ D.simplicity r₂ < D.simplicity r₁
  exact (Std.LawfulOrderLT.lt_iff (D.simplicity r₂) (D.simplicity r₁)).symm

/-- ⭐⭐ **【拉卡托斯体系上的 `Better` 恰是 `explanatory + novelty` 上的 `<`】**

**⟹ 这是全项目第一条真正消费 `lakatosSystem` 的定理**：
`EvaluationSystems.lean` §4 明说该体系「不被任何定理使用」，本条补上。

**⚠ 前件与结论的关系**：前件只有 `D` 与 `r₁ r₂`；结论是定义展开。
**不是**同义反复，但也**不深刻**。

**⚠ 不背书朴素加法**：`EvaluationSystems.lean` §4 已指出把两个可能不同量纲的量
直接相加「不可辩护」。本定理**只**登记「该体系作为 `EvaluationSystem` 值
能被 `RuleEval.Better` 消费」，**不**声称这种加权是科学上正确的评价。 -/
theorem lakatosBetter_iff (D : Dimensions C X Y) (r₁ r₂ : Rule C X Y) :
    @RuleEval.Better C X Y _ _
      (EvaluationSystem.toRuleEvaluation (lakatosSystem D)) r₁ r₂
      ↔ D.explanatory r₂ + D.novelty r₂ < D.explanatory r₁ + D.novelty r₁ := by
  show D.explanatory r₂ + D.novelty r₂ ≤ D.explanatory r₁ + D.novelty r₁
        ∧ ¬ D.explanatory r₁ + D.novelty r₁ ≤ D.explanatory r₂ + D.novelty r₂
      ↔ D.explanatory r₂ + D.novelty r₂ < D.explanatory r₁ + D.novelty r₁
  exact (Std.LawfulOrderLT.lt_iff
    (D.explanatory r₂ + D.novelty r₂) (D.explanatory r₁ + D.novelty r₁)).symm

/-! ===========================================================================
  §2  ⭐⭐⭐ **费耶阿本德论纲 → `Better` 层面的（升级版）分歧**
  ===========================================================================

`EvaluationSystems.lean` §5 的 `systems_can_disagree` 的结论是**裸 `le`**：
`(popperSystem D).le ... ∧ (occamSystem D).le ...`。
本节用 §1 的桥把它**升级**为 `RuleEval.Better`（严格序）层面的结论：
**两个体系在同一对规则上，各自判「更好」的方向相反**。
-/

/-- ⭐⭐⭐ **【两体系的 `Better` 判定必然相反（费耶阿本德论纲的严格序版）】**

若 `D.falsifiability` 与 `D.simplicity` 在同一对规则上**排序相反**
（`falsifiability r₂ < falsifiability r₁` 而 `simplicity r₁ < simplicity r₂`），
则：
- 波普尔体系判 `r₁` **严格优于** `r₂`（`Better r₁ r₂`）；
- 奥卡姆体系判 `r₂` **严格优于** `r₁`（`Better r₂ r₁`）。

**⟹ 这是「多种评价体系并存」在**主链严格序谓词**上的正面证据**：
不存在把两者统一的加权，使 `r₁` 与 `r₂` 同时最优。

**⚠ 前件与结论的关系（自审，防同义反复）**：
- 前件 `hf`、`hs` 是**两条 `<`**（数值假设）；
- 结论是两条 `RuleEval.Better`，即两条 `le ∧ ¬ le`。
- 结论的 `¬ le` 那一支**不来自**前件的任何否定式，而来自
  `lt_iff_le_not_le` 对 **同一个** `<` 的展开（`hf` 给出 `¬ snd ≤ fst`）。
- **去掉前件结论可假**：取 `D.falsifiability` 与 `D.simplicity` 均为常值，
  则两条 `Better` 都因 `¬ le` 失败而为假。
⟹ **不是**同义反复。
**⚠ 但也不强**：它没有独立于 `systems_can_disagree` 的新数学内容，
只是把后者从 `le` 提升到 `Better`（严格序），并**串联**了 §1 的桥。
`systems_can_disagree` 自身的浅度登记同样适用于本条。 -/
theorem popperAndOccamBetter_conflict (D : Dimensions C X Y) {r₁ r₂ : Rule C X Y}
    (hf : D.falsifiability r₂ < D.falsifiability r₁)
    (hs : D.simplicity r₁ < D.simplicity r₂) :
    @RuleEval.Better C X Y _ _
        (EvaluationSystem.toRuleEvaluation (popperSystem D)) r₁ r₂
      ∧ @RuleEval.Better C X Y _ _
        (EvaluationSystem.toRuleEvaluation (occamSystem D)) r₂ r₁ := by
  constructor
  · rw [popperBetter_iff]; exact hf
  · rw [occamBetter_iff]; exact hs

/-- ⭐⭐ **【两体系的 `Better` 不能同时指向同一方向】**

同一组前件下，波普尔判 `r₁` 优于 `r₂`，而奥卡姆**不**判 `r₁` 优于 `r₂`。
⟹ 两体系在**同一对规则、同一方向上**不能有一致的「更好」判定。

**⚠ 前件与结论的关系（自审，防同义反复）**：
结论的第一个合取支是 `Better r₁ r₂`（波普尔），来自 `hf`；
第二个合取支是 `¬ Better r₁ r₂`（奥卡姆），展开为
`¬ (simplicity r₂ ≤ simplicity r₁ ∧ ¬ simplicity r₁ ≤ simplicity r₂)`，
由 `hs : simplicity r₁ < simplicity r₂` 给出 `simplicity r₁ ≤ simplicity r₂`，
从而 `¬¬ ...` 那一支被破坏。
**⚠ 诚实说明**：第二个合取支**只用了 `hs` 单调方向**，
因此本条的实质就是「奥卡姆方向与波普尔相反」——
它与 `popperAndOccamBetter_conflict` **同源**，不是独立的新定理。
列在此处是因为它是「**不可调和**」这一说法的直接形式。 -/
theorem popperBetter_occamNotBetter (D : Dimensions C X Y) {r₁ r₂ : Rule C X Y}
    (hf : D.falsifiability r₂ < D.falsifiability r₁)
    (hs : D.simplicity r₁ < D.simplicity r₂) :
    @RuleEval.Better C X Y _ _
        (EvaluationSystem.toRuleEvaluation (popperSystem D)) r₁ r₂
      ∧ ¬ @RuleEval.Better C X Y _ _
        (EvaluationSystem.toRuleEvaluation (occamSystem D)) r₁ r₂ := by
  refine ⟨?_, ?_⟩
  · rw [popperBetter_iff]; exact hf
  · rw [occamBetter_iff]
    exact not_lt.mpr (le_of_lt hs)

/-! ===========================================================================
  §3  ⭐ **元评价的非自反性在具体体系上的实例化**
  =========================================================================== -/

/-- ⭐ **【波普尔体系不比自身更细】**

`EvaluationSystems.lean` §6 的 `metaBetter_irrefl` 对**任意** `EvaluationSystem`
成立。本条把它实例化到**具体**体系 `popperSystem D` 上，
确认 §1 用到的三个体系**不是** `MetaBetter` 的平凡自反点。

**⚠ 前件与结论的关系**：前件只有 `D`，**不含** `MetaBetter`。
结论由 `metaBetter_irrefl` 直接给出，**不是**同义反复。
**⚠ 很浅**：与 `metaBetter_irrefl` 同浅（后者自己已登记「证明仅 `rintro` + `exact h3 h1`」）。 -/
theorem metaBetter_irrefl_popper (D : Dimensions C X Y) :
    ¬ MetaBetter (popperSystem D) (popperSystem D) :=
  metaBetter_irrefl (popperSystem D)

/-- ⭐ **【奥卡姆体系不比自身更细】**（同上，实例化） -/
theorem metaBetter_irrefl_occam (D : Dimensions C X Y) :
    ¬ MetaBetter (occamSystem D) (occamSystem D) :=
  metaBetter_irrefl (occamSystem D)

end Consumer

end EvaluationSystems

end Fate

/-! ### §4 公理审计（`#print axioms`） -/
#print axioms Fate.EvaluationSystems.Consumer.popperBetter_iff
#print axioms Fate.EvaluationSystems.Consumer.occamBetter_iff
#print axioms Fate.EvaluationSystems.Consumer.lakatosBetter_iff
#print axioms Fate.EvaluationSystems.Consumer.popperAndOccamBetter_conflict
#print axioms Fate.EvaluationSystems.Consumer.popperBetter_occamNotBetter
#print axioms Fate.EvaluationSystems.Consumer.metaBetter_irrefl_popper
#print axioms Fate.EvaluationSystems.Consumer.metaBetter_irrefl_occam
