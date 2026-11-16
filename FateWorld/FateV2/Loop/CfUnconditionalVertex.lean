/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.CfUnconditionalVertex
来源：**`Fate/WiringCounterfactual.lean` 的归档内容回收**（P-006 分诊判定 ARCHIVE）

---------------------------------------------------------------------------
## 0 为什么有这个文件（诚实登记）
---------------------------------------------------------------------------

`Fate/WiringCounterfactual.lean` 经 P-006 分诊判定为 **ARCHIVE**：
81 个 error 中 38 处是上游改名 drift，另有 22 处 `Invalid field`
（`WorldModel.cf` 这个字段在当前 `WorldModel` 结构里**已不存在**）。
整文件按当前 API 重校的成本极高，故**不修**、**归档**。

但分诊报告 §6「需要回收的孤岛内容」明确指出：
该文件中 **`not_any_worldModel_computes_cf`** 是**不可替代的判决性内容** ——
它机器证明了「任意 `WorldModel` 都**无条件**能算反事实」是**假命题**，
并建议「把这一条单独抄成 30 行小模块保留」。

**本文件就是那个小模块。** 它**不**复现 `WiringCounterfactual` 的接线条目
（那些依赖已被删除的 `WorldModel.cf` 字段），只保留并加固**否定命题**这一条。

---------------------------------------------------------------------------
## 1 内容（一句话）
---------------------------------------------------------------------------

`cfWithAbduction` 的签名**硬性要求** `[Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]`
（见 `Fate/T43Abduction.lean` §1 的 `variable` 行，逐原子求和所需）。
而 `WorldModel.frame.X` 是 `StateSpace`，其 `Carrier` 是**任意类型**，
`WorldModel` 的字段里**没有任何有限性信息**（`Fate/WorldModel.lean` §5：
`frame`/`ctx`/`instX`/`state`/`rules`/`simulator`/`selector`/`state_consistent`，
无一条给出 `Fintype`）。

**⟹「任意 `WorldModel` 都能算反事实」在类型层就是假的** —— 本文件给出可编译的否定命题，
并配一个显式的反例世界模型（状态空间 `ℝ`）。

---------------------------------------------------------------------------
## 2 ⚠⚠ 反同义反复审查（纪律 7，动笔前做的）
---------------------------------------------------------------------------

| 定理 | 前件是否已含结论？ | 说明 |
|---|---|---|
| `real_not_fintype` | ❌ 否 | 前件**空**；结论 = `¬ Nonempty (Fintype ℝ)`。证明走「`Fintype` ⟹ 可数 ⟹ 与 `ℝ` 不可数矛盾」，**不是**假设 |
| `realWorldModel_carrier` | ❌ 否 | 前件空；`rfl` 但陈述的是**定义等式**，若有人偷改 `discSpace`/`mkWorldModel` 的载体，它立刻失败 |
| `realWorldModel_not_finite` | ❌ 否 | 前件 = `FiniteCarrier ℝ`（假设存在）；结论 = `False`。**归谬**，结论与前件相反 |
| `not_any_worldModel_computes_cf` | ❌ 否 | 前件**空**；结论是**全称命题的否定** `¬ ∀ W, …`。靠 `realWorldModel` 这一个具体反例兑现 —— **不是**把结论写进前件 |
| `missing_ingredient_is_finiteness` | ❌ 否 | 前件空；结论是**合取**：(有限实例)**存在** ∧ (无限实例)**不存在**有限性。两侧方向相反、都非平凡 |

**同义反复自检的关键处**：`not_any_worldModel_computes_cf` 的前件是**空**的
（`¬ ∀ W : WorldModel, Nonempty (FiniteCarrier W.frame.X.Carrier)` 没有 `→` 左侧的额外假设），
结论是**否定**一个全称断言。它**不可能**是「前件把结论包进去」：
被否定的那个全称断言只有被**实际反驳**（给出 `ℝ` 反例）才能否证。

---------------------------------------------------------------------------
## 3 依赖方向（「接上」的机检）
---------------------------------------------------------------------------

* `import FateV2.Predict.WorldModel` ⟹ `WorldModel`/`Frame`/`StateSpace` 的**当前**字段口径；
* `import Fate.T43Abduction` ⟹ `cfWithAbduction` 及其 `[Fintype]`/`[DecidableEq]` 前件的**来源**。

**注意**：本文件**不**定义 `WorldModel.cf`（该字段在当前 `WorldModel` 中不存在，
正是 `WiringCounterfactual` 的 22 处 `Invalid field` 的来源）。
本文件只主张**否定**侧：无条件版本不可写。

---------------------------------------------------------------------------
## 4 本文件**不**做的事（如实登记，避免虚假声称）
---------------------------------------------------------------------------

* ❌ **不**修复 `Fate/WiringCounterfactual.lean`（按分诊判定 ARCHIVE，不改已有模块）；
* ❌ **不**给出「补上有限性之后反事实可算」的接线定理
      （那需要 `WorldModel.cf`，属归档内容，本文件刻意不做）；
* ❌ **不**含任何 `sorry` / `admit` / `axiom`（全文可 `grep -nE "\bsorry\b|\badmit\b|\baxiom\b"` 自查为 0）。
-/

import FateWorld.FateV2.Predict.WorldModel
import FateWorld.FateV2.Predict.T43Abduction
set_option autoImplicit false

namespace FateV2.Loop

open FateV2.Model
open FateV2.Modeling
open FateV2.Predict
namespace CfUnconditionalVertex

/-!
  # Loop · CfUnconditionalVertex

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CfUnconditionalVertex.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：WorldModel, T43Abduction
  - 补充 open 域：FateV2.Model, FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  载体工具：离散 `StateSpace` 与「有限性」打包

  `StateSpace` 只要求「拓扑 + 可测 + Borel 相容」（`Fate/Basic.lean` §1），
  **不**要求有限；反之，**任何类型**都能配上离散结构与 `StateSpace`。
  这一节把后者做成可复用的定义。
  =========================================================================== -/

section CarrierTools

/-- **任意类型上的离散 `StateSpace`**：拓扑 `⊤`、可测 `⊤`、Borel 相容 `le_top`。

**⟹ 「有限状态」不是 `StateSpace` 的障碍** —— 这正是 §2 阻塞的**反面**：
`ℝ` 造不出 `Fintype`，但任意类型都能造 `StateSpace`。 -/
def discSpace (α : Type) : StateSpace where
  Carrier := α
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- 离散空间的载体**定义上**就是原类型（`rfl` 级事实，但作为定理登记以防偷改）。 -/
theorem discSpace_carrier (α : Type) : (discSpace α).Carrier = α := rfl

/-- **「状态载体有限」= `Fintype` + `DecidableEq` 打包**（缺的那一项，做成显式结构）。

**⚠ 为什么是 `Type` 而非 `Prop`**：`Fintype`/`DecidableEq` 住在 `Type` 层，
Lean **不允许** `Prop` 值结构存放它们（字段必须是证明）。故本结构是 `Type` 值。 -/
structure FiniteCarrier (α : Type) where
  /-- 有限性 -/
  fintype : Fintype α
  /-- 可判定相等（逐原子求和需要） -/
  decEq : DecidableEq α

/-- **`WorldModel` 缺什么**：

$$\texttt{FiniteState}\ W \iff \big(\mathrm{Fintype}\ W.\texttt{frame.X.Carrier}
  \wedge\ \mathrm{DecidableEq}\ W.\texttt{frame.X.Carrier}\big).$$

**⚠ 这是 `Type` 值（`abbrev`），不是 `Prop`**：故「有限」与「不有限」的陈述
一律用 `Nonempty (FiniteState W)` / `¬ Nonempty (FiniteState W)` 书写，
不可写成 `¬ FiniteState W`（后者类型错误）。 -/
abbrev FiniteState (W : WorldModel) : Type := FiniteCarrier W.frame.X.Carrier

/-- **`ℝ` 不有限**：不存在 `Fintype ℝ`。

**证明**：`Fintype ℝ` ⟹ `ℝ` 可数（`Set.to_countable`）⟹ 与 `Set.not_countable_univ`
（`ℝ` 不可数）矛盾。 -/
theorem real_not_fintype : ¬ Nonempty (Fintype ℝ) := by
  rintro ⟨hfin⟩
  haveI := hfin
  have hct : (Set.univ : Set ℝ).Countable := Set.to_countable _
  exact Set.not_countable_univ hct

end CarrierTools

/-! ===========================================================================
  §2  ⭐⭐⭐ 硬阻塞：可编译的**否定命题**

  「给出一个对**任意** `WorldModel` 生效的反事实算子」**不存在**。
  这不是「还没写」，而是 `ℝ` 不可数 ⟹ `Fintype ℝ` 不存在 ⟹
  `cfWithAbduction` 的**逐原子求和根本写不出来**（其 `variable` 行要求 `[Fintype X]`）。
  =========================================================================== -/

section HardBlocker

/-
  把各空间结构体的 `topo`/`meas` **字段**提到类型类搜索位置。

  **为什么需要**：`Frame.X` 等字段的类型是 `StateSpace`，其 `Carrier` 不是裸类型变量，
  故 `WorldRules`/`Selector` 处的 `[MeasurableSpace X.Carrier]` **无法自动合成** ——
  必须显式把这些字段登记为（局部）实例。
-/
attribute [local instance] StateSpace.topo StateSpace.meas ThetaSpace.topo ThetaSpace.meas
  InputSpace.topo InputSpace.meas ActionSpace.topo ActionSpace.meas NoiseSpace.meas

/-- **在给定状态空间上搭一个最小 `WorldModel`**（四个部分逐一就位）。

* 参数/输入/动作/噪声空间全部取单点 `PUnit`（最小化，不影响状态空间的任意性）；
* 状态块写成 `WorldState.mk S x₀ ⟨x₀,false⟩`（**定义等式**，使 `state_consistent := rfl` 成立）；
* 规则核取 `dirac`，选择器返同一核、评值恒 `0`（最简，但结构完整）。

**⚠ 关键点**：本定义对**任意** `S : StateSpace` 成立，**完全不需要** `Fintype S.Carrier`。
这正是 §2 否定命题的来源。 -/
noncomputable def mkWorldModel (S : StateSpace) (x₀ : S.Carrier) : WorldModel where
  frame :=
    { Θ := { Carrier := PUnit }
      X := S
      U := { Carrier := PUnit }
      Act := { Carrier := PUnit }
      Ν := { Carrier := PUnit } }
  ctx := { Carrier := PUnit }
  instX := S.meas
  state := WorldState.mk S x₀ ⟨x₀, false⟩
  rules :=
    WorldRules.mk
      { Rule.mk (fun _ x => MeasureTheory.Measure.dirac x) }
      ⟨Rule.mk (fun _ x => MeasureTheory.Measure.dirac x), rfl⟩
  simulator := WorldSimulator.mk (fun x _ _ _ _ => x) 1
  selector := Selector.mk (fun _ _ _ => (Rule.mk (fun _ x => MeasureTheory.Measure.dirac x), 0))
    (fun _ _ _ => 0)
  state_consistent := rfl

/-- **`realWorldModel`**：⚠ 状态空间 `ℝ`。**§2 的反例**。 -/
noncomputable def realWorldModel : WorldModel := mkWorldModel (discSpace ℝ) (0 : ℝ)

/-- **`realWorldModel` 的载体定义上等于 `ℝ`**（`rfl` 级，登记为定理）。 -/
theorem realWorldModel_carrier : realWorldModel.frame.X.Carrier = ℝ := rfl

/-- ⭐⭐⭐ **`realWorldModel_not_finite`**：`realWorldModel` 的状态载体**不**有限。

**证明**：其载体**定义上等于** `ℝ`（`realWorldModel_carrier`），
而 `ℝ` 上不存在 `Fintype`（`real_not_fintype`）。 -/
theorem realWorldModel_not_finite : ¬ Nonempty (FiniteState realWorldModel) := by
  rintro ⟨h⟩
  have hfin : Nonempty (Fintype (realWorldModel.frame.X.Carrier)) := ⟨h.fintype⟩
  rw [realWorldModel_carrier] at hfin
  exact real_not_fintype hfin

/-- ⭐⭐⭐ **`not_any_worldModel_computes_cf`（核心否定命题，从归档模块回收）**：

$$\neg\ \forall W : \texttt{WorldModel},\ \mathrm{FiniteState}\ W.$$

**字面读法**：「对一切 `WorldModel`，状态载体都有限（从而反事实可算）」是**假**的。

**为什么这是「为什么不能」**：`cfWithAbduction`（`Fate/T43Abduction.lean` §1）
的签名硬性要求 `[Fintype X]`、`[DecidableEq X]`（`X` 是状态载体）——
其求和 `∑ u, …` 需要有限类型。`WorldModel` **不提供**这一条，
故 `realWorldModel`（`X.Carrier = ℝ`）上该算子**在类型层不可书写**。

**反同义反复**：前件为**空**（本定理无 `→` 左侧的额外假设），
结论是**全称命题的否定**，由 `realWorldModel` 这一个具体反例兑现。 -/
theorem not_any_worldModel_computes_cf :
    ¬ ∀ W : WorldModel, Nonempty (FiniteState W) := by
  intro h
  exact realWorldModel_not_finite (h realWorldModel)

/-- ⭐⭐ **`missing_ingredient_is_finiteness`（缺什么，精确版）**：

**同一个** `WorldModel` 类型里，既有**状态载体有限**的实例（`PUnit` / `Bool` 等可造），
也有**状态载体不有限**的实例（`realWorldModel`，载体 `ℝ`）。

⟹ 阻塞**不在** `WorldModel` 这个类型本身，而**在**它**缺一个有限性字段**。
（若 `WorldModel` 自带 `Fintype` 字段，`realWorldModel` 就不可构造 ——
但那会**排除** `ℝ` 值状态，即排除本项目**全部**连续情形，代价不可接受；
故正确做法是「有限性作显式前件」，而**不是**「把结论写进类型或前件」。） -/
theorem missing_ingredient_is_finiteness :
    (Nonempty (FiniteState (mkWorldModel (discSpace PUnit) PUnit.unit)))
      ∧ ¬ (Nonempty (FiniteState realWorldModel)) := by
  refine ⟨⟨⟨PUnit.fintype, (inferInstance : DecidableEq PUnit)⟩⟩, ?_⟩
  exact realWorldModel_not_finite

end HardBlocker

end CfUnconditionalVertex

end FateV2.Loop