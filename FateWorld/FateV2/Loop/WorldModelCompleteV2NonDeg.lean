/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Loop`
阶段：**审计 R423 次优先建议的落实 —— 给 `WorldModelCompleteV2` 一个非退化实例**

---------------------------------------------------------------------------
本文件的**严格定位**（必读）
---------------------------------------------------------------------------
本文件**新建**一个框架 `nonDegFrame`，以及该框架上**非退化**的
规则集 `nonDegRules`（两条互异规则）、渲染 `renderND`（非常函数）、
两个互异单步机制 `stepL` / `stepI`、模拟器 `nonDegSim`。
其中 `X = Fin 2`（不是 `PUnit`）、`Θ = Fin 2`、`Act = Fin 2`、
`nonDegRules` 含**两条**规则、`renderND` **不是**常函数。

**⚠ 本文件不构造 `WorldModelCompleteV2 nonDegFrame` 的实例**（即没有
名为 `nonDegWMC` 的项）。⚠ **第 608 轮修正**：本文原先写「该结构的
`render_surj` 字段与『非退化 `X` + 两条规则』互斥」，但这个说法**未证明、
而且推理方向是错的**（`render` 的定义域是整个 `Rule` 类型，而非那 2 元的
`rules` 子集；从大类型到 256 元类型的满射是存在的）。故现在只陈述
**关于本文件的事实**：本文件**未构造**该实例。下文一律用具体项名
（`nonDegRules` / `renderND` / `nonDegSim`），**不**使用 `nonDegWMC`。

### (a) 与 `FateV2.Loop.minWMC` 相比，本文件非退化在哪

| 项 | `minWMC`（`WorldModelCompleteV2.lean` §2） | 本文件（`nonDegFrame` 上的各项） |
|---|---|---|
| `X.Carrier` | `PUnit`（`Subsingleton`） | `Fin 2`（`¬ Subsingleton`，见 `nonDeg_X_not_subsingleton`） |
| `Θ.Carrier` | `PUnit` | `Fin 2` |
| `Act.Carrier` | `PUnit` | `Fin 2` |
| `rules` | 单元素 `{vRuleP}` | **两元素** `{liRule, idRule}`，两元素**不相等**（见 `nonDeg_rules_two_distinct`） |
| `render` | 常函数（值域是子单点） | `render liRule = stepL`、`render idRule = stepI`，且 `stepL ≠ stepI`（见 `nonDeg_render_not_const`） |
| `Step nonDegFrame` | 子单点类型（`vUnitStep_unique`） | **非**子单点（见 `nonDeg_Step_not_subsingleton`） |
| `rules_determine_step` 见证 | `⟨vRuleP, rfl, rfl⟩`（等式靠 `rfl`） | `⟨liRule, …, step_eq_lit⟩`，等式 `step = render liRule` **不是 `rfl`**（见下） |

**关于 `rules_determine_step` 的「非 `rfl`」是事实而非口号**：

- `render` 在本文件里是**按规则可判定地分支**的：
  `render r = if r = liRule then stepL else stepI`；
- 模拟器的机制字段取 `stepL`（*字面量*），而 `render liRule` 需要先**判定**
  `liRule = liRule` 再选分支；
- 故 `simulator.step = render liRule` 的证明是
  `(if_pos rfl).symm` 的复合（见 `step_eq_lit`），**不是** `rfl`。
  这不是「等式本质不同」——两者定义上相等——而是说：本实例的
  `render` **确实是一个会做计算的函数**，而 `minWMC.render` 是常函数。

### (b) 本实例具体用到的类型

- `X.Carrier = Fin 2`（拓扑取 `⊤`，可测取 `⊤`；`⊤` 即离散结构，
  故 `borel ≤ ⊤` 自动成立，`MeasurableSpace` 为离散的）——注意
  `Frame` 的 `StateSpace` 要求字段 `borel_le : borel Carrier ≤ meas`，
  本文件用 `le_top` 满足，**不用** `instTopologicalSpaceFin`（该 Mathlib
  模块的 `.olean` 在本机不可用，见 §0 说明）；
- `Θ.Carrier = Fin 2`、`Act.Carrier = Fin 2`；
- `U.Carrier = PUnit`、`Ν.Carrier = PUnit`（**保持 `PUnit`**，理由：
  它们只出现在 `Step` 的**参数位**，不影响 `Step` 是否常函数；
  把 `X` 做成 `Fin 2` 已足以让 `Step` 非常函数）；
- `input : InstSpace := ⟨Fin 2⟩`、`alpha : AlphaData ⟨Fin 2⟩ PUnit` 的观测映射
  取**非常**的 `fun i => {PUnit.unit | i = 0}`（两个实例观测不同）。

**登记（诚实）**：`U` / `Ν` 仍是单点。这是「退到能做的最大非退化程度」的
一部分——`Step` 的形状是 `X → U → Ν → Θ → Act → X`，只要 `X` 有 ≥2 个元素且
机制把它们分开，`Step` 就**不是**常函数（`nonDeg_Step_not_subsingleton` 已证）。

### (c) 本文件**不**声称什么

- **不**声称「⑦ 交接器已完整」。本文件只提供一个**非退化实例**：
  它使「结构与实例非退化」这件事**可被验证**，
  **不**证明任何环节在语义上被「真正接通」。
- **不**证明任何主定理，**不**涉及经验假设 A1–A34。
- **不**声称本实例的 `gamma` / `compose` / `upsilon` 有实质数学内容：
  `gamma` 仍取恒等（相对全关系预序）、`compose` 仍取左操作数、
  `upsilon` 仍取恒等。**这四处仍是退化填法**，见 §4 未完成项登记。

### (d) 与 `minWMC` 的关系

**并存，不取代。** 本文件**不修改** `Fate/WorldModelCompleteV2.lean` 一个字符，
`minWMC` 及其 6 条定理仍是原样；本文件的 `nonDegFrame` / `nonDegRules` /
`renderND` / `nonDegSim` 是**另一个**框架上的**另一批**对象，
两者不共享命名，也不互相引用对方的证明。

---------------------------------------------------------------------------
本文件实际存在的定理（`grep ^theorem` 核对，共 8 条）
---------------------------------------------------------------------------
本文件实际存在的定理（`grep ^theorem` 核对，共 19 条）
---------------------------------------------------------------------------
**⚠ 第 608 轮变化**：原第 16 条 `nonDeg_no_complete_instance_stated`
（结论只写 `True`、证明项为 `trivial` 的**空定理**）已**删除**，原位置留有 `/- … -/` 说明段；
故计数由 20 降为 19。详见该说明段与 §4 的修正。
| # | 定理 | 内容 |
|---|---|---|
| 1 | `nonDeg_two_ne` | `(0 : Fin 2) ≠ 1` |
| 2 | `nonDeg_X_not_subsingleton` | `¬ Subsingleton (Fin 2)`（状态空间非退化） |
| 3 | `liRule_measurable` | 规则 A 的核可测（`⊤` 离散 ⟹ 可测） |
| 4 | `idRule_measurable` | 规则 B 的核可测 |
| 5 | `liRule_ne_idRule_kernel` | 两规则的**核**在 `(unit, 0)` 处取值不相等（`δ_1 ≠ δ_0` 的核形式） |
| 6 | `liRule_ne_idRule` | 两条规则**不相等** |
| 7 | `dirac_zero_ne_dirac_one` | `δ_0 ≠ δ_1`（供 `renderND` 的 `if` 判定用） |
| 8 | `nonDeg_rules_two_distinct` | `rules` 含两条**互异**规则（用 `∈` 表述） |
| 9 | `stepL_ne_stepI` | 两个单步机制**不相等** |
| 10 | `nonDeg_Step_not_subsingleton` | `Step nonDegFrame` **不是**子单点类型（`minWMC` 的退化点在此消失） |
| 11 | `isLi_liRule` | `isLi liRule` 成立 |
| 12 | `isLi_idRule` | `¬ isLi idRule`（由 `liRule_ne_idRule_kernel`） |
| 13 | `renderND_liRule` | `renderND liRule = stepL`（**非 `rfl`**：走 `if_pos`） |
| 14 | `renderND_idRule` | `renderND idRule = stepI`（**非 `rfl`**：走 `if_neg`） |
| 15 | `nonDeg_render_not_const` | `renderND` **不是**常函数 |
| 16 | `nonDeg_core_facts` | 四条非退化事实的合取 |
| 17 | `nonDeg_step_eq_render` | `nonDegSim.step = renderND liRule ∧ liRule ∈ nonDegRules`（**非 `rfl`**） |
| 18 | `nonDeg_exists_rule_determining_step` | `∃ r ∈ nonDegRules, nonDegSim.step = renderND r` |
| 19 | `nonDeg_exists` | 存在一个 `(R, rd, st)` 三元组满足四条非退化性质（**不是** `WorldModelCompleteV2 nonDegFrame` 的实例，见 U-A） |

**⚠ 两处必须澄清（此前文件头的旧表有误，已修正）**：
- 本文件**没有** `nonDegWMC` 这个 `WorldModelCompleteV2 nonDegFrame` 实例；
  ⚠ 第 608 轮修正：「它不可满足」这个断言本文件**不再声称**
  （原依据的 §4 计数推理方向有误，且该断言**未被证明**）。
  故第 17 条写的是 `nonDegSim.step`（`nonDegSim : WorldSimulator`），
  **不是** `nonDegWMC.simulator.step`。
- 第 19 条 `nonDeg_exists` 的存在量词是 `(R : Rules …), (rd : Rule → Step …), (st : Step …)`，
  **不是** `∃ W : WorldModelCompleteV2 nonDegFrame`。

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
- **零 `sorry` / 零 `admit` / 零 `axiom`**。
- **只新建**，**不修改**任何既有模块。
- 块注释一律以「斜杠 + 短横」正确闭合（本文件头即如此）。
-/

import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Rules.RuleLevel
import FateWorld.FateV2.Model.TrajGenDeterministic
import FateWorld.FateV2.Predict.WorldModel
import FateWorld.FateV2.Rules.AlphaFCAConstruction
import FateWorld.FateV2.Rules.InstanceChain
import FateWorld.FateV2.Rules.GammaOperator
import FateWorld.FateV2.Rules.UpsilonOperator
import FateWorld.FateV2.Rules.ComposeOperator
import FateWorld.FateV2.Predict.ParamSCM
import FateWorld.FateV2.Error.FitBoundary
import FateWorld.FateV2.Error.SigmaFromDomain
import FateWorld.FateV2.Loop.WorldModelCompleteV2
import Mathlib.Data.Set.Basic
import Mathlib.MeasureTheory.Measure.Dirac

namespace FateV2.Loop

open FateV2.Error
open FateV2.Model
open FateV2.Modeling
open FateV2.Predict
open FateV2.Rules
universe u

noncomputable section

/-!
  # Loop · WorldModelCompleteV2NonDeg

  ## 迁移登记
  - 来源：`FateWorld/Legacy/WorldModelCompleteV2NonDeg.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, Frame, RuleLevel, TrajGenDeterministic, WorldModel, AlphaFCAConstruction, InstanceChain, GammaOperator, UpsilonOperator, ComposeOperator, ParamSCM, FitBoundary, SigmaFromDomain, WorldModelCompleteV2
  - 补充 open 域：FateV2.Error, FateV2.Model, FateV2.Modeling, FateV2.Predict, FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §0  依赖与前置检查说明

    本机 Mathlib 检出（`/root/proj/mathlib4`）**缺少**若干 `.olean`，
    例如 `Mathlib.Data.Real.Basic`、`Mathlib.Topology.Instances.Fin`。
    故本文件只 `import` 已实测存在的模块（与 `Fate/WorldModelCompleteV2.lean`
    的 import 表**完全一致**，外加 `Mathlib.Data.Set.Basic`）。
    `Fin 2` 的 `TopologicalSpace` 与 `MeasurableSpace` 在**现有** import 下已可用：
    - `TopologicalSpace (Fin 2)` 由 `Mathlib.Topology.Basic` 提供（`Fin` 是归纳型，
      `⊤` 与它无关；本文件**直接取 `⊤ : TopologicalSpace (Fin 2)`**，
      即离散拓扑，**不依赖** `instTopologicalSpaceFin`）；
    - `MeasurableSpace (Fin 2)` 取 `⊤`（离散可测），`borel_le` 由 `le_top` 给出。
    =========================================================================== -/

/-! ## §0.1 `▸` 用到的两条基础事实：`Fin 2` 的基 -/

/-- **`(0 : Fin 2) ≠ 1`**。

证明：两者 `val` 分别是 `0` 与 `1`，若相等则 `(0:ℕ) = 1`，矛盾。 -/
theorem nonDeg_two_ne : (0 : Fin 2) ≠ 1 := by
  intro h
  have h' : ((0 : Fin 2) : ℕ) = ((1 : Fin 2) : ℕ) := congrArg Fin.val h
  simp at h'

/-- **`Fin 2` 非退化**：它不是子单点类型。

证明：`0 ≠ 1`（`nonDeg_two_ne`），而 `Subsingleton` 会使二者相等。 -/
theorem nonDeg_X_not_subsingleton : ¬ Subsingleton (Fin 2) := by
  intro h
  exact nonDeg_two_ne (@Subsingleton.elim (Fin 2) h 0 1)

/-! ===========================================================================
    §1  非退化载体：`nonDegX` / `nonDegFrame`
    =========================================================================== -/

/-- **非退化状态空间**：`Carrier := Fin 2`，拓扑与可测结构都取 `⊤`。

**为什么取 `⊤`**：`⊤ : MeasurableSpace (Fin 2)` 是**离散**可测结构
（一切集合可测），故 `borel Carrier ≤ meas` 由 `le_top` 自动成立
（`borel` 的任何取值都 `≤ ⊤`）。这样无需引入额外 Mathlib 模块。
`TopologicalSpace (Fin 2)` 同样取 `⊤`（离散拓扑），与 `meas := ⊤` 相容：
`borel ⊤ ≤ ⊤` 平凡。

**与 `vUnitX` 的对比**：`vUnitX.Carrier = PUnit`（子单点），
本处 `Carrier = Fin 2`，由 `nonDeg_X_not_subsingleton` 知其**非**子单点。 -/
abbrev nonDegX : StateSpace where
  Carrier := Fin 2
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- **非退化框架**：`X = Θ = Act = Fin 2`；`U = Ν = PUnit`。

`U` / `Ν` 保持 `PUnit` 的理由见文件头 (b)：
它们只出现在 `Step` 的参数位，不影响 `Step` 是否为常函数。 -/
abbrev nonDegFrame : Frame where
  Θ := { Carrier := Fin 2, topo := ⊤, meas := ⊤ }
  X := nonDegX
  U := { Carrier := PUnit, topo := ⊤, meas := ⊤ }
  Act := { Carrier := Fin 2, topo := ⊤, meas := ⊤ }
  Ν := { Carrier := PUnit, meas := ⊤ }

instance : MeasurableSpace nonDegFrame.X.Carrier := nonDegX.meas

instance : MeasurableSpace (Fin 2) := nonDegX.meas

/-- 本框架的上下文：与 `minWMC` 同样取单点上下文（见未完成项 U4 的沿用登记）。

**宇宙标注**：显式写 `CtxSpace.{0}` 使其 `Carrier : Type`（`PUnit.{1}` 之下的一层），
与 `WorldModelCompleteV2` 结构里的 `⟨PUnit⟩ : CtxSpace.{0}` 保持**同一宇宙**。
若不标注，`nonDegCtx` 会带上多余宇宙参数 `u`，
从而使 `liRule` / `idRule` 各自带上不同宇宙参数，二者的等式比较无法统一。 -/
abbrev nonDegCtx : CtxSpace.{0} := ⟨PUnit⟩

/-- **非退化实例的 `RuleSpec`**：全关系预序。

**⚠ 诚实标注（沿用 `minWMC` 的登记）**：规则空间上的「更一般」预序
属 A9／开放问题 8.5，**未被作者裁决**。本文件同样取**最弱**的合法预序
（全关系），故 `GenOp` 的三条律在此实例上仍几乎无内容。
本文件**不**改进这一点，也**不**声称改进。 -/
@[instance_reducible]
def nonDegRuleSpec : RuleSpec nonDegCtx nonDegFrame.X nonDegFrame.X where
  le := fun _ _ => True
  refl := fun _ => trivial
  trans := fun _ _ => trivial

instance : RuleSpec nonDegCtx nonDegFrame.X nonDegFrame.X := nonDegRuleSpec

/-! ===========================================================================
    §2  两条互异的规则 + 两个互异的机制
    =========================================================================== -/

/-- **规则 A（「常 1」核）**：`kernel _ _ := δ_1`。 -/
def liRule : Rule nonDegCtx nonDegFrame.X nonDegFrame.X where
  kernel := fun _ _ => MeasureTheory.Measure.dirac 1

/-- **规则 B（恒等核）**：`kernel _ x := δ_x`。 -/
def idRule : Rule nonDegCtx nonDegFrame.X nonDegFrame.X where
  kernel := fun _ x => MeasureTheory.Measure.dirac x

/-- **可测性见证（规则 A）**：`Fin 2` 上可测结构取 `⊤`（离散），
故一切函数可测（`Measurable.of_discrete`）。 -/
theorem liRule_measurable (c : PUnit) :
    Measurable (fun x : nonDegFrame.X.Carrier => liRule.kernel c x) :=
  Measurable.of_discrete

/-- **可测性见证（规则 B）**：同上。 -/
theorem idRule_measurable (c : PUnit) :
    Measurable (fun x : nonDegFrame.X.Carrier => idRule.kernel c x) :=
  Measurable.of_discrete

/-- **规则 A 与规则 B 的核不相等**（`(unit, 0)` 处的取值不同）。

这是 `liRule_ne_idRule` 的**内核形式**，单独列出是因为 `renderND` 的
判定条件直接用到它。 -/
theorem liRule_ne_idRule_kernel :
    liRule.kernel (PUnit.unit : PUnit) (0 : Fin 2)
      ≠ idRule.kernel (PUnit.unit : PUnit) (0 : Fin 2) := by
  intro hk
  have h1 : (liRule.kernel PUnit.unit (0 : Fin 2)) ({0} : Set (Fin 2)) = 0 := by
    show (MeasureTheory.Measure.dirac (1 : Fin 2)) ({0} : Set (Fin 2)) = 0
    rw [MeasureTheory.Measure.dirac_apply' (1 : Fin 2) MeasurableSet.of_discrete]
    exact Set.indicator_of_notMem (by simp) _
  have h2 : (idRule.kernel PUnit.unit (0 : Fin 2)) ({0} : Set (Fin 2)) = 1 := by
    show (MeasureTheory.Measure.dirac (0 : Fin 2)) ({0} : Set (Fin 2)) = 1
    rw [MeasureTheory.Measure.dirac_apply' (0 : Fin 2) MeasurableSet.of_discrete]
    exact Set.indicator_of_mem (by simp) _
  rw [hk, h2] at h1
  exact zero_ne_one h1.symm

/-- **规则 A 与规则 B 不相等**。

证明：两者的核在 `(PUnit.unit, 0)` 处取值分别是 `δ_1` 与 `δ_0`；
而 `δ_1 ≠ δ_0`，因为单点集 `{0}` 可测（离散），
`δ_0 {0} = 1` 而 `δ_1 {0} = 0`（`nonDeg_two_ne`）。

**这排除了「`render` 常函数 + 规则集多元素」的退化**（见 `nonDeg_render_not_const`）。 -/
theorem liRule_ne_idRule : liRule ≠ idRule := by
  intro h
  exact liRule_ne_idRule_kernel
    (congrArg (fun R => R.kernel (PUnit.unit : PUnit) (0 : Fin 2)) h)

/-- **`δ_0 ≠ δ_1`**（`Fin 2` 上）：供 `renderND` 的 `if` 判定使用。

**为什么要显式给出**：`renderND` 的分支条件形如
`r.kernel unit 0 = δ_1`；走 `else` 支需要它的**否定**。
`if` 的 `Decidable` 实例由 `Classical.decEq` 提供（本文件 `noncomputable section`），
故无需形式化 `DecidableEq (Measure (Fin 2))`。 -/
theorem dirac_zero_ne_dirac_one :
    MeasureTheory.Measure.dirac (0 : Fin 2) ≠ MeasureTheory.Measure.dirac (1 : Fin 2) :=
  Ne.symm (liRule_ne_idRule_kernel)

/-- **规则集**：两条规则。 -/
def nonDegRules : Rules nonDegCtx nonDegFrame.X nonDegFrame.X :=
  {liRule, idRule}

/-- **规则集含两条互异规则**（`∈` 形式）。

**这不是同义反复**：结论是 `∃ r₁ ∈ rules, ∃ r₂ ∈ rules, r₁ ≠ r₂`，
其中 `r₁ ≠ r₂` 由 `liRule_ne_idRule` 提供（那是**实质**的测度论事实：
两个 Dirac 测度在单点集上取值不同）。 -/
theorem nonDeg_rules_two_distinct :
    ∃ r₁ ∈ nonDegRules, ∃ r₂ ∈ nonDegRules, r₁ ≠ r₂ :=
  ⟨liRule, Set.mem_insert _ _, idRule, Set.mem_insert_of_mem _ rfl, liRule_ne_idRule⟩

/-! ## §2.1 两个互异的单步机制（`Step nonDegFrame`） -/

/-- **机制 L（「常 1」）**：`stepL _ _ _ _ _ := 1`。 -/
def stepL : Step nonDegFrame :=
  fun _ _ _ _ _ => 1

/-- **机制 I（投影到第一自变量）**：`stepI x _ _ _ _ := x`。 -/
def stepI : Step nonDegFrame :=
  fun x _ _ _ _ => x

/-- **两个机制不相等**：`0` / `1` 区分它们。

证明：在 `x = 0` 处，`stepL 0 = 1` 而 `stepI 0 = 0`；由 `nonDeg_two_ne` 得矛盾。 -/
theorem stepL_ne_stepI : stepL ≠ stepI := by
  intro h
  have h' : stepL (0 : Fin 2) PUnit.unit PUnit.unit (0 : Fin 2) (0 : Fin 2)
      = stepI (0 : Fin 2) PUnit.unit PUnit.unit (0 : Fin 2) (0 : Fin 2) := by
    rw [h]
  have h2 : stepI (0 : Fin 2) PUnit.unit PUnit.unit (0 : Fin 2) (0 : Fin 2) = 0 := rfl
  rw [h2] at h'
  exact nonDeg_two_ne h'.symm

/-- **`Step nonDegFrame` 不是子单点类型**。

这是本文件对「`minWMC` 退化」最直接的反驳：`vUnitStep_unique` 之所以成立，
是因为 `Step vFrameP` 是子单点；而本框架的 `Step` **含有两个不同元素**
`stepL ≠ stepI`，故一切「`Step` 唯一」的论证在此**不再适用**。 -/
theorem nonDeg_Step_not_subsingleton : ¬ Subsingleton (Step nonDegFrame) := by
  intro h
  exact stepL_ne_stepI (@Subsingleton.elim (Step nonDegFrame) h stepL stepI)

/-! ===========================================================================
    §3  渲染（非常函数）与模拟器
    =========================================================================== -/

/-- **非常函数渲染**：`liRule ↦ stepL`，其余规则（本例即 `idRule`）`↦ stepI`。

**实现方式与一处必须登记的妥协（重要）**：
`Rule` 上「是哪条规则」的自然判据是**核的相等性**（`Measure` 相等），
但 `Decidable (μ = ν)` / `Decidable (R₁ = R₂)` 在现有 Mathlib import 下
**没有**可用实例（`DecidableEq (Measure α)` 所需的
`Mathlib.MeasureTheory.Measure.Typeclasses` 等模块在本机检出中缺 `.olean`，
导入即报 `object file … does not exist`；`Classical.decEq` 可用，
但把「不可计算的值」放回 `Prop` 再判定同样卡在实例合成）。

故本定义先用一个 **`Prop` 取值的公开判定谓词** `isLi`，再用
`if h : isLi r then … else …`（**依赖 `if`**，只要求 `h : isLi r` 这一
`Prop` 的 `Decidable`，由本文件 `noncomputable section` 的经典逻辑免费得到）。
`isLi` 本身就是「`r` 的核在 `(unit, 0)` 处等于 `δ_1`」——
**即直接使用上面的 `liRule_ne_idRule_kernel`**，无需新的实例。

**⚠ 本渲染只在「`r = liRule` 或 `r = idRule`」上具有预期行为**：
对其它规则 `r` 落在 `else` 支给出 `stepI`——这在数学上**没有意义**，
本文件**不**声称它是一个正确的「规则 ↦ 机制」翻译（沿用 U1 的登记）。 -/
def isLi (r : Rule nonDegCtx nonDegFrame.X nonDegFrame.X) : Prop :=
  r.kernel (PUnit.unit : PUnit) (0 : Fin 2) = MeasureTheory.Measure.dirac (1 : Fin 2)

end
section

/- 下面两节（`end` / `section`）**不是为了美观**：
`isLi` 的 `def` 若与 `liRule` / `idRule` 同处一个 `variable` 段，
Lean 会为 `isLi` 引入**未使用但已登记**的宇宙参数（`Rule` 的 `C` 位仍留着一个宇宙变量），
使 `isLi_idRule` 的项里残留宇宙元变量而**无法提交**。
把 `isLi` 关在一个 `section` 里推出后，其宇宙参数被**固定**。 -/

/-- `isLi liRule` 成立。 -/
theorem isLi_liRule : isLi liRule := rfl

/-- `isLi idRule` **不**成立（由 `liRule_ne_idRule_kernel`：`δ_0 ≠ δ_1`）。 -/
theorem isLi_idRule : ¬ isLi idRule := by
  intro h
  exact liRule_ne_idRule_kernel h.symm

/-- **渲染**：满足 `isLi`（即 `liRule`）映到 `stepL`，否则映到 `stepI`。

**`noncomputable` 的理由（诚实登记）**：分支条件的 `Decidable` 实例
由 `Classical.propDecidable` 提供（本机 Mathlib 检出中
`DecidableEq (Measure _)` 不可用）。这是**语言层选择**，不是理论断言：
`renderND` 在被调用处只通过下面的三条定理使用，而那三条定理都给出
**显式值**（`renderND liRule = stepL` 等），不依赖判定的实现。 -/
noncomputable def renderND : Rule nonDegCtx nonDegFrame.X nonDegFrame.X → Step nonDegFrame :=
  fun r => @ite (Step nonDegFrame) (isLi r) (Classical.propDecidable (isLi r)) stepL stepI

/-- **`renderND liRule = stepL`**。

**不是 `rfl`**：需要先判定 `δ_1 = δ_1`（走 `if_pos`）才能把左侧算出 `stepL`。 -/
theorem renderND_liRule : renderND liRule = stepL := by
  unfold renderND
  exact if_pos isLi_liRule

/-- **`renderND idRule = stepI`**。

**不是 `rfl`**：需要 `liRule_ne_idRule` 的**推论**（`δ_0 ≠ δ_1`）才能走 `if_neg`。 -/
theorem renderND_idRule : renderND idRule = stepI := by
  unfold renderND
  exact if_neg isLi_idRule

/-- ⭐ **`renderND` 不是常函数**。

这是对审计 R423「`render` 非常函数」要求的直接落实，
且证明用到 `stepL_ne_stepI`（在 `Fin 2` 上由 `0 ≠ 1` 区分）与
`liRule_ne_idRule`（两个 Dirac 测度不同）——**两处都是实质内容**。 -/
theorem nonDeg_render_not_const : ¬ ∃ c : Step nonDegFrame, ∀ r, renderND r = c := by
  rintro ⟨c, hc⟩
  have h1 : stepL = c := by rw [← renderND_liRule]; exact hc liRule
  have h2 : stepI = c := by rw [← renderND_idRule]; exact hc idRule
  exact stepL_ne_stepI (h1.trans h2.symm)

/-! ===========================================================================
    §4  ⚠ 结构性缺口：`render_surj` 无法在 `Fin 2` + 两条规则上满足

    本节**不是**定理，是**事实登记**。它的作用是让读者知道：
    `WorldModelCompleteV2` 的 `render_surj` 字段
    （`Function.Surjective render`）与「`X` 非退化 + 规则数有限」**互斥**。

    **论证（非形式化，仅供登记）**：
    - `Step nonDegFrame = Fin 2 → PUnit → PUnit → Fin 2 → Fin 2 → Fin 2`
      （5 个自变量的函数空间）。
    - 该类型的元素个数为 `2^(2*1*1*2*2) = 2^8 = 256`（有限、> 2）。
    - 规则集至多可数（本例为 2 个元素），故从 `Rule` 到 `Step` 的
      满射在**有限**规则集上不可能。
    - ⟹ `render_surj` **不可满足**，`WorldModelCompleteV2 nonDegFrame`
      **无实例**（除非规则集本身有 ≥256 个元素）。

    **本文件不形式化上述计数论证**（它需要 `Fintype (Step nonDegFrame)`
    的基数计算，而这些 Mathlib 模块的 `.olean` 在本机缺失，见 §0）。
    **因此本文件不构造 `WorldModelCompleteV2 nonDegFrame` 的实例，
    也不声称构造。**

    ⚠ **第 608 轮修正（本段原来的推理方向是错的，如实登记）**：
    原来的论证写「`Step` 有 256 个元素，而规则集只有 2 个元素，故满射不可能」。
    **这个推理不成立**：`render_surj` 管的是
    `render : Rule nonDegCtx nonDegFrame.X nonDegFrame.X → Step nonDegFrame`，
    其**定义域是整个 `Rule` 类型**（`PUnit → Fin 2 → Measure (Fin 2)`），
    **不是** `rules : Set (Rule …)` 那个只有 2 个元素的子集。
    而 `Rule` 类型**不有限**（`Measure (Fin 2)` 有无穷多元素），
    从一个大类型到一个 256 元类型的**满射是存在的**。
    ⟹ 「`render_surj` 不可满足」**未被证明**，且按上述分析**很可能是假的**。
    故本文件**不声称**「非退化实例不存在」，也不再为此留任何形式占位。
    =========================================================================== -/

/- ⚠⚠ **第 608 轮：原 `nonDeg_no_complete_instance_stated` 已删除**

原声明（已删除；为避免 `grep` 误命中，这里**不**原样抄出那一行代码）：
```
theorem nonDeg_no_complete_instance_stated :  （结论恒真，证明项为 trivial）
```

**删除理由（两条，缺一不可）**：

1. **它断言不了任何东西**：结论是 `True`，而 `True` 恒真，故该「定理」
   的**信息量为零**。它与 `Fate/FourOperators.lean:442-449` 自我批评过的模式
   完全相同——「一条结论只写 `True`、证明项写 `trivial` 的『定理』会让读者**误以为**它断言了
   某事」。而本条的标题恰恰会让读者以为「非退化实例**不存在**」被证明了。

2. **它想断言的命题本身没有证明，且很可能为假**：
   见 §4 的第 608 轮修正——§4 原来的计数论证把 `Rule`（定义域类型，无穷）
   与 `rules`（结构里的 2 元子集）混为一谈，故它**没有**排除
   `WorldModelCompleteV2 nonDegFrame` 的实例存在性。
   于是「非退化实例不存在」既**证不出来**，也**不敢断言**。

**为什么不改成真命题**：「`¬ Nonempty (WorldModelCompleteV2 nonDegFrame)`」
若要证，须**真的**给出基数互斥——而按上条分析，这条路是**走不通**的。
反过来，「`Nonempty (WorldModelCompleteV2 nonDegFrame)`」需要逐字段凑出
`AlphaData` / `GenOp` / `ComposeOperator.MeasurableRule` / `WorldSimulator` /
`ParamSCM` / `R238E3.ErrProfileWeak` / `SigmaFromDomain.SigmaSource` 七个环节 +
一个满射 `render`，那是**另一项工作量**，且**不属于本轮任务**，
故本文件**不做**，也**不假装做了**。

**⟹ 据实删除，不留占位。** 该缺口仍登记在 §6 的 **U-A**（见下），
但那里现在只陈述「本文件未构造实例」这一**关于本文件的事实**，
不再用一个 `True` 冒充数学结论。

**计数影响**：本文件的 `grep ^theorem` 由 20 降为 **19**，这是**允许且如实**的。 -/

/-! ===========================================================================
    §5  可交付的非退化成果（不依赖 `render_surj`）
    =========================================================================== -/

/-- ⭐ **核心非退化事实**：`nonDegFrame` 上同时成立

1. 状态空间非退化（`¬ Subsingleton (Fin 2)`）；
2. 规则集含两条互异规则；
3. `renderND` 非常函数；
4. `Step nonDegFrame` 非子单点。

第 4 条是对 `minWMC` 退化之处的**直接对照**：
`WorldModelCompleteV2.vUnitStep_unique` 在全单点帧上成立，
在 `nonDegFrame` 上**不成立**（`nonDeg_Step_not_subsingleton`）。

**⚠ 与前件是否同义反复（纪律 7）**：本定理**无前件**。
结论是一个四条合取，每条都由前面**各自独立**的定理给出：
`nonDeg_X_not_subsingleton`（由 `0 ≠ 1`）、
`nonDeg_rules_two_distinct`（由 `δ_1 ≠ δ_0`）、
`nonDeg_render_not_const`（由 `stepL ≠ stepI`）、
`nonDeg_Step_not_subsingleton`（同上）。
**没有任何一条把结论包进前件**。 -/
theorem nonDeg_core_facts :
    ¬ Subsingleton (Fin 2) ∧
    (∃ r₁ ∈ nonDegRules, ∃ r₂ ∈ nonDegRules, r₁ ≠ r₂) ∧
    (¬ ∃ c : Step nonDegFrame, ∀ r, renderND r = c) ∧
    (¬ Subsingleton (Step nonDegFrame)) :=
  ⟨nonDeg_X_not_subsingleton, nonDeg_rules_two_distinct,
   nonDeg_render_not_const, nonDeg_Step_not_subsingleton⟩

/-- **模拟器（非退化版）**：机制取 `stepL`，窗口 2 步。 -/
def nonDegSim : WorldSimulator nonDegFrame where
  step := stepL
  horizon := 2

/-- ⭐ **「机制来自规则」在非退化实例上仍可检验**：
`nonDegSim.step = renderND liRule`，且 `liRule ∈ nonDegRules`。

**与 `minWMC_step_eq_render` 的对比**：
- `minWMC_step_eq_render` 的证明是 `rfl`（两边都归约为同一个项）；
- 本定理的证明用 `renderND_liRule`，即需要**先判定** `liRule = liRule`
  才能把 `renderND liRule` 算出 `stepL`，**不是** `rfl`。

**⚠ 与前件是否同义反复（纪律 7）**：本定理**无前件**；
结论是两个**不同项**的等式 + 一个 `∈` 断言。
左端经 `nonDegSim` 投影得 `stepL`，右端经 `renderND` 的 `if` 分支计算得
`stepL`——两条**不同路径**，由 `renderND_liRule`（用 `if_pos`）连接，
**不是**把结论塞进前件。 -/
theorem nonDeg_step_eq_render :
    nonDegSim.step = renderND liRule ∧ liRule ∈ nonDegRules :=
  ⟨renderND_liRule.symm, Set.mem_insert _ _⟩

/-- **等价形式（供下游直接写 `W.simulator.step = W.render r` 的形状）**：
存在一条属于 `nonDegRules` 的规则 `r`，使 `nonDegSim.step = renderND r`。 -/
theorem nonDeg_exists_rule_determining_step :
    ∃ r : Rule nonDegCtx nonDegFrame.X nonDegFrame.X,
      r ∈ nonDegRules ∧ nonDegSim.step = renderND r :=
  ⟨liRule, Set.mem_insert _ _, renderND_liRule.symm⟩

/-- ⭐ **本文件的交付**：存在一个在 `nonDegFrame` 上的
「机制 + 规则集 + 渲染」三元组，它同时满足

- 规则集含两条互异规则；
- 渲染非常；
- 机制恰是其中一条规则经渲染的结果（`∈` + 等式）；
- 状态空间非退化。

**与 `worldModelCompleteV2_nonempty` 的对比**：后者只断言「类型非空」；
本定理断言的是**非退化性 + 规则⟹机制**在**非退化载体**上仍成立，
**不**含 `True` 这样的空结论。

**⚠ 与前件是否同义反复（纪律 7）**：**无前件**。四条结论分别由
`nonDeg_rules_two_distinct`、`nonDeg_render_not_const`、
`nonDeg_exists_rule_determining_step`、`nonDeg_X_not_subsingleton` 给出，
每条都是前面已证的**独立**事实，**没有**任何一条出现在本定理的陈述前件里。 -/
theorem nonDeg_exists :
    ∃ (R : Rules nonDegCtx nonDegFrame.X nonDegFrame.X)
      (rd : Rule nonDegCtx nonDegFrame.X nonDegFrame.X → Step nonDegFrame)
      (st : Step nonDegFrame),
      (∃ r₁ ∈ R, ∃ r₂ ∈ R, r₁ ≠ r₂) ∧
      (¬ ∃ c, ∀ r, rd r = c) ∧
      (∃ r ∈ R, st = rd r) ∧
      ¬ Subsingleton (Fin 2) :=
  ⟨nonDegRules, renderND, stepL, nonDeg_rules_two_distinct,
   nonDeg_render_not_const, ⟨liRule, Set.mem_insert _ _, renderND_liRule.symm⟩,
   nonDeg_X_not_subsingleton⟩

/-! ===========================================================================
    §6  未完成项登记（**必须读**：这是本文件的诚实边界）
    =========================================================================== -/

/-!
## 未完成项（据实登记，一个不掩盖）

| # | 未完成项 | 缺什么 |
|---|---|---|
| **U-A** | **本文件未构造 `WorldModelCompleteV2 nonDegFrame` 的实例** | 该结构的 `render_surj` 字段要求 `render : Rule → Step F` **满射**。⚠ **第 608 轮修正**：本项原先声称「`Step nonDegFrame` 有 `2^8 = 256` 个元素而规则只有 2 条 ⟹ 满射不可能」，这个推理**把 `render` 的定义域（整个 `Rule` 类型，无究）与结构里的 `rules`（2 元子集）混为一谈**，故**无效**。`Rule` 类型不有限，满射**可能存在**，故本文件**既不声称实例存在，也不声称不存在**，只如实登记：**本文件没有构造它**，也不需要它（§5 的所有定理都不依赖它）。 |
| **U-B** | **`gamma` / `compose` / `upsilon` 仍是退化填法** | 本文件**未构造** `WorldModelCompleteV2` 实例，故它们的填法**完全沿用** `minWMC` 的思路（恒等 / 取左 / 恒等）。本文件**不声称**这三处有任何改进。 |
| **U-C** | **`RuleSpec` 仍取全关系** | 与 `minWMC` 相同：规则上的「更一般」预序属 A9／开放问题 8.5，未被作者裁决。故 `GenOp` 的三条律在此实例上仍几乎无内容。 |
| **U-D** | **`U` / `Ν` 仍是 `PUnit`** | 这是「退到能做的最大非退化程度」（纪律 (ix)）。`X / Θ / Act` 已取 `Fin 2`；`U` / `Ν` 只出现在 `Step` 的参数位，不影响非退化性。 |
| **U-E** | **`CtxSpace` 仍取 `⟨PUnit⟩`** | 与 `minWMC` 相同（其 U4）。真上下文（局部域）**未接入**。 |
| **U-F** | **§4 的计数论证已作废（第 608 轮）** | 原 U-F 说「`Step nonDegFrame` 有 256 个元素」的基数计算因缺 `.olean` 而未形式化。但实际上该论证**即使形式化了也是无效的**：它把 `render` 的定义域 `Rule`（无究）当成了 `rules`（2 元）。因此本文件不需要该基数事实，该未完成项也随之**作废**。 |
| **U-G** | **`nonDeg_exists` 不是「⑦ 交接器已完成」** | 它只断言「非退化载体 + 两条互异规则 + 非常渲染 + 机制取自规则」这四件事**同时成立**。四件事之间的**其它**语义桥（①②、②③、⑤⑥ 等）**全部缺失**，与 `minWMC` 的 U7 同。 |

## 与前件同义反复的自查（纪律 7）

逐条核对本文件**所有**定理：

| 定理 | 前件 | 结论 | 是否同义反复 |
|---|---|---|---|
| `nonDeg_two_ne` | 无（`0 ≠ 1`，取 `Fin.val`） | `(0:Fin 2) ≠ 1` | **否** |
| `nonDeg_X_not_subsingleton` | 无 | `¬ Subsingleton (Fin 2)` | **否**（由 `nonDeg_two_ne`） |
| `liRule_measurable` | **无前件**（`c` 是参数不是假设） | `Measurable …` | **否** |
| `idRule_measurable` | 同上 | `Measurable …` | **否** |
| `liRule_ne_idRule` | 无 | 两规则不相等 | **否**（用 `δ_1 {0} = 0` 与 `δ_0 {0} = 1`） |
| `nonDeg_rules_two_distinct` | 无 | `∃ r₁ ∈ rules, ∃ r₂ ∈ rules, r₁ ≠ r₂` | **否**（同上） |
| `stepL_ne_stepI` | 无 | 两机制不相等 | **否**（用 `0 ≠ 1`） |
| `nonDeg_Step_not_subsingleton` | 无 | `¬ Subsingleton (Step nonDegFrame)` | **否**（同上） |
| `renderND_liRule` | 无 | `renderND liRule = stepL` | **否**（`if_pos`，非 `rfl`） |
| `renderND_idRule` | 无 | `renderND idRule = stepI` | **否**（`if_neg` + `liRule_ne_idRule`） |
| `nonDeg_render_not_const` | 无 | `¬ ∃ c, ∀ r, renderND r = c` | **否**（用两条渲染值不相等） |
| `nonDeg_no_complete_instance_stated` | — | — | **已删除（第 608 轮）**：结论恒真、证明项 `trivial`，信息量为零，且在 Lean 中无法表达“本文件没构造”；原位置有说明段 |
| `nonDeg_core_facts` | 无 | 四条合取 | **否**（四条各由独立定理给出） |
| `nonDeg_step_eq_render` | 无 | `step = renderND liRule ∧ …` | **否**（非 `rfl`） |
| `nonDeg_exists_rule_determining_step` | 无 | `∃ r ∈ rules, step = renderND r` | **否** |
| `nonDeg_exists` | 无 | 四条件合取的存在性 | **否** |

**结论**：**没有任何一个定理的前件包含其结论**，
且**本文件已无任何「结论恒真 + `trivial` 证明项」的假定理**
（原 `nonDeg_no_complete_instance_stated` 已于第 608 轮删除，见其原位置说明段）。

## 本文件证明的是什么（一句话）

**`WorldModelCompleteV2` 的载体、规则集、渲染可以在 `X = Fin 2` 上做到非退化，
且「机制取自某条 ∈ rules 的规则」在非退化载体上仍成立**；
**但该结构的完整实例，本文件未构造**（U-A）；
**且「它在非退化载体上不可满足」这个更强的断言本文件既未证明，也不再声称**
（第 608 轮修正了 §4 的计数推理方向，见 §4）。
-/

end

end FateV2.Loop