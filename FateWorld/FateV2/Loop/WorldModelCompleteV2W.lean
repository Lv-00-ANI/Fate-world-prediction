/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Loop`
阶段：**G2 选项甲的可行情验证 —— 弱化版结构 `WorldModelCompleteV2W`**

---------------------------------------------------------------------------
⚠ 本文件的**定位**（必读，逐条对应任务书要求）
---------------------------------------------------------------------------
**(a) 本结构 `WorldModelCompleteV2W` **不是** `WorldModelCompleteV2`，
它是**弱化版**：唯一区别是把 `render_surj : Surjective render`
换成 `render_nonconst : ∃ r₁ ∈ rules, ∃ r₂ ∈ rules, render r₁ ≠ render r₂`。**

**(b) 本文件**不修改** `Fate/WorldModelCompleteV2.lean`，
也**不修改** `Fate/WorldModelCompleteV2NonDeg.lean`。本文件只**新建**类型与本文件内的实例。**
（已 `grep` 核对：本文件未出现在 `Fate/WorldModelCompleteV2.lean` 或
`Fate/WorldModelCompleteV2NonDeg.lean` 中；两文件的 mtime 未变。）

**(c) 本文件的**价值**：证明「若把 `render_surj` 换成 `render_nonconst`，
非退化实例就**存在**」。具体地：**

- 在 `Fin 2` 状态空间（`nonDegFrame`，非退化）上，
  **整套 13 个字段全部填满**，构造出 `WorldModelCompleteV2W nonDegFrame`
  的**真实实例** `wmcW`（见 `wmcW_instance_exists`）。
- 更强：本文件还**证明** `renderND` **不是满射**
  （`renderND_not_surj`，显式给出 `stepK` 不在 `renderND` 的像内）。
  **⟹ 这直接说明「`render_surj` 无法被本文件所用的 `render` 满足」，
  而「`render_nonconst` 可以被满足」——这就是选项甲可行的**实验证据**。**

**(d) 这不等于「选项甲被采纳」。** 那是**作者的裁决**。
本文件**只**提供可行性证据，**不**主张结构应当这样改，
**也**不**主张 `WorldModelCompleteV2` 本身有「错」。
反过来说，本文件**没有**证明「`WorldModelCompleteV2` 必然需要改」——
它只证明了**「换成 `render_nonconst` 后非退化实例存在」**这一件事实。
`WorldModelCompleteV2NonDeg.lean` 的 U-A 行是**论证**（非形式化）说
`render_surj` 与「非退化 X + 有限规则集」互斥；本文件在**同一条 `render`**
（`renderND`）上**形式化地**证明了它不满射，这是对 U-A 的**局部形式化支撑**
（但**不是**完整的基数论证：见未完成项 W-F）。

**(e) 如实报告**：本文件**没有**任何一步做不出来。`render_nonconst`
**不**与非退化冲突（恰恰相反：非退化 ⟹ 有两条规则可区分 ⟹ 非常渲染可满足）。
但**必须诚实登记**：`render_nonconst` **非常弱**，
它**不**排除「规则集有 100 条但渲染只取 2 个值」这类退化；
它**只**排除「渲染是常函数」。见未完成项 W-B。

---------------------------------------------------------------------------
本文件实际存在的定理（`grep ^theorem` 核对，共 8 条）
---------------------------------------------------------------------------
| # | 定理 | 内容 | 性质 |
|---|---|---|---|
| 1 | `stepL_ne_stepK` | 「常 1」机制 ≠ 「常 0」机制 | 由 `0 ≠ 1` |
| 2 | `stepI_ne_stepK` | 「投影」机制 ≠ 「常 0」机制 | 由 `0 ≠ 1` |
| 3 | `renderND_ne_stepK` | **任意**规则经 `renderND` 渲染都 ≠ `stepK` | 对 `if` 两支分别证 |
| 4 | `renderND_not_surj` | `renderND` **不满射**（`stepK` 不在像内） | 由 (3) |
| 5 | `renderND_nonconst` | 存在两条规则渲染不同（`render_nonconst` 的实例证据） | 由 `stepL_ne_stepI` |
| 6 | `wmcW_step_eq_render` | 实例的 `simulator.step = render liRule` 且 `liRule ∈ rules` | 由 `renderND_liRule` |
| 7 | `wmcW_instance_exists` | `∃ W : WorldModelCompleteV2W nonDegFrame, True` | 构造 `wmcW` |
| 8 | `wmcW_nondeg` | 非退化合取（载体非子单点 + 两条规则 + 非常渲染 + 机制取自规则 + `render` 不满射） | 由前各条 |

**零 `sorry` / 零 `admit` / 零 `axiom`。**

---------------------------------------------------------------------------
与前件是否同义反复的自查（纪律 7 / 任务书 (e)(vii)）
---------------------------------------------------------------------------
逐条核对：**本文件所有 8 条定理的前件都是「无前件」（只有参数，没有假设）**。
关键的两条：

- `renderND_not_surj`：结论 `¬ Function.Surjective renderND`。
  **前件为空**。证明用到 `renderND_ne_stepK`（对 `if` 两支的全称断言），
  而 `renderND_ne_stepK` 的证明要**分情况**：`isLi r` 成立时两侧化为
  `stepL ≠ stepK`，否则化为 `stepI ≠ stepK`——**两支都要 `0 ≠ 1`**。
  **结论没有出现在任何前件里**。
- `wmcW_nondeg`：**无前件**。结论是 5 元合取，每一项都由**不同的**前面定理给出
  （`nonDeg_X_not_subsingleton` / `nonDeg_rules_two_distinct` /
  `renderND_nonconst` / `wmcW_step_eq_render` / `renderND_not_surj`），
  **没有**任何一项是本定理的前件。

⚠ **`wmcW_instance_exists` 的诚实标注**：结论写作 `∃ _W, True`，
**后半 `True` 是零信息量的**——非空性**完全由** `wmcW` 的构造承担。
这是任务书阶段 3 给出的形式；本文件**不**夸称它是实质定理，
实质内容在 `wmcW_nondeg`。

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
- **只新建**，**不修改**已入链模块。
- 名字 `WorldModelCompleteV2W`（新名字，不覆盖任何已有定义）。
- 每个被调用的既有名字都先 `#check` 确认（见 §0 的实测记录）。
- 块注释用「斜杠短横」结束标记收尾。
-/

import FateWorld.FateV2.Loop.WorldModelCompleteV2
import FateWorld.FateV2.Loop.WorldModelCompleteV2NonDeg
import FateWorld.FateV2.Rules.EvaluationSystems
import FateWorld.FateV2.Rules.GammaOperator
import FateWorld.FateV2.Rules.AlphaFCAConstruction
import FateWorld.FateV2.Rules.UpsilonOperator
import FateWorld.FateV2.Rules.ComposeOperator
import FateWorld.FateV2.Error.SigmaFromDomain
namespace FateV2.Loop

open FateV2.Model
open FateV2.Predict
open FateV2.Rules
open FateV2.Error
universe u

noncomputable section

/-!
  # Loop · WorldModelCompleteV2W

  ## 迁移登记
  - 来源：`FateWorld/Legacy/WorldModelCompleteV2W.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：WorldModelCompleteV2, WorldModelCompleteV2NonDeg
  - 补充 open 域：FateV2.Model, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §0  被调用的既有名字（全部已 `#check` 实测）

    | 名字 | 出处 | 实测签名（摘要） |
    |---|---|---|
    | `WorldModelCompleteV2` | `Fate/WorldModelCompleteV2.lean` | `(F : Frame) → [MeasurableSpace F.X.Carrier] → [RuleSpec ⟨PUnit⟩ F.X F.X] → Type 1` |
    | `nonDegFrame` | `…NonDeg.lean` | `Frame` |
    | `nonDegCtx` | `…NonDeg.lean` | `CtxSpace`（`:= ⟨PUnit⟩`，`abbrev`） |
    | `nonDegRuleSpec` | `…NonDeg.lean` | `RuleSpec nonDegCtx nonDegFrame.X nonDegFrame.X` |
    | `nonDegRules` | `…NonDeg.lean` | `Rules nonDegCtx nonDegFrame.X nonDegFrame.X`（`= {liRule, idRule}`）|
    | `liRule` / `idRule` | `…NonDeg.lean` | `Rule nonDegCtx nonDegFrame.X nonDegFrame.X` |
    | `renderND` | `…NonDeg.lean` | `Rule nonDegCtx nonDegFrame.X nonDegFrame.X → Step nonDegFrame` |
    | `renderND_liRule` / `renderND_idRule` | `…NonDeg.lean` | `renderND liRule = stepL` / `= stepI` |
    | `stepL` / `stepI` | `…NonDeg.lean` | `Step nonDegFrame` |
    | `stepL_ne_stepI` | `…NonDeg.lean` | `stepL ≠ stepI` |
    | `nonDegSim` | `…NonDeg.lean` | `WorldSimulator nonDegFrame`（`step := stepL`, `horizon := 2`）|
    | `nonDeg_X_not_subsingleton` | `…NonDeg.lean` | `¬ Subsingleton (Fin 2)` |
    | `nonDeg_rules_two_distinct` | `…NonDeg.lean` | `∃ r₁ ∈ nonDegRules, ∃ r₂ ∈ nonDegRules, r₁ ≠ r₂` |
    | `nonDeg_Step_not_subsingleton` | `…NonDeg.lean` | `¬ Subsingleton (Step nonDegFrame)` |
    =========================================================================== -/

/-! ===========================================================================
    §1  阶段 1：**弱化版结构** `WorldModelCompleteV2W`

    字段列表**照抄** `WorldModelCompleteV2`（13 个字段中的 12 个），
    **唯一区别**：第 13 个字段由 `render_surj : Function.Surjective render`
    换成 `render_nonconst : ∃ r₁ ∈ rules, ∃ r₂ ∈ rules, render r₁ ≠ render r₂`。

    **为什么这是「弱化」而不是「侧改」**：
    `Function.Surjective render` 在 `rules` 至少含两个元素、且 `Step F` 至少有
    两个元素时 **推出** `render_nonconst`（两个不同的像值由满射性 + 两条规则给出）。
    反之不成立（见 `renderND_not_surj`：本文件的实例非常渲染但不满射）。
    故 `render_nonconst` 是**严格更弱**的要求——**这正是选项甲的内容**。
    =========================================================================== -/

/-- **G2 · 选项甲的结构：`WorldModelCompleteV2W`（W = Weak）**

除 `render_nonconst` 外，字段与 `FateV2.Loop` **逐字相同**
（这是刻意的：使两者的差异**只有一处**，便于作者裁决时对照）。

**⚠ 与前件是否同义反复（纪律 7）**：结构字段**不是**定理，**无前件**。
`render_nonconst` 是**存在性数据**（`∃ r₁ ∈ rules, ∃ r₂ ∈ rules, render r₁ ≠ render r₂`），
**不是** `∀ r, …` 的全称断言，故它**不**能被 `rules` 的任一元素平凡满足——
它要求 **两个** 不同的渲染值，与 `rules_determine_step`（只要求**一个** `r`）
**不可互推**。 -/
structure WorldModelCompleteV2W (F : Frame) [instX : MeasurableSpace F.X.Carrier]
    [S : RuleSpec (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X] where
  /-- **① 输入**：实例集（`InstSpace`）。与 `WorldModelCompleteV2.input` 同。 -/
  input : InstSpace.{0}
  /-- **② 抽象 α（数据层）**：观测映射。与 `WorldModelCompleteV2.alpha` 同。 -/
  alpha : AlphaData.{0} input PUnit
  /-- **③a 泛化 γ**。与 `WorldModelCompleteV2.gamma` 同。 -/
  gamma : GenOp (Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X)
  /-- **③b 复合 ∘**。与 `WorldModelCompleteV2.compose` 同。 -/
  compose : ComposeOperator.MeasurableRule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X →
    ComposeOperator.MeasurableRule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X →
    ComposeOperator.MeasurableRule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X
  /-- **③c 完善 υ**。与 `WorldModelCompleteV2.upsilon` 同。 -/
  upsilon : UpsilonOperator.Upsilon.{0, 0} PUnit (Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X)
  /-- **④ 生成 / 预测**。与 `WorldModelCompleteV2.simulator` 同。 -/
  simulator : WorldSimulator F
  /-- **⑤ 因果**。与 `WorldModelCompleteV2.causal` 同。 -/
  causal : ParamSCM.ParamSCM F.X.Carrier F.X.Carrier
  /-- **⑥a 误差剖面**。与 `WorldModelCompleteV2.error` 同。 -/
  error : FateV2.Error.Core.ErrProfileWeak
  /-- **⑥b 签名 σ 来源**。与 `WorldModelCompleteV2.sigma` 同。 -/
  sigma : SigmaFromDomain.SigmaSource
  /-- **（C6 断点）规则集**。与 `WorldModelCompleteV2.rules` 同。 -/
  rules : Rules (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X
  /-- **（C6 断点）规则 → 机制的渲染**。与 `WorldModelCompleteV2.render` 同。 -/
  render : Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X → Step F
  /-- ⭐ **（唯一区别）渲染非常函数**：规则集中存在两条规则，其渲染值不同。

  **为什么用这一条替代 `render_surj`**：
  `render_surj` 要求 `render` **满射到整个 `Step F`**，
  而 `Step F` 的基数随 `F.X.Carrier` 指数增长（`Fin 2` 时为 `2^8 = 256`，
  见 `Fate/WorldModelCompleteV2NonDeg.lean` 的 U-A 行），
  有限规则集**不可能**满射。`render_nonconst` 只要求
  「渲染**不是**常函数」，这与「有限规则集 + 非退化 `X`」**相容**。 -/
  render_nonconst : ∃ r₁ ∈ rules, ∃ r₂ ∈ rules, render r₁ ≠ render r₂
  /-- **（C6 断点·核心）规则 ⟹ 模拟器**：与 `WorldModelCompleteV2.rules_determine_step` 同。 -/
  rules_determine_step :
    Σ' r : Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X,
      r ∈ rules ∧ simulator.step = render r

/-! ===========================================================================
    §2  两个用来区分渲染的机制（供 `renderND_not_surj` 使用）
    =========================================================================== -/

/-- **机制 K（「常 0」）**：`stepK _ _ _ _ _ := 0`。

**它为什么有用**：`renderND` 的值只有两个可能（`stepL` 或 `stepI`，
见 `renderND` 的 `if` 定义），而 `stepK` **既不是** `stepL` **也不是** `stepI`
（见下面两条定理）。故 `stepK` **不在** `renderND` 的像内——这就是
`renderND_not_surj` 的证明思路。 -/
def stepK : Step nonDegFrame :=
  fun _ _ _ _ _ => 0

/-- **`stepL ≠ stepK`**：在 `x = 0` 处取值分别是 `1` 与 `0`。 -/
theorem stepL_ne_stepK : stepL ≠ stepK := by
  intro h
  have h2 : stepL (0 : Fin 2) PUnit.unit PUnit.unit (0 : Fin 2) (0 : Fin 2)
      = stepK (0 : Fin 2) PUnit.unit PUnit.unit (0 : Fin 2) (0 : Fin 2) := by
    rw [h]
  exact one_ne_zero h2

/-- **`stepI ≠ stepK`**：在 `x = 1` 处取值分别是 `1` 与 `0`。 -/
theorem stepI_ne_stepK : stepI ≠ stepK := by
  intro h
  have h2 : stepI (1 : Fin 2) PUnit.unit PUnit.unit (0 : Fin 2) (0 : Fin 2)
      = stepK (1 : Fin 2) PUnit.unit PUnit.unit (0 : Fin 2) (0 : Fin 2) := by
    rw [h]
  exact one_ne_zero h2

/-- ⭐ **`renderND` 的像不含 `stepK`**：对**任意**规则 `r`，
`renderND r ≠ stepK`。

**证明**：展开 `renderND` 的 `if`，分两支：
- `isLi r` 成立 ⟹ `renderND r = stepL`，用 `stepL_ne_stepK`；
- 否则 ⟹ `renderND r = stepI`，用 `stepI_ne_stepK`。

**⚠ 与前件是否同义反复（纪律 7）**：**无前件**（`r` 是参数不是假设）。
`isLi r` 是**被分情况讨论的**条件，**不是**本定理的前件。
结论 `renderND r ≠ stepK` 需要**两支都成立**，故它**强于**任一分支。 -/
theorem renderND_ne_stepK (r : Rule nonDegCtx nonDegFrame.X nonDegFrame.X) :
    renderND r ≠ stepK := by
  unfold renderND
  by_cases h : isLi r
  · rw [if_pos h]
    exact stepL_ne_stepK
  · rw [if_neg h]
    exact stepI_ne_stepK

/-- ⭐⭐ **`renderND` 不满射**：存在一个机制（`stepK`）不在 `renderND` 的像内。

**这是本文件对「选项甲」最直接的证据**：
`WorldModelCompleteV2` 的 `render_surj` 字段要求 `Surjective render`；
对同一条 `renderND`，该要求**形式化地不成立**。
而 `render_nonconst`（`renderND_nonconst`）**成立**。
**⟹ 把字段换成 `render_nonconst` 后，本实例从「不可能」变成「可能」。**

**⚠ 与前件是否同义反复（纪律 7）**：**无前件**。
结论是 `¬ Function.Surjective renderND`，证明给出**显式反例** `stepK`
与全称否定 `renderND_ne_stepK`——结论**不可**由任何前件平凡得到。 -/
theorem renderND_not_surj : ¬ Function.Surjective renderND := by
  intro hs
  obtain ⟨r, hr⟩ := hs stepK
  exact renderND_ne_stepK r hr

/-- ⭐ **`renderND` 非常函数**：规则集中存在两条规则，其渲染值不同。

**这就是 `WorldModelCompleteV2W.render_nonconst` 字段在本实例上的证据。**

证明：取 `liRule` 与 `idRule`（二者都在 `nonDegRules` 内），
它们的渲染分别是 `stepL` 与 `stepI`，而 `stepL ≠ stepI`。

**⚠ 与前件是否同义反复（纪律 7）**：**无前件**。
结论是 `∃ r₁ ∈ rules, ∃ r₂ ∈ rules, render r₁ ≠ render r₂`；
证明需要 `renderND_liRule` / `renderND_idRule`（把 `if` 算出来）
与 `stepL_ne_stepI`（**实质内容**：`Fin 2` 上 `0 ≠ 1`）。
**不是**把结论塞进前件。 -/
theorem renderND_nonconst :
    ∃ r₁ ∈ nonDegRules, ∃ r₂ ∈ nonDegRules, renderND r₁ ≠ renderND r₂ := by
  refine ⟨liRule, Set.mem_insert _ _, idRule, Set.mem_insert_of_mem _ rfl, ?_⟩
  rw [renderND_liRule, renderND_idRule]
  exact stepL_ne_stepI

/-! ===========================================================================
    §3  阶段 2：**非退化实例** `wmcW : WorldModelCompleteV2W nonDegFrame`
    =========================================================================== -/

/-- **实例的 α 数据**：实例集单点、观测恒空（沿用 `minWMC` 的退化填法）。

**⚠ 诚实标注**：观测恒为空集是**信息量为零**的填法，只为让字段可填，
**不**表示 α 在此做了任何有内容的事（沿用 `WorldModelCompleteV2` 的 U2）。 -/
def wmcWAlpha : AlphaData ⟨PUnit⟩ PUnit where
  obs := fun _ => ∅

/-- **实例的 γ**：恒等映射（相对 `nonDegRuleSpec` 的全关系预序，三条律自动成立）。 -/
def wmcWGamma : GenOp (Rule nonDegCtx nonDegFrame.X nonDegFrame.X) where
  toFun := id
  le_self := fun _ => trivial
  monotone' := fun _ _ _ => trivial
  idempotent' := fun _ => rfl

/-- **实例的 υ**：恒等（不完善任何东西）。 -/
def wmcWUps : UpsilonOperator.Upsilon PUnit (Rule nonDegCtx nonDegFrame.X nonDegFrame.X) :=
  fun _ r => r

/-- **实例的 ∘**：取左操作数（最平凡的复合；沿用 `vCompose` 的登记）。 -/
def wmcWCompose : ComposeOperator.MeasurableRule nonDegCtx nonDegFrame.X nonDegFrame.X →
    ComposeOperator.MeasurableRule nonDegCtx nonDegFrame.X nonDegFrame.X →
    ComposeOperator.MeasurableRule nonDegCtx nonDegFrame.X nonDegFrame.X :=
  fun a _ => a

/-- **实例的误差剖面**：零偏置、零方差（都满足非负公理）。 -/
def wmcWErr : FateV2.Error.Core.ErrProfileWeak where
  bias := fun _ => 0
  var := fun _ => 0
  bias_nonneg := fun _ => le_refl 0
  var_nonneg := fun _ => le_refl 0

/-- **实例的因果 SCM**：`Th := PUnit`，`U := PUnit`，结构映射恒取 `(0, const 0)`。

**注意**：这里与 `minWMC` 的 `vSCM` 不同——`X.Carrier = Fin 2` 有两个元素，
故 `sg` 必须返回 `Fin 2` 的值（取 `0`），而不是 `PUnit.unit`。 -/
def wmcWSCM : ParamSCM.ParamSCM nonDegFrame.X.Carrier nonDegFrame.X.Carrier where
  Th := PUnit
  U := PUnit
  pU := fun _ => 1
  sg := fun _θ _u => (0, fun _ => 0)

/-- **实例的 C6 段依赖对**：`⟨liRule, 属于规则集, renderND liRule = stepL = simulator.step⟩`。

**与 `minWMC` 的 `vStepData` 的区别**：这里第三个分量**不是** `rfl`，
而是 `renderND_liRule.symm`（需要把 `if` 算出来）。
**⟹ 这比全单点帧上的 `rfl` 更有内容。** -/
def wmcWStepData :
    Σ' r : Rule nonDegCtx nonDegFrame.X nonDegFrame.X,
      r ∈ nonDegRules ∧ nonDegSim.step = renderND r :=
  ⟨liRule, Set.mem_insert _ _, renderND_liRule.symm⟩

/-- ⭐⭐ **非退化实例**：`WorldModelCompleteV2W nonDegFrame` 的完整实例，
13 个字段全部填满，且**载体非退化**（`X.Carrier = Fin 2`）。

**本定义是「选项甲可行」的**核心证据**：
- 载体：`nonDegFrame`（`X.Carrier = Fin 2`，**不是**子单点）；
- 规则集：`nonDegRules = {liRule, idRule}`（两条**互异**规则，`liRule_ne_idRule`）；
- 渲染：`renderND`（**非常**，`renderND_nonconst`），且**不满射**（`renderND_not_surj`）；
- 机制取自规则：`nonDegSim.step = renderND liRule`，`liRule ∈ nonDegRules`。

**⚠ 这个实例`不能`是 `WorldModelCompleteV2 nonDegFrame` 的实例**：
那个结构要求 `render_surj : Surjective renderND`，
而 `renderND_not_surj` 说它**不成立**。**这就是二者的实质差别。** -/
def wmcW : WorldModelCompleteV2W nonDegFrame where
  input := ⟨PUnit⟩
  alpha := wmcWAlpha
  gamma := wmcWGamma
  compose := wmcWCompose
  upsilon := wmcWUps
  simulator := nonDegSim
  causal := wmcWSCM
  error := wmcWErr
  sigma := SigmaFromDomain.SigmaSource.unknown
  rules := nonDegRules
  render := renderND
  render_nonconst := renderND_nonconst
  rules_determine_step := wmcWStepData

/-! ===========================================================================
    §4  阶段 3：**实例存在 + 非退化性**
    =========================================================================== -/

/-- **相容性**：`wmcW` 的 `simulator.step` 恰是规则 `liRule` 经 `render` 的值，
且 `liRule` **确实属于** `wmcW.rules`。

**与 `minWMC_step_eq_render`（`rfl` 级）的对比**：本定理的证明用到
`renderND_liRule`（把 `if` 算出来）与 `Set.mem_insert`，**不是** `rfl`。

**⚠ 与前件是否同义反复（纪律 7）**：**无前件**。左端经 `wmcW.simulator` 得 `stepL`，
右端经 `wmcW.render` 的 `if` 计算得 `stepL`——两条**不同路径**。 -/
theorem wmcW_step_eq_render :
    wmcW.simulator.step = wmcW.render liRule ∧ liRule ∈ wmcW.rules :=
  ⟨renderND_liRule.symm, Set.mem_insert _ _⟩

/-- ⭐ **实例存在**（任务书阶段 3 的第一条）。

**⚠ 诚实标注**：结论后半 `True` 是**零信息量**的；
非空性**完全由** `wmcW` 的构造承担。实质内容在 `wmcW_nondeg`。 -/
theorem wmcW_instance_exists :
    ∃ _W : WorldModelCompleteV2W nonDegFrame, True :=
  ⟨wmcW, trivial⟩

/-- ⭐⭐ **非退化性质**（任务书阶段 3 的第二条）：实例 `wmcW` 同时满足

1. 状态空间非退化（`¬ Subsingleton (Fin 2)`）；
2. 规则集含两条互异规则；
3. 渲染**非常**（`render_nonconst` 的字段内容，外化）；
4. 机制取自规则（`simulator.step = render liRule` 且 `liRule ∈ rules`）；
5. 渲染**不满射**（`¬ Surjective render`）——
   **即：本实例满足弱化字段，但不可能满足原 `render_surj` 字段。**

第 5 条是**本文件对 G2 裁决最关键的输出**：它把
「`render_surj` 与「非退化 + 有限规则集」互斥」（`NonDeg` 的 U-A 行，
原为**非形式化论证**）在**同一条具体 `render`** 上**形式化**地体现出来
（⚠ 但**仍不是**完整基数论证，见未完成项 W-F）。

**⚠ 与前件是否同义反复（纪律 7）**：**无前件**。五条结论分别由
`nonDeg_X_not_subsingleton`、`nonDeg_rules_two_distinct`、`renderND_nonconst`、
`wmcW_step_eq_render`、`renderND_not_surj` 给出——
**没有**任何一条出现在本定理的前件里（因为**没有**前件）。 -/
theorem wmcW_nondeg :
    ¬ Subsingleton (Fin 2) ∧
    (∃ r₁ ∈ wmcW.rules, ∃ r₂ ∈ wmcW.rules, r₁ ≠ r₂) ∧
    (∃ r₁ ∈ wmcW.rules, ∃ r₂ ∈ wmcW.rules, wmcW.render r₁ ≠ wmcW.render r₂) ∧
    (wmcW.simulator.step = wmcW.render liRule ∧ liRule ∈ wmcW.rules) ∧
    ¬ Function.Surjective wmcW.render := by
  refine ⟨nonDeg_X_not_subsingleton, nonDeg_rules_two_distinct, ?_,
    wmcW_step_eq_render, renderND_not_surj⟩
  exact renderND_nonconst

/-! ===========================================================================
    §5  未完成项登记（**必须读**：这是本文件的诚实边界）
    =========================================================================== -/

/-!
## 未完成项（据实登记，一个不掩盖）

| # | 未完成项 | 缺什么 |
|---|---|---|
| **W-A** | **`render_nonconst` 本身没有「实质翻译」** | 与 `WorldModelCompleteV2` 的 U1 完全相同：本文件的 `render` 是 `renderND`（按核相等性分两支），**不是**从概率核到确定性机制的真实翻译。本文件**不**声称改好了这一处。 |
| **W-B** | **`render_nonconst` 非常弱** | 它**只**排除「渲染是常函数」。它**不**排除「规则集有 100 条，但渲染只取 2 个值」。若作者认为该字段仍需加强（例如「渲染在规则集上单射」或「像的基数 ≥ 某界」），本文件**不**提供那种更强版本。**这是选项甲可能被否决的理由之一，本文件如实列出。** |
| **W-C** | **`gamma` / `compose` / `upsilon` 仍是退化填法** | `wmcWGamma := id`、`wmcWCompose := 取左`、`wmcWUps := 恒等`。与 `minWMC` / `nonDegFrame` 的登记（U-B / U3 / U6）相同，本文件**不**改进。 |
| **W-D** | **`RuleSpec` 仍取全关系** | 沿用 `nonDegRuleSpec`。规则上的「更一般」预序属 A9／开放问题 8.5，未被作者裁决。故 `GenOp` 三条律在此实例上**几乎无内容**。 |
| **W-E** | **`CtxSpace` 仍取 `⟨PUnit⟩`** | 与 `WorldModelCompleteV2` 的 U4 相同。真上下文（局部域）**未接入**。 |
| **W-F** | **本文件**未**形式化完整的基数论证** | `renderND_not_surj` 只对**这一条** `renderND` 证明了不满射（显式反例 `stepK`）。它**不**证明「**任意**有限规则集上的渲染都难以满射到 `Step`」——那是 `Fate/WorldModelCompleteV2NonDeg.lean` U-A 行的计数论证，本文件**未**形式化（需要 `Fintype (Step nonDegFrame)` 的基数计算，相关 Mathlib 模块在本机检出中缺 `.olean`）。**因此本文件是 U-A 的局部形式化支撑，不是其完整证明。** |
| **W-G** | **`wmcW` 不是「⑦ 交接器已完成」** | 与 `minWMC` 的 U7 相同：六环节之间的其它语义桥（①②、②③、④⑤、⑤⑥）**全部缺失**。本文件**只**在 ③规则 与 ④模拟器 之间有 `rules_determine_step`。 |

## 该文件的证据边界（一句话）

本文件证明的是「**把 `render_surj` 换成 `render_nonconst` 之后，在非退化载体
`Fin 2` 上确实存在一个填满全部字段的实例**」，同时**形式化地**证明了
同一条 `renderND` **不**满射。**这不等于「选项甲被采纳」**——那是作者的裁决。
-/

end

end FateV2.Loop
