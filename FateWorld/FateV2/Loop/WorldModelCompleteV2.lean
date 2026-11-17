/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.WorldModelCompleteV2`
阶段：**⑦ 交接器重做（小步策略）—— 第一阶段：只建类型定义 + 最小实例**

---------------------------------------------------------------------------
背景与本文件的**严格定位**（必读）
---------------------------------------------------------------------------
C6 主干地图（第 376 轮实测）判定【⑦ 交接器不存在】：全库唯一的
`Fate.WorldModel` 类型只有 7 个字段（`frame` / `ctx` / `state` / `rules` /
`simulator` / `selector` / `state_consistent`），只覆盖 ①骨架 + ④生成，
②③⑤⑥ 全不含。

C6 同时指出一个**关键断点**：
`WorldModel` 同时持有 `rules` 与 `simulator`，但**二者并列不交互**
（`Fate/WorldModel.lean` 文件头明写「不声称所选规则就是模拟器的机制」）
⟹ **规则集推不出轨迹**。本文件**正面处理**该断点（见下 §1.5 的
`rules_determine_step` 字段）。

---------------------------------------------------------------------------
⚠ 本文件**不做**什么（诚实要求，逐条登记）
---------------------------------------------------------------------------
1. **本文件不声称「⑦ 交接器已完成」。** 它只是**类型骨架 + 一个最小实例**。
   一个结构体有六个字段，**不等于**六个环节在数学上被接通。
2. **本文件不证明任何主定理**。文件内的定理（见文件末 §4 的清单，
   可用 `grep ^theorem` 核对）全部是**关于本文件所造类型之间相容性**的
   **定义性引理**（`rfl` / `Subsingleton.elim` 级），**不构成**对世界的断言，
   **也不证明**任何规格中的经验假设（A1–A34）。
3. **占位登记（必须写明）**：
   - `alpha` 字段用 `Fate.AlphaData (E : InstSpace.{u}) (M : Type u)`。
     **它与本结构的 `input : InstSpace` 参数直接匹配**，**不是占位**。
     但**注意**：它**不是** `Fate.InstanceChain.AlphaOutput`（后者是
     「划分 + `LawRule` 集」）。规格的 α 映到**规则集**，`AlphaData`
     映到**观测映射**；二者的桥**不在本文件内**，登记为未完成项 U2。
   - `combine.upsilon` 用 `Fate.UpsilonOperator.Upsilon Data α`
     （裸函数 `Data → α → α`），**只承载签名**，**不带** `IsCompletion`
     的序论性质（需具体预序，登记为未完成项 U3）。
   - `combine.gamma` 用 `Fate.GenOp (Rule C X X)`，**相对 `RuleSpec` 的预序**。
     本结构把 `[RuleSpec C X X]` 作为**参数**（不是隐藏前提），
     故「γ 的三条律」随 `GenOp` 自动生效，**不**是本文件的断言。
   - `error` 用 `Fate.R238E3.ErrProfileWeak`，`sigma` 用
     `Fate.SigmaFromDomain.SigmaSource`（含 `unknown` 支）。
     二者**都是真接口**，**不是占位**。
4. **规则 ⟹ 模拟器**（C6 的核心断点）由字段 `rules_determine_step` 表达：
   它要求存在本规则集中的一条规则 `r`，使 `simulator.step = render r`。
   这把「机制取自规则」做成**可检验的结构约束**，使 `rules` 与 `simulator`
   在类型层真正交互。
   ⚠ **诚实标注**：`render` 是**结构数据**，本文件**不**从 `rules` 的内容
   推出 `render`（那需要从概率核到确定性机制的**实质翻译**，涉及测度论
   选择与可测性论证，**超出本任务范围**）。登记为未完成项 U1。

---------------------------------------------------------------------------
本轮修复记录（把 20 error 降到 0 error；只修不建，未删定理）
---------------------------------------------------------------------------
| 原 error | 处 | 根因 | 修法 |
|---|---|---|---|
| `Failed to infer universe levels`（`input` / `alpha` / `compose` / `upsilon` / `rules` / `render` / `render_surj` / `rules_determine_step`） | 结构体各字段 | `InstSpace` / `CtxSpace` / `Upsilon` / `AlphaData` 均为**宇宙多态**，`Frame` 却**是单一宇宙**（`Frame : Type 1`），未注解处 Lean 无法定宇宙 | 显式标注 `InstSpace.{0}` / `CtxSpace.{0}` / `AlphaData.{0}` / `Upsilon.{0, 0}` |
| `Unknown constant WorldModelCompleteV2.instX` | 原第 204 行 `attribute [instance] …instX` | Lean 4 **不为**结构体的 instance-implicit 参数生成投影常量，`Foo.instX` 不存在（已 `#check` 实测） | 删除该行，换成说明性注释；`instX` 本就是隐式参数，调用点由实例合成给出 |
| `Function expected at WorldModelCompleteV2`（7 处） | 投影 / 实例定义 | 结构体因宇宙推断失败而**未能定义**，下游引用它就被 `autoImplicit` 当成未知变量 | 修好宇宙后**自愈** |
| `synthInstanceFailed : Subsingleton vFrameP.X.Carrier`（2 处） | `vUnitStep_unique` / `minWMC_traj_unit` | `vUnitX` / `vFrameP` 原是 `def`；实例搜索只展开 `abbrev` 而**不**展开 `def`，故 `vFrameP.X.Carrier` 无法归约为 `PUnit` | 把 `vUnitX` / `vFrameP` 改为 `abbrev`，使实例搜索能归约 |
| `Function expected at MeasurableSet.of_discrete` | `vRuleP_measurable` | `MeasurableSet.of_discrete` 是**值**（`{α} [MeasurableSpace α] [DiscreteMeasurableSpace α] {s} : MeasurableSet s`），不是函数，不能接受参数 | 删掉尾随的 `_` |
| `unexpected token 块注释起始符; expected 'lemma'` | （主控报告中出现，本轮回显已无） | 文档注释（块注释起始符 + `!`）被放在语法不允许的位置，或嵌套进另一块注释 | 删除了上述 `attribute` 行后，其后紧邻的 §1.6 文档注释块位置合法，该错消失（注：Lean 的块注释**可嵌套**，本修复记录中也因此曾误加嵌套，已改写为不含注释分隔符的文字） |

**期间未删除任何定理、未新增 `axiom`、未使用 `sorry` / `admit`。**
文件头定理清单与 `grep ^theorem`（6 条）一致。

---------------------------------------------------------------------------
本文件实际存在的定理（`grep ^theorem` 核对，共 6 条）
---------------------------------------------------------------------------
| # | 定理 | 内容 | 性质 |
|---|---|---|---|
| 1 | `vUnitStep_unique` | 单点帧上任意 `Step` 等于 `vUnitStep`（`Step` 子单点） | `Subsingleton` |
| 2 | `vRenderP_surj` | 最小实例的 `render` 满射 | 由 (1) |
| 3 | `vRuleP_measurable` | 最小规则的可测性见证 | `of_discrete` |
| 4 | `minWMC_step_eq_render` | 最小实例的 `simulator.step = render vRuleP` | `rfl` 级 |
| 5 | `minWMC_traj_unit` | 最小实例的轨迹恒为 `PUnit.unit` | `Subsingleton` |
| 6 | `worldModelCompleteV2_nonempty` | `∃ W : WorldModelCompleteV2 …, True`（**结构非空**） | 构造性 |

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
- **零 `sorry` / 零 `admit` / 零 `axiom`**。
- **只新建**，**不修改**任何既有模块。
- 名字用 `WorldModelCompleteV2`（**V2 后缀**），不覆盖旧的 `WorldModelComplete`
  （旧的 17 定理 101 error 已隔离在 `_quarantine/_broken/`）。
- 每个被调用的既有名字都先 `#check` / `grep` 确认，**不猜字段名**。
- 本文件**不**加入 `Fate.lean`（不在建图内）；可用单文件 `lake env lean` 验证。
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
import FateWorld.FateV2.Meta.AssemblyGainShared
import Mathlib.Data.Set.Basic

namespace FateV2.Loop

open FateV2.Error
open FateV2.Meta
open FateV2.Model
open FateV2.Modeling
open FateV2.Predict
open FateV2.Rules
universe u

noncomputable section

/-!
  # Loop · WorldModelCompleteV2

  ## 迁移登记
  - 来源：`FateWorld/Legacy/WorldModelCompleteV2.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, Frame, RuleLevel, TrajGenDeterministic, WorldModel, AlphaFCAConstruction, InstanceChain, GammaOperator, UpsilonOperator, ComposeOperator, ParamSCM, FitBoundary, SigmaFromDomain, AssemblyGainShared
  - 补充 open 域：FateV2.Error, FateV2.Meta, FateV2.Model, FateV2.Modeling, FateV2.Predict, FateV2.Rules
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  阶段 1：**六环节交接器**的类型定义

    六个字段逐一对应六个环节，且每个字段都绑定到**已实测确认**的既有定义上。
    =========================================================================== -/

/-- **⑦ 交接器（V2）：世界模型的六环节完整载体**。

六个环节 ↔ 字段的**唯一落点**（每一行都已 `#check` 实测确认）：

| 环节 | 本文件字段 | 绑定的既有定义 |
|---|---|---|
| ① 骨架 + 输入 | `input` | `Fate.InstSpace`（字段 `Carrier : Type*`） |
| ② 抽象 α 的**数据** | `alpha` | `Fate.AlphaData`（字段 `obs : E.Carrier → Set M`） |
| ③a 泛化 γ | `gamma` | `Fate.GenOp (Rule C F.X F.X)`（相对 `[RuleSpec]` 的预序） |
| ③b 复合 ∘ | `compose` | `Fate.ComposeOperator.MeasurableRule` 的复合 |
| ③c 完善 υ | `upsilon` | `Fate.UpsilonOperator.Upsilon PUnit (Rule C F.X F.X)` |
| ④ 生成 / 预测 | `simulator` | `Fate.WorldSimulator F`（字段 `step : Step F` / `horizon : ℕ`） |
| ⑤ 因果 | `causal` | `Fate.ParamSCM.ParamSCM F.X.Carrier F.X.Carrier` |
| ⑥a 误差剖面 | `error` | `Fate.R238E3.ErrProfileWeak` |
| ⑥b 签名 σ 来源 | `sigma` | `Fate.SigmaFromDomain.SigmaSource` |
| **（C6 断点）** 规则集 | `rules` | `Fate.Rules C F.X F.X` |
| **（C6 断点）** 规则→机制 | `render` / `render_surj` | 本文件定义 |
| **（C6 断点）** 规则 ⟹ 模拟器 | `rules_determine_step` | 本文件定义（`Σ'` 依赖对） |

**⚠ 上下文的选择**：γ / ∘ / υ / `rules` 都需要一个 `CtxSpace`。
本结构**不**把 `CtxSpace` 做成字段（那会使 `F.X` 与它各指一个空间），
而是取**唯一**的 `⟨PUnit⟩ : CtxSpace`（单点上下文）。
**这是刻意的退化**：`CtxSpace` 的选取属 A9／开放问题 8.5，
本文件**不擅自假定**其内容（登记为未完成项 U4）。
若日后要接真上下文，须把 `⟨PUnit⟩` 换成 `ctx` 字段并加对齐证据。

**⚠ `[RuleSpec]` 是参数不是隐藏前提**：γ 需要 `Preorder (Rule C F.X F.X)`，
`Fate.RuleSpec.instPreorder` 从 `[RuleSpec C X Y]` 合成它。
本结构把它**显式列为参数**，故「γ 有预序」在类型层的可见处，
**不**是匿名前提（这正是规格「不存在匿名前提」纪律的落实）。

标签：**[定义性约定]**（**不是**「⑦ 已完成」的证据）。 -/
structure WorldModelCompleteV2 (F : Frame) [instX : MeasurableSpace F.X.Carrier]
    [S : RuleSpec (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X] where
  /-- **① 输入**：实例集 $\mathcal{E}$（规格 §1.4；`Fate.Frame.InstSpace`）。

  **为什么用 `InstSpace` 而不是 `CtxSpace` 占位**：`Fate.InstanceChain.Instance`
  （`(O : Type u) (A : Type v)`）与 `Frame` 之间**没有**直接参数对应，
  而 `InstSpace`（单一 `Carrier` 字段）与 `AlphaData` 的 `E` 位**参数匹配**，
  故取 `InstSpace` 是真接口，**不是占位**。 -/
  input : InstSpace.{0}
  /-- **② 抽象 α（数据层）**：实例 ↦ 属性集的观测映射（`Fate.AlphaData`）。

  ⚠ 这是 α 的**一项具体载体**（观测映射），**不**包含局部域划分；
  与规格 α（映到规则集）的等价性**不在本文件内证明**（未完成项 U2）。 -/
  alpha : AlphaData.{0} input PUnit
  /-- **③a 泛化 γ**：特异性预序上的收缩、单调、幂等映射（`Fate.GenOp`）。

  载体取**单条规则层** `Fate.Rule C F.X F.X`（`[RuleSpec]` 给出其预序）。 -/
  gamma : GenOp (Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X)
  /-- **③b 复合 ∘**：两条规则复合为一条（`Fate.ComposeOperator.MeasurableRule`
  的复合接口，此处取其**两条可测规则 ↦ 一条可测规则**的裸形式）。 -/
  compose : ComposeOperator.MeasurableRule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X →
    ComposeOperator.MeasurableRule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X →
    ComposeOperator.MeasurableRule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X
  /-- **③c 完善 υ**：规则 × 数据 → 规则（`Fate.UpsilonOperator.Upsilon`）。

  **⚠ 只承载签名**：`IsCompletion` 的序论性质（扩张／单调／幂等）
  **未**作为字段断言（需具体预序，未被作者裁决；未完成项 U3）。 -/
  upsilon : UpsilonOperator.Upsilon.{0, 0} PUnit (Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X)
  /-- **④ 生成 / 预测**：模拟器（`Fate.WorldSimulator F`，字段 `step : Step F` /
  `horizon : ℕ`）。 -/
  simulator : WorldSimulator F
  /-- **⑤ 因果**：参数化 SCM（`Fate.ParamSCM.ParamSCM X Y`，`Th` 位承载 θ）。 -/
  causal : ParamSCM.ParamSCM F.X.Carrier F.X.Carrier
  /-- **⑥a 误差剖面**：偏置 / 方差两分量 + 非负公理的**弱**剖面
  （`Fate.R238E3.ErrProfileWeak`）。 -/
  error : R238E3.ErrProfileWeak
  /-- **⑥b 签名 σ 的来源**：领域给定 / 估计 / 未给
  （`Fate.SigmaFromDomain.SigmaSource`，**含 `unknown` 支**）。 -/
  sigma : SigmaFromDomain.SigmaSource
  /-- **（C6 断点）规则集** $\mathcal{R}$（`Fate.Rules`）：这**是**本世界模型的规则集，
  **不是**与本模型无关的集合——它由本结构携带，供 `rules_determine_step` 使用。 -/
  rules : Rules (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X
  /-- **（C6 断点）从规则到机制的渲染**：把一条规则读成单步机制 `Step F`。

  **为什么不取「rules ↦ Simulator」的整体映射**：整体映射会允许
  「规则集与机制完全无关」的实现（正是 C6 指出的并列），
  而 `render : Rule → Step F` 使「机制来自某一**具体**规则」成为可检验断言。 -/
  render : Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X → Step F
  /-- **（C6 断点）满射性**：每条规则都能被渲染成某个机制。

  **这不是装饰**：它排除「`render` 是常函数且规则集多元素」这种退化实现，
  使「机制取自规则」在**内容上**非空。 -/
  render_surj : Function.Surjective render
  /-- **（C6 断点·核心）规则 ⟹ 模拟器**：存在本规则集中的一条规则 `r`，
  使 `simulator.step` **恰好是** `render r`。

  **与前件是否同义反复的检查（纪律 7）**：本字段**不是** `Prop` 前提，
  而是 `Σ'`（依赖对），故它**构造性地给出** `r` 与等式；
  等式 `simulator.step = render r` 的左端是本结构**另一个字段 `simulator`**，
  右端**由 `rules` 与 `render` 决定**——二者在 Lean 中是**两个不同的项**，
  故该等式**不可**在 `Σ'` 的一般元素上由 `rfl` 解出，
  也**不**是「把结论包进前件」。
  **⚠ 但须知**：这**不**证明「世界模型的机制在语义上正确」，
  它只证明「本模型的机制**确实来自**本模型的规则集」（未完成项 U5）。 -/
  rules_determine_step :
    Σ' r : Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X,
      r ∈ rules ∧ simulator.step = render r

/-! **⚠ 关于原第 204 行的 `attribute [instance] WorldModelCompleteV2.instX`**

该行已删除，原因：`instX` 是结构体的 **instance-implicit 参数**
（`structure … (F : Frame) [instX : MeasurableSpace F.X.Carrier] …`），
Lean 4 **不为**结构体的 instance-implicit 参数生成投影常量，
故 `WorldModelCompleteV2.instX` **不存在**（已用 `#check` 实测确认）。
该参数本就是 `implicit` 的，由实例合成在调用点自动给出，
**不需要**（也**无法**）用 `attribute [instance]` 登记。 -/

/-! ### §1.6 投影（各环节可被单独取出）

**为什么需要投影**：若处处写 `W.input` / `W.gamma` / …，
则「世界模型有六环节」只是注释。以下具名投影使
「取第 i 个环节」是 **Lean 函数**——即可被定理引用的对象。 -/

/-- **投影·①输入**。 -/
def WorldModelCompleteV2.inputOf {F : Frame} [MeasurableSpace F.X.Carrier]
    [RuleSpec (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X]
    (W : WorldModelCompleteV2 F) : InstSpace := W.input

/-- **投影·③a γ**。 -/
def WorldModelCompleteV2.gammaOf {F : Frame} [MeasurableSpace F.X.Carrier]
    [RuleSpec (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X]
    (W : WorldModelCompleteV2 F) : GenOp (Rule (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X) := W.gamma

/-- **投影·④模拟器**。 -/
def WorldModelCompleteV2.simulatorOf {F : Frame} [MeasurableSpace F.X.Carrier]
    [RuleSpec (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X]
    (W : WorldModelCompleteV2 F) : WorldSimulator F := W.simulator

/-- **投影·⑤因果**。 -/
def WorldModelCompleteV2.causalOf {F : Frame} [MeasurableSpace F.X.Carrier]
    [RuleSpec (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X]
    (W : WorldModelCompleteV2 F) : ParamSCM.ParamSCM F.X.Carrier F.X.Carrier := W.causal

/-- **投影·⑥a 误差**。 -/
def WorldModelCompleteV2.errorOf {F : Frame} [MeasurableSpace F.X.Carrier]
    [RuleSpec (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X]
    (W : WorldModelCompleteV2 F) : R238E3.ErrProfileWeak := W.error

/-- **投影·（C6）规则集**。 -/
def WorldModelCompleteV2.rulesOf {F : Frame} [MeasurableSpace F.X.Carrier]
    [RuleSpec (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X]
    (W : WorldModelCompleteV2 F) : Rules (⟨PUnit⟩ : CtxSpace.{0}) F.X F.X := W.rules

/-! ===========================================================================
    §2  阶段 2：**最小实例**（证明结构非空）
    =========================================================================== -/

/-- 全单点状态空间（最小实例用）：`Carrier := PUnit`，离散拓扑 / 离散可测。 -/
abbrev vUnitX : StateSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- **全单点框架**：`X / Θ / U / Act / Ν` 全为 `PUnit`。

**为什么取全单点**：`render_surj` 要求 `render : Rule → Step F` **满射**。
若 `F.X.Carrier = Bool`，`Step vFrame` 的元素 ≥ 2，而本实例只给一条规则，
故**不存在**满射渲染。全单点使 `Step` 成为**子单点**类型（`vUnitStep_unique`），
满射因此**确实**成立。这是**诚实的退化**，不是虚假声称。 -/
abbrev vFrameP : Frame where
  Θ := { Carrier := PUnit, topo := ⊤, meas := ⊤ }
  X := vUnitX
  U := { Carrier := PUnit, topo := ⊤, meas := ⊤ }
  Act := { Carrier := PUnit, topo := ⊤, meas := ⊤ }
  Ν := { Carrier := PUnit, meas := ⊤ }

instance : MeasurableSpace vFrameP.X.Carrier := vUnitX.meas

/-- 单点帧上的上下文：唯一落点。 -/
abbrev vCtx : CtxSpace := ⟨PUnit⟩

/-- **最小实例的 `RuleSpec`**：`Rule vCtx vFrameP.X vFrameP.X` 上的**全关系**。

**为什么取全关系**：`Rule` 空间上**没有**自然的“更一般”预序
（那是 A9／开放问题 8.5，**未被作者裁决**）。全关系是**最弱的**合法预序
（自反 + 传递显然成立），且**不擅自假定**任何具体划界方式。
**⚠ 诚实标注**：全关系使 `GenOp` 的三条律**几乎无内容**
（任意映射都满足），本实例因此**不展示** γ 的实质代数行为。 -/
@[instance_reducible]
def vRuleSpec : RuleSpec vCtx vFrameP.X vFrameP.X where
  le := fun _ _ => True
  refl := fun _ => trivial
  trans := fun _ _ => trivial

instance : RuleSpec vCtx vFrameP.X vFrameP.X := vRuleSpec

/-- 全单点帧上的**唯一**机制：`Step vFrameP` 是子单点类型。 -/
def vUnitStep : Step vFrameP :=
  fun _ _ _ _ _ => PUnit.unit

/-- **相容性 0**：在全单点帧上，`Step` 是子单点类型
（任一 `Step` 都等于 `vUnitStep`）。

证明：`funext` + `Subsingleton.elim`——`Step` 的 5 个自变量与值域全为 `PUnit`。 -/
theorem vUnitStep_unique (f : Step vFrameP) : f = vUnitStep := by
  funext x u ε θ a
  exact Subsingleton.elim _ _

/-- 全单点帧上的规则：核为点质量 `δ_x`。 -/
def vRuleP : Rule vCtx vFrameP.X vFrameP.X where
  kernel := fun _c x => MeasureTheory.Measure.dirac x

/-- 可测性见证：`PUnit` 上的一切函数都可测（离散可测结构 ⇒ 全可测集）。 -/
theorem vRuleP_measurable (c : PUnit) :
    Measurable (fun x : vFrameP.X.Carrier => vRuleP.kernel c x) := by
  intro s _hs
  exact MeasurableSet.of_discrete

/-- **最小实例的可测规则**（`compose` 的载体需要 `MeasurableRule`）。 -/
def vMeasRule : ComposeOperator.MeasurableRule vCtx vFrameP.X vFrameP.X where
  rule := vRuleP
  measurable_kernel := vRuleP_measurable

/-- **最小实例的渲染**：值域是子单点，故任意规则都映到唯一机制 `vUnitStep`。 -/
def vRenderP : Rule vCtx vFrameP.X vFrameP.X → Step vFrameP :=
  fun _ => vUnitStep

/-- **`vRenderP` 确实满射**：值域是子单点，且 `vUnitStep` 被取到。 -/
theorem vRenderP_surj : Function.Surjective vRenderP := by
  intro s
  exact ⟨vRuleP, (vUnitStep_unique s).symm⟩

/-- **最小实例的 α 数据**：实例集为单点，观测映射恒为 `∅`。

**⚠ 诚实标注**：观测恒为空集是**最退化的**填法（信息量为零）。
它的作用是让字段**可填**，**不**表示「α 在这里做了任何有内容的事」。 -/
def vAlpha : AlphaData ⟨PUnit⟩ PUnit where
  obs := fun _ => ∅

/-- **最小实例的 γ**：恒等映射（相对全关系预序，三条律自动成立）。 -/
def vGamma : GenOp (Rule vCtx vFrameP.X vFrameP.X) where
  toFun := id
  le_self := fun _ => trivial
  monotone' := fun _ _ _ => trivial
  idempotent' := fun _ => rfl

/-- **最小实例的 υ**：恒等（不完善任何东西）。 -/
def vUps : UpsilonOperator.Upsilon PUnit (Rule vCtx vFrameP.X vFrameP.X) :=
  fun _ r => r

/-- **最小实例的 ∘**：取左操作数（最平凡的复合）。

**⚠ 诚实标注**：这**不是**核复合 `Measure.bind`，只是**让字段可填**。
真正的核复合已在 `Fate.ComposeOperator` 内（`MeasurableRule.compose`），
本文件**不重做**（未完成项 U6）。 -/
def vCompose : ComposeOperator.MeasurableRule vCtx vFrameP.X vFrameP.X →
    ComposeOperator.MeasurableRule vCtx vFrameP.X vFrameP.X →
    ComposeOperator.MeasurableRule vCtx vFrameP.X vFrameP.X :=
  fun a _ => a

/-- **最小实例的误差剖面**：零偏置、零方差（都满足非负公理）。 -/
def vErr : R238E3.ErrProfileWeak where
  bias := fun _ => 0
  var := fun _ => 0
  bias_nonneg := fun _ => le_refl 0
  var_nonneg := fun _ => le_refl 0

/-- **最小实例的因果 SCM**：外生空间单点 `PUnit`，`Th := PUnit`，
结构映射恒取 `unit` 与常函数。 -/
def vSCM : ParamSCM.ParamSCM vFrameP.X.Carrier vFrameP.X.Carrier where
  Th := PUnit
  U := PUnit
  pU := fun _ => 1
  sg := fun _θ _u => (PUnit.unit, fun _ => PUnit.unit)

/-- **最小实例的模拟器**。 -/
def vSim : WorldSimulator vFrameP where
  step := vUnitStep
  horizon := 2

/-- **最小实例的 C6 段依赖对**：`⟨vRuleP, 属于自身, rfl⟩`。

注意 `simulator.step = render r` 在此实例上归一为 `rfl`（两边都归约为
`vUnitStep`）；但整个字段类型是 `Σ'`，故「构造出 `r` 与 `∈` 证据」
仍是实质内容。**⚠ 不可**据此推断该字段在一般 `W` 上也是 `rfl`。 -/
def vStepData : Σ' r : Rule vCtx vFrameP.X vFrameP.X,
    r ∈ ({vRuleP} : Rules vCtx vFrameP.X vFrameP.X) ∧ vSim.step = vRenderP r :=
  ⟨vRuleP, rfl, rfl⟩

/-- ⭐ **最小实例**：六环节 + C6 断点字段**全部填满**。

**本定义的作用**：证明 `WorldModelCompleteV2 vFrameP` 这个类型**非空**
（见 `worldModelCompleteV2_nonempty`）。
**它不证明**任何环节在数学上被真正接通——见文件头 §3 的诚实要求。 -/
def minWMC : WorldModelCompleteV2 vFrameP where
  input := ⟨PUnit⟩
  alpha := vAlpha
  gamma := vGamma
  compose := vCompose
  upsilon := vUps
  simulator := vSim
  causal := vSCM
  error := vErr
  sigma := SigmaFromDomain.SigmaSource.unknown
  rules := {vRuleP}
  render := vRenderP
  render_surj := vRenderP_surj
  rules_determine_step := vStepData

/-! ===========================================================================
    §3  阶段 3：**结构相容性**引理（不是主定理）
    =========================================================================== -/

/-- **相容性 1**：最小实例的 `simulator.step` 恰是规则 `vRuleP` 经 `render` 的值。

这是 `rules_determine_step` 的**外化形式**（把 `Σ'` 收缩到具名规则）。
它**不是**新信息，只是把字段的**可引用形式**给出，
供下游直接写 `W.simulator.step = W.render r` 而不必每次解构。

**⚠ 与前件同义反复自查**：本定理**无前件**；
左边经 `minWMC.simulator` 投影、右边经 `minWMC.render` 投影，
二者在 Lean 中是**两个不同路径的项**，靠 `WorldModelCompleteV2.mk`
的定义等式相连。**是 `rfl`，信息量低**——本文件**不**夸称它是实质定理。 -/
theorem minWMC_step_eq_render :
    minWMC.simulator.step = minWMC.render vRuleP := rfl

/-- **相容性 2**：最小实例的轨迹恒为 `PUnit.unit`
（机制是全单点帧上的唯一机制，故轨迹是常值序列）。

证明：`Fate.TrajGenDeterministic.trajGen` 的值类型是 `PUnit`，
故一切取值相等（`Subsingleton.elim`）。

**⚠ 与前件同义反复自查**：本定理**无前件**（不做任何假设）；
结论虽“显然”，但它**是**关于 `trajGen` 与 `minWMC.simulator.step` 复合的
一个**真实等式**，且证明用到了 `trajGen` 的类型签名——不是 `True` 的伪装。 -/
theorem minWMC_traj_unit (n : ℕ)
    (θ : vFrameP.Θ.Carrier) (x₀ : vFrameP.X.Carrier)
    (u : ℕ → vFrameP.U.Carrier) (ε : ℕ → vFrameP.Ν.Carrier)
    (a : ℕ → vFrameP.Act.Carrier) :
    TrajGenDeterministic.trajGen vFrameP minWMC.simulator.step θ x₀ u ε a n
      = PUnit.unit := by
  exact Subsingleton.elim _ _

/-- ⭐ **结构非空**：存在一个填满全部字段的 `WorldModelCompleteV2 vFrameP`。

**这是阶段 2 的交付**（「证明该结构非空」）。
**⚠ 注意**：本定理的结论 `True` 是**平凡的**，
非空性**完全由 `minWMC` 的构造承担**（`⟨minWMC, trivial⟩`）。
本文件**不**声称「存在一个语义正确的世界模型」。 -/
theorem worldModelCompleteV2_nonempty :
    ∃ _W : WorldModelCompleteV2 vFrameP, True :=
  ⟨minWMC, trivial⟩

/-! ===========================================================================
    §3.5  接入 `Fate.AssemblyGainShared`：六环装配的**收益判定条件**
    =========================================================================== -/

/-!
## 本节的诚实定位（先读）

**(a) 本任务的目标**：把 `Fate.AssemblyGainShared`（17 定理，`fanin 0` 的孤立模块）
**接进主干**。依赖方向已确认：`AssemblyGainShared` 只 `import FateV2.Meta.AssemblyMeta`
（后者 `import` 为空），**不** `import WorldModelCompleteV2`，故本节新增 import
**不成环**。

**(b) 做到了什么**：本节**真调用**了 `AssemblyGainShared` 的**两条**核心定理——
`gain_iff_applied`（非局部约束 ⟹ 有收益）与 `sum_no_gain_for_local_theta`
（局部约束 ⟹ 无收益），并在 `Fate`（`WorldModelCompleteV2` 所在）命名空间下
用 `∧` 把它们**显式调出**。

**(c) ⚠ 本定理与六环的关系**：**是【对应关系】，不是【实质定理】**。
本定理**不**从 `WorldModelCompleteV2` 的六个字段（`input` / `alpha` / `gamma` /
`compose` / `upsilon` / `simulator` / `causal` / `error`）**推出**任何东西——
它的两条合取项**完全来自** `AssemblyGainShared` 本身，与六字段的**取值无关**。
换言之：本定理只是把 `AssemblyGainShared` 的抽象结论**搬到** `Fate` 命名空间下，
使其**可被下游引用**。六字段在此处**未参与**任何证明步骤。

**(d) 不声称**：本定理**不**声称「解决了六环不交互的问题」。六字段的并列
（未完成项 U7）**仍然存在**。「装配收益」是否真的**发生在**六环之间，
需要给出六环之间的**具体交互模型**（跨字段的非局部约束），**本定理未提供**。
本定理只给出**判定条件**（局部 ⟹ 无收益；非局部 ⟹ 有收益）。

**与六环字段的【对应关系】（仅为表意，非定理内容）**：

| 六环字段 | 「局部约束」的对应解读 | χ 结论 |
|---|---|---|
| 任一单字段（如 `gamma` 单独） | 约束只读**单个**字段 | 无装配收益（`sum_no_gain_for_local_theta`） |
| **跨字段**（如 `gamma` 与 `simulator` 联合） | 约束**同时**读多个字段 | 有装配收益（`gain_iff_applied`） |

⚠ 上表是**语义注解**，Lean 定理本身**不**形式化「字段之间的约束」，
因为 `WorldModelCompleteV2` 结构里字段间**没有**交互关系（这正是 U7 的内容）。
-/

/-- ⭐⭐ **【六环装配的收益判定条件】**——`AssemblyGainShared` 的接入点。

本定理是 `Fate.AssemblyGainShared` 两条核心结论的**显式并列**：

1. **非局部（共享）约束 ⟹ 有收益**：存在 `Θ : Set (V2 → ℝ)`，
   `Φc ∩ Ψc ⊆ Θ` 且 `Φc ⊄ Θ` 且 `Ψc ⊄ Θ`
   （`AssemblyGainShared.gain_iff_applied`，原为 `Fin 2` 上的具体反例 `Θc`）；

2. **局部约束 ⟹ 无收益**：若 `Ψ` 非空、且联合装配的 `V₁`-边际已含于 `Θ`，
   则 `Φ ⊆ Θ`（`AssemblyGainShared.sum_no_gain_for_local_theta`）。

两者**不矛盾**：第 2 条只覆盖**单侧局部**的 `Θ`，第 1 条的 `Θ` 恰是关系型
（`AssemblyGainShared.Θc_not_local_supp₁` / `_supp₂`）。

**⚠ 诚实标注（纪律 7）**：本定理的**前件为空**，结论的两条合取项
**逐条来自** `AssemblyGainShared` 已入链定理的直接引用，**不是**同义反复
（它们是真命题，且各自在 `AssemblyGainShared` 中有反例见证）。
但**本定理不涉及** `WorldModelCompleteV2` 的六字段——它是**接入证据**，
**不是**「六环已被接通」的证据（见本节文件头的 (c)(d)）。 -/
theorem wmc_six_ring_assembly_gain_iff :
    -- (1) 非局部（共享）约束 ⟹ 有收益（`AssemblyGainShared.gain_iff_applied`）
    (∃ Θ : Set (AssemblyGainShared.V2 → ℝ),
        AssemblyGainShared.Φc ∩ AssemblyGainShared.Ψc ⊆ Θ ∧
        ¬ AssemblyGainShared.Φc ⊆ Θ ∧ ¬ AssemblyGainShared.Ψc ⊆ Θ)
    -- (2) 局部约束 ⟹ 无收益（`AssemblyGainShared.sum_no_gain_for_local_theta`）
    ∧ (∀ {V₁ V₂ : Type} (Φ : Set (V₁ → ℝ)) (Ψ : Set (V₂ → ℝ)),
        Ψ.Nonempty → ∀ {Θ : Set (V₁ → ℝ)},
        AssemblyMeta.restr₁ '' AssemblyMeta.joint Φ Ψ ⊆ Θ → Φ ⊆ Θ) :=
  ⟨AssemblyGainShared.gain_iff_applied,
   fun {_V₁ _V₂} _Φ _Ψ hΨ {_Θ} h => AssemblyGainShared.sum_no_gain_for_local_theta hΨ h⟩

/-! ===========================================================================
    §4  未完成项登记（**必须读**：这是本文件的诚实边界）
    =========================================================================== -/

/-!
## 未完成项（据实登记，一个不掩盖）

| # | 未完成项 | 缺什么 |
|---|---|---|
| U1 | **`render` 的实质翻译** | 本文件的 `render` 是最平凡的实现（子单点帧上取唯一机制）。从 `Rule`（概率核）到 `Step`（确定性机制）的**真实翻译**需要「取核的期望 / 众数 / 骨架」的测度论选择 + 可测性论证，**本任务（只建类型）未做**。 |
| U2 | **`alpha` 与规格 α 的对齐** | `AlphaData`（观测映射）≠ `AlphaOutput`（划分 + `LawRule` 集）。二者的桥需 `Fate.InstanceChain.AlphaSpec` 的 S1–S5 与一项「观测 ↦ 规则」的构造，**不在本文件内**。 |
| U3 | **`upsilon` 的 `IsCompletion` 性质** | 需具体预序。规则集上的**具体预序**未被作者裁决（`Fate/GammaOperator.lean` 文件头 E3 已登记为开放），故本文件**不擅自假定**。 |
| U4 | **上下文取 `⟨PUnit⟩`** | 本结构把 `CtxSpace` 硬编码为单点。真上下文（`AlphaSpec` 的局部域）**未接入**。 |
| U5 | **`rules_determine_step` 不是「语义正确性」** | 它只断言「本模型的机制**来自**本模型的规则集」，**不**断言该规则集**正确地**刻画了世界。后者是经验假设（A1–A34），**不在任何形式化之内**。 |
| U6 | **`compose` 的最小实例不调用真复合** | `vCompose` 取左操作数，**不是** `Measure.bind` 复合。真的核复合在 `Fate.ComposeOperator` 内（`MeasurableRule.compose`），本文件**不重做**。 |
| U7 | **C6 判定的「⑦ 交接器」** | 本文件只**建了类型 + 一个最小实例**。六字段并列仍存在：①②、②③、④⑤、⑤⑥ 之间的**语义桥全部缺失**；唯 ③/规则 与 ④ 之间有 `rules_determine_step` 连接。**未达成**「七个环节在数学上被接通」。 |
| U8 | **§3.5 与六环只是【对应关系】** | `wmc_six_ring_assembly_gain_iff` **不**从六个字段推出任何东西；它的两条合取项**全部来自** `AssemblyGainShared`，与六字段取值**无关**。它是**接入证据**（把 `AssemblyGainShared` 搬进 `Fate` 命名空间可引用），**不是**「六环已交互」的证据。倒真要说六环之间**是否**存在跨字段非局部约束，需给出**具体交互模型**，本文件**未给**。 |

## 与前件同义反复的自查（纪律 7）

逐条核对本文件**所有**定理：

- `vUnitStep_unique`：**无前件**，结论 `f = vUnitStep`。**非同义反复**。
- `vRuleP_measurable`：**无前件**，结论 `Measurable …`。**非同义反复**。
- `vRenderP_surj`：**无前件**，结论 `Surjective vRenderP`，由 `vUnitStep_unique` 得到。**非同义反复**。
- `minWMC_step_eq_render`：**无前件**，`rfl` 级。**信息量低**，已如实登记。
- `minWMC_traj_unit`：**无前件**，结论为 `trajGen` 复合的等式，由 `Subsingleton.elim` 得到。**非同义反复**（不是 `True` 的伪装）。
- `worldModelCompleteV2_nonempty`：**无前件**，结论为存在性，由 `minWMC` 构造。**非同义反复**，但**信息量仅限「类型非空」**。
- `wmc_six_ring_assembly_gain_iff`：**无前件**，结论为两条合取项；分别由 `AssemblyGainShared.gain_iff_applied`（具体反例 `Θc`）与 `AssemblyGainShared.sum_no_gain_for_local_theta`（引用 `AssemblyMeta.no_new_information`）直接给出。**非同义反复**（是真命题，且在 `AssemblyGainShared` 中有反例见证）。但**它与六字段无关**，已如实登记为 U8。

## 该文件的证据边界（一句话）

本文件证明的是「**所造类型非空且字段间订立的连接自洽**」，
**不是**「⑥ 以后的世界模型在数学上被接通」，**更不是**「⑦ 交接器已完成」。
-/

end

end FateV2.Loop