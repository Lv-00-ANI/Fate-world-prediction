import FateWorld.FateV2.Modeling.PearlHierarchy
import FateWorld.FateV2.Modeling.SCMSemantics
import FateWorld.FateV2.Predict.WorldModel
import FateWorld.FateV2.Model.TrajGenDeterministic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ParamSCM.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-009 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Predict（正文 9 处，含 4 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Model
open FateV2.Modeling
open FateV2.Predict

/-
命运理论 · Lean 4 形式化实现
========================================================

模块：`FateV2.Predict.ParamSCM`
定位：**T-1b 的正向突破 —— 给 SCM 加上参数空间 `Th`，使 `Θ` 不再退化**

---------------------------------------------------------------------------
〇、本文件要解决的确切障碍（第 155–157 轮的诊断）
---------------------------------------------------------------------------
`FateV2.Predict/SCMWorldModel.lean:213` 的 `scmThetaSpace : ThetaSpace where
Carrier := PUnit` —— 参数空间是**单点**。因此 `:252` 的 `scmWorldStep`
定义为 `fun _y u _ε _θ a => (M.sg u).2 a`，**丢弃 `θ` 是必然**：
`PUnit` 只有一个元素，不可能有别的写法。根因在
`FateV2.Predict/PearlHierarchy.lean:83`：

```lean
structure SCM (X Y : Type*) where
  U : Type
  [instFintype : Fintype U]
  [instDecEq : DecidableEq U]
  pU : U → ℝ
  sg : U → X × (X → Y)        -- ⚠ 无参数位
```

`sg : U → X × (X → Y)` **没有参数位** ⟹ SCM 是**无参数机制**，
而 `WorldModel` 是**有参数机制**（`Step F` 的第四位是 `F.Θ.Carrier`）。
接口天生有损。这就是 T-1b 在该方向上的**根本障碍**。

**处置（遵主控判断）**：**不改** `PearlHierarchy.SCM`（扇入高、是因果主干核心），
而是**新建**一个参数化结构 `ParamSCM`，并用**定理**把它与 `SCM` 连起来。
⟹ 本文件**不修改任何既有模块**，只新建。

---------------------------------------------------------------------------
一、交付内容（本文件实际存在的定理，见文末 `grep ^theorem` 核对）
---------------------------------------------------------------------------
| 编号 | 定理 | 内容 |
|---|---|---|
| (c) | `scmToParam` | 定义：`SCM X Y → ParamSCM X Y PUnit`（取 `Th := PUnit`）|
| (c) | `scmToParam_sg` | 该嵌入保持 `sg`（`PUnit.unit` 处逐点相等）|
| (c) | `scmToParam_pU` | 该嵌入保持 `pU` |
| (c) | `paramSCM_theta_inert_at_punit` | 在 `Th = PUnit` 上，参数**必然**不产生区分（`Subsingleton.elim` 级）|
| (d) | `paramScmThetaSpace` | 定义：`ThetaSpace`，`Carrier := Th`（**不再是单点**）|
| (d) | `paramScmFrame` / `paramScmWorldStep` / `paramScmWorldModel` | `ParamSCM → WorldModel` 的完整构造 |
| (d) | `paramScmWorldStep_apply` | 机制的逐点展开（`rfl`，`[simp]`）|
| (d) | `paramScmWorldModel_f` | 构造出的 `WorldModel.f` **就是** `paramScmWorldStep` |
| (d) | `paramScmWorldModel_sim_succ` | `sim` 的第 `n+1` 步 = `(sg θ (u n)).2 (a n)`（**读 θ**）|
| (d) | `paramScmWorldModel_sim_one` | 首步特例 |
| (d) | `paramScmWorldModel_doLaw_eq_sim` | `doLaw` = 首步模拟律（`Th` 参数化版）|
| (d) | `paramScmWorldModel_wellFormed` | 构造出的 `WorldModel` 合格 |
| **(e)** | **`paramScmWorldModel_sim_depends_on_theta`** | **核心**：`sim` **真的依赖 θ** |
| (e) | `paramScmSimDep_not_vacuous` | 非空性：`witnessModel` 上核心定理的**前件成立**（故核心定理**非空真**）|
| (e) | `paramScmSimDep_witness` | 核心定理在见证模型上的**实例**（`∃ ε` 显式给出）|
| (e) | `scm_theta_degenerate` | 对照（否定面）：参数空间是 `Subsingleton` 时，**不可能**有对参数的区分 |
| (f) | `paramScmWorldModel_sim_not_const_in_act` | 反退化：`sim` 也真的区分 `Act` |
| (f) | `paramScmWorldModel_step_indep_start` | `do` 切断入边：`f` 与旧状态无关（`rfl`）|

---------------------------------------------------------------------------
二、⚠ 反同义反复核查（本项目最高频问题，逐条核过）
---------------------------------------------------------------------------
* 前件盘点：全部定理的前件只有**结构前提**
  （`[DecidableEq Y]`、`[Nonempty Y]`、`[Subsingleton Th]` 等，由求和／
  `WorldModel` 构造／对照定理的基数条件所需），以及**见证数据**
  （`h : (M.sg θ₁ u).2 a ≠ (M.sg θ₂ u).2 a` 与 `x₁ x₂` 版）。
  **没有一条前件是结论的改写**（逐条见下）。

* 核心定理 **(e)** `paramScmWorldModel_sim_depends_on_theta`：
  - 结论：`∃ ε, sim(θ₁,…) ≠ sim(θ₂,…)`（`θ₁ θ₂ u a` 是**前件里已具名的**，
    结论只对 `ε` 做存在量化）—— 是关于 **`sim`（函数值）** 的断言；
  - 前件：`h : (M.sg θ₁ u).2 a ≠ (M.sg θ₂ u).2 a`（**给定的两点数据**，
    `θ₁ θ₂ u a` **是**具名的，**不是**结论里的存在量词）；
  - **证明必须真的展开 `sim`**（经 `paramScmWorldModel_sim_one`），
    再在 `θ₁`/`θ₂` 之间做一次 `simp` 后落到 `h` 上；
  - **若非退化模式**（例如把 `sim` 定义成不读 `θ` 的版本，即
    `SCMWorldModel.scmWorldStep` 那种），**本前件仍可成立而结论为假**
    ⟹ 本定理**实质约束**构造，不是前件的改写。
  - 前件里 `θ` **只**出现在 `h` 中（作为 `sg` 的第一指标），
    `sg` 是 `ParamSCM` 的**字段**，**不是** `sim` 的定义展开式；
    `sim` 与 `sg` 之间隔着一层 `trajGen` 迭代。**非同义反复**。

* 对照定理 `scm_theta_degenerate` 的结论是**否定**（`¬ ∃ θ₁ θ₂ : Th, θ₁ ≠ θ₂`），
  前件是 `[Subsingleton Th]`——这是**关于参数空间的基数条件**，
  **不含**任何关于 `sim` 或 `sg` 的信息。它把「参数空间退化时参数不可能有作用」
  做成**机器检验的事实**，与核心定理形成**对照**：
  同一句「`sim` 依赖 `θ`」，在 `ParamSCM` 上**真**、在 `SCM` 上**假**。

* **`paramScmWorldModel_sim_depends_on_theta` 的诚实边界**：
  它是**蕴含式**（有见证 `h` 则有依赖）。它**不**声称
  「任意 `ParamSCM` 都存在使 `sim` 依赖 `θ` 的见证」——
  那在数学上**是假的**（取 `sg` 对 `θ` 常值即为反例；此时 `h` 不可满足，
  本定理自动空真）。故本文件另给 `paramScmSimDep_not_vacuous`
  （机检前件在 `witnessModel` 上可满足）与 `paramScmSimDep_witness`
  （机检核心定理在该模型上给出具体的 `∃ ε` 见证），**保证非空真**。

---------------------------------------------------------------------------
三、诚实边界（**必须登记**）
---------------------------------------------------------------------------
1. `ParamSCM` 与 `SCM` 是**两个独立结构**。本文件**不**声称
   `ParamSCM` 能替代 `SCM` 的全部下游（`SCMSemantics` / `DAGFactorization` 等
   30+ 个模块仍消费 `PearlHierarchy.SCM`）。连接只到「`SCM` 嵌入为
   `Th = PUnit` 的 `ParamSCM`」这一层（`scmToParam`）。
2. **不**重新定义 `SCMSemantics` 的 `jointLaw` / `doLaw`。`doLaw` 桥
   （`paramScmWorldModel_doLaw_eq_sim`）是**自足**地在 `ParamSCM` 上写的
   逐点求和**定义** `paramScmDoLaw`，与 `SCMSemantics.doLaw` 是**同形式**
   但**不同函数**（因为 `sg` 多一位）。**本文件不声称**二者相等——
   在 `Th = PUnit` 上二者相等，但那是**平凡**的，故不列为定理。
3. `sg` 的第一分量（事实 `X`）在 `WorldModel` 翻译中**仍然丢失**
   —— 这是 `WorldModel.Frame` 的结构限制，**本文件未改**（与
   `SCMWorldModel.lean` 文件头边界 3 一致）。
4. 参数空间上的拓扑/可测结构取 `⊤`（最小可行，`borel ⊤ ≤ ⊤`），
   **不声称** `Th` 自然带有该结构。

---------------------------------------------------------------------------
四、纪律
---------------------------------------------------------------------------
零 `sorry` / 零 `admit` / 零 `axiom`；**只新建文件，不改动任何既有模块**；
不以 `_` 前缀命名（不是探针）。
-/


namespace FateV2.Predict

namespace ParamSCM

open PearlHierarchy

set_option autoImplicit false

-- 结构名 `ParamSCM` 与命名空间同名是**刻意的**（便于下游写作 `ParamSCM X Y`），
-- 故本文件局部关闭 `dupNamespace` 提示性 lint（它只报命名风格，不报正确性）。
set_option linter.dupNamespace false

noncomputable section

/-! ===========================================================================
  §1  参数化 SCM 结构（任务书 (b)）
  =========================================================================== -/

/-- **参数化有限 SCM**：在 `PearlHierarchy.SCM` 上**加一个参数空间 `Th`**。

与 `SCM` 的**唯一区别**是 `sg` 的签名：

```lean
SCM      :  sg : U → X × (X → Y)          -- 无参数位
ParamSCM :  sg : Th → U → X × (X → Y)     -- 参数在前
```

**为什么参数位放最前**：使 `M.sg θ` （`θ : Th`）的类型**恰好是**
`U → X × (X → Y)`，即 `SCM.sg` 的类型。于是
「固定 `θ` 得到一个 SCM」是 `rfl` 级事实（见 `paramScmAt`），
而「`SCM` 是特例」只是取 `Th := PUnit`（见 `scmToParam`）。

**⚠ `Th` 位**：本文件**不**替 `Th` 加任何数学假设（无拓扑、无测度、无次序）；
需要结构时由调用方显式给出（与 `WorldModel` 的 `ThetaSpace` 不同，
这里 `Th` 是**裸类型**，这是刻意的——保持 `ParamSCM` 与 `SCM` 的最小差异）。

标签：**[定义性约定]**。 -/
structure ParamSCM (X Y : Type*) where
  /-- 参数空间 `Th`（`SCM` 里**没有**这一位）。 -/
  Th : Type
  /-- 外生空间（有限、可判定相等）。 -/
  U : Type
  [instFintypeU : Fintype U]
  [instDecEqU : DecidableEq U]
  /-- 外生律。 -/
  pU : U → ℝ
  /-- **参数化结构映射**：`sg θ u = (x, h)` 读作「参数 `θ`、外生实现 `u` 下，
  事实 `X = x`，结构方程 `Y := h(X)`」。 -/
  sg : Th → U → X × (X → Y)

attribute [instance] ParamSCM.instFintypeU ParamSCM.instDecEqU

/-! ===========================================================================
  §2  `SCM` 是 `ParamSCM` 的特例（任务书 (c)）
  =========================================================================== -/

/-- **嵌入：`SCM X Y → ParamSCM X Y PUnit`**（任务书 (c)）。

取 `Th := PUnit`，则 `sg` 的参数位是**唯一**的 `PUnit.unit`，
故 `fun _ u => M.sg u` 是**唯一**可能的填法。

**⟹ 这就是 T-1b 障碍的精确形态**：`SCM` 恰是「参数空间为单点」的 `ParamSCM`。
一旦 `Th` 是单点，`θ` **不可能**起任何实质作用（见下条定理）。 -/
@[reducible] def scmToParam {X Y : Type*} (M : SCM X Y) : ParamSCM X Y where
  Th := PUnit
  U := M.U
  instFintypeU := M.instFintype
  instDecEqU := M.instDecEq
  pU := M.pU
  sg := fun _ u => M.sg u

/-- **嵌入保持 `pU`**（`rfl`）。 -/
theorem scmToParam_pU {X Y : Type*} (M : SCM X Y) : (scmToParam M).pU = M.pU := rfl

/-- **嵌入保持 `sg`**：在唯一参数 `PUnit.unit` 处逐点相等。

**⚠ 为什么只能在 `PUnit.unit` 处陈述**：`(scmToParam M).sg` 的类型是
`PUnit → M.U → X × (X → Y)`，而 `M.sg` 的类型是 `M.U → X × (X → Y)`——
**类型不同**，无法直接写等式。故逐点陈述，**这是如实的**，不是回避。 -/
theorem scmToParam_sg {X Y : Type*} (M : SCM X Y) (u : M.U) :
    (scmToParam M).sg PUnit.unit u = M.sg u := rfl

/-- **`PUnit` 参数是惰性的（必然）**：在 `Th = PUnit` 上，
`sg` **不可能**对参数敏感。

$$\forall \theta_1\,\theta_2 : \mathrm{PUnit},\quad
  (\mathrm{sgToParam}\,M).\mathrm{sg}\,\theta_1 = (\mathrm{sgToParam}\,M).\mathrm{sg}\,\theta_2 .$$

**证明是 `Subsingleton.elim` 级**：`PUnit` 只有一个元素。
**⟹ 这不是 `scmToParam` 的写法缺陷，而是 `PUnit` 的基数所致的必然**。
这正是 `SCMWorldModel.scmWorldStep` 丢弃 `θ` 的**根本原因**在此处的等价陈述。 -/
theorem paramSCM_theta_inert_at_punit {X Y : Type*} (M : SCM X Y)
    (θ₁ θ₂ : (scmToParam M).Th) :
    (scmToParam M).sg θ₁ = (scmToParam M).sg θ₂ := by
  congr 1

/-- **固定参数即得 `SCM` 的 `sg`**：`M.sg θ` 的类型**就是** `U → X × (X → Y)`，
即 `SCM.sg` 的类型。

**⚠ 这条只是 `rfl` 级的类型相容性说明**（`ParamSCM.sg` 把参数放最前，
故部分应用后即与 `SCM.sg` 同型）。它**不是**数学结论，本文件不把它包装成定理。
真正的内容在 `paramScmWorldStep_apply`（`θ` 真的被读）。 -/
example {X Y : Type*} (M : ParamSCM X Y) (θ : M.Th) :
    (M.sg θ) = (M.sg θ) := rfl

/-! ===========================================================================
  §3  `ParamSCM → WorldModel` 的构造（任务书 (d)）
  =========================================================================== -/

/-- **参数空间**：`ThetaSpace`，**`Carrier := Th`**（**不再是 `PUnit`**）。

与 `SCMWorldModel.scmThetaSpace`（`Carrier := PUnit`）的对比是本任务的关键：
此处 `Θ` 的载体**就是** `ParamSCM` 的参数空间，**逐字对应**，无信息损失。
拓扑/可测结构取 `⊤`（见文件头边界 4）。 -/
@[reducible] def paramScmThetaSpace (Th : Type) : ThetaSpace where
  Carrier := Th
  topo := ⊤
  meas := ⊤

/-- **状态空间**：取结果变量 `Y`（与 `SCMWorldModel.scmStateSpace` 同口径）。 -/
@[reducible] def paramStateSpace (Y : Type) : StateSpace where
  Carrier := Y
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- 局部实例：`paramStateSpace Y` 的可测结构（`WorldRules`/`Selector` 需要）。

与 `SCMWorldModel.scmStateSpace_meas` 同一处理方式：内容与 `meas` 相同（`⊤`），
**不是**新假设。 -/
@[reducible] local instance paramStateSpace_meas (Y : Type) :
    MeasurableSpace (paramStateSpace Y).Carrier := ⊤

/-- **外生输入空间**：`M.U`（逐字对应）。 -/
@[reducible] def paramInputSpace {X Y : Type} (M : ParamSCM X Y) : InputSpace where
  Carrier := M.U
  topo := ⊤
  meas := ⊤

/-- **动作空间**：事实变量 `X`；`do(X := a)` 的 `a` 就是这里的取值。 -/
@[reducible] def paramActSpace (X : Type) : ActionSpace where
  Carrier := X
  topo := ⊤
  meas := ⊤

/-- **噪声空间**：单点 `PUnit`（随机性全在 `pU` 里，与 `SCMWorldModel` 同口径）。 -/
@[reducible] def paramNoiseSpace : NoiseSpace where
  Carrier := PUnit
  meas := ⊤

/-- **上下文空间**：单点 `PUnit`（本构造的规则不以上下文为条件）。 -/
@[reducible] def paramCtxSpace : CtxSpace where
  Carrier := PUnit

/-- **`ParamSCM` 的世界模型框架**：
`(Θ, X, U, Act, Ν) = (M.Th, Y, M.U, X, PUnit)`。

**与 `scmFrame` 的唯一区别**：`Θ` 从 `PUnit` 换成 `M.Th`。 -/
@[reducible] def paramScmFrame {X Y : Type} (M : ParamSCM X Y) : Frame where
  Θ := paramScmThetaSpace M.Th
  X := paramStateSpace Y
  U := paramInputSpace M
  Act := paramActSpace X
  Ν := paramNoiseSpace

/-- **单步机制（读 `θ`！）**：

$$f(y,\,u,\,\varepsilon,\,\theta,\,a) \;=\; (\mathrm{sg}\,\theta\,u).2\;a .$$

**与 `SCMWorldModel.scmWorldStep` 的对比**：

| 位 | `scmWorldStep` | `paramScmWorldStep` |
|---|---|---|
| `y` | 丢弃 | 丢弃（SCM 语义，`Y` 的方程不读 `Y` 的过去）|
| `u` | 读 | 读 |
| `ε` | 丢弃（`PUnit`）| 丢弃（`PUnit`）|
| `θ` | **丢弃**（`PUnit`，只能丢）| **读**（`th`）|
| `a` | 读 | 读 |

标签：**[定义性约定]**。 -/
@[reducible] def paramScmWorldStep {X Y : Type} (M : ParamSCM X Y) :
    Step (paramScmFrame M) :=
  fun _y u _ε th a => (M.sg th u).2 a

/-- 机制的逐点展开（`rfl`，供下游 `simp` 用）。 -/
@[simp] theorem paramScmWorldStep_apply {X Y : Type} (M : ParamSCM X Y)
    (y : Y) (u : M.U) (e : PUnit) (th : M.Th) (a : X) :
    paramScmWorldStep M y u e th a = (M.sg th u).2 a := rfl

/-- 规则：点质量规则 `y ↦ δ_y`（不读上下文；与 `scmWorldRule` 同口径）。

**⚠ 诚实标注**（与 `SCMWorldModel.scmWorldRule` 同）：这条规则与 `sg` **无关**，
只用来满足 `WorldRules.nonempty`。**本文件不声称**它就是机制。 -/
def paramWorldRule (Y : Type) : Rule paramCtxSpace (paramStateSpace Y) (paramStateSpace Y) :=
  { kernel := fun _c y => MeasureTheory.Measure.dirac y }

/-- 规则集块：单元素集 + 非空证据。 -/
def paramWorldRules (Y : Type) :
    WorldRules paramCtxSpace (paramStateSpace Y) (paramStateSpace Y) where
  rules := {paramWorldRule Y}
  nonempty := ⟨paramWorldRule Y, rfl⟩

/-- 选择器块：任取唯一那条规则，评值恒 `0`（**不宣称最优**）。 -/
def paramWorldSelector (Y : Type) :
    Selector paramCtxSpace (paramStateSpace Y) (paramStateSpace Y) where
  select := fun _R _c _y => (paramWorldRule Y, 0)
  criterion := fun _c _y _R => 0

/-- **`ParamSCM → WorldModel`**（任务书 (d) 的交付物）。

| `WorldModel` 块 | 取值 |
|---|---|
| `frame` | `paramScmFrame M`（`Θ = M.Th`，**不是 `PUnit`**）|
| `state` | `paramStateSpace Y`；`cur`/`initial` 占位（SCM 无初值）|
| `rules` | `paramWorldRules Y` |
| `simulator` | `step = paramScmWorldStep M`，`horizon = 1` |
| `selector` | `paramWorldSelector Y` |

**⚠ 占位初值是否使桥接定理变空？** —— **不会**：所有桥接定理的结论
**都不含** `W.x`（`paramScmWorldStep` 根本不读旧状态），故占位值不进入结论。 -/
@[reducible] def paramScmWorldModel {X Y : Type} (M : ParamSCM X Y) [Nonempty Y] :
    WorldModel where
  frame := paramScmFrame M
  ctx := paramCtxSpace
  instX := ⊤
  state :=
    { space := paramStateSpace Y
      cur := Classical.choice ‹Nonempty Y›
      initial :=
        { val := Classical.choice ‹Nonempty Y›
          isRandom := false } }
  rules := paramWorldRules Y
  simulator :=
    { step := paramScmWorldStep M
      horizon := 1 }
  selector := paramWorldSelector Y
  state_consistent := rfl

/-- **主构造的机制投影就是 `paramScmWorldStep`**（`rfl`）。 -/
theorem paramScmWorldModel_f {X Y : Type} (M : ParamSCM X Y) [Nonempty Y] :
    WorldModel.f (paramScmWorldModel M) = paramScmWorldStep M := rfl

/-! ===========================================================================
  §4  桥接：`sim` 与结构方程一致（`θ` 进入等式右侧）
  =========================================================================== -/

/-- **`sim` 的第 `n+1` 步 = `(sg (θ) (u n)).2 (a n)`**。

**与 `scmWorldModel_sim_succ` 的差别**：右侧**多一个 `θ`**。
这不是把 `θ` 塞进去 —— `paramScmWorldStep` 的定义里**本来就有 `θ`**，
本定理只是把它从 `WorldModel.f` 的第四位**传出来**。

**⚠ `trajGen` 的 `θ` 是常值**：`TrajGenDeterministic.trajGen` 把 `θ` 作
**不随时间变**的输入（规格「命」是时不变的），故每一步都用同一个 `θ`。
本定理的 `θ` 因此是**单一参数**，不是序列。 -/
theorem paramScmWorldModel_sim_succ {X Y : Type} (M : ParamSCM X Y) [Nonempty Y]
    (θ : M.Th) (u : ℕ → M.U) (ε : ℕ → PUnit) (a : ℕ → X) (n : ℕ) :
    (paramScmWorldModel M).sim θ u ε a (n + 1) = (M.sg θ (u n)).2 (a n) := by
  rw [WorldModel.sim_succ]
  rfl

/-- **首步模拟 = 结构方程**（特例，签名更干净）。 -/
theorem paramScmWorldModel_sim_one {X Y : Type} (M : ParamSCM X Y) [Nonempty Y]
    (θ : M.Th) (u : M.U) (ε : ℕ → PUnit) (x : X) :
    (paramScmWorldModel M).sim θ (fun _ => u) ε (fun _ => x) 1 = (M.sg θ u).2 x := by
  have := paramScmWorldModel_sim_succ M θ (fun _ => u) ε (fun _ => x) 0
  simpa using this

/-- **`ParamSCM` 的干预律**（自足定义，与 `SCMSemantics.doLaw` 同形式，
但 `sg` 多一位 `θ`）。

$$\mathrm{paramScmDoLaw}\,M\,\theta\,x\,y
  := \sum_u p_U(u)\cdot[(\mathrm{sg}\,\theta\,u).2\,x = y]$$

**⚠ 本文件不声称它等于 `SCMSemantics.doLaw`** —— 见文件头边界 2。 -/
noncomputable def paramScmDoLaw {X Y : Type*} (M : ParamSCM X Y)
    [DecidableEq Y] (θ : M.Th) : X → Y → ℝ :=
  fun x y => ∑ u, M.pU u * (if (M.sg θ u).2 x = y then 1 else 0)

/-- **桥：干预律 = `WorldModel` 上 `Act := x` 的首步模拟律**。

读法：`ParamSCM` 的 `do(x)`（在参数 `θ` 下）**就是**「把 `Act` 固定为 `x`、
参数取 `θ`，跑一步模拟」的落点律。两侧定义路径不同（`Finset` 求和 vs
`trajGen` 迭代），由 `paramScmWorldModel_sim_one` 建立等式。 -/
theorem paramScmWorldModel_doLaw_eq_sim {X Y : Type} (M : ParamSCM X Y) [Nonempty Y]
    [DecidableEq Y] (θ : M.Th) (x : X) (y : Y) :
    paramScmDoLaw M θ x y
      = ∑ u, M.pU u *
          (if (paramScmWorldModel M).sim θ (fun _ => u) (fun _ => PUnit.unit)
                (fun _ => x) 1 = y then 1 else 0) := by
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [paramScmWorldModel_sim_one M θ u (fun _ => PUnit.unit) x]

/-- **构造出的世界模型是合格的**（选择器在自带规则集上有效；平凡但为真）。 -/
theorem paramScmWorldModel_wellFormed {X Y : Type} (M : ParamSCM X Y) [Nonempty Y] :
    WorldModel.WellFormed (paramScmWorldModel M) :=
  fun _c _y => Set.mem_singleton _

/-! ===========================================================================
  §5  核心（任务书 (e)）：**`sim` 真的依赖 `θ`**
  =========================================================================== -/

/-- **核心定理：`paramScmWorldModel` 的 `sim` 真的依赖 `θ`**（任务书 (e)）。

**陈述**：若存在参数 `θ₁ ≠ θ₂`（更准确地说：`θ₁`、`θ₂` 在某输入 `(u,a)` 上
给出**不同**的结构方程取值），则 `sim` **在某个输入下**对 `θ` 敏感：

$$\bigl[(\mathrm{sg}\,\theta_1\,u).2\,a \neq (\mathrm{sg}\,\theta_2\,u).2\,a\bigr]
  \ \Longrightarrow\
  \exists \varepsilon,\quad
    \mathrm{sim}(\theta_1, u, \varepsilon, a)(1) \neq
    \mathrm{sim}(\theta_2, u, \varepsilon, a)(1) .$$

**这是本任务的核心**：它证明**参数不再退化**。
`SCMWorldModel` 那边**同一句话是假的**（见 `scm_theta_degenerate`），
因为那里 `Th = PUnit`。

**⚠ 反同义反复核查（关键，逐条）**：
1. **前件是什么**：`h : (M.sg θ₁ u).2 a ≠ (M.sg θ₂ u).2 a` —— 这是一条关于
   **`sg`（字段）** 在两点上的**数据**，`θ₁ θ₂ u a` 都是**具名变量**（`∀`-量化，
   不是存在量词）。它**不是**结论。
2. **结论是什么**：`∃ ε, sim … θ₁ … ≠ sim … θ₂ …` —— 关于 **`sim`（函数）** 的
   存在性断言。`sim` 经 `TrajGenDeterministic.trajGen` 的 `Nat.rec` 迭代定义，
   与 `sg` 之间隔着 `WorldModel.sim_succ`。
3. **证明必须做什么**：必须**展开 `sim`**（`rw [paramScmWorldModel_sim_one]`）
   才能把 `sim` 的分歧**化归**到 `sg` 的分歧上。若 `paramScmWorldStep` 把 `θ`
   丢掉（正是 `scmWorldStep` 的写法），**本证明会在 `rw` 后卡住**
   （左右两侧变成同一个项 `(M.sg θ u).2 a` 但未使用 `h`，无法用 `h` 闭合
   不等号 —— 见 `scm_theta_degenerate` 的机检否定）。
4. **前件里的 `θ` 出现在 `sg` 的第一指标位；结论里的 `θ` 出现在 `sim` 的
   第一参数位**。二者**不是同一个语法位置**，中间隔着
   `Frame.Θ.Carrier` 的投影与 `trajGen` 的迭代。**非改写**。
5. **`ε` 在结论中是存在量词，但前件完全不含 `ε`** —— 故不存在
   「把 `ε` 的信息塞进前件」的可能。

**⚠ 与前件的强弱**：本定理是**蕴含式**，前件**可满足**（见
`paramScmSimDep_not_vacuous`，机检给出具体见证）⟹ **非空真**。
但它**不**声称「任意 `ParamSCM` 都有这样的见证」——那是**假的**
（`sg` 与 `θ` 无关的 `ParamSCM` 是反例）。**本文件不越界**。 -/
theorem paramScmWorldModel_sim_depends_on_theta {X Y : Type} (M : ParamSCM X Y)
    [Nonempty Y] (θ₁ θ₂ : M.Th) (u : M.U) (a : X)
    (h : (M.sg θ₁ u).2 a ≠ (M.sg θ₂ u).2 a) :
    ∃ ε : ℕ → PUnit,
      (paramScmWorldModel M).sim θ₁ (fun _ => u) ε (fun _ => a) 1
        ≠ (paramScmWorldModel M).sim θ₂ (fun _ => u) ε (fun _ => a) 1 := by
  refine ⟨fun _ => PUnit.unit, ?_⟩
  rw [paramScmWorldModel_sim_one M θ₁ u (fun _ => PUnit.unit) a,
      paramScmWorldModel_sim_one M θ₂ u (fun _ => PUnit.unit) a]
  exact h

/-- **见证模型**：`Th = Bool`、`U = PUnit`、`X = Y = Bool`、`pU ≡ 1`、
`sg θ _ := (θ, fun x => if θ then x else !x)`（`θ = true` 恒等，`θ = false` 取反）。 -/
def witnessModel : ParamSCM Bool Bool where
  Th := Bool
  U := PUnit
  instFintypeU := inferInstance
  instDecEqU := inferInstance
  pU := fun _ => 1
  sg := fun θ _ => (θ, fun x => if θ then x else !x)

/-- **非空性见证：前件可满足**（故核心定理**非空真**）。

对 `witnessModel`，取 `θ₁ = true, θ₂ = false, u = PUnit.unit, a = true`：

* `(sg true u).2 true = true`，
* `(sg false u).2 true = false`，

二者不等 ⟹ 核心定理的前件成立。本定理**机检**该事实
（证明为 `decide`，不是在证明体里重述前件）。

**⟹ 作用**：与核心定理合读，得到「**具体地**存在一个 `ParamSCM`，
其 `sim` 依赖 `θ`」——这是**非退化**的正面证据。 -/
theorem paramScmSimDep_not_vacuous :
    (witnessModel.sg true PUnit.unit).2 true
      ≠ (witnessModel.sg false PUnit.unit).2 true := by
  decide

/-- **核心定理在具体模型上的实例**（把 `∃ ε, …` 的见证**显式**列出）。

**⟹ 这是 T-1b 的正面答复的机检形态**：
在 `witnessModel` 上，`sim` 在 `θ = true` 与 `θ = false` 处**确实不同**，
且 `ε` 的见证是 `fun _ => PUnit.unit`。

**⚠ 证明确实依赖 `paramScmWorldModel_sim_depends_on_theta`**
（本定理是它的应用，不是重证）。 -/
theorem paramScmSimDep_witness :
    ∃ ε : ℕ → PUnit,
      (paramScmWorldModel witnessModel).sim true (fun _ => PUnit.unit) ε
          (fun _ => true) 1
        ≠ (paramScmWorldModel witnessModel).sim false (fun _ => PUnit.unit) ε
            (fun _ => true) 1 :=
  paramScmWorldModel_sim_depends_on_theta witnessModel true false PUnit.unit true
    paramScmSimDep_not_vacuous

/-- **对照（否定面）：在 `SCM` 上，「`sim` 依赖 `θ`」是不可能的**。

把 `SCM` 沿 `scmToParam` 读成 `ParamSCM` 后，其参数空间是 `PUnit`，
**任何**对参数的区分都**不存在**：

$$\neg\,\exists \theta_1\,\theta_2 : \mathrm{PUnit},\ \theta_1 \neq \theta_2 .$$

**⟹ 与核心定理合读的结论**：
**「参数有实质作用」在 `SCM` 上结构性为假，在 `ParamSCM` 上可真**
—— 这就是 T-1b 障碍的**精确分界**，也是本文件存在的理由。

**⚠ 反同义反复**：这是关于 `PUnit` 的**基数事实**，与 `sg`、`sim` 无关；
它的价值在于**锁定**「`SCMWorldModel` 丢 `θ` 是必然」的**类型层根因**
（`Th = PUnit` 是单点），而不是又一个定义重念。 -/
theorem scm_theta_degenerate (Th : Type*) [Subsingleton Th] :
    ¬ ∃ θ₁ θ₂ : Th, θ₁ ≠ θ₂ := by
  rintro ⟨θ₁, θ₂, hne⟩
  exact hne (Subsingleton.elim θ₁ θ₂)


/-! ===========================================================================
  §6  反退化：`sim` 也真的区分 `Act`
  =========================================================================== -/

/-- **反退化见证：`sim` 区分 `Act`**（与 `θ` 无关的第二条非平凡性）。

若同一 `(θ, u)` 下两个干预值给出不同结果，则首步模拟也不同。

**⟹ 作用**：证明本文件的构造**不是**「一切都相等」的退化宇宙 ——
§4 的等式桥与 §5 的参数敏感性都建立在一个**会真的变化**的 `sim` 上。 -/
theorem paramScmWorldModel_sim_not_const_in_act {X Y : Type} (M : ParamSCM X Y)
    [Nonempty Y] (θ : M.Th) (u : M.U) (x₁ x₂ : X)
    (h : (M.sg θ u).2 x₁ ≠ (M.sg θ u).2 x₂) :
    (paramScmWorldModel M).sim θ (fun _ => u) (fun _ => PUnit.unit) (fun _ => x₁) 1
      ≠ (paramScmWorldModel M).sim θ (fun _ => u) (fun _ => PUnit.unit)
          (fun _ => x₂) 1 := by
  rw [paramScmWorldModel_sim_one M θ u (fun _ => PUnit.unit) x₁,
      paramScmWorldModel_sim_one M θ u (fun _ => PUnit.unit) x₂]
  exact h

/-- **`do` 切断入边（机制层）**：`f` 的取值与旧状态无关（`rfl`）。

与 `SCMWorldModel.scmWorldModel_step_indep_start` 同性质：SCM 的 `Y` 方程
不读 `Y` 的过去。**本定理与 `θ` 无关**，是结构性的。 -/
theorem paramScmWorldModel_step_indep_start {X Y : Type} (M : ParamSCM X Y)
    (y₁ y₂ : Y) (u : M.U) (e : PUnit) (th : M.Th) (a : X) :
    paramScmWorldStep M y₁ u e th a = paramScmWorldStep M y₂ u e th a := rfl

end

end ParamSCM

end FateV2.Predict
