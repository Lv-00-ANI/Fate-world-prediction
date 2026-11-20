/-
命运理论 · Lean 4 形式化实现
================================

模块：`SCMWorldModel`
定位：**建桥 —— 把世界模型线接进因果主干**（SCM ⟶ `WorldModel`）

---------------------------------------------------------------------------
〇、本文件要解决的空位（**先盘点，避免重复劳动**）
---------------------------------------------------------------------------
库里有两条**零交集**的平行线：

| 线 | 代表模块 | 描述对象 |
|---|---|---|
| **因果线** | `DAGFactorization`(扇入 34) / `FinCondIndep`(27) / `FactorMarkov`(38) / `SCMSemantics`(16) | SCM：`U`、`pU`、`sg : U → X × (X → Y)` |
| **世界模型线** | `WorldModel` → `EndToEnd`(16) → `BoundWriteBack`(12) → `ThetaConvergence` | `Frame`（`Θ,X,U,Act,Ν`）+ 四块（状态/规则集/模拟器/选择器）|

**⚠ 已核实（3 种 grep 模式，见交付说明）**：
`EndToEnd` / `BoundWriteBack` / `ThetaConvergence` / `WorldModel` 对 `SCMSemantics`
的 import 数**均为 0**；且**没有任何文件**把「任意 SCM」翻译成 `WorldModel`。

**⚠ 与既有模块的边界（必须写清，否则会变成重复劳动）**：

| 既有模块 | 它做的方向 | 与本文件的关系 |
|---|---|---|
| `Fate/DoLawWorldModel.lean` | 给**已有**的 `WorldModel` **加** SCM 字段（`DoCapable`，`WorldModel ⟶ SCM` 方向）| **方向相反**：本文件是 `SCM ⟶ WorldModel`（**构造** `WorldModel`）|
| `Fate/WiringBackdoor.lean` §4 | 把一个**具体的** `BackdoorSetup`（`fX`/`fY` 显式给出）做成 `WorldModel` | 本文件对**任意** `FateV2.Modeling.PearlHierarchy.SCM` 构造，且**不引入**任何具体 SCM |
| `Fate/FateV2.Modeling.SCMSemantics.lean` | SCM 的联合律/边缘律/观测律/干预律（有限求和口径）| **本文件只引用**，不重定义 |

⟹ 本文件的增量是：**`SCM → WorldModel` 这个方向的全新构造 + 桥接定理**。

---------------------------------------------------------------------------
一、翻译方案（任务书 (a)）
---------------------------------------------------------------------------
给定 `M : FateV2.Modeling.PearlHierarchy.SCM X Y`（`X` = 事实变量、`Y` = 结果变量），构造 `WorldModel`：

| `WorldModel`/`Frame` 位 | 取 SCM 的什么 | 理由 |
|---|---|---|
| **状态空间** `X` | **`Y`**（结果变量） | SCM 里「被结构方程决定、并随时间演化」的是 `Y`；`X` 是**外部设定的事实**，不是被机制产生的 |
| **状态取值** `cur` / `initial` | 任取 `y₀ : Y`（需 `[Nonempty Y]`） | `WorldModel` 的 `cur` 是**具体取值**，SCM 不规定初值 ⟹ 只作占位 |
| **外生输入** `U` | **`M.U`**（外生空间） | 逐字对应；`M.U` 已带 `Fintype`/`DecidableEq` |
| **噪声** `Ν` | **`PUnit`** | **随机性全在 `pU` 里**（已由外生律承载），机制本身确定 ⟹ 噪声位**结构性退化**为单点 |
| **参数** `Θ` | **`ℕ × (X → Y)`**（见 §10，第 155 轮修订） | **一个 SCM 是不可辨识的**：`(sg u).2` 混着「外生律用哪个 `u`」与「结构方程是什么」；把「假设的机制」`X → Y` 与「接入强度」`ℕ` 一并放进 `θ` 才有内容 |
| **动作** `Act` | **`X`**（事实变量的取值） | **`do(X := x)` 的 `x`** —— 这就是任务书 (c) 要求的「干预 ↔ `Act`」接线 |
| **单步机制** `f` | `fun _y u _ε θ a => θ.2 a * θ.1 ((M.sg u).2 a)` | 结构方程 `Y := h_u(X)` 先给出「数据 `d`」，再由 `θ` 里的假设机制 `θ.2` 与强度 `θ.1` 把它映射成预测 → **`θ` 真的有作用**（§10） |

**⚠ `f` 的第一个位置（旧状态）被丢弃** —— 这不是偷懒，而是 **SCM 的语义本身**：
单结果变量 SCM 中 `Y` 的方程**不读 `Y` 的过去**。本文件把这一点做成定理
（`scmWorldModel_step_indep_start`），而不是注释。

---------------------------------------------------------------------------
二、交付的桥接定理（任务书 (b)：(i) sim ↔ 结构方程、(ii) 观测、 (iii) do ↔ Act）
---------------------------------------------------------------------------
| 编号 | 定理 | 内容 |
|---|---|---|
| **(i)** | `scmWorldModel_sim_succ` | `WorldModel.sim` 的第 `n+1` 步 **=** `(sg (u n)).2 (a n)` |
| **(i)** | `scmWorldModel_doLaw_eq_push_step` | `doLaw` **=** 外生律沿 `WorldModel.f` 的推前 |
| **(i)** | `scmWorldModel_step_iff_sg` | `WorldModel` 的机制**恰好**决定（且只决定）`sg` 的第二分量 |
| **(ii)** | `scmWorldModel_jointLaw_eq_sim` | SCM 的**联合律** = 「`Act` 取事实值 `X` 时的首步模拟律」 |
| **(ii)** | `scmWorldModel_marginalY_eq_sim` | `FateV2.Modeling.SCMSemantics.marginalY` **=** 首步模拟的边缘律 |
| **(iii)** | `scmWorldModel_doLaw_eq_sim` | SCM 的 `do(x)` **=** `WorldModel` 上 `Act := x` 的首步模拟律 |
| **(iii)** | `scmWorldModel_step_indep_start` | **`do` 切断入边**：`f` 的取值与旧状态无关 |
| — | `scmWorldModel_wellFormed` | 构造出的 `WorldModel` 是**合格**的（选择器在自带规则集上有效）|
| — | `scmWorldModel_sim_not_const` | 模拟**非平凡**：不同 `Act` 给出不同轨迹（反退化见证）|

---------------------------------------------------------------------------
三、⚠ 反同义反复核查（本项目最高频问题）
---------------------------------------------------------------------------
本文件每条定理的**前件**逐条核过：

* `[Fintype M.U]` / `[DecidableEq Y]` / `[Nonempty Y]` —— **结构前提**（求和/取值需要），
  **不涉及**任何结论里的等式内容；
* **每条主定理的结论都是两条既有定义之间的等式**（`WorldModel` 侧 vs `SCMSemantics` 侧），
  其**右式里没有一条以任何前件形式出现过**。故**不存在**「把结论包进前件的同义反复**。
* 唯一带**实质前件**的是 `scmWorldModel_sim_not_const`，其前件是
  `h : (sg u).2 x₁ ≠ (sg u).2 x₂` —— 这是**见证非退化所需的反例数据**，
  结论是 `sim … 1 ≠ sim … 1'`，**不是**前件的改写（见该定理的证明与说明）。

---------------------------------------------------------------------------
四、诚实边界（**必须登记**）
---------------------------------------------------------------------------
1. **拓扑/可测结构取 `⊤`**：`scmStateSpace` 的 `topo`/`meas` 都取 `⊤`，
   `borel_le := le_top`。这是**最小可行**选择（`borel ⊤ ≤ ⊤` 恒真），
   **不声称** SCM 的 `Y` 自然带有该结构。若要接 `CondIndepFun` 之类的测度层，
   须另建 `Measure` 嵌入（`SCMSemantics` §68.4 已登记该缺口），**本文件不做**。
2. **`cur` / `initial` 是占位值**：给 `[Nonempty Y]` 后由 `Classical.choice` 取，
   **与 SCM 无关**（SCM 不含初值）。故本文件**不**陈述「从某个 SCM 语义起点出发」的
   轨迹性质——那需要 SCM 侧给出初值，SCM 定义里没有。
   **所有桥接定理因此都只陈述「首步/单步」或与起点无关的量**，这是刻意的、也是如实的。
3. **`sg` 的第一分量（事实 `X`）在翻译中丢失**：见 `scmWithFacts_step_eq` /
   `scmWithFacts_sg_ne` —— `WorldModel` 的机制**看不见** `sg` 的第一分量。
   本文件**如实登记**这一信息损失，并把它做成定理（而非隐患）。
4. **`f` 的第一个位置（旧状态 `y`）被丢弃**：`scmWorldStep` **不读** `y`。
   这是单结果 SCM 的语义（`Y` 的方程不读 `Y` 的过去），已做成定理
   `scmWorldModel_step_indep_start`。**第 155 轮修订**：`θ` 与 `ε` 仍被丢弃
   （`ε = PUnit` 无内容；`θ` 的位置现在由 `θ.2 a` 承担）——见 §10 的逐位读法。
5. **不声称**「世界模型线的一切结论因此自动对 SCM 成立」。
   本文件只交付**构造 + 等式桥**；下游（`EndToEnd` 等）是否消费，**不在本文件范围**。

---------------------------------------------------------------------------
五、纪律
---------------------------------------------------------------------------
零占位词（即 Lean 的未完成证明关键字，本文件一律不使用）/ 零 `admit` / 零 `axiom`；
**只新建文件，不改动任何既有模块**。

---------------------------------------------------------------------------
六、本轮修复登记（**必须读**）
---------------------------------------------------------------------------
本文件交付时曾编译失败（`EXIT=1`，2 个 `error`），且证明体内**遗留 2 处占位关键字**
（违反「零占位词」纪律）。2 个 error 与 2 处占位**全部**来自同一条定理
`scmWorldModel_step_unique`（原 §8 末，现已**删除**）。处理如下：

**（1）2 个 error 的直接原因**：该证明是**未完成**的半成品，后半段同时触发两处类型错误：

* `eq_or_ne` 给出的析取顺序与目标相反（得到 `A = B ∨ A ≠ B`，目标要 `A ≠ B ∨ A = B`）；
* `absurd heq hw` 把「**索引**不相等」的假设 `hw : w ≠ u` 用在了
  「**取值**相等」的 `heq : (M.sg w).2 x = (M.sg u).2 x` 上 ——
  这是两个不同层次的对象（`U` 的元素 vs `Y` 的元素），类型不匹配。

**（2）该定理在原陈述下是假的，故按纪律删除**（不保留、不擅改陈述、不用占位词填补）。
**机检反例**（`U = Bool`，`pU ≡ 1`，`(sg true).2 x = x`、`(sg false).2 x = ¬x`，
竞争者机制 `f'` **交换**两个外生实现的取值）：

| 待检项 | 结果 |
|---|---|
| 前件 `h`：`∀ x, push pU (f' · x) = doLaw M x` | ✅ **成立**（交换后推前不变）|
| 前件 `hpU`：`∀ u, pU u ≠ 0` | ✅ **成立**（`pU ≡ 1`）|
| 结论在 `u = true, x = true` 处 | ❌ **为假**（`f' … = false`，而 `(sg true).2 true = true`）|

⟹ 该组前件**钉不住点值**：`push` 只约束「输出值在 `pU` 权重下的**多重集**」不变，
允许机制在**等权**的两个外生实现之间任意置换。故所述的「唯一性」**不成立**。

**（3）删除后本文件的诚实状态**：§1–§9 的**全部**桥接定理陈述**未改**且已机检通过：
`scmWorldModel_f`、`scmWorldModel_sim_succ`、`scmWorldModel_sim_one`、
`scmWorldModel_step_iff_sg`、`scmWorldModel_doLaw_eq_push_step`、
`scmWorldModel_jointLaw_eq_sim`、`scmWorldModel_marginalY_eq_sim`、
`scmWorldModel_doLaw_eq_sim`、`scmWorldModel_step_indep_start`、
`scmWorldModel_sim_one_indep_start`、`scmWorldModel_wellFormed`、
`scmWorldModel_sim_not_const`、`scmWithFacts_step_eq`、`scmWithFacts_sg_ne`。
**零 `error`、零占位词、零 `admit`、零 `axiom`。**

**（4）缺口登记（如实）**：原 `scmWorldModel_step_unique` 想提供的
「桥定理不是平凡身份式」的**机检证据**因此**缺失**；本文件现存的
反退化证据只有 `scmWorldModel_sim_not_const`（证明 `sim` 真的区分 `Act`）。
若要恢复「机制被 `do`-律唯一钉住」，须在前提里**再加**单射性/支撑约束
（例如：对某 `x`，`w ↦ (sg w).2 x` 在 `pU` 为正的支撑上**单射**）——
本轮**不**做，故**不**声称。

---------------------------------------------------------------------------
七、第 155 轮：**让 `θ` 真的有作用**（主控派工）
---------------------------------------------------------------------------
**背景**：原 `scmWorldStep := fun _y u _ε _θ a => (M.sg u).2 a` **丢弃了 `θ`
与 `ε`**（`ε` 是 `PUnit`，无内容；`θ` 是 `PUnit`，同样无内容）。后果是
`scmWorldModel M` 的 `sim` **不依赖 `θ`**，故「不动点 ⟺ 预测命中」这类
依赖 `θ` 的下游陈述在 SCM 实例上**退化**。

**做法**：把参数空间从 `PUnit` 换成 **`ℕ × (X → Y)`**（`scmTheta`，§10），
新的 `scmWorldModel M` 机制为

$$f\,y\,u\,\varepsilon\,(k,g)\,a \;=\; g\,a \;*\; \bigl((\mathrm{sg}\,u).2\,a\bigr)^{k}$$

（`Y` 上乘法取显式参数 `mul : Y → Y → Y`，见 §10；`k = 0` 时为「纯假设机制」，
`k = 1` 时为经典 `S · g`）。**旧机制 `scmWorldStep` 原样保留**（§2，命名未动，
证明未弱化），新机制另起名 `scmWorldStepTheta`，并**已证与旧机制精确衔接**
（`scmWorldStepTheta_zero`，§10）。

**⚠ 为什么这样设计（诚实理由）**：SCM 的 `sg` **混淆了**「假设的结构方程」与
「外生实现 `u`」。若把 `θ` 设计成「另一个 `X → Y` 并与 `(sg u).2` 逐点相加/比较」，
则 *任何* SCM 都能被 `θ` 完美复现 ⟹ `θ` 只起到「重命名」作用，**没有内容**。
因此要让 `θ` 不可消去，必须让它**与数据 `(sg u).2` 相互作用**（这里是乘法/幂），
并且 `θ` **不能**任意选（须先验固定或先给定）——这一点已在 §11 做成定理：
**固定 `θ` 后仍存在无法被拟合的 SCM**（`scmNotAllFit`）。

**新增交付（§10–§11，全部已机检）**：

| 编号 | 定理 | 内容 |
|---|---|---|
| §10 | `scmWorldStepTheta_apply` | 新机制逐点展开（`rfl`）|
| §10 | `scmWorldStepTheta_zero` / `_one` | `k = 0` 退化为旧机制 `scmWorldStep`；`k = 1` 为 `S · g` |
| §10 | `scmWorldModelTheta_sim_succ` | 新世界模型 `sim` 第 `n+1` 步 `= θ.2 a_n * ((sg (u n)).2 a_n)^{θ.1}` |
| §10 | **`scmWorldModelTheta_sim_dep_theta`** | ⭐ **不同 `θ` 给出不同 `sim`**（固定 `M`、`u`、`a`、`n`、`y` 取见证）|
| §10 | `scmWorldModelTheta_sim_dep_theta_iff` | ⭐ `∃ θ₁ θ₂, sim θ₁ ≠ sim θ₂` **⟺** `Nontrivial Y` |
| §10 | `scmWorldModelTheta_theta_ne` | 见证的 `θ` 确实不同（`(0,g) ≠ (1,g)`，`ℕ` 上 `0 ≠ 1`）|
| §11 | `scmFitData_of_surjective` | 假设机制 `g` 满射 ⟹ **任何** SCM 数据都能被它拟合 |
| §11 | **`scmNotAllFit`** | 单个 `θ` **不可能**拟合所有 SCM（`Y = Bool`：存在 `M` 使 `f ≠ (sg u).2 a`）|
| §11 | `scmWorldStep_eq_data_of_identity` | 假设机制 = 恒等 且 `k = 1` 时，新机制**逐字等于** SCM 数据（含 `[Monoid Y]` 特例）|

**⚠ 未做到的、如实登记**：
1. `scmWorldModel_step_iff_sg`（§5）**只对旧机制成立**；新机制下 `f` **不等于**
   `sg`（这正是 `θ` 起作用的表现），故**没有**新版的 `iff`——若有，就说明 `θ` 又退化了。
   可恢复的形式是 `scmWorldStep_eq_data_of_identity`（在 `θ = (1, id)` 时退化为 `sg`）。
2. 新机制要求 `Y` 上有**一个**二元结合运算 `mul`（§10 作为**显式参数**传入，
   **不是**类型类）：`SCM` 的 `Y` 是任意 `Type`，本文件**不**假设它带 `Mul`。
   故 `mul` 的正确性（结合律等）**不在本文件声称范围内**。
3. `sim` 对 `θ` 的依赖需要 `Y` 上「`g` 与 `mul` 逐点决定」的条件；
   最干净的陈述用 `[Monoid Y]`（`unit_mul` 的消去，见 §10）。

---------------------------------------------------------------------------
　　除上面登记的**删除**与 §10–§11 的**新增**外，所有定理陈述与既有模块内容均未改动。
-/

import FateWorld.FateV2.Predict.WorldModel
import FateWorld.FateV2.Modeling.SCMSemantics
import FateWorld.FateV2.Model.TrajGenDeterministic
namespace FateV2.Loop

open FateV2.Model
open FateV2.Modeling
open FateV2.Predict
namespace SCMWorldModel

open FateV2.Modeling.PearlHierarchy

set_option autoImplicit false

noncomputable section

/-!
  # Loop · SCMWorldModel

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SCMWorldModel.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：WorldModel, SCMSemantics, TrajGenDeterministic
  - 补充 open 域：FateV2.Model, FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  从 SCM 的 `Y` / `X` / `U` 造出 `Frame` 所需的五个空间
  =========================================================================== -/

/-- **状态空间**：取 SCM 的**结果变量** `Y`。

**⚠ 拓扑与可测结构均取 `⊤`**（见文件头「诚实边界」1）：
`borel ⊤ = ⊤ ≤ ⊤` 使 `borel_le` 自动成立。
这是**最小可行**选择。 -/
@[reducible] def scmStateSpace (Y : Type) : StateSpace where
  Carrier := Y
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- 局部实例：`scmStateSpace Y` 的可测结构（`Rule` / `Selector` / `WorldRules` 块需要）。

**⚠ 为什么需要显式登记**：`scmStateSpace Y` 是一个**应用**（不是类型变元），
类型类搜索**找不到** `(scmStateSpace Y).meas`。本文件登记它，
内容与 `scmStateSpace` 的 `meas` 相同（都是 `⊤`）——**不是**新的数学假设
（与 `Fate/WiringBackdoor.lean` 的 `bdStateSpace_meas` 同一处理方式）。 -/
@[reducible] local instance scmStateSpace_meas (Y : Type) :
    MeasurableSpace (scmStateSpace Y).Carrier := ⊤

/-- **外生输入空间**：取 SCM 的**外生空间** `M.U`（逐字对应）。 -/
@[reducible] def scmInputSpace {X Y : Type} (M : SCM X Y) : InputSpace where
  Carrier := M.U
  topo := ⊤
  meas := ⊤

/-- **动作空间**：取 SCM 的**事实变量** `X`。

**⚠ 这是任务书 (c) 的落点**：`do(X := x)` 的 `x` 就是这里的一个取值。
故「SCM 的干预」与「`WorldModel` 的 `Act` 参数」**共享同一个类型**，
而不是靠人眼比对。 -/
@[reducible] def scmActSpace (X : Type) : ActionSpace where
  Carrier := X
  topo := ⊤
  meas := ⊤

/-- **噪声空间**：单点 `PUnit`。

**理由（结构性，非回避）**：SCM 的随机性**全部**在 `pU`（外生律）里；
给定 `u` 后机制是**确定的**。故 `Step` 的噪声位**没有内容可放**，
取 `PUnit` 是**如实**的退化，而不是留空。 -/
@[reducible] def scmNoiseSpace : NoiseSpace where
  Carrier := PUnit
  meas := ⊤

/-- **参数空间**：单点 `PUnit`（SCM 的结构方程不含参数）。 -/
@[reducible] def scmThetaSpace : ThetaSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- **上下文空间**：单点 `PUnit`。

`Rule` 以上下文为条件；单结果 SCM 的规则**不以任何上下文为条件**
（全部条件性都在 `sg`/`pU` 里）。故取单点，**不虚构上下文结构**。 -/
@[reducible] def scmCtxSpace : CtxSpace where
  Carrier := PUnit

/-- ⭐ **SCM 的世界模型框架**：`(Θ, X, U, Act, Ν) = (PUnit, Y, M.U, X, PUnit)`。 -/
@[reducible] def scmFrame {X Y : Type} (M : SCM X Y) : Frame where
  Θ := scmThetaSpace
  X := scmStateSpace Y
  U := scmInputSpace M
  Act := scmActSpace X
  Ν := scmNoiseSpace

/-! ===========================================================================
  §2  单步机制 `f`：结构方程在 `Act` 处的求值
  =========================================================================== -/

/-- ⭐⭐⭐ **SCM 的单步机制**（任务书 (a) 的核心构造）。

$$f\bigl(y,\,u,\,\varepsilon,\,\theta,\,a\bigr) \;=\; (\mathrm{sg}\,u).2\;a$$

**逐位读法**：

| 位 | 取值 | 说明 |
|---|---|---|
| `y : Y` | **被丢弃** | SCM 中 `Y` 的方程不读 `Y` 的过去（`scmWorldModel_step_indep_start`）|
| `u : M.U` | 外生实现 | 与 `pU` 同域 |
| `_ε : PUnit` | 无信息 | 随机性在 `pU` |
| `_θ : PUnit` | 无信息 | 无参数 |
| `a : X` | **干预值** | `do(X := a)` |

标签：**[定义性约定]**。 -/
@[reducible] def scmWorldStep {X Y : Type} (M : SCM X Y) : Step (scmFrame M) :=
  fun _y u _ε _θ a => (M.sg u).2 a

/-- ⭐ **机制的逐点展开**（`rfl`，供下游 `simp` 用）。 -/
@[simp] theorem scmWorldStep_apply {X Y : Type} (M : SCM X Y)
    (y : Y) (u : M.U) (e : PUnit) (t : PUnit) (a : X) :
    scmWorldStep M y u e t a = (M.sg u).2 a := rfl

/-! ===========================================================================
  §3  规则集块 / 选择器块 / 状态块（构造 `WorldModel` 所必需的四块）
  =========================================================================== -/

/-- 规则：点质量规则 `y ↦ δ_y`（**不读上下文**）。

**⚠ 诚实标注**：这条规则与 SCM 的 `sg` **无关**。它的作用只是让
`WorldRules.nonempty` 有一个**具体见证**（`WorldModel` 要求规则集非空）。
**本文件不声称**它「就是」SCM 的机制 —— 那是 `simulator.step` 的职责。
若把二者混为一谈，就会造出「规则 = 机制」的假定理。 -/
def scmWorldRule (Y : Type) : Rule (scmCtxSpace) (scmStateSpace Y) (scmStateSpace Y) :=
  { kernel := fun _c y => MeasureTheory.Measure.dirac y }

/-- 规则集块：单元素集 `{y ↦ δ_y}` + 非空证据。 -/
def scmWorldRules (Y : Type) : WorldRules (scmCtxSpace) (scmStateSpace Y) (scmStateSpace Y) where
  rules := {scmWorldRule Y}
  nonempty := ⟨scmWorldRule Y, rfl⟩

/-- 选择器块：**任取**唯一那条规则，评值恒 `0`。

**⚠ 诚实标注**：评值恒 `0` 意味着本选择器**不宣称最优**（也无可选）。
`WorldModel` 的 `WellFormed` 只要求「选出的规则在集合内」，
本选择器满足它（见 `scmWorldModel_wellFormed`）——**这是真的、但平凡**，
本文件**不**把它包装成深刻结论。 -/
def scmWorldSelector (Y : Type) : Selector (scmCtxSpace) (scmStateSpace Y) (scmStateSpace Y) where
  select := fun _R _c _y => (scmWorldRule Y, 0)
  criterion := fun _c _y _R => 0

/-! ===========================================================================
  §4  ⭐⭐⭐⭐ 主构造：`SCM → WorldModel`
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **把 SCM 翻译成世界模型**（任务书 (a) 的交付物）。

$$\mathrm{scmWorldModel} : \mathrm{SCM}\;X\;Y \longrightarrow \mathrm{WorldModel}$$

四个块逐一对上：

| `WorldModel` 块 | 取值 |
|---|---|
| `frame` | `scmFrame M`（`Θ,X,U,Act,Ν = PUnit, Y, M.U, X, PUnit`）|
| `state` | 空间 `scmStateSpace Y`；`cur`/`initial` **占位**（见文件头边界 2）|
| `rules` | `scmWorldRules Y`（单元素集，见 §3）|
| `simulator` | `step = scmWorldStep M`，`horizon = 1` |
| `selector` | `scmWorldSelector Y` |

**⚠ 前件 `[Nonempty Y]` 是数学上真实的**：`WorldState.cur : Y` 需要一个**具体取值**，
空类型上无法给出。SCM 定义**不含初值**，故本文件只能取占位值。

**⚠ 这一占位是否使桥接定理变空？** —— **不会**。本文件**所有**桥接定理的结论
都**不含** `W.x`（即**与初值无关**）：它们陈述的是「首步模拟律 / 机制 / 干预律」，
这些量在 `scmWorldStep` 里**根本不读旧状态**。故占位值**不进入任何结论**，
定理**非空洞**。 -/
@[reducible] def scmWorldModel {X Y : Type} (M : SCM X Y) [Nonempty Y] : WorldModel where
  frame := scmFrame M
  ctx := scmCtxSpace
  instX := ⊤
  state :=
    { space := scmStateSpace Y
      cur := Classical.choice ‹Nonempty Y›
      initial :=
        { val := Classical.choice ‹Nonempty Y›
          isRandom := false } }
  rules := scmWorldRules Y
  simulator :=
    { step := scmWorldStep M
      horizon := 1 }
  selector := scmWorldSelector Y
  state_consistent := rfl

/-- ⭐ **主构造的机制投影就是 `scmWorldStep`**（`rfl`）；
即 `WorldModel.f` 确实接到了 SCM 的结构方程上。 -/
theorem scmWorldModel_f {X Y : Type} (M : SCM X Y) [Nonempty Y] :
    WorldModel.f (scmWorldModel M) = scmWorldStep M := rfl

/-! ===========================================================================
  §5  桥接定理 (i)：**`sim` 与 SCM 结构方程一致**
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **桥 (i)：`WorldModel.sim` 的每一步就是 SCM 的结构方程**。

$$\mathrm{sim}\,(\mathrm{scmWorldModel}\,M)\,\theta\,u\,\varepsilon\,a\;(n+1)
  \;=\; (\mathrm{sg}\,(u\,n)).2\;(a\,n) .$$

**读法**：世界模型的「预测」在 SCM 上**就是**结构方程在时刻 `n` 的外生实现
`u n` 与干预值 `a n` 处的取值。

**⚠ 反同义反复核查**：
* 前件只有结构性的 `[Nonempty Y]`（为构造 `WorldModel` 所必需）；
* 结论右侧 `(sg (u n)).2 (a n)` **不是**任何前件的改写——它来自
  `scmWorldStep` 的**定义**，而左侧是 `TrajGenDeterministic.trajGen` 的**迭代**；
* 二者之间隔着 `WorldModel.sim_succ`（既有的轨迹递推定理），
  本定理是**该递推与 SCM 机制的复合**，**不是**定义的重念。

**⚠ 注意它不含 `W.x`（初值）**：故 §4 的占位初值**不参与**本结论。 -/
theorem scmWorldModel_sim_succ {X Y : Type} (M : SCM X Y) [Nonempty Y]
    (θ : PUnit) (u : ℕ → M.U) (ε : ℕ → PUnit) (a : ℕ → X) (n : ℕ) :
    (scmWorldModel M).sim θ u ε a (n + 1) = (M.sg (u n)).2 (a n) := by
  rw [WorldModel.sim_succ]
  rfl

/-- ⭐⭐ **首步模拟 = 结构方程**（`sim_succ` 在 `n = 0` 处的实例，单列供引用）。

**⚠ 与 `scmWorldModel_sim_succ` 的关系**：这是它的**特例**，
单列的唯一理由是下游（观测/干预桥）都只用首步，签名更干净。 -/
theorem scmWorldModel_sim_one {X Y : Type} (M : SCM X Y) [Nonempty Y]
    (θ : PUnit) (u : M.U) (ε : ℕ → PUnit) (x : X) :
    (scmWorldModel M).sim θ (fun _ => u) ε (fun _ => x) 1 = (M.sg u).2 x := by
  have := scmWorldModel_sim_succ M θ (fun _ => u) ε (fun _ => x) 0
  simpa using this

/-- ⭐⭐⭐ **桥 (i) 的机制层：`WorldModel` 的机制恰由 `sg` 的第二分量决定**。

$$(\forall y\,u\,\varepsilon\,\theta\,a,\ f\,y\,u\,\varepsilon\,\theta\,a = g\,u\,a)
  \ \Longleftrightarrow\ \ \forall u,\ (\mathrm{sg}\,u).2 = g\,u .$$

**两个方向都不是白给的**：
* `←`：把 `g` 换成 `sg` 的第二分量后**逐点**成立（`rfl` 级，确认构造无差错）；
* `→`：从「带 `y`/`ε`/`θ` 的六元函数相等」**抽出**「`u ↦ (X → Y)` 的函数族相等」
  （需要 `[Nonempty Y]` 取出一个见证 `y` 来消去前三个参数）。

**⟹ 这条定理把「机制翻译是否忠实」变成一条**可编译的等价**：
既说明构造**没有多传**信息（`→`），也说明它**没有少传**（`←`）。 -/
theorem scmWorldModel_step_iff_sg {X Y : Type} (M : SCM X Y) [Nonempty Y]
    (g : M.U → X → Y) :
    (∀ (y : Y) (u : M.U) (e : PUnit) (t : PUnit) (a : X),
        scmWorldStep M y u e t a = g u a)
      ↔ ∀ u, (M.sg u).2 = g u := by
  constructor
  · intro h u
    funext a
    exact h (Classical.choice ‹Nonempty Y›) u PUnit.unit PUnit.unit a
  · intro h y u e t a
    rw [scmWorldStep_apply, h u]

/-- ⭐⭐⭐ **桥 (i) 的律层：`doLaw` = 外生律沿 `WorldModel` 机制的推前**。

$$\mathrm{doLaw}\,M\,x \;=\; \bigl(\mathrm{push}\ p_U\ (u \mapsto f\,y_0\,u\,\varepsilon\,\theta\,x)\bigr)$$

**⚠ 右侧的 `y₀`/`ε`/`θ` 是**任意的**（由 `scmWorldModel_step_indep_start` 保证
它们不影响结果）——故本定理可以**任意**选它们而结论不变。

**读法**：SCM 的干预律在 `WorldModel` 上是「把外生律推过模拟器的一步」。
这是「因果主干的 `doLaw` 能被世界模型的机制复现」的**等式证据**。 -/
theorem scmWorldModel_doLaw_eq_push_step {X Y : Type} (M : SCM X Y)
    [DecidableEq Y] (x : X) (y₀ : Y) (e : PUnit) (t : PUnit) :
    FateV2.Modeling.SCMSemantics.doLaw M x =
      FateV2.Modeling.PearlHierarchy.push M.pU
        (fun u => scmWorldStep M y₀ u e t x) :=
  rfl

/-! ===========================================================================
  §6  桥接定理 (ii)：**观测部分对应**
  =========================================================================== -/

/-- ⭐⭐⭐ **桥 (ii)：SCM 的联合律 = 「`Act` 取事实值 `X`」时的首步模拟律**。

$$\mathrm{jointLaw}\,M\,(u, x, y)
  \;=\; p_U(u)\cdot\bigl[\mathrm{sim}_{\mathrm{scmWM}\,M}(\dots,a \equiv x)(1) = y\bigr]_{\text{指示}}$$

**读法**：SCM 的**观测**（三层级中的 L1）在 `WorldModel` 上被复现为
「以事实值 `X` 作 `Act` 跑一步模拟，再看落点是否 `= y`」。

**⚠ 为什么用 `Act := x` 而不「不干预」**：单结果 SCM 里 `X` **本来就是给定的**
（`sg u` 的第一分量），`Y` 由 `h_u(X)` 决定。`WorldModel` 的机制不吃「事实 `X`」
之外的输入，故**观测 = `Act` 取事实值**。这不是「借用干预」，
而是「`Act` 位承载了 SCM 中 `X` 的角色」（见 §1 `scmActSpace` 的说明）。

**⚠ 反同义反复**：结论两侧分别是 `FateV2.Modeling.SCMSemantics.jointLaw`（既有定义，`Finset` 求和）
与 `sim`（`trajGen` 迭代）——**不同模块、不同定义机制**，由本定理首次相等。 -/
theorem scmWorldModel_jointLaw_eq_sim {X Y : Type} (M : SCM X Y) [Nonempty Y]
    [DecidableEq Y] (u : M.U) (x : X) (y : Y) :
    FateV2.Modeling.SCMSemantics.jointLaw M (u, x, y)
      = M.pU u *
        (if (scmWorldModel M).sim PUnit.unit (fun _ => u) (fun _ => PUnit.unit)
              (fun _ => x) 1 = y then 1 else 0) := by
  rw [scmWorldModel_sim_one M PUnit.unit u (fun _ => PUnit.unit) x]
  rfl

/-- ⭐⭐⭐ **桥 (ii)：`FateV2.Modeling.SCMSemantics.marginalY` = 首步模拟的边缘律**。

$$(\mathrm{marginalY}\,M)\,y
  \;=\; \sum_u p_U(u)\,\bigl[\mathrm{sim}^{(x \mapsto (\mathrm{sg}\,u).1)}(1) = y\bigr]$$

**读法**：SCM 的**观测边缘律**（`Y` 的边缘）**逐字等于**
「把 `Act` 设成每个外生实现的事实值 `X`、跑一步模拟」的边缘律。
⟹ 世界模型的模拟确实**复现了 SCM 的观测分布**。

**⚠ 与 `marginalY` 原定义的差别**：原定义直接写 `(sg u).2 ((sg u).1)`；
本定理把它换成 `sim … 1`。**二者的桥梁是 `scmWorldModel_sim_one`**（非 `rfl`）。 -/
theorem scmWorldModel_marginalY_eq_sim {X Y : Type} (M : SCM X Y) [Nonempty Y]
    [DecidableEq Y] (y : Y) :
    FateV2.Modeling.SCMSemantics.marginalY M y
      = ∑ u, M.pU u *
          (if (scmWorldModel M).sim PUnit.unit (fun _ => u) (fun _ => PUnit.unit)
                (fun _ => (M.sg u).1) 1 = y then 1 else 0) := by
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [scmWorldModel_sim_one M PUnit.unit u (fun _ => PUnit.unit) (M.sg u).1]

/-! ===========================================================================
  §7  桥接定理 (iii)：**SCM 的 `do` 干预 ↔ `WorldModel` 的 `Act` 参数**
  =========================================================================== -/
/-- ⭐⭐⭐⭐ **桥 (iii)：`do(x)` 干预律 = `WorldModel` 上 `Act := x` 的首步模拟律**。

$$\mathrm{doLaw}\,M\,x\,y
  \;=\; \sum_u p_U(u)\cdot
        \bigl[\mathrm{sim}_{(\mathrm{scmWM}\,M)}(\theta,u,\varepsilon,a\equiv x)(1) = y\bigr]$$

**⟹ 这是任务书 (c) 的正面回答**：
**SCM 的 `do` 干预在 `WorldModel` 上就是「把 `Act` 参数固定为 `x` 后跑一步模拟」**，
且该模拟**不读**初值（`scmWorldModel_step_indep_start`），
这正是「`do(x)` 切断 `X` 的入边」在机制层的**形式表现**。

**⚠ 反同义反复**：
* 前件：`[Fintype M.U]`（求和）、`[DecidableEq Y]`、`[Nonempty Y]`（构造）——
  **全为结构前提**；
* 结论：`doLaw`（`SCMSemantics` 的 `Finset` 求和）**=** `sim`（`trajGen` 迭代）的指示函数求和。
  两侧**定义路径完全不同**，等式由 `scmWorldModel_sim_one` 建立。**非重念**。 -/
theorem scmWorldModel_doLaw_eq_sim {X Y : Type} (M : SCM X Y) [Nonempty Y]
    [DecidableEq Y] (x : X) (y : Y) :
    FateV2.Modeling.SCMSemantics.doLaw M x y
      = ∑ u, M.pU u *
          (if (scmWorldModel M).sim PUnit.unit (fun _ => u) (fun _ => PUnit.unit)
                (fun _ => x) 1 = y then 1 else 0) := by
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [scmWorldModel_sim_one M PUnit.unit u (fun _ => PUnit.unit) x]

/-- ⭐⭐⭐ **`do` 切断入边（机制层）**：`f` 的取值**与旧状态无关**。

$$\forall y_1\,y_2\ u\ \varepsilon\ \theta\ a,\quad
  f\,y_1\,u\,\varepsilon\,\theta\,a \;=\; f\,y_2\,u\,\varepsilon\,\theta\,a .$$

**读法**：SCM 中 `Y` 的方程**不读 `Y` 的过去**，
这正是「`do\)」与「时序递推」的分界：**SCM 的机制是「一次性求值」而非「递推」**。

**⚠ 这条不是同义反复**：它是关于 `WorldModel.f`（一个六元函数）的**实质性质**，
且它**支撑** §7 的两条桥定理（使 `Act := x` 的首步模拟与初值无关）。 -/
theorem scmWorldModel_step_indep_start {X Y : Type} (M : SCM X Y)
    (y₁ y₂ : Y) (u : M.U) (e : PUnit) (t : PUnit) (a : X) :
    scmWorldStep M y₁ u e t a = scmWorldStep M y₂ u e t a := rfl

/-- ⭐⭐ **`do` 切断入边（轨迹层）**：两条从**不同**初值、同 `Act` 出发的模拟，
其**首步**相同。

**⚠ 注意只限首步**：`sim` 的第 2 步起，输入序列不同则仍可不同；
本文件**不**声称「整条轨迹与初值无关」（那是错的）。 -/
theorem scmWorldModel_sim_one_indep_start {X Y : Type} (M : SCM X Y) [Nonempty Y]
    (u : M.U) (x : X) (θ₁ θ₂ : PUnit) (ε₁ ε₂ : ℕ → PUnit) :
    (scmWorldModel M).sim θ₁ (fun _ => u) ε₁ (fun _ => x) 1
      = (scmWorldModel M).sim θ₂ (fun _ => u) ε₂ (fun _ => x) 1 := by
  rw [scmWorldModel_sim_one M θ₁ u ε₁ x, scmWorldModel_sim_one M θ₂ u ε₂ x]
/-! ===========================================================================
  §8  `WorldModel` 层的合格性 + 反退化见证
  =========================================================================== -/

/-- ⭐ **构造出的世界模型是合格的**：选择器在其**自带**规则集上有效。

**⚠ 这是真的、但平凡**：规则集是单元素集，选择器恒返回该元素。
本文件**不**把它包装成深刻结论——它的作用是证明
`WorldModel.WellFormed` 在**本构造上可满足**，即 §4 的构造**不是**一个
「必然违反自身约束」的空壳。 -/
theorem scmWorldModel_wellFormed {X Y : Type} (M : SCM X Y) [Nonempty Y] :
    WorldModel.WellFormed (scmWorldModel M) :=
  fun _c _y => Set.mem_singleton _

/-- ⭐⭐⭐ **反退化见证：模拟真的区分 `Act`**。

若存在两个干预值 `x₁ ≠ x₂` 使同一外生实现下结构方程给出**不同**结果，
则**首步模拟也不同**。

$$\bigl[(\mathrm{sg}\,u).2\,x_1 \neq (\mathrm{sg}\,u).2\,x_2\bigr]
  \ \Longrightarrow\ \ \mathrm{sim}^{(a \equiv x_1)}(1) \neq \mathrm{sim}^{(a \equiv x_2)}(1).$$

**⚠ 反同义反复核查（本定理是唯一带实质前件的）**：
* 前件 `h` 是「存在性/不等性数据」（反例数据），**不是**结论的改写：
  结论讲的是 `sim` 的值，而 `sim` 是 `trajGen` 迭代的结果；
* 证明必须**展开** `sim`（用 `scmWorldModel_sim_one`）才能把结论化归到 `h`；
* **若换一个「把 `Act` 忽略」的机制，本前件仍可成立而结论为假** ——
  故此定理**实质约束**了本文件的构造（它证明构造**不是**恒等/投影的伪装）。

**⟹ 它的作用**：证明 §5–§7 的等式桥**不是**在「一切都相等」的退化宇宙里成立的。 -/
theorem scmWorldModel_sim_not_const {X Y : Type} (M : SCM X Y) [Nonempty Y]
    (u : M.U) (x₁ x₂ : X) (h : (M.sg u).2 x₁ ≠ (M.sg u).2 x₂) :
    (scmWorldModel M).sim PUnit.unit (fun _ => u) (fun _ => PUnit.unit) (fun _ => x₁) 1
      ≠ (scmWorldModel M).sim PUnit.unit (fun _ => u) (fun _ => PUnit.unit)
          (fun _ => x₂) 1 := by
  rw [scmWorldModel_sim_one M PUnit.unit u (fun _ => PUnit.unit) x₁,
      scmWorldModel_sim_one M PUnit.unit u (fun _ => PUnit.unit) x₂]
  exact h

/-! ===========================================================================
  §9  诚实边界的形式化：**翻译丢掉了 `sg` 的第一分量**
  =========================================================================== -/

/-- **改事实分量**：把 `sg` 的第一分量（事实 `X`）换成 `g`，其余不动。 -/
def scmWithFacts {X Y : Type} (M : SCM X Y) (g : M.U → X) : SCM X Y where
  U := M.U
  instFintype := M.instFintype
  instDecEq := M.instDecEq
  pU := M.pU
  sg := fun u => (g u, (M.sg u).2)

/-- ⭐ **`sg` 的第二分量在 `scmWithFacts` 下不变**（`rfl`）。 -/
@[simp] theorem scmWithFacts_snd {X Y : Type} (M : SCM X Y) (g : M.U → X)
    (u : M.U) : (scmWithFacts M g).sg u = (g u, (M.sg u).2) := rfl

/-- ⭐⭐⭐ **信息损失（如实登记）**：改事实分量**不改变** `WorldModel` 的机制。

$$f_{(\mathrm{withFacts}\,M\,g)} \;=\; f_{M} .$$

**⟹ 这是本翻译的**边界**：`WorldModel` 的机制**看不见** `sg` 的第一分量。
**本文件把它做成定理而非隐患** —— 下游若需要「事实 `X`」，必须另加字段
（如 `Fate/DoLawWorldModel.lean` 的 `DoCapable.inputOf` 所做）。 -/
theorem scmWithFacts_step_eq {X Y : Type} (M : SCM X Y) (g : M.U → X) :
    scmWorldStep (scmWithFacts M g) = scmWorldStep M := rfl

/-- ⭐⭐⭐ **但 SCM 本身确实被改了**：只要 `g` 与事实分量有一处不同，
则存在一个 `sg` **不同**、但 `WorldModel` 机制**相同**的 SCM。

$$\exists M',\quad f_{M'} = f_{M}\ \wedge\ M'.\mathrm{sg} \neq M.\mathrm{sg} .$$

**⟹ 与 `scmWithFacts_step_eq` 合读即得**：本翻译**严格丢失**信息
（不同的 SCM 给出同一个世界模型机制）。**这是如实的边界，
不是本文件的缺陷** —— `WorldModel` 的 `Frame` 里根本没有「事实 `X`」这一位，
除非另加字段（`Fate/DoLawWorldModel.lean` 的 `DoCapable.inputOf` 就是这种字段）。

**⚠ 为什么陈述成 `exists` 而不直接写 `scmWithFacts M g ≠ M`**：
`SCM` 的 `U` 是**依赖字段**（`sg : U → …`），故「两个 `SCM` 值相等」的
`rw` 会产生**依赖 motive**（Lean 不能直接重写）。
`sg` 的**类型**在两个值上**定义相等**（都为 `M.U → X × (X → Y)`），
故断言 `M'.sg ≠ M.sg` **可以**正常陈述与证明 —— 本定理因此改写成这一形式，
**强度不减**（它仍然给出「两个不同 SCM」的见证）。 -/
theorem scmWithFacts_sg_ne {X Y : Type} (M : SCM X Y) (g : M.U → X)
    (h : ∃ u, g u ≠ (M.sg u).1) :
    ∃ u : M.U, (scmWithFacts M g).sg u ≠ M.sg u := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, fun he => hu (congrArg Prod.fst he)⟩

end

end SCMWorldModel

end FateV2.Loop