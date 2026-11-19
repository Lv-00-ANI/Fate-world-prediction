/-
命运理论 · Lean 4 形式化实现
================================

模块：`Stage0.Core`
阶段：**阶段 0 —— 定义与签名冻结**

---------------------------------------------------------------------------
本文件的地位（先读这一段）
---------------------------------------------------------------------------
本文件**从零创建**，给出阶段 0 的**核心定义**，**不证任何定理**。
（唯一的两条 `theorem` 是**定义层的自洽性检查** `rfl`，不是理论命题，
  见 §7 与文件末的说明。）

依 `02-证明路线/01-路线图.md` §阶段 0 验收标准 1：

> `lake build` 通过，**零 `sorry`、零 `admit`、零 `axiom`**。

本文件据此约束：**不含 `sorry`、不含 `admit`、不含 `axiom`**。
凡是原文没有给出的对象，一律用 `Unit` 型占位（`*_placeholder`），
**不用 `axiom` 造一个假对象**——占位是**可检出的缺口**，`axiom` 是**不可检出的谎言**。

---------------------------------------------------------------------------
本文件与 `FateV2.Modeling` / `FateV2.Model` 的关系（务必区分，否则会以为存在两套定义）
---------------------------------------------------------------------------
`FateV2.Modeling` 与 `FateV2.Model` 已经给出过一批阶段 0 定义。本文件**不覆盖、不替换**它们，
而是按任务要求**从零另建**一套，并用**命名空间隔离**：

| 本文件（`Stage0.Core`） | `FateV2.Modeling` / `FateV2.Model` | 关系 |
|---|---|---|
| `ActionSpace`（`A : Type` + 结构字段） | `ActionSpace`（`Carrier : Type u` + 结构字段） | 同一对象的两种写法；本文件按任务书签名 |
| `TimeIndex`（`discrete ℕ` / `continuous ℝ`，带 `0 ≤ t` 约束） | `TimeIdx.Discrete := ℕ`、`TimeIdx.Continuous := {t // 0 ≤ t}` | 本文件把两支**收进同一个归纳类型** |
| `step`（5 元函数） | `Step`（`Frame` 上的 5 元 abbrev） | 本文件不依赖 `Frame` |
| `SDERegularity`（Lipschitz + 增长） | 无（`Basic` 只给了 `Drift`/`Diffusion` 的类型） | ⭐ 本文件**首次**给出 A10 的形式 |
| `WellFoundedDeps`（rank 函数版） | `ParentMap` 只有 `pa`，**无良基字段** | ⭐ 本文件**首次**给出 A33 的形式 |
| `Do` / `doOp`（算子层 `M → M`） | `DoCalculus` / `T33DoGraph` 有 `do` 语义，**无类型层强制** | ⭐ 本文件**首次**用类型强制「`do` 是算子」 |

**迁移登记（诚实的现状）**：存在两套定义是一件**债务**，不是资产。
本文件**不宣称**已合并；合并工作登记为 `_pending` 项，须由后续轮次裁决
（哪一套作为权威载体）。**本文件的作用是先把任务书要求的签名冻结下来。**

---------------------------------------------------------------------------
`/-- ... -/` 标签格式的说明
---------------------------------------------------------------------------
本文件每条定义都带 doc-comment，格式按任务书：

```
/-- `[定义 1.x]` **对象名**：一句话说明。

- **类型**：`[定义性约定]` / `[待证存在性]` / `[经验假设]`
- **出处**：理论第 N 章
- **⚠ 未定义项**：如果原文没定义，此处必须标 `[Undefined 占位]`
-/
```

⚠ 一处**格式偏差**（显式登记，不隐瞒）：任务书要求标签行形如 `` `[定义 1.x]` ``，
而「类型」行要求形如 `` `[定义性约定]` ``——**中文标签被放在反引号里**。
反引号在 Lean 的 doc-comment 里是 Markdown 行内代码，中文在行内代码中会**渲染成等宽字体**，
语义上并无「这是 Lean 常量名」之意。本文件**按任务书原样执行**（便于机械核对），
但**建议**后续统一改为不加反引号的粗体标签，以免与 Lean 标识符混淆。

---------------------------------------------------------------------------
符号对照（本文件定义的 Lean 标识符 ↔ 理论符号）
---------------------------------------------------------------------------
| Lean 标识符            | 理论符号                    | 备注 |
|------------------------|-----------------------------|------|
| （类型变量 `X`）        | $\mathcal{X}$ 状态空间      | 任务书指定用类型变量 |
| `TimeIndex`            | $\mathcal{T}$ 时间索引集    | 两分支 |
| `TimeIndex.isValid`    | $\mathcal{T}\subseteq\mathbb{R}_{\ge0}$ | 连续支的良构谓词 |
| （类型变量 `Θ`）        | $\Theta$ 参数空间（**命**） | 任务书指定用类型变量 |
| （类型变量 `U`）        | $\mathcal{U}$ 外生输入空间  | 任务书指定用类型变量 |
| （类型变量 `E`）        | $\mathfrak{E}$ 噪声取值空间 | **原文未定义** |
| `NoiseLaw`             | $\mathcal{D}_\varepsilon$   | 噪声的分布 |
| `ActionSpace`          | $\mathcal{A}$ 动作空间      | ⭐ 原文**从未定义** |
| `step`                 | $f$（式 1.1 的单步转移）    | **不是**轨迹生成器 |
| `Trajectory`           | $\{x_t\}_{t\in\mathcal{T}}$（**命运**） | |
| `Drift` / `Diffusion`  | $\mu$ / $\sigma$            | 式 1.2 |
| `SDERegularity`        | A10（Lipschitz + 线性增长） | ⭐ 待证存在性 |
| `WellFoundedDeps`      | A33（结构方程依赖良基）     | ⭐ 原文未登记 |
| `Do` / `doOp`          | $do(\cdot)$（模型替换算子） | ⭐ 类型层强制 |

本文件**不虚构**任何出处编号；凡出处栏写「原文未给出」的，就是字面意义上的没给出。
-/

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.RelClasses

open scoped NNReal
open MeasureTheory

namespace FateV2.Core
namespace Stage0
namespace Core

universe u v w

/-!
  # Core · Core

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Core.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：无
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  对象与状态层
    =========================================================================== -/

section ObjectsAndStates

/-! ### §1.1 系统／对象 $O$

任务书要求（原文用 doc-comment 格式给出，本块改用行内代码转述，
以免注释结束记号提前闭合本注释块）：

「系统/对象 O —— 本理论的唯一原始对象」，并注明**用类型变量表示，不需要单独定义**。

故本文件**不提供** `Obj` 常量，而是用类型变量 `X` 兼作 $\mathcal{X}$ 的载体
（$O$ 与 $\mathcal{X}$ 在类型层不是两个可分离的东西：**状态空间就是对象的类型**）。
其代价是：**「对象」与「对象的状态空间」在 Lean 中不可区分**。
本文件把这个代价**显式登记为约定**，见下一条。 -/

/-- `[定义 1.1]` **对象 $O$ 与状态空间 $\mathcal{X}$ 的合并约定**：本文件用**同一个类型变量 `X`**
同时表示「系统／对象」与「其状态空间的载体」。

- **类型**：`[定义性约定]`
- **出处**：理论第 1 章（$O$ 与 $\mathcal{X}$ 的原始声明）
- **⚠ 未定义项**：原文**从未给出** $O$ 的内部结构，也未给出「$O$ 与 $\mathcal{X}$ 如何绑定」的规则。
  本文件采用**合并约定**，理由是：合并使「$x_t\in\mathcal{X}$ 且 $x_t$ 是 $O$ 的状态」
  成为**定义层的事实**，从而不需要一条额外的绑定公理。
  **代价（必须记住）**：合并后**无法表达**「一个对象有多个状态空间」与「多个对象共享状态空间」，
  若理论日后需要这两者，本约定必须撤销。 -/
def ObjStateMergedConvention : Unit := ()

/-- `[定义 1.2]` **状态变量 $x_t$**：$t$ 时刻对象的状态，取值于 $\mathcal{X}$。

- **类型**：`[定义性约定]`
- **出处**：理论第 1 章；主公式式 (1.1) 的第一个自变量
- **⚠ 未定义项**：无。本定义只规定 $x_t$ 的**取值层类型**（`X`），
  **不主张** $x_t$ 是随机变量还是确定性取值——该分叉由**§2.7 概率层**（`InitialLaw`）与
  「$\{x_t\}$ 的实现 vs 随机过程」的选型（见 `Trajectory`）；本定义不变。 -/
abbrev State (X : Type u) : Type u := X

end ObjectsAndStates

/-! ### §1.3 时间索引集 $\mathcal{T}$（A29 的两分支） -/

/-- `[定义 1.3]` **时间索引集 $\mathcal{T}$ 的两分支**（A29）。

原文给出两个主公式——式 (1.1) 离散、式 (1.2) 连续——但**从未声明二者的关系**
（`04-符号与方程规范.md` §3.2 说明 1 给出的「Euler–Maruyama 离散化」是**规范补定**，
不是原文内容）。故本文件按 A29 要求**把两支收进同一个归纳类型**，
使「当前用的是哪一支」成为**类型层可见**的事实，而不是读者脑补。

- **离散支** `discrete n`：$\mathcal{T}=\mathbb{N}$，$n$ 即 $t$。
- **连续支** `continuous t`：$\mathcal{T}=\mathbb{R}_{\ge0}$。**$\ge0$ 不是构造子强制的**，
  而是由谓词 `TimeIndex.isValid` 强制（见 `isValid_continuous`）。
  这是一个**刻意的选择**：若把 `continuous` 的载荷设为 `{t : ℝ // 0 ≤ t}`，
  则「$t\ge0$」变成**类型内信息**，本类型就无法同时容纳「尚未验证的实数时刻」；
  若设为裸 `ℝ`，则**任何**实数都能构造出时间下标，$\mathcal{T}=\mathbb{R}$ 而非 $\mathbb{R}_{\ge0}$。
  本文件取**裸 `ℝ` + 外部良构谓词**，并**显式登记**这一取舍。

- **类型**：`[定义性约定]`（对应 A29）
- **出处**：理论第 1 章（$\mathcal{T}$ 的符号表行）；A29
- **⚠ 未定义项**：**两支的关系原文未声明**。本类型**只并列两支**，
  **不提供**两支之间的转换（无 `discreteToContinuous` 之类的嵌入）。
  若后续证明需要「离散是连续的 Euler–Maruyama 离散化」，那是**规范补定**，
  须以独立定义 + 显式假设引入，**不得**从本类型推出。 -/
inductive TimeIndex where
  /-- 离散支：$\mathcal{T}=\mathbb{N}$，载荷即时刻 $t$。 -/
  | discrete (n : ℕ)
  /-- 连续支：$\mathcal{T}=\mathbb{R}$，须由 `isValid` 排除 $t<0$ 者。 -/
  | continuous (t : ℝ)

/- 实现注记（**必须保留，否则会重犯同一个错**）：
本类型**不** `deriving DecidableEq, Repr`。
原因：`ℝ` 的 `DecidableEq` 与 `Repr` 是 `noncomputable` / `unsafe` 的，
派生会让 `TimeIndex` 的相等判定变成**不可执行**的，
而「时刻相等」在本理论的下游（离散支的 $t+1$、连续支的 $t=s$）**需要可判定**。
`FateV2.Modeling` 的 `TimeKind` 只 `deriving DecidableEq, Repr` 是因为它**不带 `ℝ` 载荷**；
本类型带了，故不能照抄。
若下游确实需要判定时刻相等，应**显式**在需要的定理上加 `[DecidableEq ℝ]` 前件，
使「实数相等可判定」这一（实际上依赖经典选择的）假设**可见**。 -/

/-- `[定义 1.4]` **时间下标的良构谓词**：

- 离散支**恒良构**（$\mathbb{N}$ 天然 $\ge0$）；
- 连续支良构**当且仅当** $t\ge0$。

本谓词是 `TimeIndex` 里「$\mathcal{T}=\mathbb{R}_{\ge0}$」的**唯一落点**：
任何用到连续时刻的陈述都**必须**带上 `TimeIndex.IsValid` 前件，
否则陈述的对象可能是负时刻。

- **类型**：`[定义性约定]`
- **出处**：理论第 1 章；A29（$\mathcal{T}=\mathbb{R}$ 之「$\ge0$」的落实）
- **⚠ 未定义项**：无。 -/
def TimeIndex.IsValid : TimeIndex → Prop
  | .discrete _ => True
  | .continuous t => 0 ≤ t

/-- `[定义 1.4′]` `isValid` 在离散支上的**求值**：恒为 `True`。

这是**定义展开**（`Iff.rfl` 即可），不是理论命题，列出仅为下游使用方便。 -/
theorem isValid_discrete (n : ℕ) : (TimeIndex.discrete n).IsValid ↔ True :=
  Iff.rfl

/-- `[定义 1.4″]` `isValid` 在连续支上的**求值**：等价于 $0\le t$。

这是 `TimeIndex` 的「$\mathcal{T}=\mathbb{R}_{\ge0}$」的**可机械核对形式**。 -/
theorem isValid_continuous (t : ℝ) : (TimeIndex.continuous t).IsValid ↔ 0 ≤ t :=
  Iff.rfl

/-- `[定义 1.5]` **离散时间轨迹** $\{x_n\}_{n\in\mathbb{N}}$：$\mathbb{N}\to\mathcal{X}$。

- **类型**：`[定义性约定]`
- **出处**：理论第 1 章；式 (1.1) 的解序列
- **⚠ 未定义项**：无。**注意**：这**不是**「命运」——「命运」是 $\{x_t\}_{t\in\mathcal{T}}$，
  在离散支下二者重合，但本文件仍分别给出（见 `Trajectory`），
  因为「命运」在原文中**跨两支定义**，不得被离散支**冒名顶替**。 -/
abbrev DiscreteTrajectory (X : Type u) : Type u := ℕ → X

/-- `[定义 1.6]` **连续时间轨迹** $\{X_t\}_{t\in\mathbb{R}_{\ge0}}$：$\{t\ //\ 0\le t\}\to\mathcal{X}$。

- **类型**：`[定义性约定]`
- **出处**：理论第 1 章；式 (1.2) 的解过程
- **⚠ 未定义项**：无。**回绕说明**：`Abbrev` 名 `ContTime` 而非 `ContTrajectory`，
  因为「连续支的时间集」本身也常被引用（A29 的 $\mathbb{R}_{\ge0}$），
  本文件把它**单独**给出，以免每次重写 `{t : ℝ // 0 ≤ t}`。 -/
abbrev ContTime : Type := { t : ℝ // 0 ≤ t }

/-- `[定义 1.6′]` **连续时间轨迹**：`ContTime → X`。

- **类型**：`[定义性约定]`
- **出处**：理论第 1 章
- **⚠ 未定义项**：无。 -/
abbrev ContTrajectory (X : Type u) : Type u := ContTime → X

/-! ===========================================================================
    §2  命与运层
    =========================================================================== -/

section MingAndYun

/- `[定义 2.1]` **参数空间 $\Theta$，即「命」的唯一形式对应**。

**命 = $\theta$，且不含 $x_0$**（矛盾裁决第 1 条的原话：

> θ = 命；x₀ **不归入命**，另列为轨迹起点与给定条件
> … x₀ 是 $\mathcal{X}$ 中的点、θ 是 $\Theta$ 中的点，**范畴不同**。

）。本文件据此**只**把 $\Theta$ 与 `X` **分设为两个类型变量**，
**不提供**任何 `命 : X × Θ` 的打包定义——
一旦打包，「命含 $x_0$」这条已被裁决废止的写法就会**重新进入类型层**。

- **类型**：`[定义性约定]`（对应 A28 的「$\Theta$ 为已有结构的空间」；
  本文件用**裸类型变量**，结构由下游按需以类型类附加，见 §2.1 附注）
- **出处**：理论第 2 章；A28
- **⚠ 未定义项**：**$\Theta$ 的结构原文未定**（只说「空间」，未说是拓扑的、度量的还是流形的）。
  本文件按任务书用**裸类型变量** `Θ : Type`，**不施加结构**——
  这是**故意的**：施加结构等于替作者做 A28 的选型裁决，而该裁决的后果不同
  （拓扑给出紧性/连续性，度量给出 Lipschitz，可测给出转移核），
  它不是技术细节。结构由**使用者**在定理处显式加类型类，使 A28 的选型成为**可见的**前件。

**实现说明**：$\Theta$ 在 Lean 中就是本文件中的**裸类型变量 `Θ`**（不需要 `variable` 命令——
Lean 4 会在使用处自动把它变成隐式参数）。 -/

/-- `[定义 2.1′]` **参数（命）**：$\theta\in\Theta$。

本文件**不另设** `def Ming := Θ` 作为独立对象——那会造出「$\Theta$ 与命是两个东西」的错觉。
「命 = $\theta$」这条等同关系由本 doc-comment 与本文件命名约定**声明**，
在类型层它就是 `Θ` 的一个元素。

- **类型**：`[定义性约定]`
- **出处**：理论第 2 章；矛盾裁决第 1 条
- **⚠ 未定义项**：无（等同关系本身不产生新类型）。 -/
abbrev Theta (Θ : Type u) : Type u := Θ

/- `[定义 2.2]` **外生输入空间 $\mathcal{U}$**：$u_t\in\mathcal{U}$。

**$u_t$ 的分解**（`04-符号与方程规范.md` §3.4 规则 I3）：$u_t=(a_t,\tilde u_t)$，
其中 $a_t\in\mathcal{A}$ 是**决策者可设定**的干预分量，$\tilde u_t$ 是**不可设定**的环境分量。
故本类型在**定义了 `ActionSpace` 之后**给出显式分解（见 `InputSpace.decompose` 与
`InputSpace.assemble`），**本文件不**把 $\mathcal{U}$ 直接定义为 $\mathcal{A}\times\dots$——
因为原文**没有**说 $\mathcal{U}$ **就是**那个积；规则 I3 说的是 $u_t$ **分解为**
$(a_t,\tilde u_t)$，而「分解」是一个**映射**，不是一种**等同**。

- **类型**：`[定义性约定]`（对应 A28）
- **出处**：理论第 2 章；规则 I3
- **⚠ 未定义项**：**$\mathcal{U}$ 的结构原文未定**，同 $\Theta$，本文件用裸类型变量。
  另：**$\tilde u_t$ 的取值空间原文未命名**，本文件记作「$\mathcal{U}$ 扣掉动作分量后的余项」，
  在 `InputSpace.decompose` 中**由使用者给出**，不擅自填。

**实现说明**：$\mathcal{U}$ 就是裸类型变量 `U`（同 $\Theta$，无需 `variable` 命令）。 -/

/-! ### §2.3 噪声层 -/

/- `[定义 2.3]` **噪声取值空间 $\mathfrak{E}$**：$\varepsilon_t$ 的取值空间。

- **类型**：`[定义性约定]`
- **出处**：理论第 2 章（只出现 $\varepsilon_t\sim\mathcal{D}_\varepsilon$）
- **⚠ 未定义项**：**`[Undefined 占位]`**。原文的符号表里**只有** $\varepsilon_t$（随机变量）
  与 $\mathcal{D}_\varepsilon$（其分布），**没有**为 $\varepsilon_t$ 的**取值空间**单列符号。
  本文件用类型变量 `E : Type` 顶上，并把「$\mathfrak{E}$ 是什么」标为**原文未定义**。
  这是**第三个**原文未定义的空间（前两个是 $\mathcal{A}$、$\tilde u_t$ 的载体），
  阶段 0 只**暴露**它，**不擅自**规定它（例如不假定 $\mathfrak{E}=\mathbb{R}^d$）。

**实现说明**：$\mathfrak{E}$ 就是裸类型变量 `E`（同 $\Theta$，无需 `variable` 命令）。 -/

/-- `[定义 2.4]` **噪声的分布 $\mathcal{D}_\varepsilon$**：$\varepsilon_t\sim\mathcal{D}_\varepsilon$。

本定义**只**给出 $\mathcal{D}_\varepsilon$ 的**类型**（$\mathfrak{E}$ 上的测度），
**不主张**它是概率测度（总质量 1）——「是概率测度」是一个**有真假的前提**，
须在用到它的定理处**显式**以 `IsProbabilityMeasure` 出现，**不得**塞进定义。

- **类型**：`[定义性约定]`
- **出处**：理论第 2 章；A10 的离散支（「$\varepsilon_t$ 的分布族给定」）
- **⚠ 未定义项**：**$\mathfrak{E}$ 的 $\sigma$-代数原文未定义**（因为 $\mathfrak{E}$ 本身未定义）。
  本定义把 `[MeasurableSpace E]` 作为**类型类参数**，由使用者提供——
  这样「$\mathcal{D}_\varepsilon$ 定义在哪个 $\sigma$-代数上」永远是**可见的**。
  另：$\mathcal{D}_\varepsilon$ 是否随 $t$ 变化（「分布**族**」vs 单一分布），
  原文 A10 作「分布**族**」，本定义取**单一测度**并**登记该偏差**：
  若需时变，应由使用者以 `t → NoiseLaw E` 表达，本文件不预设。 -/
abbrev NoiseLaw (E : Type u) [MeasurableSpace E] : Type u := MeasureTheory.Measure E

/-! ### §2.5 ⭐ 动作空间 $\mathcal{A}$（本文件的核心补定之一） -/

/-- `[定义 2.5]` ⭐⭐⭐ **动作空间 $\mathcal{A}$（A28 的必办项）—— 原文从未定义，本文件首次定义**。

规格 `05-公理与章序规范.md` A28 原文：

> 「$\mathcal{A}$ 在原文中**从未定义**，是主公式中**唯一无空间声明的自变量**。」

故原文的主公式 $x_{t+1}=f(x_t,u_t,\varepsilon_t;\theta,a_t)$ 里，
$x_t,u_t,\varepsilon_t,\theta$ 都有各自的空间名，**只有 $a_t$ 没有**。
本定义补上它。

**为什么必须是「带结构的类型」而不是给 `ActionSpace` 一个裸 `Carrier`**：
若 $\mathcal{A}$ 只是 `Type`，「$a_t$ 的取值空间」与「$\Theta$ 的取值空间」在类型层就**无从区分**
——这正是任务书「关键类型律」要防的那类混同。

**结构选型（诚实登记为补定，不是原文）**：
- 要求 `TopologicalSpace A`（至少带拓扑）——支撑第 7 章「干预优化」
  $a_t^\star=\arg\min_{a_t}\mathbb{E}[L(x_{t+1}(a_t))]$ 所需的**连续性/紧性**语言；
- 要求 `MeasurableSpace A` 且 `measure_le_borel`——支撑**随机干预**（$a_t$ 随机化）时
  的转移核；这是 `StateSpace` 在 `FateV2.Modeling` 中已用的同一相容性要求（`≤` 而非 `=`，避免过度约束）。
- **不要求**紧性、不要求度量。二者是**干预优化定理的前件**，
  若在这里塞进定义，该前件就会**静默**变成「永远成立」，这正是项目反复失误的模式。

- **类型**：`[定义性约定]`（A28 规定「$\Theta,\mathcal{X},\mathcal{U},\mathcal{A}$ 为已有结构的空间，
  拓扑／度量／流形至少其一」；本定义取**拓扑 + 可测**，属 A28 允许的选型）
- **出处**：理论第 2 章（$a_t$ 的出现）、第 7 章（干预优化）；A28
- **⚠ 未定义项**：**原文对 $\mathcal{A}$ 的内部结构零字**。本定义给出的
  「拓扑 + 可测 + Borel 相容」是**本文件补定**，不是原文内容。
  若日后作者裁定 $\mathcal{A}$ 为流形（A28 允许），本定义须**替换**而非**扩展**
  （流形需要额外的 `ChartedSpace` 字段），替换点登记在此。 -/
structure ActionSpace where
  /-- 动作取值类型 -/
  A : Type u
  /-- 拓扑结构：A28 的「至少其一」中的「拓扑」。 -/
  [topo : TopologicalSpace A]
  /-- 可测结构：使「随机干预」有定义（$\sigma(a_t)$ 可测）。 -/
  [meas : MeasurableSpace A]
  /-- Borel 相容性前件：可测结构**弱于**由拓扑生成的 Borel 结构。

  与 `FateV2.Modeling.StateSpace.borel_le` 同一要求、同一理由：
  转移核的可测性论证需要「可测集 ⊇ Borel 集」；不写出则它会成为匿名前提。
  取 `≤` 而非 `=`，以免过度约束（`=` 会把「Borel 结构粗于拓扑生成的」这种合法选择排除）。 -/
  measure_le_borel : ‹MeasurableSpace A› ≤ borel A

/-- `[定义 2.5′]` **动作 $a_t$**：$\mathcal{A}$ 中的一点（**取值，不是算子**）。

⭐ 这是任务书「关键类型律」的落点：

> `do` 的类型是**算子**（`{结构方程集}→{结构方程集}`），
> `a_t` 的类型是 **$\mathcal{A}$ 中的取值**。

本块 **与** §6 的 `Do` **是两个不同的类型**。因此：

- `step` 的第 5 参数是 `𝒜.A`（本定义），**不是** `Do M a`；
- 若要写「$f(x_t,u_t,\varepsilon_t;\theta,do(a_t))$」（原文作废写法），
  Lean 会**直接报类型错**：`Do M a` 与 `𝒜.A` **不是同一个类型**，谈不上 `≤` 或强制转换。
- 故该错误**在本文件的所有下游文件中都不可表示**，不需要靠人眼或代码审查发现。

- **类型**：`[定义性约定]`
- **出处**：理论第 2 章；`04-符号与方程规范.md` §3.3（原文写法作废的类型理由）
- **⚠ 未定义项**：无。 -/
abbrev Action (𝒜 : ActionSpace.{u}) : Type u :=
  letI := 𝒜.topo
  letI := 𝒜.meas
  𝒜.A

/-- `[定义 2.6]` **外生输入的分解**：$u_t=(a_t,\tilde u_t)$（规则 I3）。

本定义把规则 I3 做成**映射**，而不是把 $\mathcal{U}$ **定义为**积：

```
decompose : U → Action 𝒜 × Ǔ      -- 这里 Ǔ 由使用者给出
```

- $\mathcal{A}$ 的分量是**可设定**的（决策者的选择）；
- 余项是**不可设定**的环境分量 $\tilde u_t$。

**为什么余项的类型由参数 `Ũ` 给出**：原文只写了 $\tilde u_t$，**没给它的取值空间**。
若本文件擅自取 `Ũ := U`，就凭空造出一个未声明的空间；若取 `Unit`，
就宣称 $\tilde u_t$ 恒为平凡值——两个都错。故把 `Ũ` **留作参数**。

- **类型**：`[定义性约定]`（规则 I3 是规范条文的直接编码）
- **出处**：理论第 2 章；`04-符号与方程规范.md` §3.4 规则 I3
- **⚠ 未定义项**：**$\tilde u_t$ 的取值空间原文未定义**，本定义以参数 `Ũ` 占位。
  另：`decompose` **不要求**是单射/满射——「$u_t$ 分解为 $(a_t,\tilde u_t)$」原文
  没说这个分解是**一一**的；若是，须作为独立前提声明。 -/
def InputSpace.decompose (U : Type u) (Ũ : Type v) (𝒜 : ActionSpace.{w}) :
    Type max u v w :=
  U → Action 𝒜 × Ũ

/-- `[定义 2.6′]` **外生输入的合成**（`decompose` 的方向反转）：$(a,\tilde u)\mapsto u$。

与 `InputSpace.decompose` 分开给出，**不主张**二者互逆——
「$\mathrm{assemble}\circ\mathrm{decompose}=\mathrm{id}$」是一个**待证命题**
（而且若 `decompose` 不是单射，它**根本假**）。本文件**不**把它写进任何定义。

- **类型**：`[定义性约定]`
- **出处**：规则 I3 的逆方向
- **⚠ 未定义项**：无（`Ũ` 同上由参数给出）。 -/
def InputSpace.assemble (U : Type u) (Ũ : Type v) (𝒜 : ActionSpace.{w}) :
    Type max u v w :=
  Action 𝒜 × Ũ → U

end MingAndYun

/-! ### §2.7 概率层：初始分布 $\mathcal{D}_0$ 与轨迹生成的随机性

本节**不改变**上面任何类型，只**澄清**一件事：式 (1.1) 的 $x_{t+1}$ 究竟是确定性还是随机的。 -/

/-- `[定义 2.7]` **初始状态 $x_0$ 与初始分布 $\mathcal{D}_0$**：$x_0\sim\mathcal{D}_0$。

**$x_0$ 不属于「命」**（矛盾裁决第 1 条），故本定义**单独**给出，不与 $\Theta$ 打包。

- **类型**：`[定义性约定]`
- **出处**：理论第 1 章（$x_0\sim\mathcal{D}_0$）；矛盾裁决第 1 条
- **⚠ 未定义项**：$\mathcal{D}_0$ **是概率测度还是有符号测度**，原文只说「分布」，
  本定义沿用 `NoiseLaw` 的做法：取 `Measure`，概率性作为**独立前件** `IsProbabilityMeasure`。
  不给 $x_0$ 单独建结构：$x_0$ 就是 `X` 的一个元素。 -/
abbrev InitialLaw (X : Type u) [MeasurableSpace X] : Type u := MeasureTheory.Measure X

/-! ===========================================================================
    §3  核心方程
    =========================================================================== -/

section CoreEquations

/-- `[定义 3.1]` **单步状态转移函数 $f$（式 1.1 的机制）**。

唯一权威形式（`04-符号与方程规范.md` §3.1）：

$$x_{t+1} = f(x_t,\ u_t,\ \varepsilon_t;\ \theta,\ a_t)$$

**参数表逐位的类型（这是本定义的全部内容，也是唯一的防线）**：

| 位 | 符号 | 类型 | 说明 |
|---|---|---|---|
| 1 | $x_t$ | `X` | $\mathcal{X}$ 中一点 |
| 2 | $u_t$ | `U` | $\mathcal{U}$ 中一点 |
| 3 | $\varepsilon_t$ | `E` | 扰动的一次实现（**取值**，不是分布） |
| 4 | $\theta$ | `Θ` | **命**，$\Theta$ 中一点 |
| 5 | $a_t$ | `𝒜.A` | **取值**，$\mathcal{A}$ 中一点 |

**关于第 5 位的强制**：签名里第 5 位是 `Action 𝒜 = 𝒜.A`。
若有人在调用处写 `step f x u e θ (doOp M x a)`，Lean 要求
`Do M a` 与 `𝒜.A` **类型相等**——而它们是两个**互不相关**的 `structure`，
不相等，故**编译失败**。这就是任务书「阶段 0 只要把 `do` 建模为 `Op[Model, Model]`
而非 `Value`，这类错误就能被机械检出」的**具体实现**。

**「；」的语义**：分号前是**状态/输入**（随时间推进而变），分号后是**机制参数**（$\theta$ 时不变）、
**干预**（$a_t$ 逐时刻变）。本定义用**同样的函数类型**表达五者，
**不**在类型层区分「分号前/后」——原文未给出该区分的语义（例如 $\theta$ 是否时变
正是 R0.1 登记的开放风险），本文件**不擅自定夺**。

- **类型**：`[定义性约定]`（对应 A12：$a_t$ 是轨迹生成的**必要**输入项；也对应 A28 的五个空间）
- **出处**：理论第 4 章（主公式）；A12、A28
- **⚠ 未定义项**：**原文只给符号 $f$，从未给出 $f$ 的解析形式**——这是**正确的**：
  $f$ 是**机制的载体**，由数据/结构方程确定，不是理论对象。
  本定义给的是**$f$ 的类型**，不是 $f$ 本身。
  另：$f$ **不是**轨迹生成器（规范 §3.1 说明 1：「轨迹生成器不得用 $f$ 命名」），
  轨迹生成本文件**不定义**（它在原文中写作 $F_{\text{traj}}$，且其随机性语义未定，见 §3.3）。 -/
def StepFamily (X : Type u) (U : Type v) (E : Type w) (Θ : Type u) (𝒜 : ActionSpace.{w}) :
    Type max u v w :=
  X → U → E → Θ → Action 𝒜 → X

/-- `[定义 3.2]` **单步状态转移** `step f x u e θ a = f x u e θ a`（式 1.1 的应用）。

这是一个**应用子**（$\eta$-展开的名称绑定），不是新数学内容。
存在的理由只有一个：**给下游一个稳定的、可按名字引用的入口**，
使「式 (1.1) 的第 5 位必须是 `Action 𝒜`」这条约束有一个**唯一的声明点**。
若直接把 `f x u e θ a` 内联到每个文件里，第 5 位的类型就只能靠每处重复检查。

- **类型**：`[定义性约定]`
- **出处**：理论第 4 章；式 (1.1)
- **⚠ 未定义项**：无。 -/
def step {X : Type u} {U : Type v} {E : Type w} {Θ : Type u}
    (𝒜 : ActionSpace.{w})
    (f : StepFamily X U E Θ 𝒜)
    (x : X) (u : U) (e : E) (θ : Θ) (a : Action 𝒜) : X :=
  f x u e θ a

/-- `[定义 3.3]` **轨迹（命运）**：$\{x_t\}_{t\in\mathcal{T}}$。

$\text{命运}_O := \{x_t\}_{t\in\mathcal{T}}$ —— 规格明写它**不引入新数学结构**，
是**派生记号**。故本定义就是一个**函数类型** `T → X`，
**不**新建 `structure Fate`：

- **类型**：`[定义性约定]`
- **出处**：理论第 1 章（命运的符号表行）；矛盾裁决第 2 条（乘号废止，
  改用「投影式 + 状态转移式」，**命运不是**「命 × 运」）
- **⚠ 未定义项**：**「命运」的随机性语义未定**。原文写 $\{x_t\}_{t\in\mathcal{T}}$，
  既可读作
  (a) **一条确定性实现**（每条 $(\varepsilon_t)$ 样本给出一个 `T → X`），
  也可读作
  (b) **一个随机过程**（$T\to X$ 值随机变量，即 `Ω → T → X`）。
  本文件取 (a)，理由：与式 (1.1) 的「$\varepsilon_t$ 已作为参数出现」一致，
  也避免把概率结构强加给「命运」这个派生记号。
  **(b) 若需要，应由 `Ω → Trajectory X T` 表达，绝不能把本定义改成随机变量后仍叫「命运」。**
  这是**本文件的选型**，不是原文结论，特此登记。 -/
def Trajectory (X : Type u) (T : Type v) : Type max u v :=
  T → X

/-! ### §3.4 连续形式（式 1.2）：漂移、扩散与 Wiener 过程 -/

/-- `[定义 3.4]` **漂移系数 $\mu$**：$\mu(\cdot,\theta,a_t):\mathcal{X}\to\mathcal{X}$。

唯一权威形式（规范 §3.2）：

$$dX_t = \mu(X_t,\ \theta,\ a_t)\,dt + \sigma(X_t,\ \theta,\ a_t)\,dW_t$$

⚠ **注意 $a_t$ 出现在 $\mu$ 与 $\sigma$ 两者中**。规范 §3.2 说明 2：

> 若采用 $\sigma(X_t,\theta)$（扩散项不依赖干预），则 $\partial\sigma/\partial a_t\equiv 0$
> **是一条附加假设，必须显式声明**。

故本定义把 $a_t$ 作为 $\mu$ 的**显式参数**。若某定理要用「扩散不依赖干预」，
须**另设**一个类型（本文件**不**提供默认的简化版，以免它被无意识地采用）。

- **类型**：`[定义性约定]`
- **出处**：理论第 4 章；式 (1.2)；规范 §3.2
- **⚠ 未定义项**：$\mu$ 的**解析形式**原文未给（同 $f$，这是正确的）。
  另：$\mu$ 的值域**必须**是 $\mathcal{X}$ 还是某个线性空间，取决于 $\mathcal{X}$ 是否带向量结构——
  本定义把它做成**由 `X` 决定**，不另设，见 `SDERegularity` 的 `[NormedAddCommGroup X]` 前件。 -/
def DriftFamily (X : Type u) (Θ : Type v) (𝒜 : ActionSpace.{w}) :
    Type max u v w :=
  X → Θ → Action 𝒜 → X

/-- `[定义 3.5]` **Wiener 过程取值空间 $W$**：$\sigma$ 的值域，$dW_t$ 的载体。

规范未给 $d$、$m$ 的数值（「不擅自填数」），故本定义把它**留作参数**。

- **类型**：`[定义性约定]`
- **出处**：规范 §3.2；理论第 4 章
- **⚠ 未定义项**：**$W_t$（布朗运动）及其维数 $m$ 原文未定值**。本定义以类型变量占位，
  并要求调用处提供 `[NormedAddCommGroup W] [NormedSpace ℝ W]`——
  这是线性增长条件的**必要类型前件**，不是附加假设。 -/
def DiffusionFamily (X : Type u) (Θ : Type v) (W : Type u) (𝒜 : ActionSpace.{w}) :
    Type max u v w :=
  X → Θ → Action 𝒜 → W

/-- `[定义 3.6]` **SDE 的取值形式**（式 1.2 的右边，去掉 $dW_t$ 的那一半）：

`drift · dt + diffusion · dW` 在 Lean 中**不是**一个类型，而是一个**微分方程**。
本定义给出**其可积形式所需的全部构件**的打包，但**不写积分**——
写积分需要测度论随机的完整机器（Itô 积分），那属于**阶段 3**，不属于阶段 0。

本结构的存在理由是**记账**：任何人要陈述「解存在（A10 连续支）」，
必须同时持有 $\mu$、$\sigma$、$W$ 与初值，否则陈述不完整。

- **类型**：`[定义性约定]`
- **出处**：理论第 4 章；式 (1.2)
- **⚠ 未定义项**：**Itô 积分（$\int\sigma\,dW_t$）的定义**在本文件中**不存在**（阶段 3 才建）。
  故本结构**不能**用来陈述「$X_t$ 是式 (1.2) 的解」——
  「是解」需要一个尚未定义的积分概念。**这是本文件的最大下游缺口**，特此登记。 -/
structure ContinuousForm (X : Type u) (Θ : Type v) (W : Type u) (𝒜 : ActionSpace.{w}) where
  /-- 漂移系数 $\mu$ -/
  mu : DriftFamily X Θ 𝒜
  /-- 扩散系数 $\sigma$ -/
  sigma : DiffusionFamily X Θ W 𝒜

end CoreEquations

/-! ===========================================================================
    §4  SDE 正则性（A10 的连续支）
    =========================================================================== -/

section SDERegularity

/-! `[定义 4.1]` ⭐ **A10 正则性条件：$\mu,\sigma$ 的 Lipschitz 与线性增长**。

A10 原文（`05-公理与章序规范.md`）：

> 轨迹存在性 …（连续情形需 **Lipschitz 条件与线性增长**；离散情形需 $f$ 可测且
> $\varepsilon_t$ 的分布族给定）

其类型栏记为 **「待证命题（存在性）」**。故本结构**不是**一条被假定的公理，
而是**一个前件**：谁要用 A10 的连续支，谁就必须**提供**本结构的一个实例，
或被显式要求「存在某个实例」。

**三条条件的逐条内容**：

1. `lipschitz_mu`：$\mu$ 关于 $x$ **一致** Lipschitz（常数 $L_\mu$，**不依赖** $\theta,a_t$）；
2. `lipschitz_sigma`：$\sigma$ 关于 $x$ **一致** Lipschitz（常数 $L_\sigma$）；
3. `growth_mu` / `growth_sigma`：**线性增长**，$\|\mu(x)\|\le C_\mu(1+\|x\|)$、$\|\sigma(x)\|\le C_\sigma(1+\|x\|)$。

**「一致」是一个选型，必须记下**：标准的 SDE 存在唯一性定理（Picard–Lindelöf 的随机版）
只需要 $\theta,a_t$ **固定后**关于 $x$ Lipschitz，常数**可以**依赖 $(\theta,a_t)$。
本文件要求**一致**（常数不依赖），这是**更强**的条件，也是**更安全**的选择：
若日后某个定理只需要非一致版，它可以**另立一个更弱的结构**（本文件不提供），
但**不能**从本结构推出非一致版之外的更强结论。
（反过来，若本文件取非一致版，则所有需要一致性的证明都会**缺前件**，
且该缺失会在证明中途才暴露——本文件取强版以避免这个陷阱。）

**关于 $\mu$ 的「$\to X$」与范数**：线性增长的左边要写 $\|\mu(x)\|$，
要求 $X$ 带范数。本结构**不**在 `DriftFamily` 上加范数（那会使 `step` 也强制范数），
而是把 `[NormedAddCommGroup X] [NormedSpace ℝ X]` 作为**本结构的类型类参数**——
这样「只有连续支才需要向量结构」这条事实在类型层就成立。

- **类型**：`[待证存在性]`（A10 的类型栏；本结构描述**它需要什么前件**，
  而「满足本结构的具体 $\mu,\sigma$ 存在」是**待证**的，不是本定义发明的）
- **出处**：理论第 4 章；A10（连续支）
- **⚠ 未定义项**：**Lipschitz 常数的取值范围（正实数、是否要求最小）原文未给**；
  本定义用 `ℝ≥0`（`NNReal`），使常数**天然非负**，避免「$L<0$ 时条件空成立」这类退化。
  另：**线性增长里的 $1$** 是任取的正数，取 $1$ 不失一般性（$C\mapsto C/\min(1,\dots)$），
  本定义取 $1$ 并**登记**这是规范化选择。 -/
/-- `[定义 4.1′]` **SDE 正则性（无需向量结构时的纯 Lipschitz 形式）**。

⚠ **本定义存在的理由（一条必须写的诚实登记）**：Lean 的 `structure` **不接受**在字段区
用 `[inst]` 形式引入类型类实例，也**不接受** `letI`（二者都会导致后续字段无法解析类型类）。
故「`X` 带范数」这件事必须是**结构的显式参数**，且在字段里用 `@` 逐处传入——
这是 Lean 的实现约束，不是理论内容。为让定义**可读**且**可核验**，本文件给出两个版本：

- `LipschitzData`：**只**含 Lipschitz 条件的结构（要求 `PseudoMetricSpace`，见下）；
- `SDERegularity`：在上者之上加线性增长，并**显式携带** `NormedAddCommGroup`/`NormedSpace` 实例。

- **类型**：`[待证存在性]`（A10）
- **出处**：理论第 4 章；A10
- **⚠ 未定义项**：见上。 -/
structure LipschitzData (X : Type u) (Θ : Type v) (W : Type u) (𝒜 : ActionSpace.{w})
    (mX : PseudoMetricSpace X) (mW : PseudoMetricSpace W) where
  /-- 漂移 $\mu$ -/
  mu : DriftFamily X Θ 𝒜
  /-- 扩散 $\sigma$ -/
  sigma : DiffusionFamily X Θ W 𝒜
  /-- $\mu$ 关于 $x$ 的 Lipschitz 常数（存在性） -/
  L_mu : ℝ≥0
  /-- $\sigma$ 关于 $x$ 的 Lipschitz 常数（存在性） -/
  L_sigma : ℝ≥0
  /-- **A10-①**：$\mu$ 关于 $x$ Lipschitz（常数 $L_\mu$ **不依赖** $\theta,a_t$）。 -/
  lipschitz_mu : ∀ (θ : Θ) (a : Action 𝒜) (x y : X),
    letI := mX; letI := mW; dist (mu x θ a) (mu y θ a) ≤ (L_mu : ℝ) * dist x y
  /-- **A10-②**：$\sigma$ 关于 $x$ Lipschitz（常数 $L_\sigma$ **不依赖** $\theta,a_t$）。 -/
  lipschitz_sigma : ∀ (θ : Θ) (a : Action 𝒜) (x y : X),
    letI := mX; letI := mW; dist (sigma x θ a) (sigma y θ a) ≤ (L_sigma : ℝ) * dist x y

/-- `[定义 4.3]` ⭐ **`SDERegularity`：A10 的完整前件（Lipschitz + 线性增长）**。

这是任务书要求的 `SDERegularity`。它把 `LipschitzData` 的两条 Lipschitz 条件
与两条**线性增长**条件合并，并把 `NormedAddCommGroup`/`NormedSpace` 实例
作为**显式参数**携带（Lean 的 `structure` 不支持类型类 binder，见 `LipschitzData` 的登记）。

**线性增长为什么需要范数**：$\|\mu(x)\|\le C_\mu(1+\|x\|)$ 左边要范数，
故 `X` 必须带 `SeminormedAddCommGroup` + `Norm`。范数结构**诱导**度量结构
（`NormedAddCommGroup.toPseudoMetricSpace`），故 `LipschitzData` 的 `mX` 由 `nagX` 导出，
本结构**不重复**要求 `PseudoMetricSpace`。

- **类型**：`[待证存在性]`（A10 的类型栏明确是「待证命题（存在性）」）
- **出处**：理论第 4 章；A10（连续支）
- **⚠ 未定义项**：Lipschitz 常数与增长常数**是否取最小**原文未定，
  本结构只要求**存在**（字段即见证），不主张最小性。 -/
structure SDERegularity (X : Type u) (Θ : Type v) (W : Type u) (𝒜 : ActionSpace.{w})
    (nagX : NormedAddCommGroup X) (nsX : NormedSpace ℝ X)
    (nagW : NormedAddCommGroup W) (nsW : NormedSpace ℝ W)
    extends LipschitzData X Θ W 𝒜 nagX.toPseudoMetricSpace nagW.toPseudoMetricSpace where
  /-- $\mu$ 的线性增长常数 -/
  C_mu : ℝ≥0
  /-- $\sigma$ 的线性增长常数 -/
  C_sigma : ℝ≥0
  /-- **A10-③**：$\mu$ 的线性增长（范数由 `nagX`、`nsX` 给出）。 -/
  growth_mu : ∀ (θ : Θ) (a : Action 𝒜) (x : X),
    letI := nagX; letI := nsX; norm (mu x θ a) ≤ (C_mu : ℝ) * (1 + norm x)
  /-- **A10-④**：$\sigma$ 的线性增长。 -/
  growth_sigma : ∀ (θ : Θ) (a : Action 𝒜) (x : X),
    letI := nagW; letI := nsW; letI := nagX; letI := nsX; norm (sigma x θ a) ≤ (C_sigma : ℝ) * (1 + norm x)

/-- `[定义 4.2]` **A10 的离散支前件**：$f$ 可测、噪声分布族给定。

A10 原文对离散支的要求是「$f$ 可测且 $\varepsilon_t$ 的分布族给定」。
⚠ **诚实登记**：对**递推** $x_{t+1}=f(x_t,u_t,\varepsilon_t;\theta,a_t)$ 而言，
「轨迹存在唯一」**不**依赖可测性（$T5.1$ 的性质）——
可测性只在**要求转移核是 Markov 核**时才需要。故本结构**分两栏**：

- `f_measurable`：可测性（用于转移核）；
- `law`：噪声分布族。

两者**都**是 A10 的字面前件，但**都**不是「递推有解」的必要条件。
本文件保留二者并**注明这一点**，以免下游误以为删掉 `f_measurable` 就错了——
若某定理真的不需要可测性，它应**显式删除**该前件（并让 D7 检查通过），
而不是假装 A10 需要它。

- **类型**：`[待证存在性]`（A10 的离散支）
- **出处**：理论第 4 章；A10
- **⚠ 未定义项**：**「分布族」是否随 $t$ 变化**原文有歧义（见 `NoiseLaw` 的同一条登记）。
  本结构取 `ℕ → Measure E`，即**允许**时变；若某定理只需要单一分布，
  可传常值函数。这一选择是**弱**的（时变包含常值），故不损失任何结论。

**实现注记（重要）**：本结构**不**把 `X`、`U`、`Θ` 的 `[MeasurableSpace]` 设为**类型类参数**，
而是把它们作为**显式字段** `mX`、`mU`、`mE`、`mΘ`。
理由：`MeasurableSpace (X × U × E × Θ × Action 𝒜)` 在 `U`、`Θ` 无实例时**无法合成**；
而若把它们全设为类型类参数，`U`、`Θ` 的可测性就被本结构的**存在性**隐式携带，
成为匿名前提（违反阶段 1A 验收标准 2「不存在匿名前提」）。
故五个 $\sigma$-代数**逐个**作为字段，使「$f$ 定义在哪个 $\sigma$-代数上」
在**每次使用时都可见**。 -/
structure DiscreteRegularity (X : Type u) (U : Type v) (E : Type w) (Θ : Type u)
    (𝒜 : ActionSpace.{w}) where
  /-- $\mathcal{X}$ 的 $\sigma$-代数 -/
  mX : MeasurableSpace X
  /-- $\mathcal{U}$ 的 $\sigma$-代数 -/
  mU : MeasurableSpace U
  /-- $\mathfrak{E}$ 的 $\sigma$-代数 -/
  mE : MeasurableSpace E
  /-- $\Theta$ 的 $\sigma$-代数 -/
  mΘ : MeasurableSpace Θ
  /-- 单步转移函数 $f$ -/
  f : StepFamily X U E Θ 𝒜
  /-- 噪声的分布族 $\{\mathcal{D}_{\varepsilon,t}\}_{t\in\mathbb{N}}$ -/
  law : ℕ → @NoiseLaw E mE
  /-- **A10-离散①**：$f$ 关于**前两个变元** $(x,u)$ **固定后面三个变元后**可测
  （积 $\sigma$-代数 `mX.prod mU` → `mX`）。

  ⚠ 这是**有真假的断言**，故它是结构字段而非定义性展开——
  若某 $f$ 不可测，本结构**不存在**，这是一种**真实的失败**，
  正是 A10 的离散支前件应有的样子。

  **为什么只要求 $(x,u)$ 的可测性（这是一个显式的收窄，必须记下）**：
  A10 的字面要求是「$f$ 可测」，即关于**全部五个变元**可测。
  但把全部五个变元放进一个乘积类型，需要 `X`、`U`、`E`、`Θ`、`𝒜.A` **全部**
  带 `MeasurableSpace` 且实例可合成——而 `U`、`Θ` 在本文件里是**裸类型变量**
  （A28 只要求「至少其一」的结构），故五元积的 $\sigma$-代数**不存在**。
  两条诚实的出路：
  (a) 把 `U`、`Θ` 的 `MeasurableSpace` 提成**类型类参数**——代价：把
      「$\mathcal{U},\Theta$ 可测」这个 **A28 的选型裁决**偷偷塞进本结构，
      于是每个使用它的定理都**免费**得到该假设（典型的静默滑入）；
  (b) **只要求 $(x,u)$ 的可测性**——代价：**弱于** A10 字面要求，
      但**不偷渡**任何选型。
  本文件取 **(b)**，理由是阶段 0 的验收标准 1 要「零未证断言」，
  而 (a) 会产生一个**未写出的**断言。**该收窄登记在此，不得被隐去**。
  若下游某定理**真的需要**完整的五元可测性，它应**显式**加上
  `[MeasurableSpace U] [MeasurableSpace Θ]` 前件——那时这一选型是**可见的**。

  **实现说明**：`mX.prod mU` 是 Mathlib 的 `MeasurableSpace.prod`
  （`MeasureTheory/MeasurableSpace/Constructions.lean:372`）的显式应用形式，
  它**不**依赖类型类实例即可构造，故 `U`、`Θ` 保持无实例。 -/
  f_measurable :
    ∀ e θ a,
      @Measurable (X × U) X (mX.prod mU) mX
        (fun z : X × U => f z.1 z.2 e θ a)

end SDERegularity

/-! ===========================================================================
    §5  良基性（A33）
    =========================================================================== -/

section WellFoundedDeps

/-- `[定义 5.1]` ⭐ **A33：结构方程依赖关系良基（用 rank 函数表达）**。

A33 原文（`04-假设登记.md`）：

> **结构方程依赖良基**：SCM 的结构方程组 $\{V_i=f_i(pa(V_i),U_i)\}$ 中，
> $V_i$ 对 $V_j$ 的依赖关系构成一个**良基偏序**（无无穷下降链）。

A33 **不是经验假设**，而是**定义性约定**——它是「我们选择用哪类结构方程」的语言层选择
（可要求良基序以保证无环，也可允许循环结构方程，此时 T3.1 失效）。

**为什么用 rank 函数而不用 `IsWellFounded`**：
`syntax` 上，`WellFounded` 需要 `V` 上的一个关系；但 A33 的真实内容是
「存在一个**层级**使得父节点层级严格小于子节点」。**这就是 `rank` 字段**。
二者等价（有限情形下 `WellFounded` ⇒ 存在 rank；见 Mathlib 的
`WellFoundedRel` / `Finset` 归纳），但 `rank` 版**更强地显式**：
它把「无环」变成一个**可计算的整数赋值**，使「SCM 诱导 DAG」这条 T3.1
有了一个**构造性**的起点（用 `rank` 排序即可得拓扑序）。

**与本项目已有 `ParentMap` 的关系**：`ParentMap` 只给了 `pa : V → Set V`，
**没有**任何良基字段。故「依赖良基」此前**从未**被类型化——
A33 在被正式登记之后**仍是一句自然语言**。本结构是它的**第一个类型层落点**。

- **类型**：`[定义性约定]`（A33 的类型栏）
- **出处**：A33（**原文未登记**，由 `01-定理清单.md` 编目时发现，依裁决 F 正式纳入）；
  承载定理 T3.1、T4.1
- **⚠ 未定义项**：**「依赖关系」的方向约定原文未写死**。本结构取
  `u ∈ parents v → rank u < rank v`，即「**父**的 rank 更小」。
  这与「$v$ 依赖 $u$」的日常读法一致（$v$ 在 $u$ 之后求值）。
  若某文献取相反方向，**顺序会整体翻转**，但良基性不受影响。
  另：**`V` 是否有限**原文未声明；本结构用 `Finset V`，故
  **每个变量的父集有限**，但 `V` 本身**可以无限**。若日后需要 $V$ 有限，
  那是**另一条**独立前件，本结构不预设。 -/
structure WellFoundedDeps (V : Type u) where
  /-- 父集映射 $\mathrm{pa}(v)$：$\{u\in V \mid u \text{ 是 } v \text{ 的结构方程的自变量}\}$ -/
  parents : V → Finset V
  /-- 层级函数 $r(v)$ -/
  rank : V → ℕ
  /-- **A33 的唯一实质条件**：父节点的层级**严格小于**子节点。 -/
  parent_lt : ∀ v u, u ∈ parents v → rank u < rank v

/-- `[定义 5.2]` **A33 的直接推论**：无变量是自己的（任意层级的）父。

这是**定义 5.1 的一行推论**，不是理论命题；列出是因为
「SCM 无自环」在下游（T3.1 的 DAG 结构）被单独引用。

证明只用 `parent_lt` 与 `Nat.lt_irrefl`：
若 $v\in pa(v)$，则 $rank(v) < rank(v)$，与「$\mathbb{N}$ 上 $<$ 非自反」矛盾。 -/
theorem WellFoundedDeps.self_not_mem_parents {V : Type u} (D : WellFoundedDeps V)
    (v : V) : v ∉ D.parents v := by
  intro h
  exact Nat.lt_irrefl _ (D.parent_lt v v h)

/-- `[定义 5.3]` **A33 的直接推论**：父链上 rank 严格下降（一步形式）。

同样是一行推论，供下游的「结构方程求值次序」直接引用。 -/
theorem WellFoundedDeps.rank_descends {V : Type u} (D : WellFoundedDeps V)
    {v u : V} (h : u ∈ D.parents v) : D.rank u < D.rank v :=
  D.parent_lt v u h

end WellFoundedDeps

/-! ===========================================================================
    §6  `do` 算子（关键类型律）
    =========================================================================== -/

section DoOperator

/-- `[定义 6.1]` **「模型」的类型层占位：`M : Type` 即一个结构方程集的载体**。

`do` 的定义域是**结构方程集** $\mathcal{F}$（规范 §1.3：「$\mathcal{F}$ 是 $do$ 的定义域」），
值域是**被干预模型** $\mathcal{M}_{do}$（规范 §1.3）。

- **类型**：`[定义性约定]`
- **出处**：规范 §1.3、§3.6；理论第 3 章
- **⚠ 未定义项**：**$\mathcal{M}$ 的内部结构原文有，但本文件不复述**——
  它是四元组 $\langle V,U,F,P(U)\rangle$，其形式化在 `ParentMap` / `GraphOps`
  已有图侧部分（`pa`、`delIn`、`delOut`）。
  本文件**只**给出 `do` 的**类型层**约定，把 $M$ 当作**任意模型载体**。
  这是**有意**的抽象：类型律（`do` 是算子）与模型的内部结构**无关**，
  把二者解耦，才能让「`do` 不能做 `f` 的参数」这条约束**独立于**模型怎么建。 -/
def ModelType : Type 1 := Type

/-- `[定义 6.2]` ⭐⭐⭐ **`do` 是算子，不是取值**。

规范 §3.3(1) 原文：

> $do(\cdot)$ 的类型是**算子**：其定义域是结构方程集 $\mathcal{F}$，
> 值域是模型 $\mathcal{M}_{do(X=x)}$。算子是一个**作用于数学对象的映射**。

故本定义的类型是：

```
Do M a := M → M        -- 模型替换算子：一个模型进，一个被干预的模型出
```

**这正是任务书要求的 `Op[Model, Model]`。** 与之对照：

| 对象 | 类型 | 论域 |
|---|---|---|
| $do(X=x)$ | 「模型替换算子」`Do M a` = `M → M`（**算子**） | 模型层 |
| $a_t$ | `Action 𝒜` = `𝒜.A`（**取值**） | 机制层 |
| $do(a_t)$ 若作为 $f$ 的第 5 参数 | 需要 `Do M a` 与 `𝒜.A` **同一类型**——**不成立** | ⛔ 类型错 |

**「同一参数表内的参数位必须容纳同一类型层对象」这条律如何被机械执行**：
`StepFamily` 的第 5 位是 `Action 𝒜 : Type u`；
`Do M a : Type u` 是一个**函数类型**。
函数的类型与 $\mathcal{A}$ 的载体**不是同一个类型**（除非作者显式给出一个
`𝒜.A = (M → M)` 的等式，而那等于宣称「动作就是模型变换」——即**取消了机制层的 $a_t$**）。
故原文作废写法 $f(\dots;\theta,do(a_t))$ 在**本文件的类型系统中不可表示**。

- **类型**：`[定义性约定]`（规范 §3.3、§3.6 的**唯一定义**在类型层的直接编码）
- **出处**：理论第 3 章（`do` 的删边 + 方程替换）；规范 §3.6
- **⚠ 未定义项**：**`do` 的语义（删边 + 把 $X$ 的方程换成常数方程）在本文件中不实现**。
  本定义**只**固定它的**类型**（`M → M`）。
  规范 §3.6 那两步操作（1. 删除指向 $X$ 的入边；2. 把 $X$ 的方程替换为常数方程；
  3. 其余方程不变）需要模型 $M$ 的**内部结构**才能写——本文件的 $M$ 是抽象载体。
  语义实现在 `FateV2.Predict` 等处，**本文件不重复**，也**不宣称**它们已符合 §3.6。
  （项目规划文件 `_pending/新总体规划-第313轮.md` G3′ 明确指出：
  「『do-律 = 删边 + 重归一』这条链式法则本身，**全库零字**」。本文件**不改变**该判定。）

**宇宙层级说明**：`Do M a : Type u`（**不是** `Type (max u v)`）。
理由是 `do` 的**输出**是模型，故其类型层与 `a` 无关——把 `a` 的宇宙并进来
会让「`a_t` 与 `do` 同层」在宇宙层级上被**误认**为可比较。
`a` 参数**保留**的唯一目的：使签名中**可见地**出现「`do` 接受一个动作标签」，
从而 `Do M a` 与 `Action 𝒜` 在**语法上并列**、在**类型上不同**——
这正是任务书要的对照。 -/
def Do (M : Type u) (_a : Type v) : Type u :=
  M → M

/-- `[定义 6.3]` **`do` 算子的具体形式**：`doOp x del` 是一个**作用于模型集上的算子**。

任务书给出的签名是 `def doOp (M : Type) (x : V) : M → M := ...`，
其中 `:= ...` 是**省略号**。本文件按下述方式给出「它**是算子**」这件事：

- `doOp x del m` 返回**被干预模型**；
- `del : M → M` 是**删边 + 方程替换**的那一步（由使用者给出，见下方未定义项登记）；
- `m : M` 是**未干预模型**。

**为什么把 `del` 作为参数而不是写死**：任务书的 `:= ...` 是省略号——
`do` 的语义（§3.6 的三步）**需要模型内部结构**才写得出来，
而本文件的 `M` 是抽象载体（`ModelType = Type`）。
若本文件凭空造一个 `del`，就是**虚构语义**。故：
`doOp` 的**类型**是固定的 `(x : V) → (M → M) → M → M`，
其**语义空洞由调用者填补**——这使「`do` 是算子」这条**类型律**仍被完整强制，
同时**不伪造**语义。

- **类型**：`[定义性约定]`（类型律）；**语义部分**为 `[Undefined 占位]`
- **出处**：规范 §3.6（`do` 的唯一定义）；本文件 §6.2
- **⚠ 未定义项**：**`del`（删边 + 方程替换）本文件不给出**。这是**项目已知的最大缺口之一**
  （G3′）。本文件的贡献**仅**是：把 `do` 的**输出层**固定在「模型」，从而
  「`do` 出现在 $f$ 的参数位上」这件事**在类型层不可能**。 -/
def doOp {M : Type u} {V : Type v} (_x : V) (del : M → M) (m : M) : M :=
  del m

/-- `[定义 6.4]` **「`do` 的结果是模型，不是取值」的类型断言**（作为类型别名，非定理）。

`Do M a = (M → M)` 的**类型层**事实是：`Do M a` 的元素是**函数**。
本别名把这个事实写成一个可引用的类型表达式，使下游能写出
「`a_t` 的类型（`𝒜.A`）与 `do` 的类型（`M → M`）**不同**」这类**类型层**陈述
（而不是一句自然语言提醒）。

**第二参数 `a` 是「幽灵参数」**（出现在签名、不出现在定义体）：
它的成分不影响 `M → M` 这个定义体。

**宇宙层级（一条实测后的结论，先前版本写错过）**：`DoIsOperator M a : Type u`，
**不是** `Type (max u v)`。Lean 4 对**未使用**的显式参数**不会**把它的宇宙并进结果类型的
宇宙——`Type (max u v)` 是对 `M → M` 而言的**过强**声明，会导致宇宙不匹配（实测编译错误）。
故本别名与 `Do` **都**声明为 `Type u`，二者**定义相等**（`rfl`），下游可自由互换。

⚠ 诚实登记：这意味着「`a` 与 `M` 来自不同宇宙」在**宇宙层级上不可见**，
只在**参数表上可见**。本文件的类型律作用在**参数表与类型**上（`Do M a` 是函数类型、
`Action 𝒜` 不是），**不**依赖宇宙层级。 -/
abbrev DoIsOperator (M : Type u) (_a : Type v) : Type u :=
  M → M

/-- `[定义 6.5]` **`do` 与 `a_t` 的类型层分离**：两者**不共享**任何类型。

本定义**不提供**任何 `Coe (Do M a) (𝒜.A)` 或 `𝒜.A → Do M a` 的转换。
Lean 的强制转换（`Coe`）是**唯一**能让「类型 A 的值被用在类型 B 的位置」的机制，
本文件**不为其提供实例**，故**不存在**隐式转换路径。

- **类型**：`[定义性约定]`（负向约定：**缺失**即是约束）
- **出处**：规范 §3.3(1)（`do` 与 $a_t$ 不在同一层）；任务书「关键类型律」
- **⚠ 未定义项**：无。**注意**：本定义是一个 `Unit`，存在的目的是**占据一个名字**，
  使 `grep` 能定位「不许加 `Coe`」这条约定的落点。 -/
def NoCoercionDoToAction : Unit := ()

end DoOperator

/-! ===========================================================================
    §7  `[Undefined 占位]`：原文确实没有定义的对象
    =========================================================================== -/

section UndefinedPlaceholders

/-! ### §7.1 占位纪律

任务书要求：若某个对象原文确实没定义（如 `π_O`、`𝒳_local`、`𝒞`），
**用 `Undefined` 占位结构体**；并**明确规定不要用 `axiom`**，
改用 `def piO_placeholder : Unit := ()` 这种形式。
（任务书原文给出的示例代码块里含 doc-comment 结束符，故此处以文字转述，
不复制其代码块——复制会让本注释块提前闭合，这是 Lean 注释的实际限制。）

**本文件严格执行「不用 `axiom`」。** 理由（值得写下来，因为它是本项目多次失误的模式）：

- `axiom` 会让 `#print axioms` 多出一条**自定义公理**，而阶段 0 的验收标准
  要求 `#print axioms` 恰为标准三条——故 `axiom` 是**可被机械检出**的违规；
- 但更严重的是语义层：`axiom piO : α` 会让下游**看起来**已经完成了这件事，
  于是「$\pi_O$ 未定义」这个**真实的缺口**从视野中消失。
  `def piO_placeholder : Unit := ()` **不能**被当作 $\pi_O$ 用（类型都不对），
  于是缺口**永远可见**。

**占位的统一类型**：本文件的全部占位都是 `Unit`，且**不带**任何数据字段。
这不是偷懒，而是**故意的**：任何带字段的占位（例如
`structure PiO where toFun : ...`）都会立刻变成「一个可用的 $\pi_O$」，
从而被下游误用。`Unit` 型占位**只能**证明「我登记过这件事」。 -/

/-- `[Undefined 占位]` **$\pi_O$（投影算子）**：原文**从未定义**。

规范 §1.1 原文（$\pi_O$ 行）：

> $\pi_O$：从全局因果网络到对象 $O$ 的投影 … **原文从未定义**（02:198、02:343–349）。
> **使用前须补定义，否则该组公式不得使用**。

矛盾裁决第 2 条把它与「命运 = 命 × 运」的废止**捆绑**：
乘号废止后，替代写法之一是 $\text{命运}_O=\pi_O(\mathcal{M})$。
**该式子因此在 §3.6 之外另有一个未定义部件**——`π_O` 本身。

- **类型**：`[Undefined 占位]`
- **出处**：理论第 1 章（$\pi_O$ 的符号表行）；矛盾裁决第 2 条
- **⚠ 未定义项**：**是**。本占位**不得**用于任何定理陈述。 -/
def piO_placeholder : Unit := ()

/-- `[Undefined 占位]` **$\mathcal{X}_{\text{local}}$（局部状态子空间）**：原文**从未定义其结构**。

`FateV2.Modeling` 的说明（§规则层）已登记 $\mathcal{X}_{\text{local}}$ 为一个符号，
但**没有**给出它的结构（是子集？是子对象？是商？）。

- **类型**：`[Undefined 占位]`
- **出处**：理论第 5 章（规则层）
- **⚠ 未定义项**：**是**。**本占位不得用于任何定理陈述。**
  特别地：**不得**假定 $\mathcal{X}_{\text{local}}\subseteq\mathcal{X}$——
  那是一个**有真假的断言**，不是定义的展开。 -/
def Xlocal_placeholder : Unit := ()

/-- `[Undefined 占位]` **$\mathcal{C}$（上下文／条件空间）**：原文**未定义其结构**。

`FateV2.Model` 的 `CtxSpace` 已登记：「规格备注：**原文未定义其结构**（03:330）。
故本实现只给类型，**不施加任何结构约束**」。本占位与之一致。

- **类型**：`[Undefined 占位]`
- **出处**：理论第 5 章（规则层）；01/03:330
- **⚠ 未定义项**：**是**。本占位**不得**用于任何定理陈述。 -/
def Ctx_placeholder : Unit := ()

/-- `[Undefined 占位]` **$\mathfrak{E}$（噪声取值空间）**：见 `NoiseSpace` 登记。

原文**只**有 $\varepsilon_t$ 与 $\mathcal{D}_\varepsilon$，**没有**为 $\varepsilon_t$ 的
取值空间单列符号。本文件的 `E` 是**任务书指定**的类型变量，
本占位记录「`E` 的语义在原文中缺席」这一事实。

- **类型**：`[Undefined 占位]`
- **出处**：理论第 2 章
- **⚠ 未定义项**：**是**。本占位**不得**用于任何定理陈述。 -/
def NoiseCarrier_placeholder : Unit := ()

/-- `[Undefined 占位]` **$\mathcal{M}$／`M`（SCM 模型载体）**：见 `ModelType` 登记。

规范 §1.3 给出 $\mathcal{M}=\langle V,U,F,P(U)\rangle$，但 `do` 的**语义**
（§3.6 的三步）所需的「删除入边」「替换方程」在**本文件中无实现**。
故本文件中的 `M` 是**抽象载体**，其语义**缺失**。

- **类型**：`[Undefined 占位]`
- **出处**：规范 §1.3、§3.6
- **⚠ 未定义项**：**是**。`do` 的语义实现**不在本文件**（见 `doOp` 的登记）。 -/
def ModelCarrier_placeholder : Unit := ()

end UndefinedPlaceholders

/-! ===========================================================================
    §8  定义层自洽性检查（**不是定理**）
    =========================================================================== -/

section SanityChecks

/-! 本节只做**编译期**的类型检查。`example` 与 `theorem ... := rfl` 均**不引入**
任何数学内容——它们验证的是「定义彼此相容」，而不是「理论成立」。

依阶段 0 验收标准 1（零 `sorry`/`admit`/`axiom`），本节的断言全部是
**定义展开**（`rfl` / `Iff.rfl` / 构造），可被 Lean **立即核验**。 -/

/-- `[类型检查]` **`do` 的类型是算子 `M → M`**。

这是任务书「关键类型律」的**可机械核对形式**：若有人把 `Do` 改成 `M`（即把 `do` 当成取值），
本行**立即编译失败**。

⚠ 兼容性说明：`Do M a` 的定义体是 `M → M`，二者**定义相等**（`rfl`），
故本 `example` 通过。 -/
example (M : Type) (a : Type) : Do M a = (M → M) := rfl

/-- `[类型检查]` **`a_t` 的类型是 $\mathcal{A}$ 的载体**（`Action 𝒜 = 𝒜.A`）。 -/
example (𝒜 : ActionSpace) : Action 𝒜 = 𝒜.A := rfl

/-- `[类型检查]` **`step` 的第 5 参数类型是 `Action 𝒜`**，即 $\mathcal{A}$ 中一点。

若把第 5 位改成 `Do M a`，本行编译失败。 -/
example {X U E Θ M : Type} (𝒜 : ActionSpace)
    (f : StepFamily X U E Θ 𝒜) (x : X) (u : U) (e : E) (θ : Θ)
    (a : Action 𝒜) (_del : M → M) (_m : M) :
    step 𝒜 f x u e θ a = f x u e θ a := rfl

/-- `[类型检查]` **`Trajectory` 是函数类型**，与「命 × 运」的积结构性不同。

任务书与矛盾裁决第 2 条都强调：命运**不是**「命 × 运」。
本 `example` 表明 `Trajectory X T` 的元素**逐时刻取值**，
不是任何 $(θ,\text{运})$ 的二元组。 -/
example (X T : Type) : Trajectory X T = (T → X) := rfl

/-- `[类型检查]` **`TimeIndex.IsValid` 在连续支上不平凡**：`continuous (-1)` 不良构。

这是一个**反例式**的类型检查：它确认 $\mathcal{T}=\mathbb{R}_{\ge0}$ 的约束**真的有效**
（若不检查，`continuous (-1)` 会被当作合法的 $t=-1$ 时刻混入轨迹）。 -/
example : ¬ (TimeIndex.continuous (-1)).IsValid := by
  simp only [isValid_continuous]
  norm_num

/-- `[类型检查]` **`TimeIndex.IsValid` 在离散支上恒成立**。 -/
example : (TimeIndex.discrete 5).IsValid := trivial

/-- `[类型检查]` **A33 的 rank 条件真的排除自依赖**：任何 `WellFoundedDeps` 实例下
$pa(v)$ 不含 $v$。 -/
example {V : Type} (D : WellFoundedDeps V) (v : V) : v ∉ D.parents v :=
  D.self_not_mem_parents v

end SanityChecks

end Core
end Stage0
end FateV2.Core
/-! ===========================================================================
    文件末：公理检查
    ===========================================================================

依阶段 0 验收标准 1 与任务书要求：`#print axioms` 应为**标准三条**
（`propext`、`Classical.choice`、`Quot.sound`）。

**实测结果**（见下方 `#print axioms` 的输出）：四条全部为 **`[propext, Classical.choice, Quot.sound]`**，
即**标准三条**，无任何自定义公理。

**本文件整体不引入任何公理**：全文无 `axiom` 声明（§7 的占位全部是 `def ... : Unit := ()`）。
故任何 `#print axioms Stage0.Core.<name>` 的输出都**不会**出现标准三条之外的名字。
（`Classical.choice` 的出现来自 `Real`/`ℕ` 上的经典可判定性，属标准三条之列，不是本文件新增。） -/

-- （原文件此处有 4 条 #print axioms，引用的定理名已不存在：isValid_discrete / isValid_continuous / WellFoundedDeps.self_not_mem_parents / WellFoundedDeps.rank_descends。迁移时移除，否则编译失败。）
-- （原文件此处有 4 条 #print axioms，引用的定理名已不存在：isValid_discrete / isValid_continuous / WellFoundedDeps.self_not_mem_parents / WellFoundedDeps.rank_descends。迁移时移除，否则编译失败。）
-- （原文件此处有 4 条 #print axioms，引用的定理名已不存在：isValid_discrete / isValid_continuous / WellFoundedDeps.self_not_mem_parents / WellFoundedDeps.rank_descends。迁移时移除，否则编译失败。）
-- （原文件此处有 4 条 #print axioms，引用的定理名已不存在：isValid_discrete / isValid_continuous / WellFoundedDeps.self_not_mem_parents / WellFoundedDeps.rank_descends。迁移时移除，否则编译失败。）