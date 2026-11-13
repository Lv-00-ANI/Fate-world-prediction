/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.Frame
阶段：**阶段 0 —— 定义与签名冻结**（规格 `02-证明路线/01-路线图.md` §阶段 0）
　　　**+ 作者裁决 Q-1 / Q-2 的落实**（`作者裁决-Q1到Q6.md`）

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
给出规格 `01-路线图.md` §阶段 0 「范围」栏所列的**其余定义**：
- **四元定义**：命 $\theta$、运 $(u,\varepsilon)$、因果 $f$、命运 $\{x_t\}$
- **核心方程的类型签名**（离散式与连续式）
- **规则层**：$R$、$\mathcal{R}$、$\circ$、$\sim$、$\alpha$、$\gamma$、$\upsilon$、
  $\mathcal{E}$、$\mathcal{X}_{\text{local}}$

依阶段 0 验收标准 1：**零 `sorry`、零 `admit`、零 `axiom`**。

---------------------------------------------------------------------------
作者裁决的落实（`作者裁决-Q1到Q6.md`，**最高优先级**）
---------------------------------------------------------------------------
| 裁决 | 内容 | 本文件的落实 |
|---|---|---|
| **Q-1** | θ **不是给定参数，而是从实例提取的规律**；「慢」改为「样本上稳定」 | `ThetaIsExtracted`、`ThetaStableOn`、`thetaStableOn_union`；**删除** `TimeScaleRegime` |
| **Q-2** | 取 **(a) 状态可直接获取** | `currentRegime = .direct`、`ObservedState`（恒等）；(b) 保留为备选构造子但不引用 |

**Q-1 的实质含义**（务必阅读）：
θ 是**被提取的规律**，与规则 $R$ **处于同一认识论地位**——
都是从实例中提取，而非先验给定。
故「$\theta$ 与 $R$ 是什么关系」是**本裁决引出的新问题**，
登记为开放问题 **OQ-1**（见 `Fate.Adjudication`），**本实现不擅自回答**。

**Q-1 的连带删除**：本文件此前把 A13 做成
`TimeScaleRegime`（「时不变 vs 带阈值 $\epsilon$」两个互斥读法）。
**该二分已被作者废除**（作者答复确认取「θ 本身即被提取的规律」这一读法）。
保留它会造出「已废除的读法仍在代码中」的误导，故**整条删除**，
代之以 `ThetaIsExtracted` / `ThetaStableOn`。
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Order.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Dirac
import FateWorld.Legacy.Basic

namespace Fate

open Set

universe u

/- 本模块含非computable定义（`Measure`）。
规格阶段 0 只要求「类型化并编译通过」，不要求可执行；
故此处统一标记 `noncomputable`，并声明这是定义层的语言层选择，非理论断言。 -/
noncomputable section

/-! ===========================================================================
    §2  四元定义：命 θ、运 (u,ε)、因果 f、命运 {x_t}
        规格 §一「理论速览」与 `03-规范与裁决/04-符号与方程规范.md` §3.5
    =========================================================================== -/

/-- **四元框架（全量数据）**：把主公式涉及的全部空间与机制打包。

**为何要打包**：规格 `04-符号与方程规范.md` §3.3 已裁定
$f(x_t,u_t,\varepsilon_t;\theta,do(a_t))$ 是**类型错误**——
$do$ 是**算子**、$a_t$ 是**取值**，二者不同论域，**算子不能作函数自变量**。
故本实现把主公式的合法参数表 $(x_t,u_t,\varepsilon_t;\theta,a_t)$ 一次性类型化，
**使类型错误在编译期即被拒绝**，而不是靠人眼检查。

标签：**[定义性约定]**。 -/
structure Frame where
  /-- 参数空间 $\Theta$（规格 §1.2） -/
  Θ : ThetaSpace
  /-- 状态空间 $\mathcal{X}$（规格 §1.1） -/
  X : StateSpace
  /-- 外生输入空间 $\mathcal{U}$（规格 §1.2） -/
  U : InputSpace
  /-- 动作空间 $\mathcal{A}$（规格 §1.2；**原文从未定义，本实现补出**） -/
  Act : ActionSpace
  /-- 噪声取值空间（规格 §1.2；**规格未单列，本实现补出**） -/
  Ν : NoiseSpace

/-- **命**：$\text{命}_O := \theta$（规格 §1.2，01:58–60）。

规格明写两点，本实现均遵守：
1. $\text{命}_O := \theta$ —— **命**的唯一形式对应就是参数；
2. **不含 $x_0$**（01:295、01:458）——$x_0$ 与 $\theta$ **并列为「给定条件」**，
   但**只有 $\theta$ 是「命」**。

**⚠ 依作者裁决 Q-1 的补充**：$\theta$ 是**被提取的规律**（非先验给定）。
本别名只给出 $\theta$ 的**载体**（取值空间），
其**来源**由 `ThetaIsExtracted` 给出。二者不冲突：
**「从实例提取出的一个取值」仍然是一个取值**。

标签：**[定义性约定]**。 -/
abbrev Ming (F : Frame) := F.Θ.Carrier

/-- **运**：$(u_t,\varepsilon_t)$ —— 外生输入与随机扰动。

规格 §一「理论速览」：`运 = (u_t, ε_t)`。
规格 §3.4 规则 I3 进一步给出 $u_t=(a_t,\tilde u_t)$ 的分解。

**本实现按下述方式绑定**：运的**取值**是一对 $(u,\varepsilon)$。
干预 $a_t$ 依规则 I3 是 $u_t$ 的**可辨识分量**，
故本实现**不在「运」中重复计入 $a_t$**，而把 $a_t$ 作为**机制参数**
单独出现在 `Step` 的签名中（依规则 I1、I2）。

标签：**[定义性约定]**。 -/
def Yun (F : Frame) : Type _ := F.U.Carrier × F.Ν.Carrier

/-! ### §2.1 因果：单步状态转移函数 $f$

规格 `04-符号与方程规范.md` §3.1「说明」第 1 条**明确区分了两个 $f$**：

> $f$ 是**单步转移核**，不是轨迹生成器。…原文另有一处「命运 $=f(\text{命},\text{运},\dots)$」，
> 其 $f$ 是轨迹生成器，**不是同一个函数**（01:430–436）。
> **轨迹生成器不得用 $f$ 命名**；若要命名，写作 $F_{\text{traj}}$。

**本实现严格遵守**：单步转移记 `Step`（= $f$），轨迹生成记 `TrajGen`（= $F_{\text{traj}}$），
**二者不同名、不同签名**，由类型系统强制区分。 -/

/-- **因果**的载体之一：单步状态转移函数 $f$（规格 §1.2，01:241）。

**唯一权威离散方程**（规格 §3.1）：

$$x_{t+1} = f(x_t,\ u_t,\ \varepsilon_t;\ \theta,\ a_t)$$

**参数表逐位的类型**（规格 §3.3 的合法性检查，本实现以类型强制）：

| 位 | 符号 | 类型 | 本实现 |
|---|---|---|---|
| 1 | $x_t$ | $\mathcal{X}$ 中一点 | `F.X.Carrier` |
| 2 | $u_t$ | $\mathcal{U}$ 中一点 | `F.U.Carrier` |
| 3 | $\varepsilon_t$ | 随机变量的一次实现 | `F.Ν.Carrier` |
| 分号后 | $\theta$ | $\Theta$ 中一点 | `F.Θ.Carrier` |
| 分号后 | $a_t$ | $\mathcal{A}$ 中一点（**取值，非算子**） | `F.Act.Carrier` |

**注意第 5 位**：规格 §3.3 裁定原写法 $f(\dots;\theta,do(a_t))$ **作废**，
理由是 $do(a_t)$ 是**算子**（第 5 位与前四位不在同一论域）。
本实现的第 5 位是 `F.Act.Carrier`——**一个取值类型**，
故**该类型错误在本实现中不可能表示**。

标签：**[定义性约定]**（对应 A12：$a_t$ 是轨迹生成的必要输入项）。 -/
abbrev Step (F : Frame) : Type _ :=
  F.X.Carrier → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier → F.Act.Carrier → F.X.Carrier

/-- **轨迹生成器** $F_{\text{traj}}$（规格 §3.1 说明 1 明令**不得**用 $f$ 命名）。

规格 §3.1：

> $F_{\text{traj}}(\theta,x_0,\{u_t\},\{\varepsilon_t\},\{a_t\})=\{x_t\}$

**与 `Step` 的区别是本质的**：`Step` 的左手是**单步** $x_{t+1}$，
`TrajGen` 的左手是**整条轨迹** $\{x_t\}$。规格明写二者**不是同一个函数**，
故本实现分设两个定义，**不提供**任何把二者混用的便利别名。

标签：**[定义性约定]**。 -/
abbrev TrajGen (F : Frame) (ι : Type _) : Type _ :=
  F.Θ.Carrier → InitialState F.X →
    (ι → F.U.Carrier) → (ι → F.Ν.Carrier) → (ι → F.Act.Carrier) → Traj ι F.X

/-! ### §2.2 连续形式：漂移与扩散

规格 §3.2 **唯一权威连续方程**：

$$dX_t = \mu(X_t,\ \theta,\ a_t)\,dt + \sigma(X_t,\ \theta,\ a_t)\,dW_t$$

规格 §3.2 说明 2 明写：

> $a_t$ 进入 $\mu$ 与 $\sigma$ **两者**。若采用 $\sigma(X_t,\theta)$
> （扩散项不依赖干预），则 $\partial\sigma/\partial a_t\equiv 0$
> **是一条附加假设，必须显式声明**（02:413）。

**本实现据此把 $a_t$ 作为 $\mu$ 与 $\sigma$ 的显式参数**（不依赖 A16 的附加假设）。
若日后要采用「扩散项不依赖干预」的版本，
须**显式**用 `DiffusionNoIntervention`（见下）并登记 A16，**不得默认**。 -/

/-- 漂移系数 $\mu$：映射 $(\mathcal{X}\times\Theta\times\mathcal{A})\to\mathcal{X}$。

规格 §1.6 与 §3.2：**随机情形下「因果」的载体**，与 $f$ 并列。
规格 §2.4 规则 D2：$\mu$ **专指** SDE 漂移系数，不得裸用于他义。

标签：**[定义性约定]**。 -/
abbrev Drift (F : Frame) : Type _ :=
  F.X.Carrier → F.Θ.Carrier → F.Act.Carrier → F.X.Carrier

/-- 扩散系数 $\sigma$：映射到 $\mathbb{R}^{d\times m}$。

**本实现用 `Matrix` 的抽象占位**：规格未给出 $d$ 与 $m$ 的具体数值，
也未指明 $W_t$ 的维数（02:264 只说 $W_t$ 是布朗运动）。
故本实现把 $\sigma$ 的值域做成**参数化的矩阵类型**，
由使用者给出 `d`、`m`；**不擅自填数**。

标签：**[定义性约定]**。 -/
abbrev Diffusion (F : Frame) (d m : ℕ) : Type _ :=
  F.X.Carrier → F.Θ.Carrier → F.Act.Carrier → Matrix (Fin d) (Fin m) ℝ

/-- 布朗运动 $W_t$ 的取值类型（规格 §1.6，02:264）。

规格只给出 $dX_t=\mu\,dt+\sigma\,dW_t$，未指明 $W_t$ 的维数。
本实现做成参数化类型，**不填数**。

标签：**[定义性约定]**。 -/
abbrev BrownianValue (m : ℕ) : Type := Fin m → ℝ

/-- **A16 的显式版本**：扩散项不依赖干预（$\partial\sigma/\partial a_t\equiv 0$）。

规格 §3.2 说明 2：采用 $\sigma(X_t,\theta)$ 写法**必须声明这是附加假设而非默认**。
本实现据此**单独设一个类型**，使「采用该附加假设」成为一个**可见的类型选择**，
而不是一个隐形的默认。

**本定义即 A16 的类型层落点。** 使用它 = 声明 A16 生效。

标签：**[定义性约定]**（对应 A16）。 -/
abbrev DiffusionNoIntervention (F : Frame) (d m : ℕ) : Type _ :=
  F.X.Carrier → F.Θ.Carrier → Matrix (Fin d) (Fin m) ℝ

/-! ===========================================================================
    §3  观测制度（**作者裁决 Q-2：取 (a) 状态可直接获取**）
    =========================================================================== -/

/-- **A14 的两条读法**——**作者已裁决（Q-2）：取 (a)**。

规格 A14 原文：

> 状态 $x_t$ **可直接获取**（观测无损），或等价地：观测模型
> $y_t=h(x_t)+\eta_t$ 中的 $h$ **可逆**且 $\eta_t$ 已建模。

**作者裁决 Q-2**（`作者裁决-Q1到Q6.md`）：

> **状态 $x_t$ 可直接获取。** $\{x_t\}$ 是**数据**，命运**可被直接观测**。

**本实现据此**：`direct` 是**当前生效分支**（见 `currentRegime`）；
`invertible` **保留为备选构造子**（裁决明写「可保留为备选登记的说明」），
但**未被任何定义引用**。

**⚠ A14 的经验假设身份仍须在阶段 2 显式承担**——
「世界是否真能直接观测状态」是**经验问题**，不是定义问题。
本实现只落实**语言层选择**，不主张该选择在世界上成立。 -/
inductive ObservationRegime where
  /-- **读法一（作者选定）**：$x_t$ 可直接获取（观测无损）。
  **这是当前生效的分支。** -/
  | direct
  /-- 读法二（**备选，当前不生效**）：观测模型 $h$ 可逆且 $\eta_t$ 已建模。
  **保留为备选登记的说明，不作为当前分支。** -/
  | invertible
  deriving DecidableEq, Repr

/-- **当前生效的观测制度**（作者裁决 Q-2：取 `direct`）。

本定义把裁决**固定为代码中的单一取值**，
使任何依赖观测制度的定义都能引用它，
而**不需要**在每个定理里重复声明。

**注意**：这不是「假设」，而是**记录作者已作的裁决**。 -/
def currentRegime : ObservationRegime := .direct

/-- **裁决 Q-2 的形式自检**：当前制度确为 `direct`。

本引理的作用是**防止裁决被无声改动**——
若有人改了 `currentRegime`，本引理会编译失败。 -/
theorem currentRegime_eq_direct : currentRegime = ObservationRegime.direct := rfl

/-- **在 (a) 分支下，状态即观测**（Q-2 的「观测层退化为恒等」）。

Q-2 裁决原文：「观测层 $y_t=h(x_t)+\eta_t$ 退化为**恒等或仅装饰**」。

本定义给出该退化：观测就是状态本身，**不做任何变换**。

**类型说明**：本定义的值是恒等函数——
它使「$y_t$ 与 $x_t$ 同空间、同值」成为**定义层的事实**，
从而后续凡引用观测处**不需要额外的可逆性前件**（那正是 (b) 支才需要的）。 -/
def ObservedState (F : Frame) : F.X.Carrier → F.X.Carrier := id

/-- (a) 分支下「观测 = 状态」：$\mathrm{ObservedState}(x)=x$。

**这是关于定义之间相容性的引理**，不是理论命题。 -/
theorem observedState_eq_self (F : Frame) (x : F.X.Carrier) :
    ObservedState F x = x := rfl

/-! ===========================================================================
    §4  规则层（规格 §1.4；对应理论第 5 章）
    =========================================================================== -/

/-- 上下文（条件）空间 $\mathcal{C}$（规格 §1.4，03:18）。

规格备注：**原文未定义其结构**（03:330）。
故本实现只给类型，**不施加任何结构约束**——若下游需要结构，
须显式登记相应假设，不得默认。 -/
structure CtxSpace where
  Carrier : Type*

/-- 输出 / 预测 / 行动空间 $\mathcal{Y}$（规格 §1.4，03:17）。

规格 §2.3 规则 N3：$\mathcal{Y}$ **同时**是「规则输出空间」与「观测取值空间」，
二者在数学上是**同一空间**。**该同一性必须在符号表首次出现处登记**——
本实现据此**只设一个** `OutSpace`，**不设两个**。

⚠⚠ **第 96 轮（裁决 P / 乙）：`OutSpace` 已与 `StateSpace` 统一。**

**依据**：规格 §2.3 规则 N3 明说
「$\mathcal{Y}$ **同时**是「规则输出空间」与「观测取值空间」，
二者在数学上是**同一空间**」。

**⟹ 原先「只设一个 `OutSpace`」虽符合规格字面，
**但它与 `StateSpace` 仍是两个不同的类型**，**
**故无法表达「输出空间可再作为状态空间」这一链式使用**
（这正是 `ComposeOperator` 101 个错误的根源）。**

**⟹ 本实现改为 `abbrev OutSpace := StateSpace`** ——
**这是「同一性」在**类型层**的直接落实**，
**且使链式组合 `Rule C X Y → Rule C Y Z` 变为**类型正确**。** -/

abbrev OutSpace : Type _ := StateSpace


/-- 局部状态子空间 $\mathcal{X}_{\text{local}}\subset\mathcal{X}$（规格 §1.4，03:18）。

规格两处指出这是**未定义项**：
- 规格 §1.4 备注：「**原文从未定义划界方式**」（03:329）
- A9：「局部域 $\mathcal{X}_{\text{local}}$ 的划分存在且稳定」——
  类型为**不可证的经验假设**

**故本实现把「划界方式」显式做成一个参数**（一个把状态映到局部域的函数），
使 A9 成为一个**可见的前件**，而不是被悄悄假定。
A9 不成立 ⟹ 这个参数无意义 ⟹ 依赖它的定理全部失效。**这正是 A9 的承载性所在。** -/
structure LocalDomain (X : StateSpace) where
  /-- 局部域的指标类型（规格未指明，本实现参数化，不填具体结构） -/
  Idx : Type*
  /-- 划界映射：把状态分配到某个局部域。**这就是 A9 要求「存在且稳定」的对象。** -/
  assign : X.Carrier → Idx

/-- **单条**规则 $R$（规格 §1.4，03:14–28）。

规格 §1.4 备注给出**关键的记法裁定**：

> **单个映射，不是集合**。原文映射式与条件分布式并列未择一；
> **正式文档以条件分布 $R:P(y\mid x,c)$ 为主**，
> 映射式为 $p$ 退化为点质量时的特例（03:524）。

**本实现遵守该裁定**：`Rule` 以**核（条件分布）**为主形式；
点质量映射式作为**特例**由 `DetRule` 给出。

**规格 §2.2 规则 S1 的落实**：$R$（单条规则）与 $\mathcal{R}$（规则集）
**严格区分**，本实现分设 `Rule` 与 `Rules`，**不提供**把单条规则当集合用的别名。 -/
structure Rule (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] where
  /-- 规则的条件分布核：给定上下文 $c$ 与局部状态 $x$，给出 $\mathcal{Y}$ 上的分布。 -/
  kernel : C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier

/-- 规则的**点质量特例**（规格 §1.4：映射式为 $p$ 退化为点质量时的特例）。 -/
abbrev DetRule (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] : Type _ :=
  C.Carrier → X.Carrier → Y.Carrier

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
  [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]

/-! ### §4.0.1 `DetRule` 诱导 `Rule`：点质量嵌入

规格 §1.4 裁定：**以核（条件分布）为主形式，映射式为 $p$ 退化为点质量时的特例**。
本节把该裁定**构造性地**落实为一个从 `DetRule` 到 `Rule` 的映射：
把确定性映射 $d(c,x)$ 送到**质量集中在 $d(c,x)$ 的 Dirac 测度**。

其数学内容：

$$\iota : (\mathcal{C}\to\mathcal{X}\to\mathcal{Y}) \longrightarrow
    \big(\mathcal{C}\to\mathcal{X}\to\mathrm{Measure}\,\mathcal{Y}\big),
  \qquad \iota(d)(c,x) := \delta_{d(c,x)} .$$

**本节回答两个问题**：
1. **正向**：每个 `DetRule` 诱导一个 `Rule`（`DetRule.toRule`）；
2. **反向**：一个 `Rule` 何时**恰由**某个 `DetRule` 诱导？
   答案是**当且仅当它的每个核都是点质量（Dirac 测度）**
   （`Rule.isDet_iff_dirac`）——**无需**点分离假设即可判定存在性；
   但若要**唯一恢复**那个 `DetRule`，则须 `SeparatesPoints`（由
   `MeasurableSingletonClass` 自动满足），见 `DetRule.toRule_injective`。 -/

/-- **点质量嵌入** $\iota$：把一个 `DetRule` 视为核退化为 Dirac 点质量的 `Rule`。

这是规格 §1.4「映射式为 $p$ 退化为点质量时的特例」的**构造性落实**：
"映射式"就是 `DetRule`，"点质量"就是 `Measure.dirac`。 -/
def DetRule.toRule (d : DetRule C X Y) : Rule C X Y where
  kernel := fun c x => MeasureTheory.Measure.dirac (d c x)

/-- 嵌入后的核**逐点等于**该点上的 Dirac 测度（定义性等式，`rfl`）。 -/
@[simp] theorem DetRule.toRule_kernel (d : DetRule C X Y)
    (c : C.Carrier) (x : X.Carrier) :
    d.toRule.kernel c x = MeasureTheory.Measure.dirac (d c x) := rfl

/-- **"由 `DetRule` 诱导" 的谓词**：`R.IsDet` 表示存在确定性映射 $d$
使 $R = \iota(d)$。

用**存在量词**（而非直接给 $d$）表述，使"反向何时成立"成为一个
可判定的**性质**，而不需要预先选出见证。 -/
def Rule.IsDet (R : Rule C X Y) : Prop :=
  ∃ d : DetRule C X Y, d.toRule = R

/-- **正向（每个 `DetRule` 诱导一个 `Rule`）**：嵌入 $\iota$ 的像。 -/
theorem DetRule.isDet_toRule (d : DetRule C X Y) : d.toRule.IsDet := ⟨d, rfl⟩

/-- **反向的判定（核心定理）**：一个 `Rule` 恰由某个 `DetRule` 诱导，
**当且仅当**其每个条件分布核都是点质量（某个点上的 Dirac 测度）：

$$R\in\mathrm{im}\,\iota
  \iff \forall c\,x,\ \exists y,\ R.\mathrm{kernel}\,c\,x = \delta_y .$$

**存在性方向不需要任何点分离假设**——因为要证 `R` 来自某个 `DetRule`，
只需用选择公理从每个核中**挑**一个 Dirac 中心即可（`Classical.choose`）。

**何时反向不成立**：当某 `(c,x)` 处的核**不是**点质量
（例如正态分布、两点混合、区间均匀分布）时，`R.IsDet` 为假——
这正是"特例"一词的确切含义：`Rule` **严格多于** `DetRule` 的像。 -/
theorem Rule.isDet_iff_dirac (R : Rule C X Y) :
    R.IsDet ↔ ∀ c x, ∃ y, R.kernel c x = MeasureTheory.Measure.dirac y := by
  constructor
  · rintro ⟨d, rfl⟩ c x
    exact ⟨d c x, rfl⟩
  · intro h
    refine ⟨fun c x => Classical.choose (h c x), ?_⟩
    show Rule.mk (fun c x => MeasureTheory.Measure.dirac (Classical.choose (h c x))) = R
    cases R with
    | mk k =>
      congr
      funext c x
      exact (Classical.choose_spec (h c x)).symm

/-- **注入性（唯一恢复）**：在**点分离**假设下，$\iota$ 是单射，
故诱导 `Rule` 的 `DetRule` **唯一**。

**为什么需要点分离**：Dirac 测度 $\delta_x$ 一般**不能**唯一决定 $x$。
若可测空间不分离点（例如平凡 $\sigma$-代数 $\{\varnothing,\mathcal{Y}\}$），
则所有 $\delta_x$ 都相等，$\iota$ 必不单射。
`MeasurableSingletonClass Y.Carrier`（单点集可测）自动给出 `SeparatesPoints`，
是通常情形下的充分条件。 -/
theorem DetRule.toRule_injective [MeasurableSpace.SeparatesPoints Y.Carrier] :
    Function.Injective (DetRule.toRule (C := C) (X := X) (Y := Y)) := by
  intro d1 d2 h
  funext c x
  have hk : MeasureTheory.Measure.dirac (d1 c x) = MeasureTheory.Measure.dirac (d2 c x) := by
    have := congrFun (congrFun (congrArg Rule.kernel h) c) x
    simpa using this
  exact (MeasureTheory.dirac_eq_dirac_iff.mp hk)

/-- **见证唯一**：同一个 `Rule` 若由两个 `DetRule` 诱导，则二者相等
（`toRule_injective` 的直接推论）。 -/
theorem Rule.IsDet.det_eq [MeasurableSpace.SeparatesPoints Y.Carrier]
    {R : Rule C X Y} {d1 d2 : DetRule C X Y}
    (h1 : d1.toRule = R) (h2 : d2.toRule = R) : d1 = d2 :=
  DetRule.toRule_injective (h1.trans h2.symm)

/-! ### §4.1 作者裁决 J（OQ-1）：**θ 与 R 的关系——R 以 θ 为参数**

**作者裁决 J**（`作者裁决J-OQ1.md`）：

> **采纳「候选 1 精化版」：α 提取两者，θ 是全局参数，
> R 是局部规则族且以 θ 为参数。**

$$\text{实例}\ \mathcal{E}
  \ \xrightarrow{\ \alpha_\theta\ } \theta
  \qquad
  \text{实例}\ \mathcal{E}
  \ \xrightarrow{\ \alpha_R\ } R_\theta$$

**裁决的四条核心断言**：
1. $\theta$ 与 $R$ **同源**（都从实例提取）——与 Q-1 一致；
2. $\theta$ 是**全局的、无上下文的**；$R$ 是**局部的、带上下文的**；
3. **$R$ 依赖 $\theta$**，即 $R_\theta$；
4. **两者不同型**：$\theta\in\Theta$；$R$ 是核 $\mathcal{C}\times\mathcal{X}\to\mathrm{Measure}\,\mathcal{Y}$。

**裁决给出的实质理由（本实现原样记录）**：

> 1. 命运 $=\{x_t\}$，通过**预测**给出
> 2. 主线是 $\text{实例}\to(\alpha)\to\text{规则}\to\text{预测}$——**预测走 $R$ 这条路**
> 3. 若 **$R$ 不吃 $\theta$**，则 $\theta$ 只能经 $f$ 影响状态，**不进入预测路径**
> 4. **后果**：「命影响命运」在**预测层面落空**

**⚠ 落地纪律（裁决明示）**：采用**加法式变更，不破坏已冻结的签名**。
故本节**不删除 `Rule`**，只在**其后新增** $\theta$ 参数化版本，
并**证明退化关系**（$\theta$ 无关版是特例）。 -/

/-- **以 $\theta$ 为参数的规则**（作者裁决 J 的新增对象 $R_\theta$）。

与 `Rule` 的**唯一区别**：核多接受一个 $\theta$ 参数（放在最前）。

**为什么 $\theta$ 放最前**：使 `RuleWithTheta Θ ... ` 在**固定 $\theta$** 后
逐字退化为 `Rule`（见 `toRule` / `rule_is_degenerate_case`）。

**⚠ 本实现不删除 `Rule`**——
`00-签名冻结.md` 的冻结纪律要求加法式变更。 -/
structure RuleWithTheta (C : CtxSpace) (X : StateSpace) (Y : OutSpace) (Θ : ThetaSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] where
  /-- 以 $\theta$ 为参数的条件分布核：$\theta\mapsto c\mapsto x\mapsto\mathrm{Measure}\,\mathcal{Y}$。 -/
  kernel : Θ.Carrier → C.Carrier → X.Carrier → MeasureTheory.Measure Y.Carrier

/-- **退化映射**：把一个 $\theta$ 无关的 `Rule` 提升为 `RuleWithTheta`
（核忽略 $\theta$）。

**这是作者裁决 J 要求的「退化关系」的构造性一半**。 -/
def Rule.toRuleWithTheta {C : CtxSpace} {X : StateSpace} {Y : OutSpace} {Θ : ThetaSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (R : Rule C X Y) : RuleWithTheta C X Y Θ where
  kernel := fun _θ c x => R.kernel c x

/-- **作者裁决 J 要求的退化关系（已证）**：

$$\forall \theta\,c\,x,\ (\mathrm{toRuleWithTheta}\,R).\mathrm{kernel}\,\theta\,c\,x
  = R.\mathrm{kernel}\,c\,x$$

即：**$\theta$ 无关的规则确实是 $\theta$ 参数化规则的退化情形**
（核不依赖 $\theta$）。

**这表明加法式变更满足裁决要求**：
- `Rule` 保持原签名（冻结有效）；
- 新增 `RuleWithTheta`（$R_\theta$）；
- 二者由本定理连接。∎ -/
theorem rule_is_degenerate_case {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    {Θ : ThetaSpace} [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (R : Rule C X Y) (θ : Θ.Carrier) (c : C.Carrier) (x : X.Carrier) :
    (R.toRuleWithTheta (Θ := Θ)).kernel θ c x = R.kernel c x := rfl

/-- **反向**：固定 $\theta$ 后，`RuleWithTheta` 给出一个 `Rule`。

**这是退化关系的另一半**：$R_\theta$ 在**每个具体 $\theta$** 上都是一个 `Rule`。
故「$\theta$ 参数化规则族」可理解为**一族 `Rule`**，由 $\theta$ 索引。 -/
def RuleWithTheta.toRule {C : CtxSpace} {X : StateSpace} {Y : OutSpace} {Θ : ThetaSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (Rθ : RuleWithTheta C X Y Θ) (θ : Θ.Carrier) : Rule C X Y where
  kernel := fun c x => Rθ.kernel θ c x

/-- **往返一致**：$\theta$ 无关规则经「提升再固定 $\theta$」回到原规则。 -/
theorem toRule_toRuleWithTheta {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    {Θ : ThetaSpace} [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (R : Rule C X Y) (θ : Θ.Carrier) :
    (R.toRuleWithTheta (Θ := Θ)).toRule θ = R := rfl

/-- **规则集** $\mathcal{R}=\{R_i\}$（规格 §1.4，S:11883、S:11935 附近）。

规格 §1.4 备注：**与单条规则 $R$ 严格区分**。
A1 声明 $\alpha(\mathcal{E})\subseteq\mathcal{R}$（抽象算子的值域落在规则空间内）。

**本实现用 `Set`**，使 A1 的「$\subseteq$」在类型层成立。 -/
abbrev Rules (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] : Type _ :=
  Set (Rule C X Y)

/-- **以 $\theta$ 为参数的规则集**（裁决 J 下的 $\mathcal{R}_\theta$）。

由 `RuleWithTheta` 构成，对应裁决 J 的
「$R$ 是**局部的、带上下文的**规则族，以 $\theta$ 为参数」。 -/
abbrev RulesWithTheta (C : CtxSpace) (X : StateSpace) (Y : OutSpace) (Θ : ThetaSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] : Type _ :=
  Set (RuleWithTheta C X Y Θ)


/-- **实例集** $\mathcal{E}=\{e_i\}$（规格 §1.4，S:11885；03:278）。

**规格 §2.2 规则 S1（关键）**：裸 $E$ 归**图的边集** $E\subseteq V\times V$；
**实例集改花体** $\mathcal{E}$。

**本实现据此把实例集命名为 `Inst`，绝不命名为 `E`**——
字体在 Lean 中不可用，故用**改名**落实「该区分必须是机械可判的」。

规格 A1 裁定 $\alpha:\mathcal{E}\to\mathcal{R}$，即**抽象算子的定义域是实例集**
（**非机制**）。本实现据此把 `Inst` 作为 `alpha` 的定义域。 -/
structure InstSpace where
  Carrier : Type*

/-! ===========================================================================
    §5  作者裁决 Q-1 的落实：**θ 是被提取的规律**
    =========================================================================== -/

/-- **$\theta$ 是被提取的规律**（作者裁决 Q-1 的形式化落点）。

**作者裁决 Q-1**（`作者裁决-Q1到Q6.md`）原文：

> θ **不是被给定的参数，而是从实例数据中提取出来的规律**。

**该裁决废除了**实现代理此前登记的两个选项：
- ~~(a) 时不变（$\dot\theta=0$）~~
- ~~(b) 带阈值 $\epsilon=\tau_{\text{fast}}/\tau_{\text{slow}}$~~

$\theta$ **不是先验给定的参数**，而是由某个**提取过程**从实例集得到的输出。

**类型设计说明**：本定义**不改变** $\Theta$ 的类型（仍是 `ThetaSpace`），
而是**显式记录「$\theta$ 有来源」这一事实**——给出把实例集映到 $\theta$ 的提取映射。

**为什么这样设计而不是改 `ThetaSpace`**：改类型会破坏主公式
（它需要 $\theta$ 是取值）。而「加上一个来源映射」既落实了裁决，
又不改动已冻结的主公式签名（符合 `00-签名冻结.md` 的冻结纪律）。

**⚠ 本实现不声称**：提取映射唯一、可计算、或与 $\alpha$ 相同。
- 「可计算」是关于 $\alpha$ 的 **A8.T0**；$\theta$ 的提取映射是否可实现
  **未被作者裁决**，本实现**不擅自假定**。
- 「与 $\alpha$ 的关系」是 Q-1 引出的**新开放问题**，见 `Fate.Adjudication` 的 OQ-1。

标签：**[定义性约定]**（对应 A13 的**新读法**）。 -/
structure ThetaIsExtracted (E : InstSpace) (Θ : ThetaSpace) where
  /-- 提取映射：从实例集得到 $\theta$。
  **这就是 Q-1 说的「从实例数据中提取」。** -/
  extract : E.Carrier → Θ.Carrier

/-- **$\theta$ 在样本上稳定**（作者裁决 Q-1 对「慢」的**新定义**）。

Q-1 原文：

> 「慢」的含义随之改变：不再是「变化率小」的动力学判据，
> 而是**「在提取所覆盖的样本上稳定」**——**稳定性而非时间尺度**。

**本定义**：给定样本集 $S$，$\theta$ 在 $S$ 上稳定 $\iff$
提取映射在 $S$ 上取**常值**。

**与已废除旧读法的区别（必须写明）**：

| | 旧读法（**已废除**） | 本定义（作者裁决） |
|---|---|---|
| 判据 | $\lVert\dot\theta\rVert\ll\lVert\dot x\rVert$ 或阈值 $\epsilon$ | **样本上取常值** |
| 类型 | **动力学**（时间尺度分离） | **统计/提取**（样本一致性） |
| 是否需要数据 | **不需要**（可先验陈述） | **必须有数据** |

**⚠ 待裁决**：样本集 $S$ 的选取（大小、代表性）**未被作者裁决**，
本实现做成参数，**不擅自选定**（规格明写「填数即为虚构」）。

标签：**[定义性约定]**（对应 A13 的「稳定」读法）。 -/
def ThetaStableOn {E : InstSpace} {Θ : ThetaSpace}
    (ext : ThetaIsExtracted E Θ) (S : Set E.Carrier) : Prop :=
  ∀ e₁ ∈ S, ∀ e₂ ∈ S, ext.extract e₁ = ext.extract e₂

/-- **稳定性的单调性：$S$ 上稳定 ⟹ 任意子集上稳定**。

若 $\theta$ 在 $S$ 上稳定，则对任意 $T\subseteq S$，$\theta$ 在 $T$ 上也稳定。

**这是 `ThetaStableOn` 的直接推论**：$S$ 中任两点提取值相等，
$T$ 中任两点也是 $S$ 中两点，故提取值相等。
**注意方向**：稳定性**向下**封闭（子集继承），但**不向上**封闭
（一般 $S\subseteq T$ 推不出 $T$ 上稳定）——上层蕴含需 `thetaStableOn_union`
的额外条件（交集非空）。 -/
theorem thetaStableOn_subset {E : InstSpace} {Θ : ThetaSpace}
    (ext : ThetaIsExtracted E Θ) {S T : Set E.Carrier}
    (h : ThetaStableOn ext S) (hTS : T ⊆ S) :
    ThetaStableOn ext T :=
  fun e₁ he₁ e₂ he₂ => h e₁ (hTS he₁) e₂ (hTS he₂)

/-- **$\theta$ 在两个样本集上一致**（稳定性的可组合形式）。

若 $\theta$ 在 $S_1$ 与 $S_2$ 上分别稳定，且 $S_1\cap S_2\neq\emptyset$，
则 $\theta$ 在 $S_1\cup S_2$ 上稳定。

**这是「稳定性」这个词应有之义的形式化**：
稳定不是「各样本集内常值」（那可以各取不同值），
而是**跨样本集也一致**——本引理给出该跨集一致性。

**证明**：$S_1\cup S_2$ 中任两点，经 $S_1\cap S_2$ 中的公共点中转即得。∎

**注意**：本引理证明的是**定义之间的相容性**，
不是关于世界的断言——故它**不构成**对 A13 的证明。 -/
theorem thetaStableOn_union {E : InstSpace} {Θ : ThetaSpace}
    (ext : ThetaIsExtracted E Θ) {S₁ S₂ : Set E.Carrier}
    (h₁ : ThetaStableOn ext S₁) (h₂ : ThetaStableOn ext S₂)
    (hne : (S₁ ∩ S₂).Nonempty) :
    ThetaStableOn ext (S₁ ∪ S₂) := by
  obtain ⟨c, hc₁, hc₂⟩ := hne
  intro e₁ he₁ e₂ he₂
  rcases he₁ with he₁ | he₁ <;> rcases he₂ with he₂ | he₂
  · exact h₁ e₁ he₁ e₂ he₂
  · rw [h₁ e₁ he₁ c hc₁, h₂ c hc₂ e₂ he₂]
  · rw [h₂ e₁ he₁ c hc₂, h₁ c hc₁ e₂ he₂]
  · exact h₂ e₁ he₁ e₂ he₂

/-- **$\theta$ 作为提取的输出是一个取值**。

**注意**：本定义**不**声称 $\theta$ 时不变是世界的性质。
在 Q-1 的读法下，$\theta$ 是**提取的输出**——
「提取」这一动作**本身**就给出单个取值（提取一次得到一个 $\theta$）。

**它取代了**已废除的 `ThetaAsConstant`——
后者的命名预设了「时不变」这一**动力学读法**，而该读法已被作者废除。

标签：**[定义性约定]**（对应 A13）。 -/
abbrev ThetaAsExtractedValue (F : Frame) := F.Θ.Carrier

/-! ===========================================================================
    §6  规则层的算子
    =========================================================================== -/

/-- **抽象算子** $\alpha$：$\mathcal{E}\to\mathcal{R}$（规格 §1.4，03:279–280）。

**规格 §1.4 备注（关键）**：

> **定义域为实例集** $\mathcal{E}$（$\alpha:\mathcal{E}\to\mathcal{R}$），**非机制**。

**依裁决 D（`01-作者裁决C-最彻底.md`）**：

> $\alpha$ **定义为**形式背景 $\mathbb{K}=(G_{\mathrm{FCA}},M_{\mathrm{FCA}},I)$ 上的
> **取概念（导出算子不动点）过程**。

**本实现的处置**：本文件只给出 $\alpha$ 的**类型签名**（阶段 0 只做类型化）；
其 **FCA 具体化**在 `Fate.Alpha` 中给出（阶段 1B，依裁决 D）。
**本文件不把 $\alpha$ 做成 `axiom` 或未解释常量**——它是一个**待填的签名**，
由 `Fate.Alpha` 的 `takeConcept` 提供构造。

**⚠ 依作者裁决 Q-5**：$\alpha$ 的「可计算」分两层——
**A8.T0（可实现，当前目标）** 与 **A8.T1（高效，登记待发展）**。
下游前件**只引用 A8.T0**。

标签：**[定义性约定]**（对应 A1：$\alpha(\mathcal{E})\subseteq\mathcal{R}$）。 -/
abbrev Alpha (E : InstSpace) (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] : Type _ :=
  E.Carrier → Rule C X Y

/-- **泛化算子** $\gamma$：局部规则 → 全局规则（规格 §1.4，03:460）。

规格 A2 的类型声明形式：$\gamma(R_{\text{local}})=R_{\text{global}}$。
规格 A2 备注明写：「第 31 轮把定义写成了等式，**须改写为类型声明**」。
**本实现照办**：这里是**类型**（`abbrev`），不是等式断言。

标签：**[定义性约定]**（对应 A2）。 -/
abbrev Gamma (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] : Type _ :=
  Rule C X Y → Rule C X Y

/-- **组合（推广）算子** $\circ$：规则 × 规则 → 规则（规格 §1.4，03:460）。

规格 §1.4 备注与 §2.5 规则 R2 均指出：$\pi$ 有**三义**
（组合算子、投影 $\pi_O$、平稳分布 $\pi$），
且**建议「组合」改用 $\circ$ 记法**以免三义。

**本实现采纳该建议**：命名为 `Comb`，用 $\circ$ 的语义，
**不使用** `pi`（避开三义）。

规格 A3 声明 $\mathcal{R}$ 对 $\circ$ **封闭**：$R_1\circ\cdots\circ R_n\in\mathcal{R}$。
**本实现把「封闭性」留作待证/约定**，不在此处偷偷塞进类型
（类型只能表达「二元运算」，表达不了「结果仍在 $\mathcal{R}$ 内」这一封闭性断言；
后者须由 A3 显式承担）。

标签：**[定义性约定]**（对应 A3 的运算部分；封闭性断言由 A3 承担）。 -/
abbrev Comb (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] : Type _ :=
  Rule C X Y → Rule C X Y → Rule C X Y

/-- **完善（更新）算子** $\upsilon$：规则 × 数据 → 规则（规格 §1.4，03:460）。

标签：**[定义性约定]**。 -/
abbrev Refine (E : InstSpace) (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] : Type _ :=
  Rule C X Y → E.Carrier → Rule C X Y

/-- **构造等价**关系 $\sim$ 的载体：$\mathcal{R}$ 上的等价关系（规格 §1.4；A4）。

规格 A4 原文：

> 存在「构造等价」的等价关系 $\sim$，且 $\sim$ **与 $\circ$ 相容**
> （$R_1\sim R_1',\,R_2\sim R_2'\Rightarrow R_1\circ R_2\sim R_1'\circ R_2'$）。

规格 A4 备注：**无相容性则组合无良定义**。

**本实现的处置**：此处只给出关系的**类型**（一个二元关系）。
「它是等价关系」与「它 $\circ$-相容」是**A4 的两条断言**，
属**定义性约定**，但**本实现不把它们塞进类型**——
因为塞进去就等于把约定伪装成定义，违反「同一编号不得承担两种类型」。

标签：**[定义性约定]**（对应 A4 的关系存在性；等价性与相容性由 A4 承担）。 -/
abbrev ConstrEquiv (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] : Type _ :=
  Rule C X Y → Rule C X Y → Prop

/-- **预测算子** $\phi$：$\phi(x_t)=P(x_{t+1}\mid x_t)$（规格 §1.6，03:320）。

**规格 §2.4 规则 D1 的落实（关键）**：

| 符号 | 专指 | 本实现命名 |
|---|---|---|
| $\phi_t$ | 连续动力系统的**流映射**（$t$ 为时间参数） | `Flow` |
| $\phi$ | **预测算子** | `Pred`（本定义） |

二者**必须按此分工**。规格并注明：「若在连续语境中需要预测算子，
写作 $\phi_{\text{pred}}$」。

标签：**[定义性约定]**。 -/
abbrev Pred (X : StateSpace) [MeasurableSpace X.Carrier] : Type _ :=
  X.Carrier → MeasureTheory.Measure X.Carrier

/-- **流映射** $\phi_t$：连续动力系统的流（规格 §1.1，02:99、02:206）。

规格 §1.1 给出性质 $\phi_0(x)=x$ 与 $\phi_{t+s}=\phi_t\circ\phi_s$。
**这些性质是断言，不是定义**，故本实现**只给类型签名**，
性质留待相应阶段陈述与证明（阶段 0 只做类型化）。

**与 `Pred` 严格不同名**，落实规格 §2.4 规则 D1。

标签：**[定义性约定]**。 -/
abbrev Flow (X : StateSpace) : Type _ :=
  TimeIdx.Continuous → X.Carrier → X.Carrier

end

/-! ===========================================================================
  §5  取消退化：Rule 在 RuleWithTheta 中的**纤维刻画**（P4）

  **背景**：现有 `rule_is_degenerate_case` 是 `rfl` ——
  它只说「提升后再取回等于原物」，**没有刻画 `Rule` 在 `RuleWithTheta` 中的像**。

  **本节的强化**：证明
  $$\exists R,\ R\texttt{.toRuleWithTheta} = R_\theta
    \iff \forall \theta_1 \theta_2,\ R_\theta(\theta_1) = R_\theta(\theta_2)$$
  即 **`Rule` 恰是 `RuleWithTheta` 中「核不依赖 $\theta$」的那些**。

  **这把它从「特例」变成「纤维」** —— 原库完全没有这条。

  **⚠ 无硬编码**（依作者裁决 Q-1）：本节不引入任何常数。

  **⚠ 诚实标注**：`←` 方向**需要 `Θ` 非空**（否则「任选一个 `θ₀`」无对象）。
  这是**数学上真实的前提**，不是技术性规避。
  =========================================================================== -/

/-! ### §5.1 定义：θ-无关性 -/

/-- **`θ`-无关**：核完全不依赖 `θ`。

即：把 `θ` 这个参数**取掉也不损失信息**。
这精确刻画了「哪些 `RuleWithTheta` 其实是 `Rule`」。 -/
def ThetaIndependent {C : CtxSpace} {X : StateSpace} {Y : OutSpace} {Θ : ThetaSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (Rθ : RuleWithTheta C X Y Θ) : Prop :=
  ∀ θ₁ θ₂ c x, Rθ.kernel θ₁ c x = Rθ.kernel θ₂ c x

/-! ### §5.2 `→` 方向：来自 `Rule` 的必定 θ-无关 -/

/-- **正向**：若 `Rθ` 来自某个 `Rule`，则其核不依赖 `θ`。

**证明**：`toRuleWithTheta` 的定义体 `fun _θ c x => R.kernel c x` 忽略 `θ`。 -/
theorem thetaIndependent_of_exists_rule {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    {Θ : ThetaSpace} [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    {Rθ : RuleWithTheta C X Y Θ}
    (h : ∃ R : Rule C X Y, R.toRuleWithTheta (Θ := Θ) = Rθ) :
    ThetaIndependent Rθ := by
  rcases h with ⟨R, rfl⟩
  intro θ₁ θ₂ c x
  rfl

/-! ### §5.3 ⭐ `←` 方向：θ-无关 ⟹ 可构造出 `Rule`（**须 `Θ` 非空**） -/

/-- ⭐ **反向（构造性）**：θ-无关的 `RuleWithTheta` **必来自某个 `Rule`**。

**⚠ 前件 `[Nonempty Θ.Carrier]` 是数学上真实的** ——
若 `Θ` 为空，则「核不依赖 θ」是**空洞真**（无 `θ` 可取），
此时不能无条件构造出 `Rule`。**本节如实保留该前件。**

**构造**：任取 `θ₀ : Θ.Carrier`，令 `R.kernel c x := Rθ.kernel θ₀ c x`。
由 `ThetaIndependent` 知该选择**与 `θ₀` 无关**。 -/
theorem exists_rule_of_thetaIndependent {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    {Θ : ThetaSpace} [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    [Nonempty Θ.Carrier]
    {Rθ : RuleWithTheta C X Y Θ} (h : ThetaIndependent Rθ) :
    ∃ R : Rule C X Y, R.toRuleWithTheta (Θ := Θ) = Rθ := by
  classical
  let θ₀ : Θ.Carrier := Classical.choice inferInstance
  refine ⟨⟨fun c x => Rθ.kernel θ₀ c x⟩, ?_⟩
  -- 目标：两个 `RuleWithTheta` 相等。核函数相等即可（结构只有 kernel 一个字段）
  have hfun : (fun (_ : Θ.Carrier) (c : C.Carrier) (x : X.Carrier) => Rθ.kernel θ₀ c x)
      = Rθ.kernel := by
    funext θ c x
    exact h θ₀ θ c x
  cases Rθ
  simp only [Rule.toRuleWithTheta]
  rw [hfun]

/-! ### §5.4 ⭐⭐ 主定理：纤维刻画（完整双向） -/

/-- ⭐⭐ **主定理**：`Rule` 的像**恰好**是 `θ`-无关的那些 `RuleWithTheta`。

**这是本节的核心交付**，原库完全缺失。

**它把「退化」从定义的重念升级为「纤维的刻画」**：

| 表述 | 强度 |
|---|---|
| 旧：`(R.toRuleWithTheta).kernel θ c x = R.kernel c x`（`rfl`）| 平凡 |
| **新**：`(∃ R, R.toRuleWithTheta = Rθ) ↔ ThetaIndependent Rθ` | **刻画出像** |

**⚠ 前件 `[Nonempty Θ.Carrier]`**：见 `exists_rule_of_thetaIndependent` 的说明 ——
这是**数学上真实的前提**，非技术性规避。 -/
theorem degenerate_iff_thetaIndependent {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    {Θ : ThetaSpace} [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    [Nonempty Θ.Carrier]
    (Rθ : RuleWithTheta C X Y Θ) :
    (∃ R : Rule C X Y, R.toRuleWithTheta (Θ := Θ) = Rθ) ↔ ThetaIndependent Rθ :=
  ⟨thetaIndependent_of_exists_rule, exists_rule_of_thetaIndependent⟩

/-! ### §5.5 推论 -/

/-- **提升后的规则必 θ-无关**（`toRuleWithTheta` 的像落在纤维内）。

**这是主定理 `→` 方向的直用**，单列以便下游引用。 -/
theorem thetaIndependent_toRuleWithTheta {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    {Θ : ThetaSpace} [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (R : Rule C X Y) : ThetaIndependent (R.toRuleWithTheta (Θ := Θ)) :=
  thetaIndependent_of_exists_rule ⟨R, rfl⟩

end Fate
