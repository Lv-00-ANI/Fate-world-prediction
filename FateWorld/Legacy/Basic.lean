/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.Basic
阶段：**阶段 0 —— 定义与签名冻结**（规格 `02-证明路线/01-路线图.md` §阶段 0）

---------------------------------------------------------------------------
本文件的地位
---------------------------------------------------------------------------
本文件**只做定义与类型声明，不证任何定理**。
依阶段 0 验收标准 1：**零 `sorry`、零 `admit`、零 `axiom`**。
本文件据此约束：凡未证成的陈述**不写在此处**，而是登记为 `[待证]`
并留在相应阶段的文件中。

---------------------------------------------------------------------------
全局符号对照表（Lean 标识符 ↔ 规格数学符号 ↔ 出处）
---------------------------------------------------------------------------
依规格 `03-规范与裁决/04-符号与方程规范.md` §一 的全局符号表逐条对应。

## 对象与轨迹层（规格 §1.1）

| Lean 标识符        | 规格符号                    | 出处        |
|--------------------|-----------------------------|-------------|
| `O` (Obj)          | $O$ 系统/对象               | 01:230      |
| `X` (StateSpace)   | $\mathcal{X}$ 状态空间      | 01:232      |
| `T` (TimeIdx)      | $\mathcal{T}$ 时间索引集    | 01:231      |
| `Tmax`             | $T_{\max}$ 观测窗口上界     | 01:231 推出 |
| `Traj`             | $\{x_t\}_{t\in\mathcal{T}}$ | 01:234      |
| `FateOf`           | $\text{命运}_O$             | 01:151      |

**规格 §2.1 规则 T3（裸 $T$ 禁令）的落实**：本实现**不出现**名为 `T` 的
「时间索引集」与「时间上界」的混用——时间索引集记为 `TimeIdx`，其上界记为
`Tmax`，二者类型不同，由类型系统强制区分。

## 命/运/状态转移层（规格 §1.2）

| Lean 标识符      | 规格符号                  | 出处   |
|------------------|---------------------------|--------|
| `Theta`          | $\Theta$ 参数空间         | 01:235 |
| `theta`          | $\theta$ 参数向量（**命**）| 01:236 |
| `U` (InputSpace) | $\mathcal{U}$ 外生输入空间 | 01:237 |
| `u`              | $u_t$ 外生输入            | 01:238 |
| `eps`            | $\varepsilon_t$ 随机扰动   | 01:239 |
| `DEps`           | $\mathcal{D}_\varepsilon$ | 01:240 |
| `f`              | $f$ 单步状态转移函数      | 01:241 |
| `A` (ActionSpace)| $\mathcal{A}$ 动作空间    | 01:244 |
| `a`              | $a_t$ 干预动作            | 01:242 |

**规格 §2.3 规则 N2（$\varepsilon$ 与 $\epsilon$ 分工）的落实**：
- `eps` = $\varepsilon_t$ = **随机扰动**（随机变量，运的组成部分）
- `epsBound` = $\epsilon_i$ = **误差界**（标量）
二者为**不同类型**，前者是随机变量、后者是 `ℝ`，由类型系统强制不可互换。

## 规则层（规格 §1.4）

| Lean 标识符   | 规格符号                  | 出处   |
|---------------|---------------------------|--------|
| `Rule`        | $R$ **单条**规则          | 03:14  |
| `Rules`       | $\mathcal{R}$ **规则集**  | S:11883|
| `Ctx`         | $\mathcal{C}$ 上下文空间  | 03:18  |
| `Xlocal`      | $\mathcal{X}_{\text{local}}$ 局部状态子空间 | 03:18 |
| `Y` (OutSpace)| $\mathcal{Y}$ 输出空间    | 03:17  |
| `E` (Inst)    | $\mathcal{E}$ 实例集      | S:11885|
| `alpha`       | $\alpha$ 抽象算子         | 03:279 |
| `gamma`       | $\gamma$ 泛化算子         | 03:460 |
| `comb`        | $\circ$ 组合算子          | 03:460 |
| `refine`      | $\upsilon$ 完善（更新）算子| 03:460 |

**规格 §2.2 规则 S1 的落实**：
- 裸 $E$ 归**图的边集**；**实例集**用花体 $\mathcal{E}$ → Lean 记作 `Inst`
  （**不**用 `E` 作实例集）。
- 裸 $G$ 归**因果图**；FCA 对象集 → `GFCA`（**不**用裸 `G`）。
- 裸 $B$ 禁用；FCA 概念第二分量 → `B ⊆ MFCA` 仅在 `(A,B)` 概念语境中使用。

## FCA 层（规格 §1.5）

| Lean 标识符  | 规格符号                        | 出处   |
|--------------|---------------------------------|--------|
| `GFCA`       | $G_{\mathrm{FCA}}$ FCA 对象集   | 03:97  |
| `MFCA`       | $M_{\mathrm{FCA}}$ FCA 属性集   | 03:97  |
| `Irel`       | $I$ FCA 对象–属性关系           | 03:97  |
| `FormalCtx`  | $\mathbb{K}=(G_{\mathrm{FCA}},M_{\mathrm{FCA}},I)$ | 03:94 |
| （导出算子） | $(\cdot)'$                      | 03:102 |

**导出算子的实现选择（重要，见下）**

规格 §1.5 用 $(\cdot)'$ 记**双向**导出算子对：
- $A'=\{m\in M_{\mathrm{FCA}}\mid\forall g\in A:(g,m)\in I\}$
- $B'=\{g\in G_{\mathrm{FCA}}\mid\forall m\in B:(g,m)\in I\}$

**Mathlib 的 `Mathlib.Order.Concept` 用两个具名函数记同一对算子**：
- `upperPolar r s = { b | ∀ a ∈ s, r a b }`  ← 即 $A'$
- `lowerPolar r t = { a | ∀ b ∈ t, r a b }`  ← 即 $B'$

**二者是同一对象的两种记法，不是两个概念。** 本实现**直接采用 Mathlib 的
`upperPolar`/`lowerPolar`**（依裁决 R-002：不重复造轮子），并在下文
`Fate.FCA` 中给出**记法对照引理**（把 $A'$ 与 `upperPolar` 显式绑定），
使规格的 $(\cdot)'$ 记法在 Lean 中**有唯一落点**，避免两套记法并存。

## 观测与预测层（规格 §1.6）

| Lean 标识符   | 规格符号              | 出处   |
|---------------|-----------------------|--------|
| `hObs`        | $h$ 观测模型          | 01:250 |
| `y`           | $y_t$ 观测量          | 01:251 |
| `eta`         | $\eta_t$ 观测噪声     | 01:548 |
| `phiPred`     | $\phi$ 预测算子       | 03:320 |
| `mu`          | $\mu$ SDE 漂移系数    | 02:29  |
| `sigma`       | $\sigma$ SDE 扩散系数 | 02:29  |

**规格 §2.4 规则 D1 的落实**：流映射 $\phi_t$ → `flow`；预测算子 $\phi$ → `phiPred`。
二者**不同名**，落实「带时间下标的 $\phi_t$ 是流映射；不带下标的 $\phi$ 是预测算子」。

**规格 §2.4 规则 D2 的落实**：`mu`/`sigma` **专指** SDE 漂移与扩散系数；
Lorenz 型参数**不在本文件出现**（若出现须加下标 `L`）。

---------------------------------------------------------------------------
证据边界
---------------------------------------------------------------------------
本文件为**形式化实现**，不是理论文本。凡规格中的 `[已知]`（外部既有结果）
在本实现中只**引用**，不主张为本框架成果。本实现**不虚构**文献、作者、年份与数字。
-/

import Mathlib.Order.Concept
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Basic

namespace Fate

universe u

/-! ===========================================================================
    §1  对象、状态与时间（规格 §1.1；对应理论第 1 章）
    =========================================================================== -/

/-- 系统（对象）$O$：具有可辨识状态并在时间中演化的实体。

规格 §1.1：**理论唯一原始对象**；不指人，指一切系统。
命/运/命运均附带于某个 $O$，因果**不**附带于任何 $O$（规格 §1.1 备注）。

标签：**[定义性约定]**（A1–A34 中无对应项；此为原始对象声明）。

实现说明：规格未给出 $O$ 的内部结构，只声明它是「理论唯一原始对象」。
故本实现将其作为**不透明类型参数**引入，不假定任何结构——
若日后需要 $O$ 的结构（如子系统分解），须先登记相应的假设。 -/
class Obj where
  /-- 该对象的状态取值空间（仅作占位关联，不施加结构） -/
  Carrier : Type u

/-- 状态空间 $\mathcal{X}$（规格 §1.1，01:232）。

**A28 的落实（阶段 0 验收标准 3）**：$\mathcal{X}$ 必须带结构约束。
本实现选**可测空间 + 拓扑**为其最低结构要求，理由：
理论第 4 章的转移核与第 2 章的 SDE 都以可测结构为前提。

标签：**[定义性约定]**（对应 A28；「四个空间的结构前提」）。 -/
structure StateSpace where
  /-- 状态取值类型 -/
  Carrier : Type u
  /-- 拓扑结构（A28 要求「拓扑／度量／流形至少其一」） -/
  [topo : TopologicalSpace Carrier]
  /-- 可测结构（供转移核与分布使用） -/
  [meas : MeasurableSpace Carrier]
  /-- Borel 相容性前件：可测结构**弱于**由拓扑生成的 Borel 结构。

  规格未直接规定此项，本实现**显式补出**并登记为补定项，理由：
  转移核的可测性论证需要「可测集 ≥ Borel 集」这一相容性；
  若不写出，它会在后续证明中成为**匿名前提**
  （违反阶段 1A 验收标准 2「不存在匿名前提」）。
  本实现只要求 `≤` 而不要求 `=`，以免过度约束。 -/
  borel_le : borel Carrier ≤ ‹MeasurableSpace Carrier›

/-- 时间索引集 $\mathcal{T}$（规格 §1.1、§2.1 规则 T1）。

**A29 的落实（阶段 0 验收标准 4）**：规格要求「离散分支与连续分支
**分别为两套定义**，二者关系另行登记」。故本实现**不**把 $\mathcal{T}$
做成单一类型，而是分别给出 `TimeIdx.Discrete` 与 `TimeIdx.Continuous`
两套定义（见 §1.1）。

标签：**[定义性约定]**（对应 A29）。 -/
inductive TimeKind where
  | discrete
  | continuous
  deriving DecidableEq, Repr

/-- 离散时间索引集：$\mathcal{T}=\mathbb{N}$（或 $\{0,1,\dots,T_{\max}\}$）。
规格 §1.1：离散形式取 $\mathcal{T}=\mathbb{N}$。 -/
abbrev TimeIdx.Discrete := ℕ

/-- 连续时间索引集：$\mathcal{T}=\mathbb{R}_{\ge 0}$。
规格 §1.1：连续形式取 $\mathcal{T}=\mathbb{R}_{\ge 0}$。

实现说明：用 `{t : ℝ // 0 ≤ t}` 而非 `ℝ`，以**在类型层强制** $\mathcal{T}=\mathbb{R}_{\ge0}$。 -/
abbrev TimeIdx.Continuous := { t : ℝ // 0 ≤ t }

/-- 观测窗口的时间上界 $T_{\max}$（规格 §1.1；出处 01:231 由 $\mathcal{T}$ 的基数未指明推出）。

规格 §2.1 规则 T2：**有限观测窗口的时间上界一律写作 $T_{\max}$，永不写作裸 $T$**。
本实现据此**不提供**名为 `T` 的上界记号。

标签：**[定义性约定]**。 -/
structure Tmax (kind : TimeKind) where
  /-- 离散情形：窗口上界是自然数；连续情形：是 $\mathbb{R}_{\ge0}$ 中的一元。
      规格未指明二者统一形式，故本实现**不做统一**，保持两套。 -/
  value : match kind with
    | .discrete   => ℕ
    | .continuous => TimeIdx.Continuous

/-! ### 轨迹与命运

规格 §1.1：$\{x_t\}_{t\in\mathcal{T}}$ 是**命运**的对象层所指；
$\text{命运}_O := \{x_t\}_{t\in\mathcal{T}}$，**不引入新数学结构**，是派生记号。 -/

/-- 状态轨迹 $\{x_t\}_{t\in\mathcal{T}}$：时间索引集到状态空间的映射。

规格 §1.1 明写 $\text{命运}_O$ **不引入新数学结构**、是**派生记号**，
故本实现把它实现为**函数类型**（`ι → X.Carrier`），
**不**新建 `structure Fate`——否则就是引入了规格明令不引入的结构。

标签：**[定义性约定]**。 -/
abbrev Traj (ι : Type u) (X : StateSpace) := ι → X.Carrier

/-- $\text{命运}_O$ 的**类型别名**（规格 §1.1：派生记号，非新结构）。

规格 §1.2 亦记 $\text{命}_O := \theta$（**不含 $x_0$**，01:295、01:458）。
故「命」与「命运」是**两个不同对象**，本实现分设，不得合并。 -/
abbrev FateOf (ι : Type u) (X : StateSpace) := Traj ι X

/-- 初始状态 $x_0$（规格 §1.1，01:450–454）。

规格明写：**$x_0$ 不属于「命」**；与 $\theta$ 并列为「给定条件」。
若随机，写作 $x_0 \sim \mathcal{D}_0$。

故本实现**把 $x_0$ 与 $\theta$ 分设**，不合并进「命」。
A14（$x_t$ 可直接获取 vs. 观测可逆）在类型层分叉，
见 §1.4 的 `ObservationRegime`——**此处不预设**，由 `Fate.Basic` 的共同部分承接。

标签：**[定义性约定]**。 -/
structure InitialState (X : StateSpace) where
  /-- 初始状态取值 -/
  val : X.Carrier
  /-- 是否按分布 $\mathcal{D}_0$ 随机给定 -/
  isRandom : Bool

/-! ===========================================================================
    §1.2  命与运：参数、外生输入与扰动（规格 §1.2；对应理论第 2 章）
    =========================================================================== -/

/-- 参数空间 $\Theta$（规格 §1.2，01:235）。

**A28 的落实**：$\Theta$ 带结构约束。本实现要求**拓扑 + 可测**，
理由同 $\mathcal{X}$（参数进入转移核）。

标签：**[定义性约定]**（对应 A28）。 -/
structure ThetaSpace where
  Carrier : Type u
  [topo : TopologicalSpace Carrier]
  [meas : MeasurableSpace Carrier]

/-! ### §1.2.1 命 $\theta$ 的性质（**依作者裁决 Q-1 修订**）

**作者裁决 Q-1**（`作者裁决-Q1到Q6.md`）原文：

> θ **不是被给定的参数，而是从实例数据中提取出来的规律**。

**该裁决废除**了实现代理此前登记的两个选项：
- ~~(a) 时不变（$\dot\theta=0$）~~
- ~~(b) 带阈值 $\epsilon=\tau_{\text{fast}}/\tau_{\text{slow}}$~~

**故本实现必须区分两件事**：

| 层 | 含义 | 本实现 |
|---|---|---|
| **载体层** | $\Theta$ 作为一个**空间**（其元素可被取值） | `ThetaSpace`（**保留**——主公式仍需 $\theta$ 作取值） |
| **认识论层** | $\theta$ **如何被得到**——**从实例提取**，非先验给定 | 见 `Fate.Frame` 的 `ThetaIsExtracted` |

**为什么两层都要保留**：主公式 $x_{t+1}=f(x_t,u_t,\varepsilon_t;\theta,a_t)$
确实把 $\theta$ 当**取值**用；而 Q-1 说的是该取值的**来源**。
二者不冲突——**「从实例提取出的一个取值」仍然是一个取值**。

**「慢」的含义随之改变**（Q-1 第 4 条）：
不再是「变化率小」的**动力学判据**，而是
**「在提取所覆盖的样本上稳定」**——**稳定性而非时间尺度**。

**实现位置说明**：Q-1 的完整形式化（`ThetaIsExtracted`、`ThetaStableOn`）
放在 `Fate.Frame`——因为提取映射的定义域是**实例集** $\mathcal{E}$，
而 `InstSpace` 定义在 `Fate.Frame`（模块依赖方向：
`Basic` ← `Frame`，故 `Basic` 不能引用 `InstSpace`）。 -/

/-- 外生输入空间 $\mathcal{U}$（规格 §1.2，01:237）。

规格 §1.2 备注：**仅此一义**；SCM 的外生变量集**不用此符号**
（SCM 侧改用 $U$，见规格 §1.3 与该节规则）。本实现遵守：
本文件中的 `InputSpace` **只**指 $\mathcal{U}$。

标签：**[定义性约定]**（对应 A28）。 -/
structure InputSpace where
  Carrier : Type u
  [topo : TopologicalSpace Carrier]
  [meas : MeasurableSpace Carrier]

/-- 动作空间 $\mathcal{A}$（规格 §1.2，01:244、01:546）。

**本条是阶段 0 验收标准 3 的硬性要求。**
规格《公理与章序规范》A28 原文：

> 「$\mathcal{A}$ 在原文中**从未定义**，是主公式中唯一无空间声明的自变量。」

规格 §1.2 亦记 $\mathcal{A}$ 为「原文未定义，此处补定」。
故本实现**必须**给出 $\mathcal{A}$，并给出其结构约束。

**结构选型的理由（[推断]，非规格原文）**：$\mathcal{A}$ 上的结构应
恰好支撑第 7 章「干预优化」$a_t^\star=\arg\min_{a_t}\mathbb{E}[L(x_{t+1}(a_t))]$
所需的**极小值存在性**。故本实现给出 `TopologicalSpace`（供紧性与连续性），
并记录**未**假定紧性——紧性是干预优化定理的**前件**，须显式登记，
不得偷偷塞进定义（否则该假设会静默滑入后续证明）。

标签：**[定义性约定]**（对应 A28）。 -/
structure ActionSpace where
  Carrier : Type u
  [topo : TopologicalSpace Carrier]
  [meas : MeasurableSpace Carrier]

/-- 随机扰动 $\varepsilon_t$ 的取值类型 $\mathcal{E}_\varepsilon$。

规格 §1.2：$\varepsilon_t$ 的取值空间**未在符号表中单列**，
只给了 $\varepsilon_t$ 本身与分布 $\mathcal{D}_\varepsilon$（01:239–240）。
故本实现**显式补出**该取值空间，并登记为补定项。

标签：**[定义性约定]**。 -/
structure NoiseSpace where
  Carrier : Type u
  [meas : MeasurableSpace Carrier]

/-- 随机扰动的分布 $\mathcal{D}_\varepsilon$（规格 §1.2，01:240）。

规格只声明 $\varepsilon_t\sim\mathcal{D}_\varepsilon$，未声明该分布的类。
本实现用 `Measure`，**不**假定它是概率测度——「是概率测度」须作为
显式前件出现（否则 $\mathcal{D}_\varepsilon$ 的概率语义无处安放）。

标签：**[定义性约定]**。 -/
abbrev Dist (N : NoiseSpace) [MeasurableSpace N.Carrier] : Type _ :=
  MeasureTheory.Measure N.Carrier

/-- 以 `N` 自带的 `MeasurableSpace` 为实例给出 $\mathcal{D}_\varepsilon$。 -/
abbrev Dist' (N : NoiseSpace) : Type _ :=
  letI := N.meas
  MeasureTheory.Measure N.Carrier

end Fate
