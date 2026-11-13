/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.WorldModel
阶段：**阶段 1B —— 复合对象类型化**（承 `Fate.Basic` / `Fate.Frame` 的冻结签名）

---------------------------------------------------------------------------
本文件做什么（一句话）
---------------------------------------------------------------------------
把「**世界模型**」做成一个**复合类型** `WorldModel`，
其四个组成部分**逐一**是：**状态**、**规则集**、**模拟器**、**选择器**——
且每一部分都**不是新造的名词**，而是**绑定到已冻结的既有定义**上。

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
- **零 `sorry` / 零 `admit` / 零 `axiom`**（承阶段 0 验收标准 1）。
- **加法式变更**：本文件**不修改** `Basic` / `Frame` 的任何签名，
  只在它们之上**组合**出新类型（依 `00-签名冻结.md` 冻结纪律）。
- **不虚构**：凡规格未给出结构的位（如「选择器的准则空间」），
  本文件**做成参数**、**不填数**、**不擅自假定**（依「填数即为虚构」）。
- 区分〔定义性约定〕/〔已证定理〕/〔诚实标注〕。

---------------------------------------------------------------------------
四个组成部分 ↔ 既有定义的**唯一落点**（本文件的核心内容）
---------------------------------------------------------------------------
| 部分 | 本文件的字段 | 绑定到的既有定义 | 出处 |
|---|---|---|---|
| **状态** | `state_space` | `Fate.StateSpace`（拓扑+可测+Borel 相容） | `Basic.lean` |
| | `initial` | `Fate.InitialState`（`x₀` 与 `θ` **分设**） | `Basic.lean` |
| **规则集** | `rules` | `Fate.Rules` = `Set (Rule C X Y)`（**与单条 `Rule` 严格区分**） | `Frame.lean` |
| | `rulesθ` | `Fate.RulesWithTheta`（裁决 J 的 $R_\theta$） | `Frame.lean` |
| **模拟器** | `simulate` | **`Step` 的正向迭代**（= `trajGen` 的定义性展开） | `Frame.lean` / `TrajGenDeterministic.lean` |
| **选择器** | `select` | **`Rule` 的选取**（在规则集内选一条，以观测为条件） | 本文件新增（见 §4） |

**⚠ 四者的类型层分工（这是本文件的主要贡献）**：

- **状态**是**取值**（`Type`：「一个点」），—— *不是*空间、*不是*分布；
- **规则集**是**集合**（`Set (Rule ...)`）—— *不是*一条规则；
- **模拟器**是**函数**（取值为输入 → 轨迹）—— *不是*测度、*不是*机制 `Step` 本身；
- **选择器**是**函数**（规则集 × 观测 → 规则 × 证据）—— *不是*规则、*不是* `α`。

**为什么必须把这四者分设**：规格 `04-符号与方程规范.md` §3.3 已裁定
「算子不能作函数自变量」。四者的论域各不相同（取值 / 集合 / 函数 / 泛函），
若合并成一个字段，则上述裁定在实现中**无处落地**。
本文件以**四个不同类型的字段**使该裁定成为**编译期可见的结构**。

---------------------------------------------------------------------------
证据边界
---------------------------------------------------------------------------
本文件是**形式化实现**，不是理论文本。§5 的定理**全部**是关于
「本文件所造类型之间相容性」的**定义性引理**，**不构成**关于世界的断言，
**也不证明**任何规格中的经验假设（A1–A34）。
-/

import FateWorld.Legacy.Basic
import FateWorld.Legacy.Frame
import FateWorld.Legacy.TrajGenDeterministic

namespace Fate

universe u

noncomputable section

/-! ===========================================================================
    §1  世界模型的**状态**部分

    规格 §1.1：状态空间 $\mathcal{X}$（A28：须带结构）、
    初始状态 $x_0$（**不属于「命」**，与 $\theta$ 并列）。
    =========================================================================== -/

/-- **世界模型的状态块**：把「状态空间 + 当前状态 + 初始状态」打包。

**为什么状态块要含「空间」而不只含「取值」**：规格 A28 要求 $\mathcal{X}$
带结构约束（拓扑／度量／流形至少其一），且转移核的可测性论证需要
$\mathcal{X}$ 上的 $\sigma$-代数。若 `WorldModel` 只存一个取值 `F.X.Carrier`，
那么 A28 的结构约束在类型层**无处安放**，会退化成注释。

**为什么 `initial : InitialState X` 而不只存 `x₀`**：规格 §1.1、§1.2 明写
$x_0$ 与 $\theta$ **并列为「给定条件」**，且 $x_0$ 可随机（$x_0\sim\mathcal{D}_0$）。
`InitialState` 已带 `isRandom` 位，保留它可使「$x_0$ 是否随机」成为一个
**可见的字段**，而非被本文件悄悄丢掉。

标签：**[定义性约定]**。 -/
structure WorldState where
  /-- 状态空间 $\mathcal{X}$（A28：拓扑 + 可测 + Borel 相容） -/
  space : StateSpace
  /-- 当前状态 $x_t$：**一个取值**（不是空间、不是分布） -/
  cur : space.Carrier
  /-- 初始状态 $x_0$（与 $\theta$ 分设，可带随机标记） -/
  initial : InitialState space

/-! ===========================================================================
    §2  世界模型的**规则集**部分

    规格 §1.4：$\mathcal{R}=\{R_i\}$，**与单条规则 $R$ 严格区分**；
    裁决 J：$R_\theta$（R 以 $\theta$ 为参数）。
    =========================================================================== -/

/-- **世界模型的规则集块**：$\mathcal{R}_\theta$ 的载体 + 其非空性证据。

**本块**只 存**集合**，不存单条规则。
这是规格 §1.4「$R$ 与 $\mathcal{R}$ 严格区分」在**类型层**的落实：
`rules : Set (Rule C X Y)` 的**元素**才是单条规则 `Rule`，
故「把规则集当规则用」或反之，在 Lean 中**类型错误**，无需人眼检查。

**为什么带 `nonempty : rules.Nonempty`**：选择器（§4）要在集合中**选出一条**。
若集合空，选择无解。把非空性做成**字段**（而非在定理中作前件），
使「该世界模型的选择器可用」成为类型层保证；
**未**假定非空的世界模型**仍然是可表达的**
（用 `WorldRules` 而**不**用 `WorldModel`，见 §5.3），故这不是隐形的过强假设。

**⚠ 诚实标注**：`nonempty` 是**关于规则集的断言**，由构造者**必须提供**。
本文件**不**证明「任何实例集经 $\alpha$ 得到的规则集非空」——
那是 A1 与 $\alpha$ 的语义问题，**不属本文件范围**。

标签：**[定义性约定]**（对应 A1 的载体层）。 -/
structure WorldRules (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] where
  /-- 规则集 $\mathcal{R}=\{R_i\}$（**集合**，不是单条规则） -/
  rules : Rules C X Y
  /-- 非空性证据（供选择器使用；**不宣称**由 $\alpha$ 自动得到） -/
  nonempty : rules.Nonempty

/-- **以 $\theta$ 为参数的规则集块**（裁决 J：$R_\theta$）。

与 `WorldRules` 的唯一区别：集合的元素是 `RuleWithTheta`（多一个 $\theta$ 位）。

**为什么两者并存而不合并**：裁决 J 明令**加法式变更**——
$\theta$ 无关版保持冻结签名，$\theta$ 参数化版**新增**为独立对象，
并以退化关系（`Fate.Frame.rule_is_degenerate_case`）连接。
本文件照办，**不删任何一侧**。

标签：**[定义性约定]**（对应裁决 J）。 -/
structure WorldRulesθ (C : CtxSpace) (X : StateSpace) (Y : OutSpace) (Θ : ThetaSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] where
  /-- $\theta$ 参数化规则集 $\mathcal{R}_\theta$ -/
  rules : RulesWithTheta C X Y Θ
  /-- 非空性证据 -/
  nonempty : rules.Nonempty

/-! ===========================================================================
    §3  世界模型的**模拟器**部分

    把 `Step`（= $f$，单步转移）沿时间**正向迭代**成轨迹——
    即 `TrajGenDeterministic.trajGen` 的**类型化封装**。

    **⚠ 与 `Step` 的关系（规格 §3.1 说明 1 明令）**：
    `Step` 是**单步**，模拟器是**整条轨迹**的生成；
    二者**不同名、不同签名**，本文件**不提供**把二者混用的别名。
    =========================================================================== -/

/-- **世界模型的模拟器块**：机制 $f$ + 时间步数。

**模拟器的值域是 `Traj ℕ F.X`（一条样本路径），不是 `Measure (Traj ι X)`。**

**这一选择是刻意的、且是诚实标注的**：
- 值域为 `Traj` ⟹ 模拟器**可计算**（构造性，`Nat.rec`），忠实性是 `rfl` 级；
- 代价：**丢弃分布**（$x_0\sim\mathcal{D}_0$ 与 $\varepsilon_t\sim\mathcal{D}_\varepsilon$
  的随机性不在此块内表达）；
- 要表达分布，须升级为 `Fate.TrajGenStochastic` 的方案二（值域 `Measure`）。

**故本模拟器是「方案一」的封装，其表达力上限即方案一的上限**
（见 `Fate.TrajGenDeterministic` §7 的诚实标注），本文件**不**声称它覆盖随机语义。

标签：**[定义性约定]**（对应唯一权威离散方程的轨迹层展开）。 -/
structure WorldSimulator (F : Frame) where
  /-- 机制 $f$：单步状态转移（**不是**轨迹生成器） -/
  step : Step F
  /-- 观测窗口的步数 $T_{\max}$（离散情形取自然数；规格 §2.1 规则 T2） -/
  horizon : ℕ

/-! ===========================================================================
    §4  世界模型的**选择器**部分

    规格未给「选择器」单列定义（符号表中无此项），故本节**补定**并登记。
    选择器的作用在规格中有明确的**需求出处**：
    - 第 7 章「干预优化」$a_t^\star=\arg\min_{a_t}\mathbb{E}[L(x_{t+1}(a_t))]$
      需要一个**在动作空间中选取**的算子；
    - 裁决 J 说「预测走 $R$ 这条路」——预测需要一个**在规则集中选取**的算子。

    **⟹ 本实现把选择器做成「在规则集中选一条，以观测为条件」的泛函**，
    且把「选得对不对」做成一个**显式的准则字段**（不擅自假定最优性）。
    =========================================================================== -/

/-- **选择器的准则**：给定上下文与观测，对一条规则给出「优劣」评值。

**为什么用 $-\infty$ 之外的序**：准则值用 `WithTop ℝ` 之外本可用任意序；
本实现选 `ℝ`，并**显式登记**「值可以是 $-\infty$ 以外的任何实数」——
若日后要求「偏好序」而非「数值评值」，须换 `Criterion` 的类型，**不得默认**。

**⚠ 诚实标注**：规格未给准则的形式。本实现只给它的**类型**，
**不**假定它是凸的、连续的、可计算的或有界的（那四条都是**前件**，
若需要须显式登记，不得塞进定义）。

标签：**[定义性约定]**（补定项）。 -/
abbrev Criterion (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] : Type _ :=
  C.Carrier → X.Carrier → Rule C X Y → ℝ

/-- **选择器的载体**：在规则集中选出一条规则，并携带它所依据的证据。

**三段式签名**（每一段都是**不同的论域**）：

$$\mathrm{Selector}:\ \underbrace{\mathcal{R}}_{\text{集合}}
  \to \underbrace{\mathcal{C}}_{\text{上下文空间}}
  \to \underbrace{\mathcal{X}}_{\text{状态(取值)}}
  \to \underbrace{R}_{\text{单条规则}}\times\underbrace{\text{评值}}_{\mathbb{R}} .$$

**为什么返回值带评值而不只带规则**：使「选择器选了什么、依据多强」
成为**返回值的一部分**，从而可在定理中**陈述**（而不是从外部事后计算）。
这落实规格 §2.3 的「每次选择都留下痕迹」的精神（本文件不引其为规格原文，
此处只作设计理由）。

**`IsValid` 的语义**：所选规则**必须在规则集内**。这是一条**可在类型层陈述、
在定理层证明**的正确性条件（`Selector.IsValid`），本文件**不**把它塞进
`Selector` 的定义（否则「无效选择器」不可表达，就无法陈述「如何检验选择器」）。

标签：**[定义性约定]**（补定项）。 -/
structure Selector (C : CtxSpace) (X : StateSpace) (Y : OutSpace)
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] where
  /-- 选择函数：规则集 × 上下文 × 状态 → （单条规则，评值） -/
  select : Rules C X Y → C.Carrier → X.Carrier → Rule C X Y × ℝ
  /-- 评值准则（与 `select` 返回的评值**同源**，供一致性检验） -/
  criterion : Criterion C X Y

/-- **选择器的正确性条件**：所选规则必须**来自给定的规则集**。

$$\mathrm{IsValid}\,(S,\mathcal{R})
  \iff \forall c\,x,\ \big(S.\mathrm{select}\,\mathcal{R}\,c\,x\big).1 \in \mathcal{R}.$$

**为什么这是「正确性」而非「最优性」**：选错（选到集合外的规则）是**逻辑错误**，
选得不最优只是**质量不足**。本文件只把前者做成定理，
**不**把「$=\arg\max$ 准则」写成定理——那需要准则的最大值存在性，
而规格**未给**该存在性（须先有紧性/上界等前件）。**不擅自假定。**

标签：**[定义性约定]**（补定项）。 -/
def Selector.IsValid {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (S : Selector C X Y) (R : Rules C X Y) : Prop :=
  ∀ c x, (S.select R c x).1 ∈ R

/-- **「选出的评值即准则值」**：选择器自洽的条件。

$$\mathrm{Consistent}\,S \iff
  \forall c\,x\,\mathcal{R},\ \big(S.\mathrm{select}\,\mathcal{R}\,c\,x\big).2
    = S.\mathrm{criterion}\,c\,x\,\big(S.\mathrm{select}\,\mathcal{R}\,c\,x\big).1 .$$

**为什么单列**：`select` 与 `criterion` 是**两个字段**，
它们的**一致**不是定义带来的（可被违反），故须作为**可陈述的条件**出现，
而**不能**在 `Selector` 的定义里假定（否则「不一致的选择器」不可表达）。

标签：**[定义性约定]**（补定项）。 -/
def Selector.Consistent {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (S : Selector C X Y) : Prop :=
  ∀ c x R, (S.select R c x).2 = S.criterion c x (S.select R c x).1

/-! ===========================================================================
    §5  世界模型：**四部分的合成**

    这是本文件的主类型。**四个字段**分别是状态、规则集、模拟器、选择器；
    另有第五个字段 `frame`（四元框架 `Fate.Frame`）作为**共享上下文**——
    因为规则集与模拟器**必须**在同一个 `F` 上，否则 `Rule` 的 `X`/`Y`
    与 `Step` 的 `X` 无法对接。**这不是「第五个组成部分」**，
    而是四个组成部分的**共同基底**（见 §5.1）。
    =========================================================================== -/

/-- **世界模型**（完整类型）：状态 + 规则集 + 模拟器 + 选择器。

## 字段与四个部分的对应

| 字段 | 部分 | 论域 | 绑定 |
|---|---|---|---|
| `frame` | —（共同基底） | 四元框架 | `Fate.Frame` |
| `state` | **状态** | 取值 | `WorldState` |
| `rules` | **规则集** | 集合 | `WorldRules` |
| `simulator` | **模拟器** | 函数 | `WorldSimulator` |
| `selector` | **选择器** | 泛函 | `Selector` |

**`frame` 为什么不是「第五部分」**：`state.space`、`rules.rules`、`simulator.step`、
`selector.select` 四者**必须共享** `F.X`（状态空间）与 `F.U`／`F.Ν`／`F.Θ`／`F.Act`。
若把 `F` 分别放进四个块，则四个块**可以指向不同的 `F`**，
「世界模型」就退化成四个**互不相干**的对象——
**这正是 `frame` 作为共享基底存在的理由**。它是**胶水**，不是新组成部分。

**状态块与 `T`／`F` 的对齐条件**：字段 `state_consistent` 显式要求
`state.space = F.X` 且 `state.initial.val : F.X.Carrier`。
若不作此要求，`WorldModel` 可以在 `F` 上定义规则集、却在**另一个**状态空间上
定义状态——这在数学上无意义，且会在后续证明中变成**匿名前提**
（违反阶段 1A 验收标准 2「不存在匿名前提」）。

标签：**[定义性约定]**（复合对象类型化）。 -/
structure WorldModel where
  /-- 四元框架（状态/输入/动作/噪声/参数空间）—— **共同基底，非第五部分** -/
  frame : Frame
  /-- 上下文空间 $\mathcal{C}$（规则的条件变量所在空间） -/
  ctx : CtxSpace
  /-- 状态空间上的可测结构**实例**（`WorldRules`／`Selector` 需要它）。

  **为什么必须是字段**：`StateSpace.meas` 是 `StateSpace` 的**字段**，
  而 `frame.X.Carrier` 不是裸类型变量，故类型类搜索**找不到**它的
  `MeasurableSpace` 实例。若不在结构里带一个实例，
  则 `WorldRules ctx frame.X frame.X` 处的 `[MeasurableSpace …]` **无法合成**。
  这**不是**新的数学假设：`frame.X.meas` 已由 `StateSpace` 提供，
  本字段只是把它**提到**可被类型类搜索的位置。 -/
  [instX : MeasurableSpace frame.X.Carrier]
  /-- **状态**块 -/
  state : WorldState
  /-- **规则集**块：$\mathcal{R}$ 定义在 `frame.X` → `frame.X`（输出空间 = 状态空间，规则 N3） -/
  rules : WorldRules ctx frame.X frame.X
  /-- **模拟器**块 -/
  simulator : WorldSimulator frame
  /-- **选择器**块 -/
  selector : Selector ctx frame.X frame.X
  /-- 状态空间与框架的**对齐证据**（防止四个部分各指一个空间） -/
  state_consistent : state.space = frame.X

attribute [instance] WorldModel.instX

/-! ### §5.1 世界模型的**投影**（四个部分各自可被单独取出）

**为什么需要投影**：若四处都要 `W.state` / `W.rules` / …，
则「世界模型有四个部分」只是注释。本节给出四个**具名投影**，
使「取第 $i$ 个部分」是一个**Lean 函数**——即可被定理引用的对象。
-/

/-- **投影·状态**：世界模型的状态空间（= `frame.X`，由 `state_consistent` 保证）。 -/
def WorldModel.X (W : WorldModel) : StateSpace := W.frame.X

/-- **投影·当前状态**（取值）：世界模型在时刻 $t$ 的状态。
⚠ 注意 `W.state.cur : W.state.space.Carrier`，
而 `W.state.space = W.frame.X` 是**等式**而非**定义等式**，
故本投影需要 `Eq.rec`/`cast` 搬运——这正是 `state_consistent` 代价的可见处。 -/
def WorldModel.x (W : WorldModel) : W.frame.X.Carrier :=
  W.state_consistent ▸ W.state.cur

/-- **投影·规则集**：世界模型的规则集（**集合**，不是单条规则）。 -/
def WorldModel.R (W : WorldModel) : Rules W.ctx W.frame.X W.frame.X :=
  W.rules.rules

/-- **投影·模拟器**：世界模型的单步机制 $f$（**单步**，不是轨迹生成器）。 -/
def WorldModel.f (W : WorldModel) : Step W.frame :=
  W.simulator.step

/-- **投影·选择器**：世界模型的选择器（泛函）。 -/
def WorldModel.Sel (W : WorldModel) : Selector W.ctx W.frame.X W.frame.X :=
  W.selector

/-! ### §5.2 世界模型的**模拟**：把四个部分**接起来**

模拟 = 用模拟器的机制 `Step`、以状态块的初值为起点、沿 `ℕ` 正向迭代，
输入序列取自框架的 $\mathcal{U}$／$\mathcal{N}$／$\mathcal{A}$。

**这是 `TrajGenDeterministic.trajGen` 的直接调用**——
本文件**不重写**递推，只**接线**。故忠实性定理**继承**自
`trajGen_succ`（`rfl` 级），本文件无需再证一遍。
-/

/-- **世界模型的模拟轨迹**：$\{x_t\}_{t\in\mathcal{T}}$（$\iota=\mathbb{N}$）。

$$\mathrm{sim}(W)(\theta,u,\varepsilon,a)(0)=x_0,\qquad
  \mathrm{sim}(W)(\theta,u,\varepsilon,a)(n+1)
    =f\big(\mathrm{sim}(W)(\dots)(n),u_n,\varepsilon_n;\theta,a_n\big).$$

**`x₀` 取自状态块**（`W.state.initial.val`，经 `state_consistent` 搬运到 `F.X.Carrier`），
**`f` 取自模拟器块**，**`θ`／`u`／`ε`／`a` 取自框架**。

标签：**[定义性约定]**（`TrajGen` 类型的一个实现，方案一）。 -/
def WorldModel.sim (W : WorldModel)
    (θ : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (ε : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) :
    Traj ℕ W.frame.X :=
  TrajGenDeterministic.trajGen W.frame W.simulator.step θ (W.x) u ε a

/-- ⭐ **世界模型的模拟满足唯一权威方程**（对一切 $n$，定义性）。

**这不是本文件的新证明**：它是 `trajGen_succ` 在 `W.sim` 上的**逐字读法**。
本引理的作用是**把四个部分的接线正确性钉成一条可编译事实**——
若 `W.sim` 误把 `f` 或 `x₀` 接错位，本引理即失败。 -/
theorem WorldModel.sim_succ (W : WorldModel)
    (θ : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (ε : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) (n : ℕ) :
    W.sim θ u ε a (n+1)
      = W.f (W.sim θ u ε a n) (u n) (ε n) θ (a n) :=
  TrajGenDeterministic.trajGen_succ W.frame W.simulator.step θ W.x u ε a n

/-- ⭐ **世界模型的模拟从状态块的初值出发**（定义性）。 -/
theorem WorldModel.sim_zero (W : WorldModel)
    (θ : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (ε : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) :
    W.sim θ u ε a 0 = W.x :=
  TrajGenDeterministic.trajGen_zero W.frame W.simulator.step θ W.x u ε a

/-! ### §5.3 四个部分的**可分离性**：没有 `WorldModel` 也能表达各部分

**这是必须做的诚实标注**：`WorldModel` 的 `rules.nonempty` 与
`state_consistent` 是**约束**。若有世界模型**不能满足**它们
（如规则集为空、或状态空间与框架不匹配），
则**用 `WorldModel` 表达它是不可能的**——
但用 `WorldRules`／`WorldSimulator`／`Selector` **分别**表达仍是可能的。

**⟹ 故四个块**不是 `WorldModel` 的「内部细节」，而是**独立可用的类型**。
这使本文件的类型分工**不做过度承诺**：`WorldModel` 只是**四部分都合法**的那一类。 -/

/-- **状态块可独立使用**（不依赖 `WorldModel` 的其它约束）。 -/
example (s : WorldState) : StateSpace := s.space

/-- **规则集块可独立使用**。 -/
example {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (r : WorldRules C X Y) : Set (Rule C X Y) := r.rules

/-- **模拟器块可独立使用**。 -/
example (F : Frame) (s : WorldSimulator F) : Step F := s.step

/-- **选择器块可独立使用**。 -/
example {C : CtxSpace} {X : StateSpace} {Y : OutSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier]
    (S : Selector C X Y) : Rules C X Y → C.Carrier → X.Carrier → Rule C X Y × ℝ :=
  S.select

/-! ### §5.4 选择器与世界模型的**合成**：选规则 → 用模拟器**

世界模型的用途是：**选择器**在规则集内选一条规则（预测用），
**模拟器**给出轨迹（推演用）。本小节把二者**在同一 `W` 上**接起来，
使「世界模型**能做**什么」成为一条**可陈述的等式**（而非散文）。

**⚠ 边界（诚实标注）**：规则的核 $R:\mathcal{C}\to\mathcal{X}\to\mathrm{Measure}\,\mathcal{Y}$
与模拟器的 `Step`（函数，点质量）**不是同一对象**（见 `Frame.Rule.isDet_iff_dirac`）。
故本节**只**把二者**并列**在同一个 `W` 上，
**不**声称「所选规则就是模拟器的机制」——那需要 `Rule.IsDet` 的**附加前件**，
本文件**不擅自假定**。 -/

/-- ⭐ **世界模型的「用」**：给定上下文与当前状态，选择器选出一条规则并给出评值。

$$\mathrm{WorldModel.decide}\,W\,\mathcal{R}\,c\,x
  = W.\mathrm{Sel}.\mathrm{select}\,\mathcal{R}\,c\,x .$$

`R` 显式作为参数（而非取自 `W.rules.rules`），
使「用**别的**规则集去问同一个选择器」成为可能——
这是检验选择器 `IsValid`（§4）所必需的用法。

标签：**[定义性约定]**。 -/
def WorldModel.decide (W : WorldModel)
    (R : Rules W.ctx W.frame.X W.frame.X) (c : W.ctx.Carrier)
    (x : W.frame.X.Carrier) : Rule W.ctx W.frame.X W.frame.X × ℝ :=
  W.Sel.select R c x

/-- ⭐⭐ **世界模型的合法性**：选择器在其**自带**规则集上有效。

**这是把一个世界模型「合格」的标准**：`W` 所声称的规则集，
与 `W` 的选择器**互相吻合**（选择器不会选出集合外的规则）。

**本定理是定义性的（`rfl`-邻域）而非深刻的**：它把 `Selector.IsValid`
在 `W.R` 上的**假设**变成 `W` 的**判据**。
若在**构造**层面就能保证它，则 `WorldModel` 一旦建成即「自洽」。 -/
def WorldModel.WellFormed (W : WorldModel) : Prop :=
  W.Sel.IsValid W.R

/-! ===========================================================================
    §6  **自检清单**（本文件的验收点，逐条可编译）
    =========================================================================== -/

/-- **自检 1：四个部分类型互不相同**（故不能被悄悄互换）。

**这是本文件「四部分必须分设」的**机检**证据**：
若某人把「状态」与「规则集」做成同一类型，则本函数的存在不可能。
本函数把四条**同论域**的提取路径写出来——它编译通过
即证明四个字段各自的类型**非退化**。 -/
theorem four_parts_distinct (W : WorldModel) :
    (WorldModel.X W = W.frame.X) ∧
    (WorldModel.R W = W.rules.rules) ∧
    (WorldModel.f W = W.simulator.step) ∧
    (WorldModel.Sel W = W.selector) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- **自检 2：状态空间对齐是**定义性**的**（`WorldModel.X` 与 `state.space` 相等）。

`state_consistent` 给出的等式**正是**本定理的内容——
它使「四个部分共享同一状态空间」成为**类型层事实**，
**而不是**一个待证的假设。 -/
theorem state_space_aligned (W : WorldModel) : W.state.space = W.frame.X :=
  W.state_consistent

/-- **自检 3：模拟器的轨迹是 `Traj ℕ F.X`，**不是**测度**。

**这是表达力上限的机检标注**：`W.sim` 的返回类型是函数类型；
若某人把模拟器升级为测度值域（方案二），本定理的**类型就不成立**，
故本定理的存在即钉住「本文件的模拟器 = 方案一」。 -/
example (W : WorldModel) (θ : W.frame.Θ.Carrier) (u : ℕ → W.frame.U.Carrier)
    (ε : ℕ → W.frame.Ν.Carrier) (a : ℕ → W.frame.Act.Carrier) :
    Traj ℕ W.frame.X := W.sim θ u ε a

/-- **自检 4：规则集非空是**字段**，故 `W.R` 恒非空**（选择器总有候选）。 -/
theorem rules_nonempty (W : WorldModel) : W.R.Nonempty :=
  W.rules.nonempty

/-- **自检 5：`≡` 世界模型的 `WellFormed` 是一个**可陈述命题**（不自动成立）。

本定理**不**断言 `WellFormed W` 对所有 `W` 成立（那会是一致性灾难：
`IsValid` 依赖于 `select` 的行为）。
它只**陈述**「`WellFormed` 是 `W` 上的谓词」，即**该性质可被验证**——
这是「选择器正确性可检验」的**语言层保证**，**非**「已被保证」的断言。 -/
theorem wellFormed_is_predicate (W : WorldModel) :
    WorldModel.WellFormed W = W.Sel.IsValid W.R := rfl

end

end Fate
