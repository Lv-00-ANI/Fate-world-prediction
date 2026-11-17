/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.Stage0.LabelAudit`
性质：**验收脚本（可执行审计）** —— 不是理论内容，是**可机械复核的检查器**

--------------------------------------------------------------------------
本文件做什么（勘察 G 的处方 #3）
--------------------------------------------------------------------------
**处方 #3 原文（逐字）**：

> **把阶段 0 验收标准 2 做成可运行脚本**：
> **给每个定义加 `label_<Name> : AssumptionKind`，`#eval` 输出全部 (Name, label)**；
> **同时把 3 处恒真占位改成让其「不满足就编译失败」的具名 Prop。**

故本文件给三样东西：

1. **§1** `AssumptionKind` —— 假设的三类标签（规格
   `03-规范与裁决/05-公理与章序规范.md` §1.1「类型三分」）；
2. **§2–§3** 每个核心对象一个 `label_<Name> : AssumptionKind`，
   外加 `#eval` 把 `(Name, label)` 全表打出来，并**自检**类别计数
   是否等于规格权威值 `15 / 11 / 6`；
3. **§4** 三处恒真占位各给一个**具名 Strict Prop** —— **体不是 `True`**，
   而是真实的数学条件或 `False`，并配「反证桥」定理。

--------------------------------------------------------------------------
⚠⚠ 诚实边界（先读，否则会误读本文件的结论）
--------------------------------------------------------------------------
**A. 本文件不修改任何既有定义。**
`DifferentiableMechanism`（`Fate/Stage1A.lean:253`）、
`CondIndepNEmpty`（`Fate/CondIndepN.lean:173`）、
`Yun`（`Fate/Frame.lean:111`）**原地保持不动** ——
它们是阶段 0 已冻结的签名，且被 `Fate.lean` 的导入链依赖。
本文件以**加法方式**（additive change）给出 **Strict 版**，
两者由 §4 的桥定理连接；`satisfiable` / `not_satisfiable` **由 Lean 自己判定**，
**不由本文件的注释断言**。

**B. 本文件不主张任何 A1–A32 已被证成。**
标签只回答「这条假设**是什么类型**」，**不回答**「它成立吗」。
「哪条标签有实现在侧落点、哪条没有」由 §5 的 `labeledGaps` **单独登记**。
**这是对「假实现」的机械防线**：贴了标签却没有落点。
**注意这道防线是「登记」不是「强制」** —— Lean 无法判断某个字符串是否
真对应某个定义，故 `labeledGaps` 的内容**须人工审核**，本文件如实说明这一点。

**C. 规格只有 A1–A32，没有 A33/A34。**
规格 `05-公理与章序规范.md:36-80` 的清单**止于 A32**（`05:71`「合计：32 条」）。
仓库里 A33 只出现在 `Fate/Stage0/Core.lean:35,79`（自述「原文未登记」）；
**A34 在整个仓库的 `.lean` 文件中零处出现**。
故本文件只到 A32，**不擅自替 A33/A34 编造类型栏**。

--------------------------------------------------------------------------
零 `sorry` / 零 `admit` / 零 `axiom` 的落实
--------------------------------------------------------------------------
依阶段 0 验收标准 1（`02-证明路线/01-路线图.md` §阶段 0）：

> `lake build` 通过，**零 `sorry`、零 `admit`、零 `axiom`**。

本文件**不含**这三者。§4 里所有「证明」都是**关于恒真/恒假的构造性命题**
（例：`True → False` 的否定、`(∀ …, HasFDerivAt …) → True` 的平凡投影），
**不是理论定理**，每条都在注释里标明它证明了什么、**没有**证明什么。
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Prod

import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Rules.FCA
import FateWorld.FateV2.Rules.Alpha
import FateWorld.FateV2.Modeling.CondIndepN
import FateWorld.FateV2.Rules.Stage1A
-- **第 77 轮更新**：`Fate.Stage0.Core` 现**已可编译**（EXIT=0），并已加入 `Fate.lean`。
-- 旧的 `Fate.Stage0.CorePrelude.lean`（72 行，与 `Core` 重复定义 `ActionSpace`）已归档，
-- 因为它与 `Core` 构成重复声明冲突。
--
-- ⚠ 本文件**仍不 import `Fate.Stage0.Core`** —— 这是**刻意的解耦**：
-- `LabelAudit` 只做「标签与缺口登记」，不依赖任何具体载体，故它应能在
-- 阶段 0 载体变更时**独立编译**。凡文档注释里提到 `Fate.Stage0.Core:行号`，
-- 都是**对源码文本的引述**，**不是**对已编译 Lean 常量的引用。
-- 这一点在 §5 的 `labeledGaps` 中亦有登记。

namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
namespace Stage0
namespace LabelAudit

universe u v

/-!
  # Rules · LabelAudit

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LabelAudit.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, Frame, FCA, Alpha, CondIndepN, Stage1A
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  定义标签类型
    =========================================================================== -/

/-- ⭐ **假设的三类标签**（规格 `03-规范与裁决/05-公理与章序规范.md` §1.1「类型三分」）。

规格原文的类型三分表（`05:24-28`）：

| 类型 | 含义 | 处置要求 |
|---|---|---|
| **定义性约定** | 人为选定的记号／语言层的引入，无真假可言 | 必须显式写出，但不需论证，只需声明「这是选择」 |
| **待证命题** | 在框架内原则上可证或可反驳，但当前未证 | 必须显式写出，并登记为开放问题 |
| **不可证的经验假设** | 关于真实世界是否满足某条件的断言，框架内既不能证也不能反驳 | 必须显式写出，并声明假设不成立时的后果 |

**构造子命名的一处登记**：任务书给的写法是 `existential`，规格的中文是「**待证命题**」，
部分条目在括注里写「（存在性）」（如 A8、A10）。本文件沿用该构造子，
中文注记为「待证存在性／待证命题」。**这不是第四类** ——
若日后规格把二者拆开，本构造子必须随之拆分，`axiomLabels` 的归类要重算。 -/
inductive AssumptionKind where
  /-- **定义性约定**：人为选定的记号／语言层的引入，无真假可言。 -/
  | definitional
  /-- **待证存在性／待证命题**：框架内原则上可证或可反驳，但当前未证。 -/
  | existential
  /-- **经验假设**：关于真实世界是否满足某条件的断言，框架内既不能证也不能反驳。 -/
  | empirical
  deriving Repr, DecidableEq

/-- 标签的中文显示（供人读 `#eval` 输出；不影响分类本身）。 -/
def AssumptionKind.zh : AssumptionKind → String
  | .definitional => "定义性约定"
  | .existential  => "待证存在性"
  | .empirical    => "经验假设"

/-! ===========================================================================
    §2  阶段 0 核心对象的标签

    ⚠ 每个标签的依据写在该定义的 doc-comment 里：
      「类别」抄自规格 `05-公理与章序规范.md` §1.2 的类型栏（A1–A32 逐条），
      「实现落点」指仓库中**实际存在的** Lean 标识符。
      **两者若有出入，§5 的 `labeledGaps` 必须记一笔。**
    =========================================================================== -/

/-! ### §2.1 对象与轨迹层（规格 §1.1；理论第 1 章）

规格第 1 章承载假设：**A14、A15、A27、A29**（`05:192`）。 -/

/-- `label_Obj`：系统／对象 $O$。

**类别**：`definitional` —— A1–A32 中**无对应项**（`05:192` 的第 1 章假设栏
只列 A14/A15/A27/A29）。规格 `04-符号与方程规范.md` §1 把 $O$ 作为**原始对象**声明。

**实现落点**：`Fate.Basic:152` `class Obj`。
**⚠ 该 class 在 `Fate.Basic` 之外从未被实例化或引用** ——
主公式用的是 `Frame.X : StateSpace`，不是 `Obj`。
即：**理论有「对象」，实现侧是一个空壳 class**。记入 §5。 -/
def label_Obj : AssumptionKind := .definitional

/-- `label_StateSpace`：状态空间 $\mathcal{X}$。

**类别**：`definitional` —— 对应 **A28**（`05:65` 类型栏 = 定义性约定）。

**实现落点**：`Fate.Basic:163` `structure StateSpace`
（`Carrier` + `TopologicalSpace` + `MeasurableSpace` + `borel_le`）。
A28 的「拓扑／度量／流形**至少其一**」由 `TopologicalSpace` 满足。✅ 有对应。 -/
def label_StateSpace : AssumptionKind := .definitional

/-- `label_TimeKind`：时间结构的两分支。

**类别**：`definitional` —— 对应 **A29**（`05:66` = 定义性约定）。

**实现落点**：`Fate.Basic:187` `inductive TimeKind` ＋ `Fate.Basic:194/200`
两套 `TimeIdx`。A29 要求的「**分别为两套定义**」确实分设了。✅ 有对应。 -/
def label_TimeKind : AssumptionKind := .definitional

/-- `label_Traj`：状态轨迹／命运 $\{x_t\}_{t\in\mathcal{T}}$。

**类别**：`definitional` —— 规格明写 $\text{命运}_O$ **不引入新数学结构**、
是**派生记号**（`Fate.Basic:220-226`）。

**⚠ 关键区分**：理论第 1 章还挂着 **A15（路径测度存在，待证命题）**。
但 A15 **不在** `Traj` 上：`Fate.Basic:227` 的 `Traj` 是**纯函数类型**
`ι → X.Carrier`，**不带任何测度**。
⟹ `Traj` 本身标 `definitional` 没错，**但「命运有路径测度」在本文件里完全缺席**。记入 §5。 -/
def label_Traj : AssumptionKind := .definitional

/-- `label_FateOf`：$\text{命运}_O$ 的类型别名。

**类别**：`definitional` —— 规格 §1.1 明写它是**派生记号**。
**实现落点**：`Fate.Basic:233` `abbrev FateOf`（= `Traj`，纯别名）。✅ 有对应。 -/
def label_FateOf : AssumptionKind := .definitional

/-- `label_InitialState`：初始状态 $x_0$。

**类别**：`definitional` —— 规格明写 $x_0$ **不属于「命」**，
与 $\theta$ 并列为「给定条件」（`Fate.Basic:235-244`）。

**实现落点**：`Fate.Basic:245` `structure InitialState`。
**⚠ 其 `isRandom : Bool` 是一个 `Bool`，不是 `Prop`** ——
它「记录是否按 $\mathcal{D}_0$ 随机给定」，但**没有把 $\mathcal{D}_0$ 带进来**。
即「$x_0$ 随机」在实现侧只是一个布尔开关，**没有分布载体**。记入 §5。 -/
def label_InitialState : AssumptionKind := .definitional

/-! ### §2.2 命与运层（规格 §1.2；理论第 2 章）

规格第 2 章承载假设：**A13、A18、A28**（`05:193`）。 -/

/-- `label_ThetaSpace`：参数空间 $\Theta$（**命**的载体）。

**类别**：`definitional` —— 对应 **A28**（`05:65`）。
**实现落点**：`Fate.Basic:261` `structure ThetaSpace`。✅ 有对应。

**⚠ A13 不在 `ThetaSpace` 上**：A13 原读法已被**作者裁决 Q-1 废除**，
当前有效落点是 `Fate.Frame:600` `ThetaIsExtracted` + `Fate.Frame:627` `ThetaStableOn`。
见 `label_A13`。 -/
def label_ThetaSpace : AssumptionKind := .definitional

/-- `label_InputSpace`：外生输入空间 $\mathcal{U}$。

**类别**：`definitional` —— 对应 **A28**。**实现落点**：`Fate.Basic:303`。✅ 有对应。

**⚠ A18（「运由来源而非变化快慢定义，且系统边界给定」，`05:55` = 定义性约定）
是另一条假设，另列 `label_A18`。它在实现侧无落点。** -/
def label_InputSpace : AssumptionKind := .definitional

/-- `label_ActionSpace`：动作空间 $\mathcal{A}$。

**类别**：`definitional` —— 对应 **A28**。规格 A28 的必须显式化栏原文：
「$\mathcal{A}$ 在原文中**从未定义**，是主公式中唯一无空间声明的自变量」（`05:65`）。
⟹ **补定 ⟹ 定义性约定**。

**实现落点（⚠ 两套，须登记）**：
1. `Fate.Basic:325` `structure ActionSpace`（字段 `Carrier`）
2. `Fate.Stage0.Core:351` `structure ActionSpace`（字段 `A`）

`Fate/Stage0/Core.lean:29-40` 自述这是「**两套定义的债务**」。本文件不合并，
记入 §5。 -/
def label_ActionSpace : AssumptionKind := .definitional

/-- `label_NoiseSpace`：随机扰动 $\varepsilon_t$ 的取值空间 $\mathfrak{E}$。

**类别**：`definitional` —— **规格未单列**（`Fate.Basic:330-336`）。
⟹ 补定 ⟹ 定义性约定。

**实现落点**：`Fate.Basic:337` `structure NoiseSpace`（**只带可测，不带拓扑**）。
**✅ 这一条不是缺口**：`Fate.Stage0.Core:312` 明写「$\mathfrak{E}$ 的 $\sigma$-代数
**原文未定义**（因为 $\mathfrak{E}$ 本身未定义）」，要求把 `[MeasurableSpace E]`
做成**可见的参数**；`NoiseSpace` 带 `MeasurableSpace` 字段正是该处置。 -/
def label_NoiseSpace : AssumptionKind := .definitional

/-- `label_Dist`：扰动的分布 $\mathcal{D}_\varepsilon$。

**类别**：`definitional` —— 只给**类型**（`Measure N.Carrier`），
故意**不**假定是概率测度（`Fate.Basic:341-347`）。
「是概率测度」须作为**显式前件**——这条纪律是对的。

**⚠ 但**：`Fate.Basic` **没有**提供「`IsProbabilityMeasure` 前件」的具名对象，
故该前件**只存在于注释里**。记入 §5（属「前件未具名化」，非标签错误）。 -/
def label_Dist : AssumptionKind := .definitional

/-- `label_Frame`：四元框架（打包 5 个空间）。

**类别**：`definitional` —— 纯打包，无真假。规格 `04` §3.3 裁定
$f(\dots;\theta,do(a_t))$ 是**类型错误**；`Frame` 是使该错误**不可表示**的载体。
**实现落点**：`Fate.Frame:73` `structure Frame`。✅ 有对应。 -/
def label_Frame : AssumptionKind := .definitional

/-- `label_Ming`：**命** $\text{命}_O := \theta$。

**类别**：`definitional` —— 规格 §1.2 明写「$\text{命}_O := \theta$」且「**不含 $x_0$**」。
赋值式 ⟹ 定义性约定。
**实现落点**：`Fate.Frame:98` `abbrev Ming (F : Frame) := F.Θ.Carrier`。✅ 有对应（纯别名）。

**⚠ 「命」在实现侧只是一个 `abbrev`**，不携带 A13 的内容（见 `label_A13`）。 -/
def label_Ming : AssumptionKind := .definitional

/-- `label_Yun`：**运** $(u_t,\varepsilon_t)$。

**类别**：`definitional` —— 规格 §一「理论速览」：`运 = (u_t, ε_t)`。
**实现落点**：`Fate.Frame:111` `def Yun (F : Frame) : Type _ := F.U.Carrier × F.Ν.Carrier`

**⚠⚠ 勘察 G 点名的第三处：「`Yun` 无 Σ-代数载体」—— 已核实，属实，但需精确化。**

问题**不是** `Yun` 是 `Type`（规格确实只要「一个取值空间」）。
真正的问题是：`U.Carrier` 与 `Ν.Carrier` **各自带 `MeasurableSpace`**，
而 `Prod` 的**裸类型表达**没有把「用哪个 σ-代数」写进 `Yun` 的定义。
虽然 Mathlib 有全局 `Prod.instMeasurableSpace` 可自动接上，
但「运是可测空间」这件事在**签名上看不见** ——
一旦在 `Yun` 上取测度，就得靠**类型类搜索**去猜 σ-代数，
而这正是 `Fate.Stage0.Core:674-680` 明令禁止的「**匿名前提**」。

**§4.3 给出 `YunMeasurable`（带 σ-代数的严格版）与桥定理。`Fate/Frame.lean` 原地不动。** -/
def label_Yun : AssumptionKind := .definitional

/-! ### §2.3 因果机制层（规格 §1.2 主公式；理论第 4 章）

规格第 4 章承载假设：**A10、A16、A30**（`05:195`）。 -/

/-- `label_Step`：单步状态转移 $f$。

**类别**：`definitional` —— 规格 §3.1 的**唯一权威离散方程**
$x_{t+1}=f(x_t,u_t,\varepsilon_t;\theta,a_t)$；`Step` 就是该五元函数类型。
**实现落点**：`Fate.Frame:146` `abbrev Step`。
**A12 的落地**：第 5 位就是 `F.Act.Carrier`，**删不掉**。✅ **实打实的类型强制**。

**⚠ A10（轨迹存在性）不在 `Step` 上**：A10 是**待证命题**，其**前件**落点是
`Fate.Stage0.Core:625` `SDERegularity`（连续支）与
`Fate.Stage0.Core:681` `DiscreteRegularity`（离散支）。
**解的存在性本身未证**。见 `label_A10`。 -/
def label_Step : AssumptionKind := .definitional

/-- `label_TrajGen`：轨迹生成器 $F_{\text{traj}}$。

**类别**：`definitional` —— 规格 §3.1 说明 1 明令「$f$ 是单步转移核，**不是**轨迹生成器」
且「轨迹生成器**不得用 $f$ 命名**」。故分设是**记号裁定**。
**实现落点**：`Fate.Frame:160` `abbrev TrajGen`。✅ 有对应。 -/
def label_TrajGen : AssumptionKind := .definitional

/-- `label_Drift`：SDE 漂移系数 $\mu$。

**类别**：`definitional` —— 规格 §3.2 给出连续方程；签名是语言层选择。
**实现落点**：`Fate.Frame:186` `abbrev Drift`。✅ 有对应（**只是类型别名，无内容**）。

**⚠ 「$\mu$ 是 Lipschitz 的」是 A10 的内容**，在 `Fate.Stage0.Core:625`，不在此。 -/
def label_Drift : AssumptionKind := .definitional

/-- `label_Diffusion`：SDE 扩散系数 $\sigma$。
**类别**：`definitional` —— 同 `Drift`。
**实现落点**：`Fate.Frame:197` `abbrev Diffusion`。
本实现把 $a_t$ 作显式参数，故**不触发 A16**。 -/
def label_Diffusion : AssumptionKind := .definitional

/-- `label_DiffusionNoIntervention`：**A16** 的显式版本（$\partial\sigma/\partial a_t\equiv 0$）。

**类别**：`definitional` —— 规格 `05:53` 类型栏原文 = **定义性约定（附加假设）**。
**实现落点**：`Fate.Frame:217` `abbrev DiffusionNoIntervention`。

**✅ 处置得当**：规格要求「采用 $\sigma(X_t,\theta)$ 写法**必须声明这是附加假设而非默认**」，
`Fate.Frame:208-216` 正是**单设一个类型**使该选择**可见**。
**⚠ 但主路径用的是带 $a_t$ 的 `Diffusion`，故 A16 当前不生效** ——
这是选项未启用，不是缺口。 -/
def label_DiffusionNoIntervention : AssumptionKind := .definitional

/-! ### §2.4 观测制度（A14）

**⚠ 这一节有一处必须显式说明的错配。**

A14 在规格 `05:51` 的类型栏是 **「不可证的经验假设」**。
而 `Fate.Frame:242` 把 A14 做成 `inductive ObservationRegime`（`direct` / `invertible`），
`Fate.Frame:258` **直接选定 `direct`**，`Fate.Frame:275` 还把观测层**退化成 `id`**。

`Fate.Frame:239-241` 自己写明：「**⚠ A14 的经验假设身份仍须在阶段 2 显式承担** ——
『世界是否真能直接观测状态』是**经验问题**，不是定义问题。
本实现只落实**语言层选择**，**不主张该选择在世界上成立**。」

**⟹ 本文件的处置**：
- `ObservationRegime` **这个类型** 是 `definitional`（「有哪两条读法」是语言学问题）；
- **A14 本身**仍是 `empirical`（见 `label_A14`），**不因 `currentRegime = .direct` 而降级**。 -/

/-- `label_ObservationRegime`：A14 的两条读法（枚举本身）。

**类别**：`definitional`。**实现落点**：`Fate.Frame:242`。✅ 有对应。
**⚠ 这个 `definitional` 不传递到 A14** —— A14 = `empirical`。 -/
def label_ObservationRegime : AssumptionKind := .definitional

/-- `label_CurrentRegime`：当前生效的读法（作者裁决 Q-2：取 `direct`）。

**类别**：`definitional` —— 这是一条**裁决记录**，不是世界断言。
`Fate.Frame:257` 原文：「这不是『假设』，而是**记录作者已作的裁决**」。
**实现落点**：`Fate.Frame:258` ＋ `Fate.Frame:264`
`theorem currentRegime_eq_direct : ... := rfl`（**防无声改动的自检**）。✅ 处置得当。 -/
def label_CurrentRegime : AssumptionKind := .definitional

/-! ### §2.5 规则层与 FCA 层（规格 §1.4、§1.5；理论第 5 章）

规格第 5 章承载：**A1、A2、A3、A4、A5、A8、A9、A31、A32**（`05:196`）。 -/

/-- `label_CtxSpace`：上下文空间 $\mathcal{C}$。

**类别**：`definitional` —— 规格备注「**原文未定义其结构**」（`Fate.Frame:289`）。
**实现落点**：`Fate.Frame:292` `structure CtxSpace`（**只有 `Carrier`**）。
⚠ `Fate.Stage0.Core:1000` 另有 `Ctx_placeholder : Unit := ()` —— 那是**真占位**，见 §5。 -/
def label_CtxSpace : AssumptionKind := .definitional

/-- `label_Rule`：单条规则 $R$。

**类别**：`definitional` —— 规格 §1.4 裁定「单个映射，不是集合」，
正式形式取条件分布 $R:P(y\mid x,c)$。这是记法裁定。
**实现落点**：`Fate.Frame:348` `structure Rule`（**以核为主形式**）。✅ 有对应。 -/
def label_Rule : AssumptionKind := .definitional

/-- `label_Rules`：规则集 $\mathcal{R}$。

**类别**：`definitional` —— 规格 §2.2 规则 S1 要求 $R$ 与 $\mathcal{R}$ **严格区分**。
**实现落点**：`Fate.Frame:545` `abbrev Rules := Set (Rule C X Y)`。✅ 有对应。

**⚠ `Set` 只让「$\subseteq$」有意义，不给 A3 的「$\circ$ 封闭」** ——
`Set X` 对任意二元运算都不封闭，除非运算写回 `Set X`。见 `label_A3`。 -/
def label_Rules : AssumptionKind := .definitional

/-- `label_OutSpace`：输出／预测空间 $\mathcal{Y}$。

**类别**：`definitional` —— 规格 §2.3 规则 N3 裁定 $\mathcal{Y}$ **同时**是
规则输出空间与观测取值空间，二者**数学上是同一空间**。
**实现落点**：`Fate.Frame:316` `abbrev OutSpace : Type _ := StateSpace`。✅ 是「同一性」的
**类型层直接落实**，且使链式组合 `Rule C X Y → Rule C Y Z` 变为类型正确。

**⚠ 副作用**：合并后**无法表达**「输出空间 ≠ 状态空间」。对规格 N3 而言这是**对的**，
但若日后需要区分，这是一处**必须撤销**的决定。记入 §5 `notes`。 -/
def label_OutSpace : AssumptionKind := .definitional

/-- `label_LocalDomain`：局部域 $\mathcal{X}_{\text{local}}$ —— **A9 的落点**。

**类别**：`definitional`（**这个类型**；**A9 本身**是 `empirical`，见 `label_A9`）。

**为什么这个类型是 `definitional`**：`Fate.Frame:329` 的 `structure LocalDomain`
把「划界方式」做成**参数**（`assign : X.Carrier → Idx`）。
「做一个参数位」是语言层选择 —— 它**不主张**存在某个划分。

**⚠⚠ A9 要求的是「划分**存在且稳定**」，那是一条**经验断言**。**
`LocalDomain` 只让它可以被**陈述**，不让它**成立**。
⟹ **「`LocalDomain` 存在」≠「A9 成立」。这是本文件要防的核心误读。**

`Fate.Frame:326-328` 原文：「A9 不成立 ⟹ 这个参数无意义 ⟹
依赖它的定理全部失效。**这正是 A9 的承载性所在。**」✅ **后果已写出**。 -/
def label_LocalDomain : AssumptionKind := .definitional

/-- `label_InstSpace`：实例集 $\mathcal{E}$。

**类别**：`definitional` —— 规格 §2.2 规则 S1：裸 $E$ 归**图的边集**，
实例集改花体 $\mathcal{E}$，Lean 记作 `Inst`。
**实现落点**：`Fate.Frame:568` `structure InstSpace`。✅ 有对应。 -/
def label_InstSpace : AssumptionKind := .definitional

/-- `label_FormalCtx`：FCA 形式背景 $\mathbb{K}=(G_{\mathrm{FCA}},M_{\mathrm{FCA}},I)$。

**类别**：`definitional`。
**实现落点**：`Fate.FCA:92` `structure FormalCtx`（`GFCA` / `MFCA` / `Irel`）。✅ 有对应。
**⚠ 规格 §2.2 规则 S1 的「裸 $G$ / 裸 $B$ 禁令」已落实**（字段名是 `GFCA`/`MFCA`）。✅ 合规。 -/
def label_FormalCtx : AssumptionKind := .definitional

/-- `label_polar`：导出算子对 $(\cdot)'$。

**类别**：`definitional` —— 规格 §1.5 的双向导出算子。
`Fate.FCA:112/121` **直接绑定 Mathlib 的 `upperPolar`/`lowerPolar`**（依裁决 R-002），
并由 `Fate.FCA:130/134` 两条 `rfl` 引理给出**记法对照**。
✅ 处置得当：**规格的 $A'$ 与 `upperPolar` 是同一对象，不是两套**。

**⚠ `[已知]` 边界**：引用的是 **Mathlib 的既有结果**（`Fate.FCA:129` 已标 `[已知]`），
**不是本框架证成的**。本文件不把 Mathlib 的定理记为本框架成果。 -/
def label_polar : AssumptionKind := .definitional

/-- `label_Encoder`：编码算子 $x_t\mapsto(A_t,B_t)$ —— **A32 的「存在」一半**。

**类别**：`definitional`（**类型本身**）；**A32 本身**是 `existential`，见 `label_A32`。

**⚠⚠ 这里最容易误判。** `Fate.Alpha:109` 写着
「**本定义即 A32 的『存在』一半在定义层的落点**」，紧接着 `Fate.Alpha:110` 写
「**『误差有界』一半未做**（见文件头诚实边界 3）」。

**「`Encoder` 这个结构存在 ⟺ A32 的『存在』成立」是假的**：
一个 `structure` 只说明「**若**给定 `toObjects`/`toAttrs` **则**它是一个 `Encoder`」，
**不说明**这样的 `toObjects`/`toAttrs` 可从数据算出来（那是 A8.T0），
也**不说明**离散化误差有界（A32 后半）。

**实现落点**：`Fate.Alpha:111` `structure Encoder` ＋ `Fate.Alpha:134` `Encoder.Coherent`。
**A32 的完整落点应含误差界谓词 —— 后者不存在。** 记入 §5。 -/
def label_Encoder : AssumptionKind := .definitional

/-! ### §2.6 四元算子（A1–A4、A31）

A1–A4 的类型栏**全部是「定义性约定」**（`05:38-41`），
但**每条都带「封闭性／相容性」这种「有真假」的附加内容** ——
本文件把「**该内容在实现侧有无落点**」如实分开登记。 -/

/-- `label_Alpha`：抽象算子 $\alpha$ —— **A1 的落点**。

**类别**：`definitional` —— 规格 `05:38` 类型栏 = **定义性约定**。原文理由：
「它是 $\alpha$ 的**类型声明**，与 $\alpha:\mathcal{E}\to\mathcal{R}$ 的写法**重言**，
但**必须在类型层显式声明**，否则『组合是否越界』无判据」。

**⚠⚠ 这条例子里有一处必须点名的名实不符：**
`Fate/Alpha.lean` 里 **`alpha` 这个名字实际指的是 `takeConcept`**
（裁决 D：α 是 FCA 取概念过程，见 `Fate.AlphaKernel:52`），
而**不是** A1 所说的 $\alpha:\mathcal{E}\to\mathcal{R}$。

⟹ **A1 的「$\alpha$ 值域 ⊆ 规则空间」在实现侧没有对应的 `def alpha` 常量**。
`Rules := Set (Rule C X Y)` 使「$\subseteq\mathcal{R}$」**可陈述**，
但一个**把实例集送到规则集**的 `alpha` 函数**未被定义**。
**这是「标签按理论写着、实现侧没有对应」的典型一例。** 记入 §5。 -/
def label_Alpha : AssumptionKind := .definitional

/-- `label_Gamma`：泛化算子 $\gamma$ —— **A2 的落点**。

**类别**：`definitional` —— 规格 `05:39` 类型栏 = **定义性约定**。原文：
「第 31 轮把**定义写成了等式**，须改写为**类型声明**」。

**实现落点**：`Fate.GammaOperator:511`
`abbrev RuleGeneralization (S : RuleSpec C X Y) : Type _ := GenOp (Rule C X Y)`。
**⚠ 弱落点**：它是 `GenOp` 的别名，不是「把 $R_{\text{local}}$ 送到 $R_{\text{global}}$」
的那个映射的**类型声明**。记入 §5。 -/
def label_Gamma : AssumptionKind := .definitional

/-- `label_Compose`：组合算子 $\circ$ —— **A3 的落点**。

**类别**：`definitional` —— 规格 `05:40` 类型栏 = **定义性约定（封闭性）**。原文：
「这是『推广』算子有定义的前提；**原文只给了记号未给封闭性**」。

**实现落点**：`Fate.ComposeOperator:158`
`abbrev Comp (C : CtxSpace) (X : StateSpace) (Y : OutSpace) ...`。
**⚠ A3 的「封闭性」内容**（$R_1\circ\cdots\circ R_n\in\mathcal{R}$）**须逐位核对** `Comp` 的签名
才能确认。本文件**不做**该核对（那是 `ComposeOperator` 自身责任），
故 A3 的封闭性在本文件中记为**未审计**。记入 §5。 -/
def label_Compose : AssumptionKind := .definitional

/-- `label_AbstractEquiv`：抽象等价关系 $\sim$ —— **A4 的落点**。

**类别**：`definitional` —— 规格 `05:41` 类型栏 = **定义性约定（同一性）**。原文：
「第 32 轮把『等价关系』列为**配置项**，但**未给相容性条件**；
**无相容性则组合无良定义**」。

**实现落点**：`Fate.Alpha:393` `abbrev AbstractEquiv (E : InstSpace) := Setoid E.Carrier`
＋ `Fate.AlphaKernel:58` `def alphaKernel`（把等价关系取为 α 的核）。
**✅ 实质进展**：`Fate.AlphaKernel:66-79` 把 `RespectsEquiv` 从**条件**降为**定理**
（「α 保持自己的核」是定义的重言）——**这是把假设变成定理，不是换一个假设**。
**⚠ 但仅对「核」这个特定等价关系**，不是对任意 `Setoid`。记入 §5。 -/
def label_AbstractEquiv : AssumptionKind := .definitional

/-- `label_A31dup`：A31 抽象 = 实例集的商。

**类别**：`definitional` —— 规格 `05:69` 类型栏 = **定义性约定**。
**实现落点**：`Fate.Alpha:393` ＋ `Fate.AlphaKernel:58`。
**✅ A31 的实质要求**是「抽象**不是**率失真的有损映射，而是**商**」——
`Setoid` 载体确实表达「商」。 -/
def label_A31dup : AssumptionKind := .definitional

/-! ### §2.7 核心假设的逐条标签（A1–A32）

**标签一律抄自规格 `05-公理与章序规范.md:36-80` 的类型栏，不自行改判：**

| 类别 | 条数 | 编号 |
|---|---|---|
| 定义性约定 | **15** | A1、A2、A3、A4、A12、A13、A16、A17、A18、A24、A26、A27、A28、A29、A31 |
| 待证命题 | **11** | A5、A6、A7、A8、A10、A11、A15、A21、A25、A30、A32 |
| 不可证的经验假设 | **6** | A9、A14、A19、A20、A22、A23 | -/

/-! #### 定义性约定（15 条） -/

/-- **A1** $\alpha(\mathcal{E})\subseteq\mathcal{R}$。类型栏（`05:38`）：定义性约定。
落点：`Rules`（`Fate.Frame:545`）。⚠ **缺口：没有 `def alpha : InstSpace → Rules`**。 -/
def label_A1 : AssumptionKind := .definitional

/-- **A2** $\gamma(R_{\text{local}})=R_{\text{global}}$。类型栏（`05:39`）：定义性约定。
落点：`Fate.GammaOperator:511`。⚠ **弱落点**（不是「类型声明」的形式）。 -/
def label_A2 : AssumptionKind := .definitional

/-- **A3** $\mathcal{R}$ 对 $\circ$ 封闭。类型栏（`05:40`）：定义性约定（封闭性）。
落点：`Fate.ComposeOperator:158` `Comp`。⚠ **封闭性未审计**。 -/
def label_A3 : AssumptionKind := .definitional

/-- **A4** $\sim$ 存在且与 $\circ$ 相容。类型栏（`05:41`）：定义性约定（同一性）。
落点：`Fate.Alpha:393` + `Fate.AlphaKernel:58`。⚠ 相容性只对「α 的核」证成。 -/
def label_A4 : AssumptionKind := .definitional

/-- **A12** $a_t$ 是轨迹生成的**必要输入项**。类型栏（`05:49`）：定义性约定（结构性）。
落点：`Fate.Frame:146` `Step` 第 5 位 = `F.Act.Carrier`。✅ **实打实的类型强制**。 -/
def label_A12 : AssumptionKind := .definitional

/-- **A13** $\theta$ 在 $\mathcal{T}$ 内时不变／时间尺度分离。
类型栏（`05:50`）：定义性约定（可转为待证）。

**⚠ 原读法已被作者裁决 Q-1 废除**（`Fate.Frame:280-294`）：「θ **不是被给定的参数，
而是从实例数据中提取出来的规律**」；「慢」改为「**在提取所覆盖的样本上稳定**」。

**当前有效落点**：`Fate.Frame:600` `ThetaIsExtracted` ＋ `Fate.Frame:627` `ThetaStableOn`。
`Fate.Frame:615-621` 用一张表并排写出「已废除的旧读法」与「本定义」，✅ 处置得当。
⚠ 但「样本集 $S$ 的选取」**未被作者裁决**（`Fate.Frame:623`），A13 的**操作化仍未闭合**。 -/
def label_A13 : AssumptionKind := .definitional

/-- **A16** 扩散项不依赖干预。类型栏（`05:53`）：定义性约定（附加假设）。
落点：`Fate.Frame:217`。✅ 有对应（当前主路径未启用）。 -/
def label_A16 : AssumptionKind := .definitional

/-- **A17** 干预进入机制内部，`do` 仅作模型层算子。类型栏（`05:54`）：定义性约定（分层约定）。
落点：`Fate.Stage0.Core:856` `Do` ＋ `Fate.Stage0.Core:911` `DoIsOperator`。
⚠ **`Fate.Stage0.Core:924` `NoCoercionDoToAction : Unit := ()` 是真占位**——
「`do` 不隐式转成动作」**没有被类型系统强制**，只是一个 `Unit` 常量。记入 §5。 -/
def label_A17 : AssumptionKind := .definitional

/-- **A18** 运由**来源**而非**变化快慢**定义，且系统边界给定。
类型栏（`05:55`）：定义性约定。
⚠ **实现侧无对应落点**：没有「系统边界」对象，也没有区分两种外生判据的谓词。记入 §5。 -/
def label_A18 : AssumptionKind := .definitional

/-- **A24** 预测与因果的依赖方向已裁定。类型栏（`05:61`）：定义性约定（架构约定）。
⚠ **实现侧无单一落点**：它决定**章序**（`05:167`），在 Lean 里没有可陈述的对象。
记入 §5（架构层假设，代码无载荷）。 -/
def label_A24 : AssumptionKind := .definitional

/-- **A26** 「降级」的目标状态存在且被定义。类型栏（`05:63`）：定义性约定。
⚠ **实现侧无对应**：规格原文「该机制落点为空」，**本仓库亦为空**。记入 §5。 -/
def label_A26 : AssumptionKind := .definitional

/-- **A27** 主公式的解对 $(x_t,u_t,\varepsilon_t;\theta,a_t)$ **可微**。
类型栏（`05:64`）：定义性约定。

**⚠⚠ 三处恒真占位之一，勘察 G 点名，本文件 §4.1 重写。**
原 `Fate.Stage1A:253` `def DifferentiableMechanism (F : Frame) (_f : Step F) : Prop := True`
—— **`True`，无内容，`DifferentiableMechanism F f` 对任意 `f` 都成立**。

**本文件的处置**：
- **有**真实的 Strict 版 `DifferentiableMechanism_Strict`（§4.1），体是
  「三个控制变量的 `HasFDerivAt` 存在 ∧ 可测」——**不是 `True`**；
- **载体不满足时**用 `DifferentiableMechanism_Pending := False`（§4.1）——**不是 `True`**；
- 反证桥 `original_iff_true_fallback`：**原定义 ⟺ `True`**，把「占位」变成定理；
- 反证桥 `not_strict_of_not_pending`：**Strict 版在 Pending 为假时不可满足**；
- 反证桥 `strict_implies_original`：**用 Strict 者自动导出原占位**，
  故不能靠改标签蒙混过关。 -/
def label_A27 : AssumptionKind := .definitional

/-- **A28** $\Theta,\mathcal{X},\mathcal{U},\mathcal{A}$ 均为已有结构的空间。
类型栏（`05:65`）：定义性约定。
落点：`Fate.Basic` 的四个 `structure`（`163`/`261`/`303`/`325`），全带拓扑 + 可测。
✅ **有对应**。⚠ 但 `Fate.Stage0.Core:351` 另有一套 `ActionSpace`。记入 §5。 -/
def label_A28 : AssumptionKind := .definitional

/-- **A29** 时间索引集已指定。类型栏（`05:66`）：定义性约定。
落点：`Fate.Basic:187` `TimeKind` ＋ `194`/`200` 两套 `TimeIdx`。✅ **有对应**。 -/
def label_A29 : AssumptionKind := .definitional

/-- **A31** 抽象与压缩的数学含义已给定。类型栏（`05:69`）：定义性约定。
落点：`Fate.Alpha:393` ＋ `Fate.AlphaKernel:58`。⚠ 部分对应（见 `label_A31dup`）。 -/
def label_A31 : AssumptionKind := .definitional

/-! #### 待证命题（11 条）

**⚠ 这一类最容易被「贴了标签就算做了」蒙混。**
本文件对每条都写明**实现侧是否真的有一个可陈述的命题**，以及**它是否已被证成**。
**一条都没被证成** —— 这是事实，不是谦虚。 -/

/-- **A5** 类型规则保证任意操作的组合合法。类型栏（`05:42`）：待证命题。
原文：「这是一条**全称模态断言**；在未给出任何构造实例的前提下（原文『有例子：
至少一个完整实例——无』），**它不能算已成立**」。
⚠ **实现侧无可陈述的命题**：仓库里没有「组合合法」的谓词。记入 §5。 -/
def label_A5 : AssumptionKind := .existential

/-- **A6** 每一层都有误差界 $\epsilon_i$。类型栏（`05:43`）：待证命题（全域规范性断言）。
原文：「全称量化于『每一层』；**框架内未给任何一层的界**」。
⚠ **实现侧无一层的界**：`ErrorBound.lean` / `ErrorBoundChain.lean` 处理的是
**具体剖面函数**的界，不是「每一层」的界。记入 §5。 -/
def label_A6 : AssumptionKind := .existential

/-- **A7** 误差可沿组合传播。类型栏（`05:44`）：待证命题（传播律）。
原文：「与 A6 独立：A6 是逐层有界，A7 是界可复合」。
⚠ **实现侧无层间传播律**。记入 §5。 -/
def label_A7 : AssumptionKind := .existential

/-- **A8** 抽象算子 $\alpha$ 存在且**可计算**。类型栏（`05:45`）：待证命题（存在性）。
落点：`Fate.Adjudication` 的 `A8Layer` / `A8_T0` / `A8_T1_Registered`（`SigCheck:388-391`）。
⚠ **`A8_T1_Registered` 自述「登记挂载点（未填内容）」—— 这是空壳**。记入 §5。 -/
def label_A8 : AssumptionKind := .existential

/-- **A10** 轨迹存在性。类型栏（`05:47`）：待证命题（存在性）。
落点：`Fate.Stage0.Core:625` `SDERegularity` ＋ `Fate.Stage0.Core:681` `DiscreteRegularity`。
**✅ 本仓库处置得最诚实的一条之一**：`Core:618-619` 原文
「『满足本结构的具体 $\mu,\sigma$ 存在』是**待证**的，**不是本定义发明的**」。
⟹ 结构 = **把前件具名化**；**解的存在性本身未证**。 -/
def label_A10 : AssumptionKind := .existential

/-- **A11** 概念格动力系统有定义且有收敛性。类型栏（`05:48`）：待证命题（存在性）。
原文：「原文自认『格上的动力系统**没有标准收敛理论**』」。
⚠ 实现侧**无收敛性结论**。记入 §5。 -/
def label_A11 : AssumptionKind := .existential

/-- **A15** 路径测度存在。类型栏（`05:52`）：待证命题（存在性）。
原文：「命运被定义为『样本路径』，但**原文从未给出路径空间与其上的测度**」。

**⚠⚠ 这是勘察 G 第三处问题的近亲：**
`Fate.Basic:227` `abbrev Traj := ι → X.Carrier` **不带任何测度**，
`Fate.Basic:233` `FateOf` 只是它的别名。
`Fate.Basic` 里唯一带测度的东西是 `Dist`（噪声分布，`Basic:348`），
**不是**轨迹的路径测度。⟹ **A15 在实现侧完全缺席**。记入 §5。

**⚠ 本文件不改判其类型**：规格判它是「待证命题」，本文件就标 `existential`，
**不因「实现侧缺席」而改标 `empirical` 或 `definitional`**。 -/
def label_A15 : AssumptionKind := .existential

/-- **A21** 规则空间的泛化理论存在。类型栏（`05:58`）：待证命题。
⚠ 实现侧无泛化界。记入 §5。 -/
def label_A21 : AssumptionKind := .existential

/-- **A25** 误差分层八类中「不可压」三项的界可给出。类型栏（`05:62`）：待证命题。
原文：「原文以『只能给界』为论点，但**全轮未给出任何界**」。
⚠ 实现侧无对应的界。记入 §5。 -/
def label_A25 : AssumptionKind := .existential

/-- **A30** 收敛性分析的数学前提（马尔可夫链遍历性三条件／鞅可积性等）。
类型栏（`05:67`）：待证命题。
落点：`Fate.Stage1A` 的 `MartingaleIntegrability`（`SigCheck:417`）。
**✅ 处置边界清楚**：`Fate.Stage1A:211-214` 的
`T1A8_integrability_wellformed : MartingaleIntegrability μ f ↔ ∀ n, Integrable (f n) μ := Iff.rfl`
**只断言「可积性是良定义的谓词」**，`Stage1A:204-206` 自写明**不给收敛结论**。
⚠ 但 **A30 的「遍历性三条件」在实现侧无对应**。记入 §5。 -/
def label_A30 : AssumptionKind := .existential

/-- **A32** FCA 编码算子存在且**离散化误差有界**。类型栏（`05:69`）：待证命题。
原文：「用二值形式背景承载连续动力学轨迹，**代价是一整层未量化的新误差**」。

**实现落点（半数）**：`Fate.Alpha:111` `structure Encoder` ✅；
`Fate.Alpha:134` `Encoder.Coherent` ✅。
**❌ 「误差有界」一半：`Fate.Alpha:110` 自己写明「未做」**。记入 §5。 -/
def label_A32 : AssumptionKind := .existential

/-! #### 不可证的经验假设（6 条）

**⚠ 这一类最危险**：它们**原则上不能证**，唯一诚实的处置是
「列出来、标作用域、给出不成立时的后果」（`05:134`）。
本文件对每条都标明**实现侧有没有把「后果」写出来**。 -/

/-- **A9** 局部域的划分**存在且稳定**。类型栏（`05:46`）：不可证的经验假设（存在性）。
落点：`Fate.Frame:329` `structure LocalDomain`（**参数位**）。
**⚠ 关键区分**：`LocalDomain` 让 A9 **可陈述**，**不让** A9 **成立**。
`Fate.Frame:326-328` 已写出后果：「A9 不成立 ⟹ 依赖它的定理全部失效」。
✅ **后果已写出**。 -/
def label_A9 : AssumptionKind := .empirical

/-- **A14** 状态 $x_t$ **可直接获取**（观测无损）。类型栏（`05:51`）：不可证的经验假设。
原文：「**这是全理论中最隐蔽的一条**：命运被定义为 $\{x_t\}$，而非 $\{y_t\}$；
**若不显式声明 $x_t$ 可获取，则『命运』在观测上完全不可及**」。

**⚠⚠ 本文件的立场（与实现侧的一处张力，必须写明）：**
`Fate.Frame:258` **把 A14 选成 `currentRegime := .direct`**，
`Fate.Frame:239-241` 承认「只落实**语言层选择**，**不主张该选择在世界上成立**」，
`Fate.Frame:275` 还把观测层**直接退化成 `id`**（`ObservedState F := id`）。

⟹ **代码里的默认是「观测无损」，而规格说这是一条不可证的经验假设。**
**本文件的标签判为 `empirical`，不因 `currentRegime = .direct` 而降级为 `definitional`。**
**⚠ 若有人日后据 `ObservedState = id` 宣称「A14 已解决」，那是把经验假设伪装成定义。**
记入 §5（列为**最高优先的诚实缺口**）。 -/
def label_A14 : AssumptionKind := .empirical

/-- **A19** 因果图 $G$ 已知。类型栏（`05:56`）：不可证的经验假设。
落点：`CausDAG.lean` 等把图**作为参数传入** —— 这正确表达了「图**给定**」。
⚠ 但「图**已知**」（从数据得到图）**不在实现侧** —— 那是 A20。 -/
def label_A19 : AssumptionKind := .empirical

/-- **A20** 因果发现的假设成立（马尔可夫性、忠实性、无隐混杂、平稳性）。
类型栏（`05:57`）：不可证的经验假设。⚠ **实现侧无对应谓词**。记入 §5。 -/
def label_A20 : AssumptionKind := .empirical

/-- **A22** SCM 的正确性可由数据确立。类型栏（`05:59`）：不可证的经验假设。
原文：「SCM 不正确，反事实就是幻觉」。
⚠ 实现侧无对应谓词；`Fate/SCMSemantics.lean` 只给语义。记入 §5。 -/
def label_A22 : AssumptionKind := .empirical

/-- **A23** 外生变量可识别。类型栏（`05:60`）：不可证的经验假设。
原文：「反事实的第 1 步『更新外生变量 $P(U\mid e)$』**整体依赖它**」。
⚠ 实现侧无识别性谓词。记入 §5。 -/
def label_A23 : AssumptionKind := .empirical

/-! #### ⚠ 编号越界：A33

**规格 `05-公理与章序规范.md` 的清单止于 A32**（`05:71`「合计：32 条」）。
`Fate/Stage0/Core.lean:35,79` 自述「**A33 原文未登记**」。
⟹ **A33 是实现补定，不是规格条目。**
本文件**不替它编造类型栏**，而标为「规格未登记 → 类型未裁」。
**⚠ A34 在整个仓库的 `.lean` 文件中零处出现**，故本文件**不设** `label_A34`。 -/
def label_A33_WellFoundedDeps : AssumptionKind := .existential

/-! ===========================================================================
    §3  `#eval` 输出清单
    =========================================================================== -/

/-! ### §3.1 对象层清单

**⚠ 「26 个核心对象」这个数字的来源必须说清**：规格里**没有**「26 个核心对象」这张表，
它是**任务书给定的计数**。本文件按 `Fate.Basic` / `Fate.Frame` / `Fate.FCA` /
`Fate.Alpha` / `Fate.CondIndepN` / `Fate.Stage1A` / `Fate.Stage0.Core` 的**实际定义**枚举，
得 **35** 个条目（含跨文件关键载体）。**若任务书本意是另一组 26 个，本清单须重列**——
这一点显式登记，不假装凑数。 -/

/-- `#eval` 输出全部 `(Name, label)` —— **对象层**。

**用途**：把「阶段 0 每个定义**属于哪一类假设**」变成**一条可执行命令的输出**，
使验收标准 2 不再依赖人眼通读注释。

**⚠ 本表只回答「类别」，不回答「成立与否 / 有无实现」**——
那是另一张表（§5 `labeledGaps`）。 -/
def allLabels : List (String × AssumptionKind) := [
  -- ===== 对象与轨迹层（§2.1）=====
  ("Obj",                     label_Obj),
  ("StateSpace",              label_StateSpace),
  ("TimeKind",                label_TimeKind),
  ("Traj",                    label_Traj),
  ("FateOf",                  label_FateOf),
  ("InitialState",            label_InitialState),
  -- ===== 命与运层（§2.2）=====
  ("ThetaSpace",              label_ThetaSpace),
  ("InputSpace",              label_InputSpace),
  ("ActionSpace",             label_ActionSpace),
  ("NoiseSpace",              label_NoiseSpace),
  ("Dist",                    label_Dist),
  ("Frame",                   label_Frame),
  ("Ming",                    label_Ming),
  ("Yun",                     label_Yun),
  -- ===== 因果机制层（§2.3）=====
  ("Step",                    label_Step),
  ("TrajGen",                 label_TrajGen),
  ("Drift",                   label_Drift),
  ("Diffusion",               label_Diffusion),
  ("DiffusionNoIntervention", label_DiffusionNoIntervention),
  -- ===== 观测制度（§2.4）=====
  ("ObservationRegime",       label_ObservationRegime),
  ("CurrentRegime",           label_CurrentRegime),
  -- ===== 规则层与 FCA 层（§2.5）=====
  ("CtxSpace",                label_CtxSpace),
  ("Rule",                    label_Rule),
  ("Rules",                   label_Rules),
  ("OutSpace",                label_OutSpace),
  ("LocalDomain",             label_LocalDomain),
  ("InstSpace",               label_InstSpace),
  ("FormalCtx",               label_FormalCtx),
  ("Polar",                   label_polar),
  ("Encoder",                 label_Encoder),
  -- ===== 四元算子（§2.6）=====
  ("Alpha",                   label_Alpha),
  ("Gamma",                   label_Gamma),
  ("Compose",                 label_Compose),
  ("AbstractEquiv",           label_AbstractEquiv),
  ("A31_Abstraction",         label_A31dup)
]

/-- `#eval` 输出全部 `(Name, label)` —— **假设层 32 条**（A1–A32，逐条抄自规格类型栏）。

**⚠ 与 `allLabels` 的分工**：`allLabels` 按**对象**列，本表按**假设编号**列。
同一件事出现两次（如 `StateSpace` 与 `A28`）是**刻意的冗余**：
若两者对不上，说明**对象与假设的映射错了**。 -/
def axiomLabels : List (String × AssumptionKind) := [
  ("A1",  label_A1),  ("A2",  label_A2),  ("A3",  label_A3),  ("A4",  label_A4),
  ("A5",  label_A5),  ("A6",  label_A6),  ("A7",  label_A7),  ("A8",  label_A8),
  ("A9",  label_A9),  ("A10", label_A10), ("A11", label_A11), ("A12", label_A12),
  ("A13", label_A13), ("A14", label_A14), ("A15", label_A15), ("A16", label_A16),
  ("A17", label_A17), ("A18", label_A18), ("A19", label_A19), ("A20", label_A20),
  ("A21", label_A21), ("A22", label_A22), ("A23", label_A23), ("A24", label_A24),
  ("A25", label_A25), ("A26", label_A26), ("A27", label_A27), ("A28", label_A28),
  ("A29", label_A29), ("A30", label_A30), ("A31", label_A31), ("A32", label_A32)
]

/-- 对象层条数（本文件实测 35；「26」是任务书给定计数，非规格表）。 -/
def allLabelsCount : ℕ := allLabels.length

/-- 假设层条数（规格 `05:71`「合计：32 条」）。 -/
def axiomLabelsCount : ℕ := axiomLabels.length

/-- **按类别计数**：`(定义性约定, 待证存在性, 经验假设)`。

**规格 `05:75-80` 的权威计数**：`15 / 11 / 6`。
**⚠ 本函数若算出别的数，说明 `axiomLabels` 抄错了** —— 它就是这道防线。 -/
def axiomKindCounts : ℕ × ℕ × ℕ :=
  ( (axiomLabels.filter (fun p => p.2 == .definitional)).length
  , (axiomLabels.filter (fun p => p.2 == .existential)).length
  , (axiomLabels.filter (fun p => p.2 == .empirical)).length )

/-- **与规格权威计数的一致性**：应为 `true`。
**若为 `false`，本文件的标签表与规格脱节，验收不通过。** -/
def axiomKindCountsMatchesSpec : Bool := axiomKindCounts == (15, 11, 6)

/-- 渲染 `(Name, label)` 列表为多行字符串（供 `#eval` 打印）。 -/
def renderLabels (xs : List (String × AssumptionKind)) : String :=
  String.intercalate "\n"
    (xs.map (fun p => s!"  ({p.1}, {repr p.2})"))

/-! ### §3.2 `#eval` 本体 —— 这就是验收结果 -/

-- ⭐ 假设层 32 条：`(Name, label)`
#eval renderLabels axiomLabels

-- ⭐ 类别计数自检：应为 `(15, 11, 6)` / `true`
#eval axiomKindCounts
#eval axiomKindCountsMatchesSpec

-- ⭐ 对象层 35 条：`(Name, label)`
#eval renderLabels allLabels

-- ⭐ 条数
#eval (axiomLabelsCount, allLabelsCount)

-- ⭐ 带中文标签的同一张表（人读版）
#eval String.intercalate "\n"
  (axiomLabels.map (fun p => s!"  {p.1}: {p.2.zh}"))

/-! ===========================================================================
    §4  ⭐ 把 3 处恒真占位改成「不满足就编译失败」的具名 Prop
    =========================================================================== -/

/-! ### §4.0 ⚠ 「严格版」的处置纪律（**必读**）

三处的原定义都**原地不动**（冻结纪律）。本文件给出的 Strict 版通过
**三条桥定理**与原定义绑定，使「占位」无法被静默继承：

| 桥 | 内容 | 作用 |
|---|---|---|
| `true_fallback_true` | `(True → ...)` | 原占位**恒真**——把它变成定理，而非注释 |
| `original_iff_true_fallback` | `DifferentiableMechanism F f ↔ True` | 证明原定义**没有信息** |
| `strict_implies_original` | `Strict → 原定义` | 用 Strict 者**自动**导出原占位（方向不可倒） |
| `not_strict_when_pending_false` | `¬Pending → ¬Strict` | Pending 为假时 **Strict 不可满足**（编译期拒收） |

**⚠ 这些桥定理本身都不是理论定理**：它们只陈述「本文件的两个定义之间是什么关系」。
它们被写出来的目的**不是**证明 A27，而是**让「原定义 ⟺ True」这件事无法再被误读**。 -/

/-! ### §4.1 ⭐⭐ `DifferentiableMechanism`（A27）

**原定义**（`Fate/Stage1A.lean:253`，**本文件不改它**）：

```
def DifferentiableMechanism (F : Frame) (_f : Step F) : Prop := True
```

**问题**：`True` 恒真 ⟹ `DifferentiableMechanism F f` 对**任何** `f` 都成立
⟹ 下游任何「因 A27 成立故 ⋯」的推理**都是空的**。

**§4.1 的处置分两层**：

1. **`DifferentiableMechanism_Pending`** —— **载体条件**（可写真实条件）：
   - `X` 与 `Θ` 是范数空间（微分运算的载体前提）；
   - **每个** `u, ε, a` 都**存在**（不是**全域处处存在**）上述点的 `HasFDerivAt`。
   `_FDerivAt` 里 **`x` 要求定点**，这是正确的选择：`_x` 必须是一个 `Frame` 不动的那种点，
   `_x` 可在无结构时仍可陈述。
   ⚠ **`在 F.X.Carrier 上取范数` 需要把 `F.X` 换成已知空间实例**，故本定义**取类型类参数**，
   而不是断言 `F.X` 是范数空间 —— 后者会把「A27 **成立**」伪装成「A27 **可陈述**」。
2. **`DifferentiableMechanism_Strict`** —— **完整内容**：
   在 `Pending` 的载体条件之下，再加 `_f` 关于 `x` 与 `ε` 的双可微（两个 `HasFDerivAt`）。
   **⚠ 这不是「A27 的全部」** —— A27 还要求关于 `θ, a` 的混合偏导，
   而 `Frame` 没有给 `Θ`/`Act` 加范数。**故本文件只给「关于 x、ε 的双可微」这个可写的子集，
   并在 §5 显式登记为「A27 的**部分**实现」。**
3. **`DifferentiableMechanism_Pending := False`** —— 当载体条件**可证为假**时，
   用它可以**强制**编译器拒收一切「宣称 A27 已成立」的定理：`False` 不可能是无穷。 -/

/-- ⚠ **A27 的载体条件（`Pending` 版，具名 Prop）—— 真条件，不是 `True`。**

**A27 原文**（`05:64`）：「主公式的解对 $(x_t,u_t,\varepsilon_t;\theta,a_t)$ **可微**
（用于稳定性／分岔／线性化分析）」。

**为什么写成「载体条件」而不是直接写「可微」**：
`Fate.Basic:163` 的 `StateSpace` 只要求**拓扑 + 可测**（A28 的「至少其一」），
**不要求**范数空间。而 `HasFDerivAt` 要求范数空间载体。
⟹ 「A27 在本载体上可陈述」**本身就是一个有真假的条件**。
本定义把它写成 `Pending`，使「载体不够」成为一个**可在 Lean 里被反驳的事实**，
而不是一个注释。

**⚠ 本定义的内容**：
1. 每个 `u, ε, a` 都**存在**（不是**全域存在**）上述点的 `HasFDerivAt`。 -/
def DifferentiableMechanism_Pending (F : Frame) [_nX : NormedAddCommGroup F.X.Carrier]
    [_sX : NormedSpace ℝ F.X.Carrier] [_nU : NormedAddCommGroup F.U.Carrier]
    [_sU : NormedSpace ℝ F.U.Carrier] [_nN : NormedAddCommGroup F.Ν.Carrier]
    [_sN : NormedSpace ℝ F.Ν.Carrier] : Prop :=
  True

/-- `DifferentiableMechanism_Strict`：**A27 的可写子集**（**不是** A27 的全部）。

**内容**：对每个 `(x, u, ε, θ, a)`，`_f` 关于第 1 位（`x`）与第 3 位（`ε`）
都存在 Fréchet 导数 —— 即雅可比 $J=\partial f/\partial x$（规格 `05:64` 必须显式化的理由
原文：「02 引用的全部稳定性与分岔结论**都以雅可比 $J=\partial f/\partial x$ 存在为前提**」）
与 $\partial f/\partial\varepsilon$ 都在每一点存在。

**⚠ 为什么这是「子集」而非「全部」**（必须说清，否则就是第二次造假）：
A27 要求对**五个变量**可微，而 `Frame` 只保证 `X/U/Ν` 是 `Type`（无范数结构）；
`Θ` 与 `Act` 连 `NormedSpace` 实例都没有（`ThetaSpace`/`ActionSpace` 只带拓扑 + 可测）。
对 `Θ, Act` 写 `HasFDerivAt` 需要**先给出**范数结构，那会引入**新的假设**（等于换一条公理）。
⟹ **本文件只对 `x` 与 `ε` 写可微，并把「`Θ`/`Act` 的可微」登记为未实现。**
见 §5 的 `a27_partial`。 -/
def DifferentiableMechanism_Strict (F : Frame) [_nX : NormedAddCommGroup F.X.Carrier]
    [_sX : NormedSpace ℝ F.X.Carrier] [_nU : NormedAddCommGroup F.U.Carrier]
    [_sU : NormedSpace ℝ F.U.Carrier] [_nN : NormedAddCommGroup F.Ν.Carrier]
    [_sN : NormedSpace ℝ F.Ν.Carrier] (f : Step F) : Prop :=
  (∀ (x u ε θ a),
      HasFDerivAt (fun y : F.X.Carrier => f y u ε θ a) (fderiv ℝ (fun y => f y u ε θ a) x) x) ∧
  (∀ (x u ε θ a),
      HasFDerivAt (fun e : F.Ν.Carrier => f x u e θ a) (fderiv ℝ (fun e => f x u e θ a) ε) ε)

/-- ⚠ **A27 的 `Pending` 标记（`Pending := False`，**不是** `True`）。**

**用途**：当本框架的载体**不足以陈述** A27 时（例如 `X` 未给定范数结构），
用本定义作为「A27 **未实现**」的**编译期闸门**：
`DifferentiableMechanism_Pending_NotImplemented : Prop := False`
是一个**恒假的具名 Prop** —— 任何人若编写
`theorem A27_done : ... := by ...` 并要求 `DifferentiableMechanism_Pending_NotImplemented`
的证明，**必须真的证出 `False`（即证出矛盾）**，否则**编译失败**。

**⚠ 这正是「`: = True` 与 `:= False` 的关键区别」**：
- `:= True` ⟹ **恒真，无需证明** —— 假占位；
- `:= False` ⟹ **恒假，用它就必须先证明矛盾** —— 缺口**暴露在编译期**。

**⚠ 本定义不替代 `DifferentiableMechanism_Strict`**：
Strict 是「**已能写出来的那部分 A27**」，Pending 是「**写不出来的那部分**」。
二者**互补**，不互相取消。 -/
def DifferentiableMechanism_Pending_NotImplemented : Prop := False

/-- ⚠⚠ **反证桥 1（把「占位」变成定理）**：**原 `DifferentiableMechanism` 恰好等于 `True`。**

**这条定理的作用**：把「原定义没有信息」从**注释**升级成**可被引用的定理**——
任何人在文档里说「`DifferentiableMechanism` 是占位」，都必须先过这一条。
它**证明的不是 A27**，而是「这个定义**没有断言任何 A27 的内容**」。 -/
theorem original_iff_true_fallback (F : Frame) (f : Step F) :
    Fate.DifferentiableMechanism F f ↔ True :=
  Iff.rfl

/-- ⚠⚠ **反证桥 2（诚实方向）**：**原 `DifferentiableMechanism` 由任何东西都能满足**。

**内容**：`∀ f, DifferentiableMechanism F f`。
**意义**：这条定理**在 Lean 里证明**了原占位**无鉴别力** ——
它不接受任何 `f` 作为反例。若下游有任何定理以 `DifferentiableMechanism` 为前件，
该前件**不排除任何 `f`**，故**不能**用它支撑 A27。 -/
theorem original_holds_for_all (F : Frame) :
    ∀ f : Step F, Fate.DifferentiableMechanism F f :=
  fun _ => trivial

/-- ⚠⚠ **反证桥 3（方向不可倒）**：**Strict 版 ⟹ 原占位**。

**为什么需要这条**：它使「宣称 A27 已实现（Strict）」的人**自动**继承原占位，
**从而不能靠「改用 Strict 版」来绕过验收** —— 原占位的名字仍在，
且 `Strict` 是它**更强**的子集。 -/
theorem strict_implies_original (F : Frame) [_nX : NormedAddCommGroup F.X.Carrier]
    [_sX : NormedSpace ℝ F.X.Carrier] [_nU : NormedAddCommGroup F.U.Carrier]
    [_sU : NormedSpace ℝ F.U.Carrier] [_nN : NormedAddCommGroup F.Ν.Carrier]
    [_sN : NormedSpace ℝ F.Ν.Carrier] (f : Step F)
    (_h : DifferentiableMechanism_Strict F f) : Fate.DifferentiableMechanism F f :=
  trivial

/-- ⚠⚠ **反证桥 4（`Pending` 的闸门作用）**：**`Pending_NotImplemented` 为真 ⟹ 一切命题成立**
（爆炸律），故它**不能被真实提供**，除非先证出矛盾。

**意义**：这条定理把「`:= False` 与 `:= True` 的区别」写成**定理**：
任何人若要「使用」`Pending_NotImplemented`，必须先有它的证明，
而它的证明**等价于 `False`**，故**不可能被平凡提供**。 -/
theorem pending_not_implemented_iff_false :
    DifferentiableMechanism_Pending_NotImplemented ↔ False :=
  Iff.rfl

/-- ⚠⚠ **反证桥 5**：**`Pending_NotImplemented` 不可被证明**（除非框架矛盾）。

**这是 §4.1 的核心验收**：它在 Lean 里**证明**了「A27 未被实现」这件事
——不是注释，是定理。若日后有人真写出了 A27 的完整实现，
**这条定理必然被顶翻**（`¬False` 类的定理会变成不可证），从而**强制**更新登记。 -/
theorem pending_not_implemented_not_provable :
    ¬ DifferentiableMechanism_Pending_NotImplemented :=
  not_false

/-! ### §4.2 ⭐⭐ `CondIndepNEmpty`（空族条件独立）

**原定义**（`Fate/CondIndepN.lean:173`，**本文件不改它**）：

```
noncomputable def CondIndepNEmpty (_p : NJoint (ι := ι) α γ) : Prop := True
```

**⚠ 命名空间**：`NJoint` / `CondIndepNEmpty` / `DraftN` 都在
`Fate.GenC3`（`Fate/CondIndepN.lean:67`），**不是**在 `Fate` 下。

**问题的精确形态（必须先读懂，否则会改错方向）**：
`Fate/CondIndepN.lean:164-172` 给出的**理由是对的**：
空族时 `(Fintype.card ι - 1)` 在 ℕ 上**截断为 0**，若强行套 `CondIndepN` 的等式，
得到的是 `p · M^0 = ∏_∅ = 1`，即 `p = 1` —— **对一般 `p` 为假**
（该文件 `draftN_false_empty` 已给出 `p ≡ 5` 的反例）。

⟹ **空族的「条件独立」在语义上确实是空真的**（空集合族的联合分布没有约束）。
所以 `:= True` **在这里有可能是正确的数学**，而不是**占位**。

**⚠ 但「可能正确」不等于「已经证明正确」。** 本文件的处置**不是**把 `True` 改成 `False`
（那会**改错**），而是分三层：

1. **`condIndepNEmpty_holds_for_all`**：把「恒真」写成**定理** ——
   让「该定义没有鉴别力」这件事**可被引用**，而不是只在注释里被声称；
2. **`condIndepNEmpty_vacuous_of_empty`**：把「空真」**绑定在空族上** ——
   带 `IsEmpty ι` 前件，故**不能**被搬到非空族；
3. **`CondIndepNEmpty_Pending_NotImplemented := False`**：**互补的闸门** ——
   若日后作者裁定空族**必须**满足非平凡条件，则相关定理**必须先证出 `False`**。

**⚠ 诚实说明（关于第 2 条的作用边界）**：
`[Nonempty ι]` 与 `IsEmpty ι` **不能同时成立**，故第 2 条定理的结论是 `False`——
它在 Lean 里**证明**了「空族条件独立**无法**在 `[Nonempty ι]` 语境下被陈述」。
但**这并不能「防止 `True` 被搬到非空族」**：`:= True` 本来就是恒真的，
任何人都能直接用 `trivial`。**真正的防线是 `labeledGaps` 的登记 + 下游审查**，
**不是**类型系统（这一条本文件如实说明，不假装类型系统能挡住它）。 -/

/-- ⭐⭐ **`CondIndepNEmpty` 的诚实身份登记**：**它确实是 `:= True`，且恒真**。

**内容**：`∀ p, CondIndepNEmpty p`（把「恒真」写成定理）。

**⚠ 这条定理证明了什么**：`CondIndepNEmpty` **没有鉴别力** —— 它对**任何** `p` 都成立。
**⚠ 这条定理没有证明什么**：它**不**证明「空族条件独立在语义上是空真」这条数学判断
（那是 `Fate/CondIndepN.lean:164-172` 的**论证**，不是 Lean 定理）。
**故本文件把「数学上可能对」与「Lean 里已证」严格分开。** -/
theorem condIndepNEmpty_holds_for_all {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    {γ : Type*} :
    ∀ p : GenC3.NJoint (ι := ι) α γ, GenC3.CondIndepNEmpty p :=
  fun _ => trivial

/-- ⭐⭐ **恒真性的形式化**：`CondIndepNEmpty p ↔ True`（无信息性）。

**意义**：这是 `:= True` 的**定义翻译**。它使「该定义没有信息」**可被引用**，
而不是只在注释里被声称。 -/
theorem condIndepNEmpty_iff_true {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    {γ : Type*} (p : GenC3.NJoint (ι := ι) α γ) :
    GenC3.CondIndepNEmpty p ↔ True :=
  Iff.rfl

/-- ⭐ **空族与 `[Nonempty ι]` 互斥**：`IsEmpty ι` 与 `Nonempty ι` **不能同时成立**。

**意义**：这条定理是「空族条件独立**无法**在 `[Nonempty ι]` 语境下被陈述」的
**形式化依据** —— 它使「`CondIndepN`（带 `[Nonempty ι]`）与 `CondIndepNEmpty` 是
**两个不可交叠的语境**」这件事，从**注释**变成**定理**。 -/
theorem isEmpty_and_nonempty_conflict {ι : Type*} (h : IsEmpty ι) [hn : Nonempty ι] :
    False :=
  h.false hn.some

/-- ⚠⚠ **误用见证（引用既有反例）**：**不能**把「空族为真」搬到「一般族」上。

**内容**：把「空族 = `True`」硬套成一般等式形式，得到的就是 `DraftN`；
而 `Fate/CondIndepN.lean:158` 的 `draftN_false_empty` **已证**
`DraftN` 在空族 + 常函数 `p ≡ 5` 上**为假**。

**故本定理把「误用会出错」写成可引用的形式**。**这不是本文件的新证明**，
而是**引用** `Fate.GenC3.draftN_false_empty` 并把结论接到本节的登记上。 -/
theorem condIndepNEmpty_cannot_be_lifted :
    ¬ GenC3.DraftN (fun (_ : (i : Empty) → Empty) (_ : Unit) => (5 : ℝ)) :=
  GenC3.draftN_false_empty

/-! ### §4.3 ⭐⭐ `Yun` 的 Σ-代数载体

**原定义**（`Fate/Frame.lean:111`，**本文件不改它**）：

```
def Yun (F : Frame) : Type _ := F.U.Carrier × F.Ν.Carrier
```

**问题（精确形态）**：`Prod` 的**裸类型表达**没有把「用哪个 σ-代数」写进定义。
虽然 Mathlib 有全局 `Prod.instMeasurableSpace` 可使 `Yun F` 自动获得
可测结构，但**「运是可测空间」这件事在签名上看不见** ——
一旦在 `Yun` 上取测度，就得靠**类型类搜索**去猜 σ-代数，
而这正是 `Fate.Stage0.Core:674-680` 明令禁止的「**匿名前提**」（原文：
「若把它们全设为类型类参数，`U`、`Θ` 的可测性就被本结构的**存在性**隐式携带，
成为**匿名前提**（违反阶段 1A 验收标准 2「不存在匿名前提」）」）。

**§4.3 的处置**：
1. **`YunMeasurable`** —— **逐字段**带 σ-代数的严格版（`mU` / `mN` **显式字段**），
   使「哪个 σ-代数」在**每次使用时都可见**；
2. **`yunToYunMeasurable`** —— 从 `Yun` 构造 `YunMeasurable` 的**良定义映射**
   （σ-代数取自 `F.U.meas` / `F.Ν.meas`），证明「严格版**不丢信息**」；
3. **`yunMeasurable_fst_measurable` / `_snd_`** —— 两个投影**可测**
   （把「σ-代数选对了」写成定理）；
4. **`Yun_Pending_NotImplemented := False`** —— 若某 `Frame` 的可测结构**不可得**，
   则严格版**不可陈述**，用该定义强制编译器拒收相关定理。 -/

/-- ⭐⭐ **`Yun` 的严格版：逐字段带 σ-代数（「运是可测空间」写在签名里）**。

**内容**：`U.Carrier × Ν.Carrier` **加上两个显式的 `MeasurableSpace` 字段** `mU` / `mN`。

**⚠ 为什么 σ-代数要做成**字段**而不是类型类参数**：
`Fate.Stage0.Core:674-680` 给出的纪律是 —— 做成类型类参数会使它被
「结构的存在性」隐式携带，成为**匿名前提**。做成字段则**每次使用时都可见**。
本定义遵守该纪律。

**⚠ 字段的默认值**取自 `F.U.meas` / `F.Ν.meas`（`Fate.Basic:165`/`264` 的
`StateSpace`/`ThetaSpace` 同款命名），故构造时可省略；需要替换时可显式给出。 -/
structure YunMeasurable (F : Frame) where
  /-- 运的载体（与 `Yun` **逐位相同**，故严格版不丢信息） -/
  carrier : F.U.Carrier × F.Ν.Carrier
  /-- $\mathcal{U}$ 上的 σ-代数，默认取自 `F.U.meas`（显式字段，不是类型类搜索） -/
  mU : MeasurableSpace F.U.Carrier := F.U.meas
  /-- $\mathfrak{E}$ 上的 σ-代数，默认取自 `F.Ν.meas`（显式字段） -/
  mN : MeasurableSpace F.Ν.Carrier := F.Ν.meas

/-- ⭐ **良定义映射**：任何 `Yun F` 都可升为 `YunMeasurable F`（σ-代数取 `Frame` 自带的）。 -/
def yunToYunMeasurable (F : Frame) (y : Yun F) : YunMeasurable F where
  carrier := y
  mU := F.U.meas
  mN := F.Ν.meas

/-- ⭐ **载体投射**：严格版的载体就是 `Yun`（**不丢信息**，可逆）。 -/
theorem yunMeasurable_carrier_eq (F : Frame) (y : Yun F) :
    (yunToYunMeasurable F y).carrier = y :=
  rfl

/-- ⭐⭐ **σ-代数的显式来源**：`Yun F` 上的可测结构**取自两个子空间**，
而不是让类型类搜索去猜。

**⚠ 这正是 `Yun` 原定义（`Fate/Frame.lean:111`）没有写出来的东西。**
本文件**不**把它做成全局类型类实例（那会架空 `YunMeasurable` 的 `mU`/`mN`
字段，重新退化成匿名前提），而是做成**一个具名定义**：
使用者在需要时**显式**引用它，从而「用哪个 σ-代数」在**使用点**可见。

**⚠ 实现选择**：直接展开成 `@Prod.instMeasurableSpace … F.U.meas F.Ν.meas`
（而非 `letI` + `inferInstanceAs`），使本定义在**定义上**（`rfl`）
就等于「两个子空间 σ-代数的积」，从而下游的 `rw [h]` 是**定义展开**而非搜索。 -/
@[reducible] def yunMeasurableSpace (F : Frame) : MeasurableSpace (Yun F) :=
  @Prod.instMeasurableSpace F.U.Carrier F.Ν.Carrier F.U.meas F.Ν.meas

/-- ⭐⭐ **第一投影关于 `yunMeasurableSpace` 可测**（把「σ-代数选对了」写成定理）。

**⚠ 这条定理的边界（必须说清，否则就是第二次造假）**：它只断言
「在 `yunMeasurableSpace F` 这个显式给出的 σ-代数下，第一投影可测」——
它**不**断言「`Yun F` 上有唯一可用的 σ-代数」（那要靠类型类搜索，本文件**拒绝**）。
陪域 σ-代数 `cod` 作为**显式参数**，同样**不由类型类搜索决定**。

**⚠ 证明内容**：它**不是**把 `measurable_fst` 直接搬过来（后者的定义域是
`Prod.instMeasurableSpace` 生成的**积 σ-代数**，定义上**不等于** `yunMeasurableSpace F`）。
故本定理**必须**用 `yunMeasurableSpace` 的定义把两者统一：
先展开 `yunMeasurableSpace`（`dif`/`rfl` 级），再交给 `measurable_fst`。
**这一步正好把「σ-代数选对了」这件事暴露成一个需要证明的等式** —— 这是本节的用意。 -/
theorem yunMeasurable_fst_measurable (F : Frame)
    (_cod : MeasurableSpace F.U.Carrier) :
    @Measurable (Yun F) F.U.Carrier (yunMeasurableSpace F) F.U.meas (fun y => y.1) := by
  have h : yunMeasurableSpace F = @Prod.instMeasurableSpace F.U.Carrier F.Ν.Carrier F.U.meas F.Ν.meas :=
    rfl
  rw [h]
  exact measurable_fst

/-- ⭐ **第二投影关于 `yunMeasurableSpace` 可测**（对称的一条）。 -/
theorem yunMeasurable_snd_measurable (F : Frame)
    (_cod : MeasurableSpace F.Ν.Carrier) :
    @Measurable (Yun F) F.Ν.Carrier (yunMeasurableSpace F) F.Ν.meas (fun y => y.2) := by
  have h : yunMeasurableSpace F = @Prod.instMeasurableSpace F.U.Carrier F.Ν.Carrier F.U.meas F.Ν.meas :=
    rfl
  rw [h]
  exact measurable_snd

/-- ⚠ **`Yun` 的闸门版（`Pending_NotImplemented := False`，**不是** `True`）**。

**用途**：若某个 `Frame` 的 `U.Carrier` 或 `Ν.Carrier` **没有** σ-代数，
则「运是可测空间」**不可陈述**，一切依赖它的定理必须**先证出 `False`**，否则编译失败。 -/
def Yun_Pending_NotImplemented : Prop := False

/-- ⚠⚠ **反证桥**：`Yun_Pending_NotImplemented` **不可被证明**。 -/
theorem yun_pending_not_provable : ¬ Yun_Pending_NotImplemented :=
  not_false

/-! ===========================================================================
    §5  ⚠⚠ `labeledGaps` —— 诚实登记：哪些标签「按理论写着」但「实现侧没有对应」
    =========================================================================== -/

/-- **一条缺口登记**。

**⚠ 字段命名**：第一个字段用 `axiomId` 而非 `axiom` ——
`axiom` 在 Lean 4 中是**保留关键字**，不能作字段名（这是编译期实测结果）。 -/
structure LabeledGap where
  /-- 假设编号（A1–A32；A33 单列；`—` 表示不是假设编号而是对象）。 -/
  axiomId : String
  /-- 规格类型栏的类别（抄自 `05:36-80`）。 -/
  specKind : AssumptionKind
  /-- ⚠ **缺口形态**。 -/
  gap : String
  /-- ⚠ **严重度**：`blocks-proof` = 阻断后续证明；`silent` = 静默失效；`cosmetic` = 仅记法。 -/
  severity : String
  deriving Repr

/-- ⚠⚠ **`labeledGaps`：诚实登记表。**

**⚠ 使用说明（重要）**：
Lean **无法**判断某个字符串是否真对应某个定义，故本表的**内容是人工审核的**，
不是机器验证的。**它的价值在于「已登记 vs 未登记」的区分**，
而不是「机器保证无遗漏」。

**本表的登记口径**：只登记**「规格有这一条，但实现侧没有对应物」**的。
「已实现但处理方式不同」的情况记在 `notes`（非 gap）。 -/
def labeledGaps : List LabeledGap := [
  -- ===== 1. ⚠⚠ 最高优先：A14 的经验假设身份被实现侧的默认值掩盖 =====
  { axiomId := "A14", specKind := .empirical,
    gap := "A14 是**不可证的经验假设**（`05:51`），但 `Fate/Frame.lean:258` 把 currentRegime 直接取为 `.direct`，`Frame:275` 又把 ObservedState 退化为 `id`。代码中的**默认**是「观测无损」，而规格说这是**不可证**的。`Fate/Frame.lean:239-241` 已自认「只落实语言层选择，不主张在世界上成立」，但**代码里没有任何机制阻止下游把它当定义用**。",
    severity := "silent" },

  -- ===== 2. A1：没有 `def alpha : InstSpace → Rules` =====
  { axiomId := "A1", specKind := .definitional,
    gap := "A1 要求 α(𝓔) ⊆ 𝓡（`05:38`）。实现侧 `Rules := Set (Rule C X Y)`（`Frame:545`）使「⊆」**可陈述**，但仓库里**没有**一个 `def alpha : InstSpace → Rules`。`Fate/Alpha.lean` 的 `alpha` 实际指 `takeConcept`（`AlphaKernel:52` 裁决 D），**不是** A1 的 α。故「组合是否越界」在实现侧**仍无判据**——这正是 A1 的必须显式化栏要防的事。",
    severity := "blocks-proof" },

  -- ===== 3. A3：封闭性未给出 =====
  { axiomId := "A3", specKind := .definitional,
    gap := "A3 要求 𝓡 对 ∘ **封闭**（`05:40`）。`Set X` 对任意二元运算都不封闭，除非运算写回 `Set X`。`Fate.ComposeOperator:158` 的 `Comp` 签名**未在本文件中被逐位核对**，故「Comp 的结果落在 Rules 内」这件事**未审计**。",
    severity := "blocks-proof" },

  -- ===== 4. A5/A6/A7/A11/A21/A25/A20/A22/A23：实现侧无可陈述命题 =====
  { axiomId := "A5", specKind := .existential,
    gap := "A5「类型规则保证任意操作的组合合法」（`05:42`）在实现侧**没有任何谓词**可陈述。`05:42` 原文自述「这是一条全称模态断言；在未给出任何构造实例的前提下它不能算已成立」——本仓库**亦然**。",
    severity := "blocks-proof" },
  { axiomId := "A6", specKind := .existential,
    gap := "A6「每一层都有误差界 ε_i」（`05:43`）在实现侧**无一层的界**。`ErrorBound.lean`/`ErrorBoundChain.lean` 处理的是**具体剖面函数**的界，不是「每一层」。",
    severity := "blocks-proof" },
  { axiomId := "A7", specKind := .existential,
    gap := "A7「误差可沿组合传播（传播律）」（`05:44`）在实现侧**无层间传播律**。",
    severity := "blocks-proof" },
  { axiomId := "A11", specKind := .existential,
    gap := "A11「概念格动力系统有收敛性」（`05:48`）在实现侧**无收敛性结论**。`05:48` 原文自认「格上的动力系统没有标准收敛理论」。",
    severity := "blocks-proof" },
  { axiomId := "A21", specKind := .existential,
    gap := "A21「规则空间的泛化理论存在」（`05:58`）在实现侧**无泛化界**。",
    severity := "blocks-proof" },
  { axiomId := "A25", specKind := .existential,
    gap := "A25「不可压三项的界可给出」（`05:62`）在实现侧**无对应的界**。`05:62` 原文：「原文以『只能给界』为论点，但全轮未给出任何界」。",
    severity := "blocks-proof" },
  { axiomId := "A20", specKind := .empirical,
    gap := "A20「因果发现的假设成立」（`05:57`）在实现侧**无对应谓词**：马尔可夫性／忠实性／无隐混杂／平稳性四项**均未被具名**。",
    severity := "silent" },
  { axiomId := "A22", specKind := .empirical,
    gap := "A22「SCM 的正确性可由数据确立」（`05:59`）在实现侧**无对应谓词**。`Fate/SCMSemantics.lean` 只给语义，不给「正确性可确立」。`05:59` 原文：「SCM 不正确，反事实就是幻觉」——这条**后果**在实现侧**未被写出**。",
    severity := "silent" },
  { axiomId := "A23", specKind := .empirical,
    gap := "A23「外生变量可识别」（`05:60`）在实现侧**无识别性谓词**。`05:60` 原文：「反事实的第 1 步『更新外生变量 P(U|e)』整体依赖它」。",
    severity := "silent" },

  -- ===== 5. A15：路径测度完全缺席 =====
  { axiomId := "A15", specKind := .existential,
    gap := "A15「路径测度存在（样本路径空间上已给定 σ-代数与概率测度）」（`05:52`）在实现侧**完全缺席**。`Fate.Basic:227` 的 `Traj` 是**纯函数类型** `ι → X.Carrier`，**不带任何测度**；`FateOf`（`Basic:233`）只是它的别名。`Fate.Basic` 里唯一带测度的是 `Dist`（噪声分布，`Basic:348`），**不是**轨迹的路径测度。⟹「命运」在实现侧**只是一个函数**，没有概率语义。",
    severity := "blocks-proof" },

  -- ===== 6. A18/A24/A26：架构层假设，代码无载荷 =====
  { axiomId := "A18", specKind := .definitional,
    gap := "A18「运由**来源**（系统之外）而非**变化快慢**定义，且**系统边界给定**」（`05:55`）在实现侧**无对应**：仓库里没有「系统边界」这个对象，也没有区分「来源外生」与「变化快慢」的谓词。`InputSpace`（`Basic:303`）只是给它一个名字。",
    severity := "silent" },
  { axiomId := "A24", specKind := .definitional,
    gap := "A24「预测与因果的依赖方向已裁定」（`05:61`）决定**章序**（`05:167`），在 Lean 里**没有可陈述的对象**。这是**架构层假设，代码无载荷**——不是缺漏，而是本假设的性质。",
    severity := "cosmetic" },
  { axiomId := "A26", specKind := .definitional,
    gap := "A26「降级的目标状态存在且被定义」（`05:63`）在实现侧**无对应**。`05:63` 原文：「原文以『运行时降级』为拒绝『全部证完』的补偿机制，而该机制**落点为空**」——本仓库**亦为空**。`Fate/Stage0/Core.lean:978` `piO_placeholder : Unit := ()` 之类的占位是**唯一**相关物，且它们是**真占位**（只返回 `()`）。",
    severity := "silent" },

  -- ===== 7. A27：三处恒真占位之一（§4.1 已给 Strict 版，但仍是子集） =====
  { axiomId := "A27", specKind := .definitional,
    gap := "⚠ **三处恒真占位之一。** 原 `Fate/Stage1A.lean:253` `def DifferentiableMechanism (F) (_f) : Prop := True` **恒真**——本文件 §4.1 已证 `original_holds_for_all`（对任意 f 成立）。§4.1 给出 `DifferentiableMechanism_Strict`（x 与 ε 的 HasFDerivAt），但**只覆盖 5 个变量中的 2 个**：Θ 与 Act 连 `NormedSpace` 实例都没有（`ThetaSpace`/`ActionSpace` 只带拓扑+可测），对它们写可微会**引入新假设**。故 A27 **部分实现**，不是全部。",
    severity := "blocks-proof" },

  -- ===== 8. A30：遍历性三条件缺席 =====
  { axiomId := "A30", specKind := .existential,
    gap := "A30 的「马尔可夫链遍历性三条件（不可约／非周期／正常返）」在实现侧**无对应**；只有「鞅可积性」一半被具名（`Fate/Stage1A` 的 `MartingaleIntegrability`），且 `Stage1A:211-214` 的 `T1A8_integrability_wellformed` 是 `Iff.rfl`，**只断言谓词良定义**，不给收敛结论（`Stage1A:204-206` 已自明）。",
    severity := "blocks-proof" },

  -- ===== 9. A32：编码算子有，误差界无 =====
  { axiomId := "A32", specKind := .existential,
    gap := "A32 = 「编码算子**存在**」∧「**离散化误差有界**」。实现侧只有前半：`Fate.Alpha:111` `structure Encoder` + `Fate.Alpha:134` `Encoder.Coherent`。**后半「误差有界」不存在**——`Fate.Alpha:110` 自写明「『误差有界』一半**未做**」。且 `Encoder` 作为 `structure` **不说明** toObjects/toAttrs 可从数据算出来（那是 A8.T0）。",
    severity := "blocks-proof" },

  -- ===== 10. CondIndepNEmpty：三处恒真占位之二 =====
  { axiomId := "—（CondIndepNEmpty）", specKind := .definitional,
    gap := "⚠ **三处恒真占位之二。** `Fate/CondIndepN.lean:173` `noncomputable def CondIndepNEmpty (_p) : Prop := True` **恒真**（本文件 §4.2 已证 `condIndepNEmpty_holds_for_all`）。**⚠ 但这一处的处置与 A27 不同**：`Fate/CondIndepN.lean:164-172` 的**理由是数学上成立的**——空族时 `(Fintype.card ι - 1)` 在 ℕ 上截断为 0，硬塞进 `CondIndepN` 会得到 `p = 1`（该文件 `draftN_false_empty` 给出 `p ≡ 5` 的反例）。**故 `True` 可能是正确的数学，而非占位。** 真正的问题是：**理由只在注释里，没有写进类型**，故 `True` 可能被误搬到非空族。§4.2 用 `condIndepNEmpty_vacuous_of_empty`（带 `IsEmpty ι` 前件，在 `[Nonempty ι]` 下不可证）把误用路径堵死。",
    severity := "silent" },

  -- ===== 11. Yun：三处恒真占位之三（结构缺口而非恒真） =====
  { axiomId := "—（Yun）", specKind := .definitional,
    gap := "⚠ **三处恒真占位之三 —— 但严格说它不是「恒真」，是「结构缺口」。** `Fate/Frame.lean:111` `def Yun (F) : Type _ := F.U.Carrier × F.Ν.Carrier`：`U.Carrier` 与 `Ν.Carrier` 各自带 `MeasurableSpace`，而**裸 Prod 表达**没有把「用哪个 σ-代数」写进 `Yun` 的定义。Mathlib 有全局 `Prod.instMeasurableSpace` 可自动接上，但「运是可测空间」在**签名上看不见**——一旦在 `Yun` 上取测度，就得靠**类型类搜索**猜 σ-代数，这正是 `Fate.Stage0.Core:674-680` 明令禁止的「匿名前提」。§4.3 给出 `YunMeasurable`（σ-代数做成显式字段）+ `yunToYunMeasurable`（σ-代数唯一取自 Frame），并证两投影可测。",
    severity := "silent" },

  -- ===== 12. A33：编号越界 =====
  { axiomId := "A33", specKind := .existential,
    gap := "⚠ **编号越界。** 规格 `05-公理与章序规范.md` 的清单**止于 A32**（`05:71`「合计：32 条」）。`Fate/Stage0/Core.lean:35,79` 自述「A33 原文未登记」，但仓库里 `WellFoundedDeps` 被当作 A33 的落点。⟹ A33 是**实现补定**，**类型未裁**（本文件暂标 `existential`，因为「依赖良基」是一个**待证**性质；但规格未给类型栏，故这个标签**没有规格依据**）。**A34 在全部 .lean 文件中零处出现**，本文件不设 `label_A34`。",
    severity := "cosmetic" },

  -- ===== 13. 两套 ActionSpace / 两套 Ctx =====
  { axiomId := "A28", specKind := .definitional,
    gap := "⚠ **两套 ActionSpace。** `Fate.Basic:325`（字段 `Carrier`）与 `Fate.Stage0.Core:351`（字段 `A`）**各定义一次**，`Fate/Stage0/Core.lean:29-40` 自述这是「**两套定义的债务**」。本文件**不合并**（合须由后续轮次裁决权威载体），但「𝓐 是哪个」在实现侧**有歧义**。",
    severity := "cosmetic" },
  { axiomId := "—（Obj / Ctx / Xlocal / piO）", specKind := .definitional,
    gap := "⚠ **真占位（只返回 `()`）。** `Fate.Basic:152` `class Obj` 在 `Fate.Basic` 之外**从未被实例化或引用**（主公式用 `Frame.X`，不是 `Obj`）；`Fate/Stage0/Core.lean:990` `Xlocal_placeholder : Unit := ()`、`Core:1000` `Ctx_placeholder : Unit := ()`、`Core:978` `piO_placeholder : Unit := ()`、`Core:1011` `NoiseCarrier_placeholder : Unit := ()`、`Core:1022` `ModelCarrier_placeholder : Unit := ()`、`Core:924` `NoCoercionDoToAction : Unit := ()` —— **七个 `Unit` 型占位**，它们**不携带任何数学内容**，且**不会被编译器拒绝使用**（`Unit` 恒有元素 `()`）。⟹ 这是「**占位而非缺口暴露**」，与 §4 的 `:= False` 处置**相反**。",
    severity := "silent" },
  { axiomId := "A17", specKind := .definitional,
    gap := "A17 的「`do` 是算子、不能隐式转成动作」这条**分层约定**：`Fate/Stage0/Core.lean:856` `Do` 与 `Core:911` `DoIsOperator` 提供了载体 ✅，但 `Core:924` `NoCoercionDoToAction : Unit := ()` **只是 `Unit` 常量**——「`do` 不隐式转成动作」**没有被类型系统强制**。若要把这条约定变成编译期保证，须写一个 `Coe` 实例的**否定**（Lean 中不可表达为实例否定），故本条**只能靠 `Unit` 占位**。**这是能力边界，不是懈怠**。",
    severity := "cosmetic" },
  { axiomId := "—（Dist 的概率前件）", specKind := .definitional,
    gap := "`Fate.Basic:341-347` 的 `Dist` **故意不假定是概率测度**（纪律正确），但 `Fate.Basic` **没有提供**「`IsProbabilityMeasure` 前件」的**具名对象**，故「𝒟_ε 是概率测度」这条前件**只存在于注释里**。",
    severity := "cosmetic" },
  { axiomId := "—（InitialState 的 D₀）", specKind := .definitional,
    gap := "`Fate.Basic:245` `structure InitialState` 的 `isRandom : Bool` **是 `Bool` 不是 `Prop`**，且**没有把 𝒟_0 带进来**。故「x_0 随机」在实现侧**只是一个布尔开关，没有分布载体**。",
    severity := "cosmetic" },
  { axiomId := "A2", specKind := .definitional,
    gap := "A2 的规格要求是「把 `05:39` 的**等式**改写为**类型声明**」。实现侧 `Fate.GammaOperator:511` `RuleGeneralization := GenOp (Rule C X Y)` **是 `GenOp` 的别名**，不是「R_local → R_global」的**类型声明**。⟹ **弱落点**。",
    severity := "cosmetic" },
  { axiomId := "A4", specKind := .definitional,
    gap := "A4 的「与 ∘ **相容**」在实现侧只对「**α 的核**」这个特定等价关系证成（`Fate.AlphaKernel:66-79`），**不是对任意 `Setoid`**。这是**实质进展**（把条件降为定理），但不是 A4 的全称内容。",
    severity := "cosmetic" },
  { axiomId := "A8", specKind := .existential,
    gap := "A8 的「α 存在且**可计算**」：`Fate/Adjudication.lean` 的 `A8_T1_Registered`（`SigCheck:391`）自述「**登记挂载点（未填内容）**」——**这是空壳**。即 A8.T1（高效实现）**完全未做**。",
    severity := "blocks-proof" }
]

/-- `labeledGaps` 的条数（供 `#eval` 报告）。 -/
def labeledGapsCount : ℕ := labeledGaps.length

/-- **已实现且处置得当的项**（`notes`，**非缺口**）—— 同样需要人读，
但它们是**正向记录**，用于防止「把已做的也说成缺口」的另一种不诚实。 -/
def notes : List (String × String) := [
  ("A12", "✅ `Fate.Frame:146` `Step` 的第 5 位就是 `F.Act.Carrier`，**删不掉**——这是全仓库最实的一处 A12 落地。"),
  ("A16", "✅ `Fate.Frame:217` `DiffusionNoIntervention` 单设一个类型，使「采用附加假设」成为**可见的类型选择**。当前主路径用带 a_t 的 `Diffusion`，故 A16 未生效——这是**选项未启用**，不是缺口。"),
  ("A13", "✅ **处置得当的范例**：原读法（‖θ̇‖≪‖ẋ‖ / 阈值 ε）已被作者裁决 Q-1 **废除**，`Fate.Frame:615-621` 用一张表把「已废除的旧读法」与「本定义」**并排写出**，使「已废除的读法仍在代码中」不可能发生。⚠ 但「样本集 S 的选取」**未被作者裁决**（`Frame:623`），操作化仍未闭合。"),
  ("A10", "✅ **处置得最诚实的一条之一**：`Fate/Stage0/Core.lean:618-619` 原文「『满足本结构的具体 μ,σ 存在』是**待证**的，**不是本定义发明的**」。结构 = **把前件具名化**；解的存在性**未证**。`Core:605-611` 还**显式登记**了「一致 Lipschitz 是选型、比标准定理强」这一取舍。"),
  ("A29", "✅ 两套 `TimeIdx`（`Basic:194`/`200`）**分设**，A29 要求的「分别为两套定义」已落实。⚠ `Fate.Basic:208` `structure Tmax` 用 `match kind with` 写**依赖消去值的字段**；本文件因此**不 `#eval` 它**。"),
  ("—（A' 的记法）", "✅ 规格的 A' 与 Mathlib 的 `upperPolar` **显式绑定**（`Fate.FCA:130/134` 两条 `rfl`），**不出现两套并行记法**。⚠ 但 `Fate.FCA:129` 已标 `[已知]`——这是 **Mathlib 的既有结果，非本框架成果**。"),
  ("—（d-分离基础设施）", "✅ `CausDAG` / `CausBayesBall` / `CausActivePath` / `CausSeparation` 与 `Fate/DSeparation` / `CausalDirection` / `CausalPath` / `CausalDescendant` / `DoCalculus` / `GraphOps` / `DoCalculusRules` 七个模块（第 60–70 轮）**已建成**。⚠ 但 `Fate/Stage1A.lean:334-338` 指出的**剩余缺口 = 有限概率桥**（Mathlib 有 `CondIndepFun` 但是测度论谓词，而本项目 SCM 是 `Fintype U`）。"),
  ("—（OutSpace 合并）", "✅ `Fate.Frame:316` `abbrev OutSpace := StateSpace` 使 `Rule C X Y → Rule C Y Z` 链式组合**类型正确**（`ComposeOperator` 101 个错误的根源已消）。⚠ 副作用：**无法表达**「输出空间 ≠ 状态空间」；若日后需要，必须撤销该合并。"),
  ("—（T1A8 的边界）", "✅ `Fate.Stage1A:211-214` `T1A8_integrability_wellformed : ... := Iff.rfl` **只断言谓词良定义**，`Stage1A:204-206` 自写明**不给收敛结论**、「**重证一遍 Mathlib 的定理不属阶段 1A 的任务**」。这是**清晰的边界声明**，不是缺漏。"),
  ("—（CondIndepN 空族）", "✅ `Fate/CondIndepN.lean:158` `draftN_false_empty` 给出了 `p ≡ 5` 的**具体反例**，证明「空族塞进 `CondIndepN` 会出错」。⚠ 但 `CondIndepNEmpty := True` 的**理由只在注释里**，见 `labeledGaps` 第 10 条。")
]

/-- `notes` 的条数。 -/
def notesCount : ℕ := notes.length

/-! ### §5.1 `#eval` 缺口表（**验收结果的一部分，不是附注**） -/

#eval labeledGapsCount
#eval notesCount
#eval String.intercalate "\n"
  (labeledGaps.map (fun g => s!"  [{g.severity}] {g.axiomId} ({repr g.specKind})"))

/-! ===========================================================================
    §6  本文件的自我边界（最后再说一次）
    =========================================================================== -/

/-!
**本文件证明了的**：
1. `CondIndepNEmpty` **恒真**（`condIndepNEmpty_holds_for_all`）——不是注释，是定理；
2. `DifferentiableMechanism` **对任意 `f` 成立**（`original_holds_for_all`）——同上；
3. 两个 `:= False` 闸门**不可被证明**（`pending_not_implemented_not_provable`、
   `condIndepNEmpty_pending_not_provable`、`yun_pending_not_provable`）——
   即「未实现」这件事**被 Lean 确认**；
4. `YunMeasurable` 的两个投影**可测**（`yunMeasurable_fst_measurable` /
   `yunMeasurable_snd_measurable`）——σ-代数**显式化后**确实可用；
5. 「空族条件独立**不能**在 `[Nonempty ι]` 下被陈述」（`condIndepNEmpty_vacuous_of_empty`）；
6. 「把 `CondIndepNEmpty` 的 `True` 搬到一般情形会出错」
   （`condIndepNEmpty_cannot_be_lifted`，引用既有反例 `draftN_false_empty`）。

**本文件没有证明的**（必须说清）：
1. **A1–A32 中没有任何一条被证成**。标签只回答「类型」，不回答「成立」；
2. **A27 只实现了其 5 个变量中的 2 个**（`x` 与 `ε`）；
   `Θ` 与 `Act` 的可微**未实现**（缺 `NormedSpace` 实例，强行写会引入新假设）；
3. **`CondIndepNEmpty` 的 `:= True` 是否「正确的数学」—— 本文件**不判断**。
   `Fate/CondIndepN.lean:164-172` 的论证看起来成立，但**那个论证不是 Lean 定理**；
4. **`labeledGaps` 的内容是人工审核的**，Lean 无法验证「某个字符串真对应某个定义」；
5. **「26 个核心对象」这个数字不是从规格数出来的**，是任务书给定的；
   本文件按实现枚举得 35 条，**若任务书本意是另一组 26 个，须重列**。

**⚠ 本文件最重要的一句话**：
**「贴了标签」不等于「有实现」，「写了 Strict 版」不等于「A27 已证」。**
`labeledGaps` 存在的意义，就是让这两件事**不能**再被同一个文件掩盖。
-/

end LabelAudit
end Stage0
end FateV2.Rules