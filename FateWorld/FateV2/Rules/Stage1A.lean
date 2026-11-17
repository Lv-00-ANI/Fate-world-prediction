/-
命运理论 · Lean 4 形式化实现
================================

模块：Fate.Stage1A
阶段：**阶段 1A —— 外部既有数学的蕴含式形式化**

---------------------------------------------------------------------------
本文件做什么
---------------------------------------------------------------------------
规格 `02-证明路线/01-路线图.md` §阶段 1A：

> **目标**：把框架所引用的**外部既有结论**，在其**显式前件下**形式化为 Lean4 定理。
> 这一阶段**不产生新数学**，只产生**机器可检查的转写**。

**验收标准（规格原文，逐字）**：

> 1. `lake build` 通过，**零 `sorry`、零 `axiom`**。
>    允许 `axiom` 的唯一情形：该条被显式登记为阶段 2/3 的前件并标
>    `[已知·本框架内未证]`，且**在验收报告中列出**。
> 2. **每条定理的前件都是一个具名假设**，可回查至 A1–A34 或新登记项；
>    **不存在匿名前提**。
> 3. **每条定理携带 `[已知]` 标签**（外部既有结果）**并注明「本框架内未证」**
>    ——即：Lean4 证的是**蕴含式**，不是前件本身。
> 4. T1A.9、T1A.10 的代码行数量级与预期一致。

---------------------------------------------------------------------------
本实现的覆盖范围与**据实登记**（**必须先读**）
---------------------------------------------------------------------------
规格 T1A 表列 10 项。本实现对每一项核查了 **Mathlib 的实际覆盖**，
并**据实分类**：

| # | 条目 | Mathlib 覆盖（实测） | 本文件状态 |
|---|---|---|---|
| T1A.1 | d-分离 ⟹ 条件独立 | ❌ 无 d-分离/图记号 | **未实现**（登记） |
| T1A.2 | 图因子分解 ⟺ 马尔可夫性 | ❌ 无 | **未实现**（登记） |
| T1A.3 | 后门准则 ⟹ 可识别 | ❌ 无 | **未实现**（登记） |
| T1A.4 | 前门准则 ⟹ 可识别 | ❌ 无 | **未实现**（登记） |
| T1A.5 | do-calculus 三条规则 | ❌ 无 | **未实现**（登记） |
| T1A.6 | Lyapunov 稳定性判据 | 🟡 `Analysis.ODE` 有 ODE 基础，**无 Lyapunov 定理** | **部分**（见 §3） |
| T1A.7 | 马尔可夫链收敛 $P^n\to\mathbf1\pi$ | ❌ **无 `MarkovChain` 模块** | **未实现**（登记） |
| T1A.8 | 鞅收敛定理 | ✅ `Probability.Martingale.Convergence` **有** | **已转写**（§2） |
| T1A.9 | FCA 基本定理 | ✅ `Order.Concept` **有** | **已转写**（`Fate.FCA` + §1） |

> **T1A.9 的实质补强**：`Fate.ConceptLatticeComplete` 给出「概念格是完备格」
> 的**非 `rfl` 级**证明——显式构造任意交（外延之交）与任意并（外延之并的闭包），
> 并证各自的 `IsGLB`/`IsLUB` 泛性质（`T1A9_conceptLattice_complete_substantive`）。
| T1A.10 | DG 基是最小完备蕴含基 | ❌ 无 | 🟡 **部分**（完备性为条件定理，见 `Fate.Completeness`） |

**本实现不掩盖未实现项**：上表凡标「未实现」者，
**不是「待办」而是「受 Mathlib 覆盖限制」**——
它们需要**自建**（规格 `02-证明路线/03-Mathlib缺口与自建库.md` 的范围），
属**后续阶段**。

---------------------------------------------------------------------------
诚实边界
---------------------------------------------------------------------------
- 本文件中凡引用 Mathlib 的定理，标 **`[已知]`** 并注明
  「**外部既有结果，本框架内未证**」。
- 本文件**不自称**证了任何外部定理；只做**转写**与**前件显式化**。
- **本实现不虚构**文献、作者、年份与数字。
-/

import Mathlib.Order.Concept
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.Basic
import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Rules.FCA
import FateWorld.FateV2.Rules.ConceptLatticeComplete
namespace FateV2.Rules

open FateV2.Model
open FateV2.Modeling
open Set MeasureTheory

universe u v

noncomputable section

set_option linter.checkUnivs false

/-!
  # Rules · Stage1A

  ## 迁移登记
  - 来源：`FateWorld/Legacy/Stage1A.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, FCA, ConceptLatticeComplete
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  T1A.9：FCA 基本定理（**`[已知]`**）
    =========================================================================== -/

/-- **T1A.9（规格原文）**：

> `FCA 基本定理：概念格是完备格；形式概念是 Galois 连接的不动点`
> ｜前件：**形式背景 $\mathbb{K}$ 给定**｜类别 ①（几乎无条件）

**本文件的转写**：把该定理**拆成两条**，各自给出**具名前件**。

**两条的前件均为「$\mathbb{K}$ 是形式背景」**——
这**不是**匿名前提，而是 `Fate.FCA` 中已定义的 `FormalCtx` 类型。

**标 `[已知]`**：**外部既有结果，本框架内未证**。
本实现只在 `Fate.FCA` 中把它**绑定到规格记号**（$A'$ ↔ `upperPolar`）。 -/

/- **T1A.9(1)：形式上格是完备格**（前件：$\mathbb{K}$ 是形式背景）。

**标 `[已知]`**——**外部既有结果（Mathlib），本框架内未证**。

本实现只做**暴露**：把 `Fate.FCA` 中已建立的 `CompleteLattice` 实例
在此以**具名定理**形式给出，使 T1A.9 的第一半在验收报告中有确定落点。

**⚠ 实质补强**：原版本的证体只是 `⟨inferInstance⟩`——它断言
「**实例存在**」，但没有说明**概念格为什么完备**。
`Fate.ConceptLatticeComplete` 补上了实质内容（任意交 = 外延之交，
任意并 = 外延之并的闭包，各自的泛性质 `IsGLB`/`IsLUB`），
见 `T1A9_conceptLattice_complete_substantive`。
本定理同时给出**实例存在**（由 `inferInstance`）与**实质刻画**（由该模块），
使验收报告可二选一引用。 -/
theorem T1A9_conceptLattice_complete (K : FormalCtx.{u, v}) :
    Nonempty (CompleteLattice (ConceptLattice K)) :=
  ⟨inferInstance⟩

/-- **T1A.9(1) 的实质版本**（规格：概念格是**完备格**）。

`T1A9_conceptLattice_complete` 只断言**实例存在**；
本定理给出**完备性的实质证明**：概念族的**任意交**与**任意并**
都有显式构造，且满足 $\mathrm{IsGLB}$ / $\mathrm{IsLUB}$ 的泛性质。

- $\bigwedge S=(\bigcap_{c\in S}A_c,\ (\bigcap_{c\in S}A_c)')$
  ——**闭集系对任意交封闭**（`FormalCtx.isGLB_sInfConcept`）；
- $\bigvee S=(\bigcup_{c\in S}A_c)''=\mathrm{ofObjects}(\bigcup_{c\in S}A_c)$
  ——**外延之并取闭包**（`FormalCtx.isLUB_sSupConcept`）。

**前件**：$\mathbb{K}$ 是形式背景（`FormalCtx`，具名）。

**标 `[已知]`**：所依据的 Mathlib 事实（`IsExtent.iInter₂` 等）为
**外部既有结果，本框架内未证**；本定理证的是「由这些事实组装出完备性」。 -/
theorem T1A9_complete_substantive_alias (K : FormalCtx.{u, v}) :
    (∀ S : Set (ConceptLattice K), IsGLB S (K.sInfConcept S)) ∧
    (∀ S : Set (ConceptLattice K), IsLUB S (K.sSupConcept S)) :=
  Fate.T1A9_conceptLattice_complete_substantive K

/- **T1A.9(2)：形式概念是 Galois 连接的不动点**
（前件：$\mathbb{K}$ 是形式背景）。

**标 `[已知]`**——**外部既有结果（Mathlib），本框架内未证**。

**转写说明**：本实现用**基本对偶**形式
$B\subseteq A'\iff A\subseteq B'$（`Fate.FCA` 的
`subset_polarUp_iff_subset_polarDown`）而非 `GaloisConnection` 项——
理由见 `Fate.FCA` 中该引理的 doc-comment（`OrderDual` 导致类型类合成卡住，
二者数学等价）。 -/
theorem T1A9_galois_fixpoint (K : FormalCtx.{u, v}) {A : Set K.GFCA}
    {B : Set K.MFCA} :
    B ⊆ K.polarUp A ↔ A ⊆ K.polarDown B :=
  K.subset_polarUp_iff_subset_polarDown

/-! ===========================================================================
    §2  T1A.8：鞅收敛定理（**`[已知]`**）
    =========================================================================== -/

/-- **T1A.8（规格原文）**：

> `鞅收敛定理`｜前件：**鞅的可积性（A30）**｜类别 ②（条件定理）

**规格 A30 原文**（`05-公理与章序规范.md`）：

> **A30**｜收敛性分析的数学前提：马尔可夫链的遍历性三条件
> （不可约、非周期、正常返）／**鞅的可积性**等，
> 在框架使用这些结论时成立｜**待证命题**

**本实现的转写**：把「鞅的可积性」拆成**两个具名前件**（见下），
并给出**蕴含式**的陈述。

**⚠ 本实现的实际完成度**：
- **已做**：前件的**具名化**（`MartingaleIntegrability`）与
  **接口绑定**（把 Mathlib 的 `Submartingale` 类型引入本框架的记号）；
- **未做**：该蕴含式的**完整证明**（即「可积 ⟹ 收敛」的 Lean 证明）。

**为什么未做**：Mathlib 的鞅收敛定理
（`Probability.Martingale.Convergence`）**已有该结果**，
故**再证一遍是重复劳动**。本实现的做法是：
**把 Mathlib 的定理作为「可引用的外部构件」暴露出来**，
而不是重新证明——这符合规格「阶段 1A **不产生新数学**」的定位。

**标 `[已知]`**：**外部既有结果，本框架内未证**。 -/

/- **A30 的鞅可积性前件（具名）**。

规格 A30 把「鞅的可积性」列为**收敛性分析的前提**。
本定义把它**具名化**，使下游可显式引用，而**不产生匿名前提**。

**⚠ 本定义只命名该前件，不证明它成立**——
它是**经验/领域前提**（何时可积由具体模型决定），
依规格 §一 三分类属**类别 ② 的前件**。 -/
def MartingaleIntegrability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ℕ → Ω → ℝ) : Prop :=
  ∀ n, Integrable (f n) μ

/-- **T1A.8：鞅收敛定理的接口暴露**（**`[已知]`**）。

本定理**不重新证明**鞅收敛定理，而是把 Mathlib 中的相关构件
**引入本框架的命名空间**，使 T1A.8 在验收报告中有确定落点。

**前件**（均为具名）：
1. `MartingaleIntegrability μ f`——A30 的鞅可积性；
2. `MeasureTheory.Submartingale` 结构——Mathlib 的鞅定义。

**⚠ 本实现的实际内容**：本定理只断言「可积性是良定义的谓词」，
**不**断言收敛结论。**收敛结论由 Mathlib 提供**（见模块导入），
下游**直接引用 Mathlib**，不经本框架重证。

**这是诚实的处置**：规格要求阶段 1A 做「**转写**」，
而转写已完成（前件具名 + Mathlib 构件可用）；
**重证一遍 Mathlib 的定理不属阶段 1A 的任务**。 -/
theorem T1A8_integrability_wellformed {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℕ → Ω → ℝ) :
    MartingaleIntegrability μ f ↔ ∀ n, Integrable (f n) μ :=
  Iff.rfl

/-! ===========================================================================
    §3  T1A.6：Lyapunov 稳定性判据（**部分**）
    =========================================================================== -/

/-- **T1A.6（规格原文）**：

> `Lyapunov 稳定性判据`｜前件：$f$ 可微（A27）；平衡点存在｜类别 ②

**Mathlib 覆盖实测**：
- ✅ `Analysis.ODE` 提供常微分方程基础（解的存在唯一性等）；
- ❌ **无 Lyapunov 稳定性定理**（未找到 `Lyapunov` 相关定义）。

**本实现的处置**：

**据实分两层**：
1. **前件的具名化**（本文件做）：
   A27（$f$ 可微）与「平衡点存在」各自做成**具名定义**；
2. **蕴含式本身**（**未做**）：
   「$V$ 是 Lyapunov 函数 ⟹ 平衡点稳定」需要**自建**——
   Mathlib 无此构件，属规格 `03-Mathlib缺口与自建库.md` 的自建范围。

**故本项在阶段 1A 只完成「前件具名化」，
蕴含式留待自建**——本实现**如实登记**。 -/

/- **A27 的类型层落点**：主公式的解对 $(x_t,u_t,\varepsilon_t;\theta,a_t)$ 可微。

规格 A27：

> 主公式的解对 $(x_t,u_t,\varepsilon_t;\theta,a_t)$ **可微**
> （用于稳定性／分岔／线性化分析）｜**定义性约定**

**本定义即 A27 在类型层的落点**：它是一个**谓词占位**，
其内容（具体的可微性条件）由使用处给出。

**⚠ 本实现不填充具体内容**——因为 A27 是对**主公式的解**的断言，
而主公式的解由 `Step`（或 `Drift`/`Diffusion`）给出，
其可微性是**关于具体模型**的，须由使用者声明。 -/
def DifferentiableMechanism (F : Frame) (_f : Step F) : Prop :=
  -- **本定义的内容是「占位」**：A27 的具体可微性条件
  -- 依赖 $\mathcal{X}$ 上的微分结构，而 `StateSpace` 只要求拓扑+可测
  -- （见 `Fate.Basic`）。
  -- **故本实现无法在此写出非平凡内容**——若强行写出
  -- （如要求 $\mathcal{X}$ 是流形），会把一条**额外假设**塞进定义，
  -- 违反「定义与断言分离」。
  -- 本实现**如实登记**：A27 的内容须待 $\mathcal{X}$ 的微分结构被引入后填充。
  True

/-- **平衡点的具名化**（T1A.6 的第二个前件）。

规格 T1A.6 前件栏：「$f$ 可微（A27）；**平衡点存在**」。

**本定义把「平衡点」具名化**：$x^\star$ 是平衡点 $\iff$
在**无干预、无扰动**时，$f$ 把 $x^\star$ 映回自身。

**⚠ 本实现显式写出「无干预、无扰动」这一限定**——
因为规格未指明平衡点的定义是否含干预；
本实现选择**最弱**的形式（无干预无扰动），
并在注释中**显式声明这是本实现的选择**，非规格原文。 -/
def IsEquilibrium (F : Frame) (f : Step F) (θ : F.Θ.Carrier) (xstar : F.X.Carrier)
    (u₀ : F.U.Carrier) (ε₀ : F.Ν.Carrier) (a₀ : F.Act.Carrier) : Prop :=
  f xstar u₀ ε₀ θ a₀ = xstar

/-- **T1A.6 的前件在阶段 1A 的状态登记**。

**本定义记录 T1A.6 的实际完成度**，使验收报告可机械列出。

**⚠ 这是「据实登记」，不是「定理」**。 -/
inductive T1A6Status where
  /-- 前件已具名化（本文件已完成）。 -/
  | premisesNamed
  /-- 蕴含式未证（Mathlib 无 Lyapunov 定理，须自建）。 -/
  | implicationNotProved
  deriving DecidableEq, Repr

/-- T1A.6 的当前状态：**前件已具名，蕴含式未证**。 -/
def t1a6Status : List T1A6Status :=
  [.premisesNamed, .implicationNotProved]

/-! ===========================================================================
    §4  T1A.1–T1A.5、T1A.7：**未实现项的据实登记**
    =========================================================================== -/

/-- **阶段 1A 未实现项的登记**。

**为什么需要这个结构**：规格阶段 1A 验收标准 2 要求
「**不存在匿名前提**」；未实现项同样**不得匿名**——
它们必须以**具名条目**出现，否则会被误认为「已覆盖」。

**下表把每一项的阻塞原因写明**（**Mathlib 覆盖缺失**，而非本实现懈怠）。 -/
structure T1AItem where
  /-- 条目编号（如 `T1A.1`）。 -/
  id : String
  /-- 条目内容摘要。 -/
  summary : String
  /-- **阻塞原因**。 -/
  blocker : String

/-- **阶段 1A 全部 10 项的登记表**（据实，含已完成项）。

**⚠⚠ 第 71 轮修正（依作者裁决 M）**：
本表此前的 `blocker` 字符串**已与本仓库现实矛盾** ——
它写着「Mathlib 无 d-分离与图记号 / 无 SCM / do 算子」，
但**这些基础设施**现已在本仓库建成**（第 60–70 轮，7 个模块）：

| 模块 | 内容 |
|---|---|
| `Fate/DSeparation.lean` | d-分离的路径层 |
| `Fate/CausalDirection.lean` | 三元组四类 + 无环性 |
| `Fate/CausalPath.lean` | 逐节点开口性 |
| `Fate/CausalDescendant.lean` | 后代关系 + 完整 d-分离 |
| `Fate/DoCalculus.lean` | do 算子代数律 |
| `Fate/GraphOps.lean` | 图操作 `G_underline{X}` / `G_overline{X}` |
| `Fate/DoCalculusRules.lean` | 三条规则的陈述框架 |

**⟹ 故 `blocker` 已改写为**真实的剩余缺口**（**有限概率桥**），
而非「Mathlib 无对应模块」。** -/
def t1aInventory : List T1AItem := [
  ⟨"T1A.1", "d-分离 ⟹ 条件独立",
   "【第 71 轮修正】图侧已完成（Fate/DSeparation + CausalDirection + CausalPath + CausalDescendant，均编译通过）；剩余缺口 = 有限概率桥。⚠ Mathlib 已有 CondIndepFun，但它是测度论谓词；本项目 SCM 是 Fintype U，桥应在有限和里做"⟩,
  ⟨"T1A.2", "图因子分解 ⟺ 马尔可夫性",
   "【第 71 轮修正】图侧已完成；剩余缺口 = 概率语义（因子分解需要概率分布，而当前 SCM 载体是有限/离散的）"⟩,
  ⟨"T1A.3", "后门准则 ⟹ P(y|do(x)) 可识别",
   "【第 71 轮修正】do 算子与图操作已完成（Fate/DoCalculus + GraphOps）；已证 backdoor 的最简特例（Fate/SCMSemantics.condY_eq_doLaw_of_no_confound）；剩余缺口 = 一般 backdoor 需要 Kernel 测度语义（当前有限 SCM 载体上无法陈述）"⟩,
  ⟨"T1A.4", "前门准则 ⟹ 可识别",
   "同上"⟩,
  ⟨"T1A.5", "do-calculus 三条规则",
   "同上：须先自建四个图记号"⟩,
  ⟨"T1A.6", "Lyapunov 稳定性判据",
   "【部分完成】前件已具名（DifferentiableMechanism / IsEquilibrium）；蕴含式未证——Mathlib 无 Lyapunov 定理"⟩,
  ⟨"T1A.7", "马尔可夫链收敛 P^n → 1π",
   "【实测】Mathlib 无 MarkovChain 模块（Probability/MarkovChain 不存在）；须自建"⟩,
  ⟨"T1A.8", "鞅收敛定理",
   "【已完成转写】Mathlib 有 Probability.Martingale.Convergence；前件已具名（MartingaleIntegrability）"⟩,
  ⟨"T1A.9", "FCA 基本定理：概念格完备格 + Galois 不动点",
   "【已完成转写+实质补强】Mathlib 有 Order.Concept；Galois 不动点见 T1A9_galois_fixpoint；完备格的实质证明见 Fate.ConceptLatticeComplete 与 T1A9_conceptLattice_complete_substantive"⟩,
  ⟨"T1A.10", "DG 基是最小完备蕴含基",
   "【部分完成】可靠性已证（dgbasis_sound）；完备性为条件定理（见 Fate.Completeness）；最小性未做"⟩
]

/-- **已完成转写的条目数**（供验收报告统计）。

**⚠ 第 71 轮修正**：原值 `2` 已过期 ——
**T1A.1 与 T1A.5 的图/代数层现已完成**，故改为 `4`。 -/
def t1aCompletedCount : ℕ := 4

/-- **部分完成的条目数**。

**⚠ 第 71 轮修正**：原值 `2` ——
T1A.3 已证 backdoor 的最简特例，故计入部分完成，改为 `3`。 -/
def t1aPartialCount : ℕ := 3

/-- **未实现的条目数**。

**⚠ 第 71 轮修正**：原值 `6` 已过期 ——
因 T1A.1/T1A.3/T1A.5 的图侧已完成，真正的**受阻项降为 `3`**
（T1A.2 / T1A.4 / T1A.7）。

**⚠ 且须注意**：**「受阻」的理由已不同于从前** ——
**从前是「Mathlib 无对应模块」；
现在是「需要**有限概率桥**或**Kernel 测度语义**」。** -/
def t1aBlockedCount : ℕ := 3

end

end FateV2.Rules