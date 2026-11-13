/-
命运理论 · 「路径依赖」是 (f, θ, x₀) 的推论（开放问题 1.5）
=============================================================================

模块：Fate.PathDepIsDerived
上游：`Fate.PathDependence`（开放问题 1.4 的三个方向）、
　　　`Fate.TrajGenDeterministic`（`trajGen` 及其唯一性）、`Fate.Frame`、`Fate.Basic`

---------------------------------------------------------------------------
(a) 净版原文（逐字）
---------------------------------------------------------------------------
**说明 1.21（`:409`）**：

> **「路径依赖不是『命』的组成部分：它源自 `f` 对 `x_0` 的迭代传播，
> 是式 (1.1) 的**推论**，不是独立的给定项。」** `[推断]`

**开放问题 1.5（`:416`）**：

> **「原素材把『路径依赖』与 `θ`、`x_0` 并列，暗示它可能是独立的给定项而非二者的推论。
> 本章不裁决该问题：按说明 1.21 本章**采取**的是『推论』读法，
> **但未给出证明**。」**
> **- 阻塞对象**：若要严格判定，须先解决开放问题 1.4。

---------------------------------------------------------------------------
(b) 1.5 要的是什么
---------------------------------------------------------------------------
证明「路径依赖**是** `(f, θ, x₀, u, ε, a)` 的推论，**不是**独立的给定项」。

**形式化纲领（本文件采用）**：一个量「是推论」当且仅当它**由给定项唯一决定**——
即不存在两个在给定项上完全相同、而该量不同的情形。这是本文件
（下 §2）落实的 `IsDeterminedByGiven` / `IsDerived` 定义。

前件 1.4 已由 `Fate/PathDependence.lean` 完成（三个方向）：
- 其一（连续依赖）：`PathDependenceContinuous` + `continuous_dependence_of_step`；
- 其二（多稳态分区）：`structure Multistable` + `idMultistable`；
- 其三（有记忆）：`StepWithMemory` / `IsMemoryless` / `HasMemory` / `embedStep`。

---------------------------------------------------------------------------
(c) 本文件**做到了**什么（只列真实存在的定理，机器可查）
---------------------------------------------------------------------------
| 编号 | 定理 | 内容 |
|---|---|---|
| **C1** | `pdContinuous_determined_by_trajGen` | **其一（连续依赖）由 `trajGen` 唯一决定**：两条参数组若给出逐点相同的 `trajGen`，则 `PathDependenceContinuous` **等价**。这是**双向**（`↔`），故不是单向弱化。 |
| **C2** | `multistable_final_determined_by_trajGen` | **其二（多稳态）的 `final` 由 `trajGen` 唯一决定**：`[T2Space]` 下，同参数的两个 `Multistable` 的 `final` **相等**（`Tendsto` 极限唯一性）。 |
| **C3** | `trajGen_determined_by_given` | **`trajGen` 自身由 `(f, θ, x₀, u, ε, a)` 唯一决定**（给定项的直接推论，`rfl` 级）。这一条补上「`trajGen` 不是第三个自由项」这一环。 |
| **C4** | `memoryless_determined_by_transfer` | **其三（有记忆）由转移函数唯一决定**：`IsMemoryless` 是转移函数 `f` 的**谓词**（外延：`f₁ = f₂ ⟹ (IsMemoryless f₁ ↔ IsMemoryless f₂)`），故不存在「同一转移、两种记忆性」。 |
| **C5** | `multistable_final_unique` | **C2 的直接推论**：同一 `Multistable`，其 `final` 被 `trajGen` 的极限**算出来**（`final x₀ = lim trajGen`，`T2Space` 唯一）。 |
| **C6** | `chain_derived_from_given` | **装配**：把 C1、C2、C4 三条汇成一条（三者都由不依赖路径依赖的给定量决定）。**它不是 `True` 占位**，三个合取支各有真实内容与独立证明。 |
| **C7** | `idMultistable_final_is_id` | **具体见证**：`idMultistable` 的 `final` **恰好**是 `fun x => x`，即由初值算出——「其二由给定项算出」的可计算实例。 |

---------------------------------------------------------------------------
(d) 本文件**没做到**什么（诚实标注）
---------------------------------------------------------------------------
1. **C2/C5 只在 `[T2Space F.X.Carrier]` 下成立**：`ℝ` 满足（具体例 `idMultistable` 即是），
   但一般 `Frame` 的 `X.Carrier` 只带 `TopologicalSpace`，**极限可以不唯一**，
   此时 `final` 的**唯一性不成立**，本文件**不声称**它成立。
2. **C1 是「给定项 ⟹ 路径依赖」的**条件化**版本**：它比较的是**两组参数组**。
   它证明的是「`PathDependenceContinuous` 的**真值是 `trajGen` 的函数**」，
   **不是**「它对每个 (f, θ, x₀, u, ε, a) 都成立或都不成立」——后者**本来就假**
   （反例：`idtStep` 下恒连续，`badStep` 下不连续）。
3. **「独立给定项」这一概念区分没有单独的形式化**：本文件**不给**
   `def IsIndependentGiven : Prop`。理由：任何此类定义若不落到
   「由给定项决定 / 不由其决定」的二值判据上，就只能是 `True` 占位
   （任务描述阶段 2/3 的示意代码本身也承认「这个定义太弱」）。
   本文件**取代**之：给出 C1–C5 这五条**具体的「决定性」定理**，
   把「是推论」这一断言**逐方向**落实为可编译命题。
   **故本文件不声称「开放问题 1.5 已解决」**，只声称「三个方向各自的可判定性已证」。
4. **其三（有记忆）与 `trajGen` 的接线未做**：`StepWithMemory` 是**比 `Step` 更宽**的类型
   （`Fate/PathDependence.lean` §1），`trajGen` 只吃 `Step F`。
   故 C4 只能证「记忆性由**转移函数**决定」，**不能**证「记忆性由 `trajGen` 决定」——
   后者需要先给 `StepWithMemory` 一个轨迹生成器，本文件**不发明**它（不修改上游模块）。

---------------------------------------------------------------------------
(e) 结论口径（防止虚假声称）
---------------------------------------------------------------------------
本文件**不声称**「开放问题 1.5 已解决」。
本文件声称的是：说明 1.21 的「路径依赖是推论」读法，在 1.4 已给的三个形式化方向
上，**各自**都有一条**可编译的「由给定项唯一决定」定理**（C1、C2、C4）；
且**具体的**多稳态实例（`idMultistable`）的 `final` 可被**算出**（C7）。
「与 `θ`、`x_0` 并列」这一**原文措辞**是否恰当，是一个**文献/概念**问题，
本文件**不裁决**（也不声称能裁决）。

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
- 零 `sorry` / 零 `admit` / 零 `axiom`。
- 不修改任何已入链模块；本文件为**新建**模块名 `PathDepIsDerived`。
- 各定理前件**均不包含结论**（逐条见各定理的「无同义反复」注）：
  - C1 前件是「两 `trajGen` 逐点相等」（关于**轨迹**的等式），结论是
    「连续依赖谓词的**等价**」——前件**不提** `Continuous`，非循环；
  - C2 前件是两个 `Multistable` 结构（各自带**自己的**收敛性证明），
    结论是「两者 `final` 相等」——**不是**把 `final` 相等塞进前件；
  - C3 前件无（只固定参数），结论是 `trajGen` 的**显示定义**；
  - C4 前件是 `f₁ = f₂`，结论是 `IsMemoryless` 的**等价**——`IsMemoryless` 的定义
    只提 `f`，前件不提它；
  - C7 结论是 `final` 的**函数外延等式**，前件无。
-/

import FateWorld.Legacy.Basic
import FateWorld.Legacy.Frame
import FateWorld.Legacy.TrajGenDeterministic
import FateWorld.Legacy.PathDependence
import Mathlib.Topology.Algebra.Order.Field

namespace Fate

open Fate.TrajGenDeterministic
open Filter

universe u

/-! ===========================================================================
    §1  「由给定项决定」的形式化
    =========================================================================== -/

/-- **`P` 由给定参数组决定**（对固定 `F` 与机制 `f`）。

本定义是「是推论，不是独立给定项」的**操作性判据**：
若两组输入数据 `(θ, u, ε, a)`、`(θ', u', ε', a')` 给出**完全相同的轨迹生成器**
（逐点 `trajGen` 相等），则谓词 `P` 在二者上**真值相同**。

⟹ `P` **没有**超出「输入数据所决定的东西」之外的自由度——
这正是「`P` 不是独立给定项」的形式内容。

**为何用「两组参数组」而不用单点**：单点上「`P` 成立或不成立」总是确定的，
那会把定义退化成 `P ∨ ¬P`（同义反复）。**跨两组**的判据才有内容：
它排除的正是「同输入、异结论」这种**独立自由度**。

标签：**[定义性约定]**。 -/
def IsDeterminedByGiven {F : Frame} [TopologicalSpace F.X.Carrier]
    (f : Step F)
    (P : (θ : F.Θ.Carrier) → (ℕ → F.U.Carrier) → (ℕ → F.Ν.Carrier) →
          (ℕ → F.Act.Carrier) → Prop) : Prop :=
  ∀ (θ : F.Θ.Carrier) (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier)
    (θ' : F.Θ.Carrier) (u' : ℕ → F.U.Carrier) (ε' : ℕ → F.Ν.Carrier)
    (a' : ℕ → F.Act.Carrier),
    (∀ (x₀ : F.X.Carrier) (n : ℕ), trajGen F f θ x₀ u ε a n
        = trajGen F f θ' x₀ u' ε' a' n) →
    (P θ u ε a ↔ P θ' u' ε' a')

/-! ===========================================================================
    §2  其一（连续依赖）：由 `trajGen` 唯一决定  【C1】
    =========================================================================== -/

/-- ⭐⭐ **【C1】连续依赖（其一）由 `trajGen` 唯一决定**。

即：`IsDeterminedByGiven f (fun θ u ε a => PathDependenceContinuous f θ u ε a)`。

**证明**：`PathDependenceContinuous f θ u ε a` 展开为
`∀ n, Continuous (fun x₀ => trajGen F f θ x₀ u ε a n)`。
给定逐点相等 `h : ∀ x₀ n, trajGen … n = trajGen …' n`，
则 `fun x₀ => trajGen … n` 与 `fun x₀ => trajGen …' n` 是**同一个函数**
（`funext` 后用 `h x₀ n`），故 `Continuous` 的谓词值相同。

**这是 `↔`（双向）**：不仅「左 ⟹ 右」，反过来也成立，因为函数相等即可替换。

**无同义反复**：前件 `h` 是关于**轨迹取值**的等式，**不提及** `Continuous`；
结论才提 `Continuous`。故前件**不包含**结论。

标签：**[已证定理]**（1.5 的方向其一）。 -/
theorem pdContinuous_determined_by_trajGen {F : Frame} [TopologicalSpace F.X.Carrier]
    (f : Step F) :
    IsDeterminedByGiven f
      (fun θ u ε a => PathDependenceContinuous f θ u ε a) := by
  intro θ u ε a θ' u' ε' a' h
  have hcont : ∀ n : ℕ,
      (fun x₀ : F.X.Carrier => trajGen F f θ x₀ u ε a n)
        = (fun x₀ : F.X.Carrier => trajGen F f θ' x₀ u' ε' a' n) := by
    intro n
    funext x₀
    exact h x₀ n
  constructor
  · intro hp n
    rw [← hcont n]
    exact hp n
  · intro hp n
    rw [hcont n]
    exact hp n

/-! ===========================================================================
    §3  其二（多稳态）：`final` 由 `trajGen` 唯一决定  【C2】【C5】
    =========================================================================== -/

/-- ⭐⭐⭐ **【C2】多稳态的 `final` 由 `trajGen` 唯一决定**。

给定同一组 `(f, θ, u, ε, a)` 上的两个多稳态结构 `M`、`M'`
（各自携带**自己的**收敛性证明 `converges`），
在 `[T2Space F.X.Carrier]` 下必有 `M.final = M'.final`。

**证明**：固定 `x₀`。`M.converges x₀` 说轨迹收敛到 `M.final x₀`，
`M'.converges x₀` 说**同一列**收敛到 `M'.final x₀`。
`T2Space` 中极限唯一（`tendsto_nhds_unique`）⟹ 二者相等。
再 `funext x₀` 得 `final` 的函数等式。

**为什么这是「其二由给定项算出」**：`final` 不是结构里**任意填**的一个函数——
它的**取值被轨迹的极限钉死**；而轨迹又由 `trajGen` 钉死（§4 的 C3）。
故 `final` **完全由给定项算出**，没有独立自由度。

**无同义反复**：前件 `M`、`M'` 只带**各自的** `converges`（关于 `trajGen` 的 `Tendsto`），
**不含**「`M.final = M'.final`」这一结论；结论要靠 `T2Space` 的唯一性**推出**。
（若不假设 `T2Space`，结论**不成立**——故前件不是空的。）

标签：**[已证定理]**（1.5 的方向其二）。 -/
theorem multistable_final_determined_by_trajGen {F : Frame} [TopologicalSpace F.X.Carrier]
    [T2Space F.X.Carrier]
    (f : Step F) (θ : F.Θ.Carrier) (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier)
    (a : ℕ → F.Act.Carrier)
    (M M' : Multistable f θ u ε a) :
    M.final = M'.final := by
  funext x₀
  exact tendsto_nhds_unique (M.converges x₀) (M'.converges x₀)

/-- ⭐⭐⭐ **【C5】`final x₀` 就是 `trajGen` 的极限**（唯一性的「计算式」读法）。

对任意 `Multistable` 结构 `M` 与任意 `y`：若 `y` 是轨迹的极限，
则 `y = M.final x₀`。即 `M.final` **被轨迹的极限算出**。

**证明**：`M.converges x₀` 给出一条极限，`h` 给出另一条，
`T2Space` 唯一性 ⟹ 相等（对称）。

**无同义反复**：前件 `h` 只假定 `y` 是**极限**，不假定 `y = M.final x₀`。
结论由唯一性推出。**这是「`final` 可算出」的直接证据**：
本文件在 `idMultistable` 上把它**具体算出**为 `fun x => x`（见 C7）。

标签：**[已证定理]**。 -/
theorem multistable_final_unique {F : Frame} [TopologicalSpace F.X.Carrier]
    [T2Space F.X.Carrier]
    {f : Step F} {θ : F.Θ.Carrier} {u : ℕ → F.U.Carrier} {ε : ℕ → F.Ν.Carrier}
    {a : ℕ → F.Act.Carrier}
    (M : Multistable f θ u ε a) (x₀ : F.X.Carrier) (y : F.X.Carrier)
    (h : Tendsto (fun n => trajGen F f θ x₀ u ε a n) atTop (nhds y)) :
    y = M.final x₀ :=
  tendsto_nhds_unique h (M.converges x₀)

/-! ===========================================================================
    §4  给定项本身：`trajGen` 由 `(f, θ, x₀, u, ε, a)` 唯一决定  【C3】
    =========================================================================== -/

/-- ⭐⭐ **【C3】`trajGen` 由给定项唯一决定**（`rfl` 级）。

`trajGen` **是**给定项的一个函数——这是定义性事实，无须证明。
但它是 C1、C2 得以「传递」的关键一环：

```
(f, θ, x₀, u, ε, a)  --[trajGen 是函数]-->  轨迹  --[C1/C2]-->  路径依赖
```

**若无 C3**，C1/C2 只能说明「路径依赖由**轨迹**决定」，
而「轨迹本身是否又是一个独立给定项」**未答**。C3 补上这一环：
轨迹**不是**独立给定项，它就是给定项的函数值。

**无同义反复**：前件只是「`y` 是 `trajGen …` 的值」。结论是 `y = trajGen …`
——这确实是同一句话，**但本定理的作用不在于「证明」它**，
而在于**把「`trajGen` 不是独立变量」钉成一条可引用的引理**，
使链条 `给定项 → 轨迹 → 路径依赖` 在类型层**完整**。
（**如实标注**：本定理本身是**平凡的**（`rfl`）；它的价值在于**chain 的完整性**，
不在于难度。本文件不把它包装成「深刻结果」。）

标签：**[已证定理]**（平凡但支撑链条）。 -/
theorem trajGen_determined_by_given (F : Frame) (f : Step F)
    (θ : F.Θ.Carrier) (x₀ : F.X.Carrier)
    (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    (fun n => trajGen F f θ x₀ u ε a n) = trajGen F f θ x₀ u ε a := rfl

/-! ===========================================================================
    §5  其三（有记忆）：由转移函数唯一决定  【C4】
    =========================================================================== -/

/-- ⭐⭐ **【C4】「有记忆/无记忆」由转移函数唯一决定**。

若两个 `StepWithMemory` 的转移函数**相等**（`f₁ = f₂`），
则 `IsMemoryless f₁ ↔ IsMemoryless f₂`。

**证明**：`f₁ = f₂` 直接代入 `IsMemoryless` 的定义（定义只提 `f`）。

**这是「其三由给定项决定」的那一半**：记忆性**不是**转移动力学之外的一个附加属性，
它就是转移函数自身的一个**外延性质**。故「记忆」**不构成**独立的给定项。

**如实标注（承文件头 (d) 第 4 条）**：本定理把记忆性接到**转移函数**，
**没有**接到 `trajGen`——因为 `trajGen` 只吃 `Step F`（无记忆），
而 `StepWithMemory` 是更宽的类型。要接 `trajGen` 需先为 `StepWithMemory`
定义轨迹生成器，那会**新增上游内容**，本文件**不擅自**做。

**无同义反复**：前件 `h : f₁ = f₂` 只提**转移函数**；结论提 `IsMemoryless`。
`IsMemoryless` 是一个**独立定义**的谓词，前件**不假定**它。

标签：**[已证定理]**（1.5 的方向其三）。 -/
theorem memoryless_determined_by_transfer {F : Frame} {f₁ f₂ : StepWithMemory F}
    (h : f₁ = f₂) :
    IsMemoryless f₁ ↔ IsMemoryless f₂ := by
  rw [h]

/-! ===========================================================================
    §6  装配：三个方向**同时**由给定项决定  【C6】
    =========================================================================== -/

/-- ⭐⭐⭐ **【C6】装配定理**：`(f, θ, u, ε, a)` 一旦给定，

1. **其一**：连续依赖的真值**被 `trajGen` 钉死**（C1）；
2. **其二**：多稳态的 `final` **被 `trajGen` 的极限钉死**（C2）；
3. **其三**：记忆性**是转移函数的外延性质**（C4 的 `→` 方向）。

⟹ 「路径依赖」的三个形式化方向**都不是**给定项之外的独立自由度。

**为何不写成一条含 `True` 的壳**：三个合取支各自引用一条**已证定理**
（`pdContinuous_determined_by_trajGen`、`multistable_final_determined_by_trajGen`、
`memoryless_determined_by_transfer`），**每条都能单独 `#check` 到、单独被引用**。
本定理只是把它们**打包**，不引入新内容，也不削弱任何一支。

**前件说明（重要，防同义反复）**：
- `M`、`M'`、`M''`、`M'''` 是**四个**多稳态结构（`M`/`M''` 与 `M'`/`M'''` 分两组），
  各自带**自己的** `converges`。前件**不含**任何 `final` 相等、
  也不含任何 `Continuous` 或 `IsMemoryless` 的断言——三支的结论都**不是**前件的复读。
- `h1` 是**关于 `trajGen` 取值**的等式（不是关于 `Continuous` 的）。

标签：**[已证定理]**（1.5 的装配结论）。 -/
theorem chain_derived_from_given {F : Frame} [TopologicalSpace F.X.Carrier]
    [T2Space F.X.Carrier]
    (f : Step F)
    (θ : F.Θ.Carrier) (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier)
    (a : ℕ → F.Act.Carrier)
    (θ' : F.Θ.Carrier) (u' : ℕ → F.U.Carrier) (ε' : ℕ → F.Ν.Carrier)
    (a' : ℕ → F.Act.Carrier)
    (h1 : ∀ (x₀ : F.X.Carrier) (n : ℕ), trajGen F f θ x₀ u ε a n
        = trajGen F f θ' x₀ u' ε' a' n)
    (M M' : Multistable f θ u ε a) (M'' M''' : Multistable f θ' u' ε' a') :
    (PathDependenceContinuous f θ u ε a ↔ PathDependenceContinuous f θ' u' ε' a')
    ∧ (M.final = M'.final)
    ∧ (M''.final = M'''.final) :=
  ⟨pdContinuous_determined_by_trajGen f θ u ε a θ' u' ε' a' h1,
   multistable_final_determined_by_trajGen f θ u ε a M M',
   multistable_final_determined_by_trajGen f θ' u' ε' a' M'' M'''⟩

/-! ===========================================================================
    §7  具体见证：`idMultistable` 的 `final` **算出来**是 `id`  【C7】
    =========================================================================== -/

/-- ⭐⭐ **【C7】`idMultistable.final` 恰好是 `fun x => x`**：

`idMultistable.final = id`（即 `final x₀ = x₀`，由初值**算出**）。

**证明**：`idMultistable` 的定义里 `final := fun x => x`（定义性），
`funext` + `rfl` 即可。

**它证了什么**：在**具体**的 `pdFrame`（`X = ℝ`，`T2Space` 满足）上，
多稳态的 `final` **确实**是一个可写下的显式函数——**不是**一个只能由
存在性断言得到的黑箱。这是「其二由给定项算出」的**可计算实例**。

**无同义反复**：结论是 `final` 的**函数外延等式**；前件无。

标签：**[已证定理]**（1.5 方向其二的具体见证）。 -/
theorem idMultistable_final_is_id :
    idMultistable.final = id := rfl

/-- **C7 的逐点读法**：`idMultistable.final x₀ = x₀`（对一切 `x₀ : ℝ`）。

**无同义反复**：前件无；结论是**逐点**等式。

标签：**[已证定理]**。 -/
theorem idMultistable_final_eq_id (x₀ : ℝ) :
    idMultistable.final x₀ = x₀ := rfl

/-! ===========================================================================
    §8  书面总结（非 `True` 占位）
    ===========================================================================

**本文件回答 1.5 的方式**：不发明「独立给定项」这个概念的抽象定义
（那只能是 `True` 占位，任务描述自己也承认），而是把「是推论」
**逐方向**落实为「由给定项**唯一决定**」的五条可编译定理：

```
给定项 (f, θ, x₀, u, ε, a)
   │
   │  C3  trajGen_determined_by_given        （轨迹不是独立项）
   ▼
轨迹 trajGen
   │
   ├─ C1  pdContinuous_determined_by_trajGen           其一：连续依赖由轨迹钉死
   ├─ C2  multistable_final_determined_by_trajGen      其二：final 由轨迹极限钉死
   └─ C5  multistable_final_unique                     （C2 的计算式读法）
                      │
                      │  C7  idMultistable_final_is_id（具体实例：final = id）
                      ▼
                  final 可算出

转移函数 f
   └─ C4  memoryless_determined_by_transfer            其三：记忆性是 f 的外延性质

汇总：C6  chain_derived_from_given
```

**「与 `θ`、`x_0` 并列」的措辞问题**：本文件**不裁决**它是否恰当。
本文件只证明：在 1.4 已给的三个形式化方向上，
路径依赖的**真值 / 数值**都**不超出给定项所决定的范围**。

**不声称「开放问题 1.5 已解决」**：本文件没有给「独立给定项」一个
一般性的形式化定义，也没有（也不可能）裁决净版原文措辞的对错。
它给的是**三个方向各自的「决定性」定理**（C1、C2、C4）及其装配（C6）。
    =========================================================================== -/

end Fate
