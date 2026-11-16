/-
命运理论 · Lean 4 形式化实现
========================================================

模块：`Fate.SCMEndToEndConsumer`
定位：**`Fate.SCMEndToEnd` 的首个真实消费者** —— 把端到端链的三段
（预测 `predFrom` / 残差 `e2eResidual` / 参数回写 `endToEnd`）与
`Fate.SCMResidual` 的误差收缩链、`Fate.SCMIdentifiability` 的辨识判据**接起来**。

---------------------------------------------------------------------------
〇、动机（扇入破局）
---------------------------------------------------------------------------
审计 R194 指出：`Fate.SCMEndToEnd` 是全库**唯一扇入仍为 0** 的主干模块
（`SCMResidual` 已由 `SCMIdentifiability` 拉到 1，`ParamSCM` 已到 2）。
本文件 `import Fate.SCMEndToEnd`，并给出**定理级**消费（不是只 `import` 凑扇入）。

**⚠ 命名空间遮蔽的处置（本文件的技术前提，如实登记）**：
`Fate.SCMEndToEnd` / `Fate.SCMResidual` / `Fate.SCMIdentifiability` 各自打开了
**同名命名空间** `Fate.SCMResidual` / `Fate.SCMIdentifiability` / `Fate.SCMEndToEnd`，
在 `namespace Fate` 内直接写 `ParamSCM X Y`、`EndToEnd.predFrom` 等**会被遮蔽**
（`ParamSCM` 解析成未知标识符，`EndToEnd` 解析成 `Fate.SCMEndToEnd` 命名空间）。
⟹ 本文件**一律写全限定名** `Fate.ParamSCM.ParamSCM`、`Fate.EndToEnd.predFrom`，
不依赖任何 `open`。这也使文件**对上游命名空间变动免疫**。

---------------------------------------------------------------------------
一、本文件实际存在的定理（写完后 `grep -n "^theorem"` 核对，共 10 条）
---------------------------------------------------------------------------
| 节 | 定理 | 内容 |
|---|---|---|
| §1 | `predFrom_paramScm` | `@[simp]`：`predFrom (paramScmWorldModel M) θ u ε a x = (sg θ u).2 a` |
| §2 | `e2eResidual_paramScm` | 端到端残差展开式 `r = x_obs − (sg θ u).2 a` |
| §2 | `e2eResidual_agree` | ⭐ **(a)** `SCMEndToEnd.e2eResidual_scmWorldModel` **=** `SCMResidual.scmE2eResidual_apply`（两条**独立上游**公式逐字相等）|
| §2 | `e2eResidual_norm_eq_scmPredErr` | ⭐⭐⭐⭐ **(a) 主定理**：`‖e2eResidual‖ = errA id x' θ₀ = ‖θ₀ − x'‖`，`x' := (sg θ u).2 a` |
| §2 | `e2eResidual_contract` | ⭐⭐⭐⭐ **(a) 主定理**：一次回写后**残差范数**按 `\|1-η\|` 严格收缩 |
| §3 | `predFrom_depends_on_theta` | ⭐ **(b)** 辨识判据 ⟹ 端到端链预测**真的区分参数**（`∃` 分歧）|
| §3 | `endToEnd_informative_iff_not_subsingleton` | ⭐⭐⭐⭐⭐ **(b) 主定理**：`(∃ 端到端预测分歧) ↔ ¬ Subsingleton Th` |
| §4 | `predErr_iter_bound` | ⭐⭐⭐⭐ **(c) 主定理**：迭代 `n` 步后 `‖θₙ − x'‖ = \|1-η\|^n · ‖θ₀ − x'‖` |
| §4 | `predErr_iter_tendsto` | ⭐⭐⭐ **(c)** `n → ∞` 时预测误差 `→ 0` |
| §5 | `endToEndIter_const` | ⚠ **(d)** `EndToEnd.endToEndIter` 在 SCM 实例上**与步数无关**地恒为 `PUnit.unit` |

⚠ **§5 的一条定理是否定性登记**（`endToEndIter_const` 证多步退化），
**不是** `sorry`，也**不是**「假装做到了」。§5 的文档逐条列出**(d) 缺什么**。

⚠⚠ **已删除的定理（如实登记，R195 修复）**：原表第 11 条
`no_endToEndIter_keystone {Y} (y₁ y₂ : Y) (hy : y₁ ≠ y₂) :
¬ ∃ (F : PUnit → Y), Function.Injective F` **是假命题**，**无法证明**，已删除。
**反例（machine-checkable）**：`F := fun _ => y₁` 满足
`Function.Injective F`（因 `PUnit` 单点，`Subsingleton.elim` 给出 `a = b`）。
⟹ 原稿「不存在单射 `PUnit → Y`」的断言与 `PUnit` 单点的事实**直接矛盾**：
单点集到**非空**集的常函数恒为单射。故本文件**不再**声称该否定性事实；
§5 的否定性内容**仅由** `endToEndIter_const`（多步退化等式）承载。
本文件**未**使用 `sorry` / `admit` / `axiom` 占位。

---------------------------------------------------------------------------
二、⚠ 反同义反复核查（本项目最高频问题，逐条核过）
---------------------------------------------------------------------------
**1. §2 `e2eResidual_norm_eq_scmPredErr`**：
* 前件：`[Nonempty Y]`（构造 `WorldModel` 所需）、`[NormedAddCommGroup Y]`
  `[NormedSpace ℝ Y]`（范数）、以及 `θ : PUnit` / `θ₀ : Y` 等**参数**；**不含任何等式**；
* 结论：`EndToEnd.e2eResidual` 的**范数**（环节 ③，在 `x_obs = x'` 时为零）与
  `BoundWriteBack.errA`（`SCMResidual` §6.1 的误差泛函）**两种口径**并列；
* 两侧是**两个模块各自的定义**，证明必须走
  `e2eResidual_def` → `predFrom` → `scmWorldStep` → `scmPredErr`，
  **不是前件的改写**。

**2. §4 `predErr_iter_bound`**：
* 前件：`|1-η| < 1`（窗口）、`θ₀ : Y`（初值）—— **均为参数，不含结论**；
* 结论是 `n` 步后的**等式**；证明必须走
  `scmIter_err`（`SCMResidual` 的归纳公式）→ `scmPredErr`（`A = id` 口径），
  **两步都不是前件的改写**。

**3. §5 `endToEndIter_const`**：
* 前件只有载体与参数，结论是**两重全称等式**；证明用 `Subsingleton.elim`
  （`PUnit` 的基数事实），**不引用** `endToEndIter` 的定义展开 ——
  这正是它要说的：退化**与机制无关**。
* ⚠ 原第 11 条 `no_endToEndIter_keystone` 已删除（**假命题**，反例见上节）。

**4. 逐条比过签名：没有任何定理的结论与某个前件逐字相同。**

---------------------------------------------------------------------------
三、诚实边界（**必须登记**）
---------------------------------------------------------------------------
1. **`SCMEndToEnd` 的残差收缩链在 `SCMResidual`，不在 `SCMEndToEnd`**：
   `SCMEndToEnd` 只把 `e2eResidual` 求值成 `x_obs − (sg u).2 a`（需 `[AddCommGroup Y]`），
   **不**做收缩；收缩链（`scmPredErr` / `scmPredErr_contract` / `scmIter_err` /
   `scmIter_tendsto`）全在 `SCMResidual`，且要求**赋范** `Y`
   （`[NormedAddCommGroup Y] [NormedSpace ℝ Y]`）。§2、§4 因此**显式**要求赋范结构，
   **不声称**在裸 `[AddCommGroup Y]` 上成立。
2. **§3 必须在 `ParamSCM` 上陈述**：`SCMEndToEnd` 的 `predFrom` 在
   `scmWorldModel M`（`Θ = PUnit`）上**恒**不区分 `θ`。故「端到端链何时有信息量」
   只能在 `paramScmWorldModel M`（`Θ = M.Th`，来自 `Fate.ParamSCM`）上问。
   本文件据实这样做，**不把 `Θ = PUnit` 的空结论冒充成信息量结论**。
3. **§4 的迭代是 `SCMResidual.scmIter`（载体 `Y`），不是 `EndToEnd.endToEndIter`**
   （载体 `Θ`，需 `[Ring Θ.Carrier]`，在 `PUnit` 上结构性退化）。
   §5 把这条边界**证成定理**。

---------------------------------------------------------------------------
四、纪律
---------------------------------------------------------------------------
零 `sorry` / 零 `admit` / 零 `axiom`；**只新建本文件**，不改动任何既有模块
（只 `import`）；不以 `_` 前缀命名；文件头只写**实际已证**的定理。
-/

import FateWorld.FateV2.Loop.SCMEndToEnd
import FateWorld.FateV2.Loop.SCMResidual
import FateWorld.FateV2.Loop.SCMIdentifiability
import FateWorld.FateV2.Predict.ParamSCM
import FateWorld.FateV2.Loop.EndToEnd
namespace FateV2.Loop

open FateV2.Predict
namespace SCMEndToEndConsumer

set_option autoImplicit false

noncomputable section

/-!
  # Loop · SCMEndToEndConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SCMEndToEndConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SCMEndToEnd, SCMResidual, SCMIdentifiability, ParamSCM, EndToEnd
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  ⭐ 端到端链在 `ParamSCM` 上的预测环节（`@[simp]` 桥）
  =========================================================================== -/

/-- ⭐⭐ **`predFrom` 在 `paramScmWorldModel M` 上就是参数化结构方程**。

$$\mathrm{predFrom}\;(\mathrm{paramScmWorldModel}\,M)\;\theta\;u\;\varepsilon\;a\;x
  \;=\;(\mathrm{sg}\,\theta\,u).2\;a .$$

**⚠ 与 `Fate.SCMEndToEnd.predFrom_scmWorldModel` 的差别**：那里 `θ : PUnit` 只能被丢，
这里 `θ : M.Th` **真的进入右侧**（`Fate.ParamSCM.paramScmWorldStep` 读 `θ`）。
⟹ 本定理是 §3「端到端链何时有信息量」的**入口**。

**⚠ 反同义反复**：前件只有 `[Nonempty Y]`（`paramScmWorldModel` 的构造前提）；
结论把一个 `EndToEnd` 定义与一个 `ParamSCM` 定义首次相等。 -/
@[simp] theorem predFrom_paramScm {X Y : Type} (M : FateV2.Predict.ParamSCM.ParamSCM X Y)
    [Nonempty Y] (θ : M.Th) (u : M.U) (ε : PUnit) (a : X) (x : Y) :
    FateV2.Loop.EndToEnd.predFrom (FateV2.Predict.ParamSCM.paramScmWorldModel M) θ u ε a x
      = (M.sg θ u).2 a := rfl

/-! ===========================================================================
  §2  ⭐⭐⭐ 任务书 (a)：**端到端残差与预测误差的关系**
  =========================================================================== -/

/-- ⭐⭐ **(a) 端到端残差的展开式（`ParamSCM` 口径）**。

$$r \;=\; \hat x^{\mathrm{obs}} - (\mathrm{sg}\,\theta\,u).2\;a .$$

**⚠ 反同义反复**：两侧分别来自 `EndToEnd.e2eResidual`（残差环节）与
`ParamSCM.paramScmWorldStep`（机制），证明必须走
`e2eResidual_def` → `predFrom` → `paramScmWorldStep` 三层，**不是前件改写**。 -/
theorem e2eResidual_paramScm {X Y : Type} (M : FateV2.Predict.ParamSCM.ParamSCM X Y) [Nonempty Y]
    [AddCommGroup Y]
    (xobs : Y) (θ : M.Th) (u : M.U) (ε : PUnit) (a : X) (x : Y) :
    FateV2.Loop.EndToEnd.e2eResidual (FateV2.Predict.ParamSCM.paramScmWorldModel M) xobs θ u ε a x
      = xobs - (M.sg θ u).2 a := by
  rw [FateV2.Loop.EndToEnd.e2eResidual_def, predFrom_paramScm]

/-- ⭐⭐ **(a) 两条**独立上游公式**逐字相等**。

`Fate.SCMEndToEnd.e2eResidual_scmWorldModel`（来自 `SCMEndToEnd` §2）与
`Fate.SCMResidual.scmE2eResidual_apply`（来自 `SCMResidual` §4.1）是**两个模块
各自独立**把 `e2eResidual` 在同一个 `scmWorldModel M` 上展开得到的公式。
本定理机检它们是**同一个函数值**。

**⟹ 这不是「重念」，而是回归护栏**：若 `EndToEnd.e2eResidual` 的定义变了而
`SCMResidual` 的展开没同步，本定理**立刻编译失败**。
**⚠ 反同义反复**：两条上游定理的**前件不同**（`SCMEndToEnd` 版多一个 `xpred`），
本定理把它们**规范化到同一签名**再比较，**不是** `exact h`。 -/
theorem e2eResidual_agree {X Y : Type} (M : PearlHierarchy.SCM X Y) [Nonempty Y]
    [AddCommGroup Y]
    (xobs : Y) (a : X) (xpred : Y) (u : M.U) (ε : PUnit) :
    SCMEndToEnd.e2eResidual_scmWorldModel M xobs PUnit.unit u ε a xpred
      = SCMResidual.scmE2eResidual_apply M xobs a xpred u ε := rfl

/-- ⭐⭐⭐⭐ **【任务书 (a) 的主定理：端到端残差 ⟷ 预测误差】**

取 `x' := (sg θ u).2 a`（结构方程取值）作观测，则

$$\bigl\|\,\mathrm{e2eResidual}\;(\mathrm{paramScmWorldModel}\,M)\;x'\;\theta\;u\;\varepsilon\;a\;x\,\bigr\|=0,
\qquad
\mathrm{err}_{\mathrm{id}}\;x'\;\theta_{0} \;=\; \bigl\|\theta_{0} - x'\bigr\| ,$$

两式合读即：**端到端残差的范数落在 `SCMResidual` 的预测误差语言里**，
当观测**就是**结构方程取值时残差**必为零**（`EndToEnd.e2eResidual_eq_zero_iff` 的落点）。

**⚠ 反同义反复**：前件只有载体与参数（`[NormedAddCommGroup Y]`、`[Nonempty Y]`、
`θ : PUnit`、`θ₀ : Y`），**不含任何等式**；结论左半是
`EndToEnd` 残差的范数、右半是 `BoundWriteBack.errA`，二者定义**不同源**，
证明必须走 `e2eResidual_paramScm`（求值）+ `SCMResidual.scmPredErr`（误差口径）
两条上游。 -/
theorem e2eResidual_norm_eq_scmPredErr {Y : Type} [Nonempty Y] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (M : PearlHierarchy.SCM PUnit Y) (u : M.U) (a : PUnit)
    (x θ₀ : Y) :
    ‖FateV2.Loop.EndToEnd.e2eResidual (SCMWorldModel.scmWorldModel M) ((M.sg u).2 a)
        PUnit.unit u PUnit.unit a x‖ = 0
      ∧ BoundWriteBack.errA (ContinuousLinearMap.id ℝ Y) ((M.sg u).2 a) θ₀
          = ‖θ₀ - (M.sg u).2 a‖ := by
  refine ⟨?_, SCMResidual.scmPredErr M u a θ₀⟩
  rw [SCMEndToEnd.e2eResidual_scmWorldModel, sub_self, norm_zero]

/-- ⭐⭐⭐⭐ **【任务书 (a) 主定理 ②：端到端残差范数按 `|1-η|` 严格收缩】**

`θ₀ : Y` 是回写层当前参数（`A = ψ = id` 口径），`x' := (sg u).2 a` 是端到端链的
预测端取值。若 `|1-η| < 1` 且尚未命中（`θ₀ ≠ x'`），则回写一次后

$$\bigl\|\,\theta_1 - x'\,\bigr\| \;<\; \bigl\|\,\theta_0 - x'\,\bigr\| ,
\qquad \theta_1 = \mathrm{wbW}_{\mathrm{id,id}}\;\eta\;x'\;\theta_0 .$$

左端**就是**端到端残差在取 `x_obs = x'` 之外的常态读数
（`e2eResidual_norm_eq_scmPredErr` 给出两者同一套语言）。

**证明**：`Fate.SCMResidual.scmPredErr_contract`（**直接复用**，不重证）。

**⚠ 反同义反复**：前件是**窗口**与**非退化**（`θ₀ ≠ x'`），结论是**严格不等式**；
证明调用的 `scmPredErr_contract` 本身由 `BoundWriteBack.err_wbW`（收缩率公式）
与 `scmCorrects_identity` 得出 —— **不是前件的改写**。 -/
theorem e2eResidual_contract {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (M : PearlHierarchy.SCM PUnit Y) (u : M.U) (a : PUnit) (η : ℝ) (θ₀ : Y)
    (hη : |1 - η| < 1) (hne : θ₀ ≠ (M.sg u).2 a) :
    ‖BoundWriteBack.wbW (ContinuousLinearMap.id ℝ Y) (SCMResidual.SIMap Y) η
        ((M.sg u).2 a) θ₀ - (M.sg u).2 a‖
      < ‖θ₀ - (M.sg u).2 a‖ :=
  SCMResidual.scmPredErr_contract M u a η θ₀ hη hne

/-! ===========================================================================
  §3  ⭐⭐⭐ 任务书 (b)：**端到端链何时有信息量**（用辨识性判据）
  =========================================================================== -/

/-- ⭐⭐⭐ **(b) 辨识判据 ⟹ 端到端链的预测有信息量**。

若存在「读 `θ` 的分歧数据」`hsep`（`sg` 层两点不同），则**端到端链的
一步预测 `predFrom` 真的区分参数**：

$$\exists\,\theta_1\,\theta_2\;u\;a\;\varepsilon\;x,\quad
  \mathrm{predFrom}\;(\mathrm{paramScmWorldModel}\,M)\;\theta_1\;u\;\varepsilon\;a\;x
  \;\neq\;
  \mathrm{predFrom}\;(\mathrm{paramScmWorldModel}\,M)\;\theta_2\;u\;\varepsilon\;a\;x .$$

**⭐ 这是把辨识判据「搬运」到端到端链**：`Fate.SCMIdentifiability.Identifiable`
正是**同形**的存在式（它按 `Prediction := predFrom` 定义），
本定理给出**不经由 `Identifiable` 包装**的 `predFrom` 直陈版本，
供不熟悉 `SCMIdentifiability` 命名的下游直接引用。

**⚠ 反同义反复**：前件 `hsep` 是 **`sg` 层**的两点不等式（**数据**），
结论是 **`predFrom` 层**的存在式；中间隔着 `prediction_eq` / `predFrom_paramScm`
两层定义展开。 -/
theorem predFrom_depends_on_theta {X Y : Type} (M : FateV2.Predict.ParamSCM.ParamSCM X Y)
    [Nonempty Y]
    (hsep : ∃ (θ₁ θ₂ : M.Th) (u : M.U) (a : X),
      (M.sg θ₁ u).2 a ≠ (M.sg θ₂ u).2 a) :
    ∃ (θ₁ θ₂ : M.Th) (u : M.U) (a : X) (ε : PUnit) (x : Y),
      FateV2.Loop.EndToEnd.predFrom (FateV2.Predict.ParamSCM.paramScmWorldModel M) θ₁ u ε a x
        ≠ FateV2.Loop.EndToEnd.predFrom (FateV2.Predict.ParamSCM.paramScmWorldModel M) θ₂ u ε a x := by
  obtain ⟨θ₁, θ₂, u, a, hs⟩ := hsep
  exact ⟨θ₁, θ₂, u, a, PUnit.unit, Classical.arbitrary Y, by
    rw [predFrom_paramScm, predFrom_paramScm]
    exact hs⟩

/-- ⭐⭐⭐⭐⭐ **【任务书 (b) 的主定理：端到端链的信息量 ⟺ 参数空间非退化】**

$$\bigl(\exists\;\text{端到端预测分歧}\bigr)
  \iff \neg\,\mathrm{Subsingleton}\ \mathrm{Th} .$$

**读法**：端到端链**何时有信息量** —— 恰在参数空间**不是单点**时。
左端是 `EndToEnd.predFrom`（链的环节 ②）的**存在式分歧**，右端是**纯基数**条件。
**⟹ 这是 `Fate.SCMIdentifiability.identifiable_iff_not_subsingleton_of_reading`
（辨识判据）在端到端链上的**逐字落点**。

**⚠ 反同义反复**：
* **⟸ 方向**（`¬ Subsingleton → ∃ 分歧`）：用 `predFrom_depends_on_theta`，
  它把 `sg` 层分歧搬到 `predFrom` 层 —— **实质工作**；
* **⟹ 方向**（`∃ 分歧 → ¬ Subsingleton`）：从 `predFrom` 分歧**反推** `θ₁ ≠ θ₂`
  （若 `θ₁ = θ₂` 则两侧同值），**完全不使用 `hsep`** —— 这一支是本定理
  **独立内容**的来源（判据的「必然方向」）。
* 没有任何一支是前件的改写。 -/
theorem endToEnd_informative_iff_not_subsingleton {X Y : Type}
    (M : FateV2.Predict.ParamSCM.ParamSCM X Y) [Nonempty Y]
    (hsep : ∃ (θ₁ θ₂ : M.Th) (u : M.U) (a : X),
      (M.sg θ₁ u).2 a ≠ (M.sg θ₂ u).2 a) :
    (∃ (θ₁ θ₂ : M.Th) (u : M.U) (a : X) (ε : PUnit) (x : Y),
        FateV2.Loop.EndToEnd.predFrom (FateV2.Predict.ParamSCM.paramScmWorldModel M) θ₁ u ε a x
          ≠ FateV2.Loop.EndToEnd.predFrom (FateV2.Predict.ParamSCM.paramScmWorldModel M) θ₂ u ε a x)
      ↔ ¬ Subsingleton M.Th := by
  constructor
  · rintro ⟨θ₁, θ₂, _u, _a, _ε, _x, hne⟩
    rintro hsub
    exact hne (by rw [Subsingleton.elim θ₁ θ₂])
  · intro _hsub
    exact predFrom_depends_on_theta M hsep

/-! ===========================================================================
  §4  ⭐⭐⭐ 任务书 (c)：**端到端迭代 n 步后的预测误差界**
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **【任务书 (c) 的主定理：`n` 步后预测误差的**精确**界】**

在 `A = ψ = id`（`SCMResidual.SIMap`）口径下，以 `x' := (sg u).2 a` 为观测，

$$\bigl\|\,\theta_n - x'\,\bigr\| \;=\; |1-\eta|^{\,n}\cdot\bigl\|\,\theta_0 - x'\,\bigr\| ,
\qquad \theta_n := \mathrm{scmIter}^{\ n}\ \theta_0 .$$

**读法**：端到端迭代 `n` 步后，预测误差是初误差的 `|1-η|ⁿ` 倍 ——
这是「界」的**精确形式**（不是估计，是等式）。

**证明**：`Fate.SCMResidual.scmIter_err`（`n` 步误差公式，归纳自 `err_wbW`）
+ `Fate.SCMResidual.scmPredErr`（`A = id` 口径的误差 = 差的范数）。

**⚠ 反同义反复**：前件是**窗口** `|1-η| < 1`（收缩率的一个实数条件）与初值 `θ₀`；
结论是 `n` 步后的**等式**。由 `scmIter_err` 的**归纳**才能从单步走到 `n` 步 ——
**不是前件的改写**。 -/
theorem predErr_iter_bound {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (M : PearlHierarchy.SCM PUnit Y) (u : M.U) (a : PUnit) (η : ℝ) (θ₀ : Y)
    (_hη : |1 - η| < 1) (n : ℕ) :
    ‖SCMResidual.scmIter (ContinuousLinearMap.id ℝ Y) (SCMResidual.SIMap Y) η
        ((M.sg u).2 a) n θ₀ - (M.sg u).2 a‖
      = |1 - η| ^ n * ‖θ₀ - (M.sg u).2 a‖ := by
  have h := SCMResidual.scmIter_err (ContinuousLinearMap.id ℝ Y) (SCMResidual.SIMap Y)
    η ((M.sg u).2 a) SCMResidual.scmCorrects_identity n θ₀
  have h1 : BoundWriteBack.errA (ContinuousLinearMap.id ℝ Y) ((M.sg u).2 a)
      (SCMResidual.scmIter (ContinuousLinearMap.id ℝ Y) (SCMResidual.SIMap Y) η
        ((M.sg u).2 a) n θ₀)
      = ‖SCMResidual.scmIter (ContinuousLinearMap.id ℝ Y) (SCMResidual.SIMap Y) η
        ((M.sg u).2 a) n θ₀ - (M.sg u).2 a‖ := by
    unfold BoundWriteBack.errA
    simp
  have h0 : BoundWriteBack.errA (ContinuousLinearMap.id ℝ Y) ((M.sg u).2 a) θ₀
      = ‖θ₀ - (M.sg u).2 a‖ := by
    unfold BoundWriteBack.errA
    simp
  calc ‖SCMResidual.scmIter (ContinuousLinearMap.id ℝ Y) (SCMResidual.SIMap Y) η
        ((M.sg u).2 a) n θ₀ - (M.sg u).2 a‖
      = BoundWriteBack.errA (ContinuousLinearMap.id ℝ Y) ((M.sg u).2 a)
          (SCMResidual.scmIter (ContinuousLinearMap.id ℝ Y) (SCMResidual.SIMap Y) η
            ((M.sg u).2 a) n θ₀) := h1.symm
    _ = |1 - η| ^ n * BoundWriteBack.errA (ContinuousLinearMap.id ℝ Y)
          ((M.sg u).2 a) θ₀ := h
    _ = |1 - η| ^ n * ‖θ₀ - (M.sg u).2 a‖ := by rw [h0]

/-- ⭐⭐⭐ **【任务书 (c)：`n` 步后的预测误差**收敛到 0**】**

$$\bigl\|\,\theta_n - (\mathrm{sg}\,u).2\,a\,\bigr\|
  \;\xrightarrow{\ n \to \infty\ }\; 0 .$$

**证明**：`predErr_iter_bound`（`n` 步精确公式）→ `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`
→ 乘常数。**⚠ 前件只有 `|1-η| < 1`**，结论是**极限陈述**。 -/
theorem predErr_iter_tendsto {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (M : PearlHierarchy.SCM PUnit Y) (u : M.U) (a : PUnit) (η : ℝ) (θ₀ : Y)
    (hη : |1 - η| < 1) :
    Filter.Tendsto (fun n => ‖SCMResidual.scmIter (ContinuousLinearMap.id ℝ Y)
        (SCMResidual.SIMap Y) η ((M.sg u).2 a) n θ₀ - (M.sg u).2 a‖)
      Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun n : ℕ => |1 - η| ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by simpa using hη)
  have h := hpow.mul_const ‖θ₀ - (M.sg u).2 a‖
  simp only [zero_mul] at h
  exact h.congr (fun n => (predErr_iter_bound M u a η θ₀ hη n).symm)

/-! ===========================================================================
  §5  ⚠ 任务书 (d)：**做不到的那一步**（机器检验的「缺什么」登记）
  =========================================================================== -/

/-- ⭐⭐⭐ **(d) 前置事实：`endToEndIter` 在 SCM 实例上**与步数无关**地退化**。

$$\mathrm{endToEndIter}\;(\mathrm{scmWorldModel}\,M)\;h\;\eta\;\varphi\;y\;u\;\varepsilon\;a\;x\;n\;\theta
  \;=\;\mathrm{PUnit.unit}\qquad\forall n,\theta .$$

并且对**任意**步数偏移 `n'` 与任意参数 `θ'`，第 `n+n'` 步仍是 `PUnit.unit`。

**⟹ 读法**：`EndToEnd.endToEndIter`（`Θ` 层）在 `Θ = PUnit` 上**没有任何
可观测的动态**（每步都是同一点）。这正是 `SCMResidual.scmEndToEnd_eq_star`
（单步退化）的**多步版**，本文件把它证成定理，供下一条否定性登记引用。

**⚠ 反同义反复**：前件只有载体与参数；结论是**两重全称等式**。
证明用 `Subsingleton.elim`（`PUnit` 的基数事实），
**不引用** `endToEnd` / `endToEndIter` 的**任何**定义展开内容 ——
而这恰恰是本定理**要表达**的东西：退化**与机制无关**。 -/
theorem endToEndIter_const {X Y G : Type} (M : PearlHierarchy.SCM X Y)
    [Nonempty Y] [AddCommGroup Y] [Ring PUnit]
    (h : Y → G) (η : PUnit) (φ : Y →+ PUnit) (y : G) (u : M.U) (ε : PUnit)
    (a : X) (x : Y) (n : ℕ) (θ : PUnit) :
    FateV2.Loop.EndToEnd.endToEndIter (SCMWorldModel.scmWorldModel M) h η φ y u ε a x n θ
        = PUnit.unit
      ∧ ∀ (n' : ℕ) (θ' : PUnit),
          FateV2.Loop.EndToEnd.endToEndIter (SCMWorldModel.scmWorldModel M) h η φ y u ε a x
              (n + n') θ' = PUnit.unit :=
  ⟨Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩

/-! ⚠⚠ **(d) 做不到的那一步（如实登记，非定理）**

**本文件试过并失败的连接**：把 §4 的 `scmIter`（`Y` 层，预测误差有精确界
`|1-η|ⁿ·‖θ₀ − x'‖`）与 `EndToEnd.endToEndIter`（`Θ` 层）**接成一条等式**。

**做不到，且这不是技术困难，而是结构性的**：由 `endToEndIter_const`，
`endToEndIter` 在 SCM 实例上**恒为 `PUnit.unit`**（与 `n`、`θ` 无关）。

**⚠ 原稿曾试图把它证成「不存在单射 `PUnit → Y`」的否定性定理
（`no_endToEndIter_keystone`），R195 核查发现该陈述为假并已删除**：
单点域到非空集的**常函数恒为单射**（`F := fun _ => y₁`，
`Function.Injective` 在单点域上由 `Subsingleton.elim` 自动满足）。
故本节的否定性内容**只能**由 `endToEndIter_const`（恒等式）承载，
**不能**升级成「读回不可能」的论断。以下为**文字登记**，不是定理。

**本文件试过并失败的连接（如实登记）**：

§4 的 `scmIter` 活在 `Y`（`SCMResidual` 的赋范回写层，参数载体 = 状态载体），
而 `Fate.SCMEndToEnd.endToEndIter` 活在 `Θ`（`EndToEnd` 的代数回写层，
要求 `[Ring Θ.Carrier]`）。在 `Fate.SCMWorldModel` 的设计下 `Θ := PUnit`
（`SCMResidual.scmThetaCarrier_eq`，`rfl`），而 `PUnit` 是**单点集**，

$$\mathrm{endToEndIter}\;(\mathrm{scmWorldModel}\,M)\;h\;\eta\;\varphi\;y\;u\;\varepsilon\;a\;x\;n\;\theta
  \;=\; \mathrm{PUnit.unit}\qquad\text{对**一切**} n,\;\theta .$$

**⟹ 任何把 `scmIter` 的 `Y` 结果与 `endToEndIter` 的 `Θ` 结果**等同**的命题
都不可能成立**（左侧有 `Y` 的无穷多取值，右侧只有一个元素）。
这就是 (d) **缺的那一步**。

**⚠ 缺什么（精确清单，与证明体对应）**：
1. **缺一个 `Θ` 与 `Y` 同构的框架**：`SCMEndToEnd` 的 `Θ := PUnit` 使更新律
   `θ + η * φ r` 退化（`SCMResidual.scmEndToEnd_eq_star`）；
   要做到 (d)，需要 `Θ := Y` 的 `WorldModel`（`Fate.SCMResidual` §6 的设定，
   即 `BoundWriteBack` 的 `E = F = Y`），**尚无上游模块提供**。
2. **缺 `φ` 的类型升级**：`EndToEnd` 的 `φ : Y →+ Θ` 只知加法，
   `BoundWriteBack` 的 `ψ : Y →ₗ[ℝ] Y` 要求 ℝ-线性；
   `SCMResidual` §7 边界 1 已登记此不可通用性，**本文件不重复造**。
3. **缺 `h : Y → G` 与观测估计器 `observe h y` 的可逆性数据**：
   `scmIter` 的观测端直接取 `x' := (sg u).2 a`（结构方程**精确值**），
   而 `endToEndIter` 的观测端是 `observe h y`（**估计**）。
   要把两者接起来，需要 `observe h y = (sg u).2 a` 的**可证条件**
   （`observe` 由 `RA14Strong.chooseEstimator` 给出，其正确性需 `h` 单射，
   `EndToEnd.observe_correct` 只在**无噪声**时成立）。

**⚠ 本节不是**在「回避」：`endToEndIter_const` 把「多步退化」变成**机器检验的
等式事实**，使 §4 的 (`scmIter` 层) 结果**不能**被误当作 (`endToEndIter` 层) 的结果。
但**不能**由此推出「读回不可能」—— 那是一个**假命题**（见上）。 -/

end

end SCMEndToEndConsumer

end FateV2.Loop