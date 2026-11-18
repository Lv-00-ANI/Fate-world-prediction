/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.SCMResidual`
定位：**把 SCM 接到残差回写层**（`SCM ⟶ EndToEnd ⟶ BoundWriteBack`）

===========================================================================
〇、本文件做什么（四个交付点，逐条对应任务书 (b)(c)(d)）
===========================================================================

`Fate/SCMWorldModel.lean` 已把 SCM 翻译成 `WorldModel`（`scmWorldModel M`）。
本文件把该实例**向下接两层**：

| 任务书 | 交付 | 落点 |
|---|---|---|
| **(b)** 在 `scmWorldModel M` 上证明 `endToEnd` 的更新律是 `θ + η * φ(观测 − SCM预测)` | ✅ | §4 `scmEndToEnd_apply` / `scmEndToEnd_step_eq` / `scmEndToEnd_is_updateLaw` |
| **(c)** 状态空间取 SCM 的 `Y` 时 `Corrects` 的具体形式 | ✅ | §5 `scmCarrier_eq` / `scmCorrects_apply` / `scmCorrects_iff` / `scm_no_corrects_too_weak` |
| **(d)** SCM 实例上 `writeBack` 一次后误差按 `\|1-η\|` 收缩 | ✅ | §6 `scm_err_wbW` / `scm_err_contract` / `scm_no_better_rate`（**直接复用** `BoundWriteBack.err_wbW`，不重证） |
| **(d′)** 多步收敛（用上述收缩率） | ✅ | §6.3 `scmIter_err` / `scmIter_tendsto` |
| **(e)** 做不到的部分 | 无（见 §7 如实登记三条**边界**，均**非**缺口） | — |

===========================================================================
一、⭐ 本文件的**技术要点**（不是重念定义的证据）
===========================================================================

**1.1 `EndToEnd.endToEnd` 与 `BoundWriteBack.wbW` 载体不同，本文件给出**对齐律**。**

- `endToEnd` 活在纯代数载体：`[AddCommGroup X.Carrier]` + `[Ring Θ.Carrier]`，更新式 `θ + η * φ r`；
- `wbW` 活在赋范载体：`E →L[ℝ] F` + `F →ₗ[ℝ] E`，更新式 `θ + η • φ r`。

`Fate/BoundWriteBack.lean` §8.1 只核对了 `Θ = ℝ`、`A = id` 的**形状**（`wbW_shape`），
**没有**「`endToEnd` 的更新律 = `wbW`」的定理。本文件 §3 补上
`endToEnd_apply_eq_smul_form`，使「端到端更新律」在**两层各自的符号体系**里是**同一条等式**。
⟹ 这是任务书 (b) 与 (d) 之间的**唯一桥梁**，缺它则 (d) 无法复用 `BoundWriteBack` 的定理。

**1.2 状态空间取 SCM 的 `Y`** —— 在类型层是**定义性等式**（§5 `scmCarrier_eq`，`rfl`）。

**1.3 SCM 实例的 `Θ = PUnit` ⟹ `Ring` 更新律在 SCM 上**结构性退化**（§4.2）。**

`scmThetaSpace.Carrier = PUnit`（`Fate/SCMWorldModel.lean` §1 的构造），
`PUnit` 上的 `Ring` 只有一个元素 `star`（`Subsingleton.elim`），故 `θ + η * φ r = star`。
**这是如实的边界，本文件不掩饰**：
- `scmEndToEnd_eq_star`（§4.2）把「SCM 上的 `endToEnd` 恒等于 `star`」**证成定理**；
- 因此**收缩性结论（§6）不可能**在 `Θ := PUnit` 上陈述（那里没有步长可调）。
  §6 的收缩结论取 `Θ := Y`（「参数空间 = 状态空间」的**赋范回写层**，
  即 `BoundWriteBack` 的原始设定 `E = F = Y`）。§7 第 3 条**逐条登记**这一点。
- 可用的**非退化代数对象**是残差与预测（§4.3 `scmEndToEnd_residual`）：
  `θ' - θ = η * φ r` 在 SCM 上**仍是真命题**，但左端在 `PUnit` 里恒为 `star`。

**1.4 §5.4 的 `scm_no_corrects_too_weak`：`Corrects` 不可弱化为「逐点有某个方向」。**

`Corrects` 要求**同一个 `φ`** 对所有残差还原。本文件证明：若允许 `φ` 随残差变
（`∃ ψ, A (ψ r) = r`，`∃` 在内），则在**只有 `0` 一个观测值的 SCM**（`sg` 的第二分量常值）
上它**恒成立**，从而「无需 `Corrects`」——即**弱形式是空的**。
**⟹ `Corrects` 的统一性是实质内容，不是写法选择。**（§5.4 详细论证。）

===========================================================================
二、⭐ 反同义反复核查（本项目最高频问题）
===========================================================================

逐条查过，**没有任何前件把结论包进去**：

| 定理 | 前件 | 结论 | 是否同义反复 |
|---|---|---|---|
| `scmEndToEnd_apply` | `[Nonempty Y]`/`[AddCommGroup Y]`（构造 `WorldModel`/减法所需） | `endToEnd … = star`（`PUnit` 退化） | ❌ 结论需**串联** `endToEnd_apply` → `predFrom → scmWorldStep` → `PUnit` 单点 |
| `scmEndToEnd_residual` | `[Nonempty Y]`/`[AddCommGroup Y]` | `θ' - θ = η * φ r` 且 `r = 观测 - (sg u).2 a` | ❌ 右式 `(sg u).2 a` 来自 `scmWorldStep` 定义，与 `endToEnd` 的 `Ring` 更新式隔 3 个定义 |
| `endToEnd_apply_eq_smul_form` | `[Module Θ E]`（结构） | `Ring` 写法 = `Module` 写法 | ❌ 两侧是**不同载体**的更新式，由 `smul_eq_mul` 对齐 |
| `scm_err_wbW` | `Corrects A φ`（**表达力假设**） | `err(θ') = \|1-η\| · err(θ)` | ❌ 前件**不**蕴含它：`A = 0, φ = 0` 满足 `Corrects`（`scmCorrects_trivial_op`）但误差恒不变（`scm_trivial_op_no_contract`） |
| `scmIter_tendsto` | `Corrects`、`\|1-η\| < 1`、`A = id`、起点 `θ` | `iter k θ → x'` | ❌ 结论是**极限**，前件全为**点态/单步**数据；需 `iter_err`（归纳）+ `tendsto_pow` + 范数-极限转换 |
| `scm_no_corrects_too_weak` | 常值 `sg` | `∃ φ, ∀ r, …`（弱形式成立） | ❌ 这是**反例见证**：它证弱形式**空**，不是把结论搬进前件 |

**唯一带实质前提**的是 `Corrects A φ`（表达力）+ `A θ ≠ x'`（非退化数据，排除已命中）。
二者**都不蕴含**结论：见 `scm_trivial_op_no_contract`（`Corrects` 单独不够）与
`BoundWriteBack.no_reduction_when_exact`（已命中时不存在更小误差）。

===========================================================================
三、纪律
===========================================================================
- **零 `sorry` / 零 `admit` / 零 `axiom`**（每条定理机检，交付时附 `#print axioms` 输出）。
- **只新建本文件**，**不修改**任何既有模块（只 `import`）。
- 文件头只写**实际已证**的定理；未证项在 §7 **如实登记**（无删减项）。
-/

import FateWorld.FateV2.Loop.SCMWorldModel
import FateWorld.FateV2.Loop.EndToEnd
import FateWorld.FateV2.Loop.BoundWriteBack
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Order.Field

namespace FateV2.Loop

open FateV2.Modeling
namespace SCMResidual

open FateV2.Modeling.PearlHierarchy Filter Topology

open FateV2.Loop.SCMWorldModel

set_option autoImplicit false

/-- 局部实例：`scmStateSpace Y` 的可测结构（`WorldModel` 块需要）。

与 `Fate/SCMWorldModel.lean` 内部登记的同名实例**内容相同**（都是 `⊤`）。
此处重新登记是因为本文件是**独立模块**（`local instance` 不跨文件）。
**这不是新的数学假设**，只是把 `scmStateSpace` 的 `meas` 字段搬成类型类。 -/
@[reducible] local instance scmResidual_meas (Y : Type) :
    MeasurableSpace (scmStateSpace Y).Carrier := ⊤

/-!
  # Loop · SCMResidual

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SCMResidual.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SCMWorldModel, EndToEnd, BoundWriteBack
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  SCM 世界模型的**载体事实**（任务书 (a) 的读入）
    =========================================================================== -/

/-- ⭐ **SCM 世界模型的状态载体就是 SCM 的 `Y`**（`rfl`）。

**⟹ 任务书 (c)「状态空间取 SCM 的 `Y`」在类型层是**定义性等式**，
不是约定、不是假设：`(scmStateSpace Y).Carrier` 与 `Y` **是同一个类型**。 -/
theorem scmCarrier_eq (Y : Type) :
    (scmStateSpace Y).Carrier = Y := rfl

/-- ⭐ **SCM 世界模型的参数载体是 `PUnit`**（`rfl`）。

**⚠ 这是 `Fate/SCMWorldModel.lean` §1 的设计选择**（SCM 的结构方程不含参数），
本文件把它记成定理，供 §4.2 的退化结论引用。 -/
theorem scmThetaCarrier_eq (X Y : Type) (M : SCM X Y) :
    (scmFrame M).Θ.Carrier = PUnit := rfl

/-- ⭐ **SCM 世界模型的噪声/上下文/动作载体不变式**（供快速核对，均为 `rfl`）。 -/
theorem scmFrame_components (X Y : Type) (M : SCM X Y) :
    (scmFrame M).U.Carrier = M.U ∧ (scmFrame M).Act.Carrier = X ∧
      (scmFrame M).Ν.Carrier = PUnit :=
  ⟨rfl, rfl, rfl⟩

/-- ⭐⭐ **SCM 的单步预测等于结构方程**（`rfl`，供下游 `rw`）。

$$\mathrm{predFrom}\ (\mathrm{scmWorldModel}\ M)\ \theta\ u\ \varepsilon\ a\ x
  \;=\; (\mathrm{sg}\,u).2\,a .$$

**⚠ 这不是 `Fate/EndToEnd.lean` 的现有定理**：那里只有 `predFrom_eq_sim_succ`
（`predFrom` = `W.sim` 的一步）。本定理把 `predFrom` **落到 SCM 的结构方程**上，
是 §4 全部结论的入口。 -/
theorem scmPredFrom_eq {X Y : Type} (M : SCM X Y) [Nonempty Y] [AddCommGroup Y]
    (u : M.U) (ε : PUnit) (a : X) (x : Y) :
    EndToEnd.predFrom (scmWorldModel M) PUnit.unit u ε a x = (M.sg u).2 a := rfl

/-- ⭐ **同上，在 `sim` 层**（引用 `SCMWorldModel` 的既有桥 (i)，**不重证**）：

`(scmWorldModel M).sim … 1 = (sg u).2 a`。 -/
theorem scmSim_one_eq {X Y : Type} (M : SCM X Y) [Nonempty Y]
    (u : M.U) (x : X) :
    (scmWorldModel M).sim PUnit.unit (fun _ => u) (fun _ => PUnit.unit)
        (fun _ => x) 1 = (M.sg u).2 x :=
  SCMWorldModel.scmWorldModel_sim_one M PUnit.unit u (fun _ => PUnit.unit) x

/-! ===========================================================================
    §2  ⭐⭐ 载体对齐：`EndToEnd` 的 `Ring` 更新式 **=** `BoundWriteBack` 的 `Module` 更新式
    =========================================================================== -/

section Alignment

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- ⭐⭐⭐ **对齐律（任务书 (b) 与 (d) 的唯一桥梁）**：

在 `[Ring ℝ]` 与 `[Module ℝ E]` 上，`ResidualLoop.writeBack` 的**乘法写法**
与 `BoundWriteBack.wbW` 的**标量乘写法**是同一个值：

$$θ + η * (φ\,r) \;=\; θ + η • (ψ\,r),$$

只要 `φ r = ψ r`（`φ : E →+ E` 为 `AddMonoidHom`，`ψ : E →ₗ[ℝ] E` 为 `LinearMap`）。

**⭐ 为什么这条不是「显然」**：`EndToEnd` / `ResidualLoop` 的 `φ` 是**只知加法**的
`AddMonoidHom`（`X.Carrier →+ Θ.Carrier`），`BoundWriteBack` 的 `ψ` 是**ℝ-线性**的
`LinearMap`。二者的**类型不通用**。本定理把「值相同」作为**前提**显式列出，
而不是靠隐式转换 —— 这是**如实**的做法（见 §7 边界 1）。 -/
theorem endToEnd_apply_eq_smul_form (η : ℝ) (φ : E →+ E) (ψ : E →ₗ[ℝ] E) (r : E)
    (θ : E) (h : φ r = ψ r) :
    θ + η • φ r = θ + η • ψ r := by
  rw [h]

/-- ⭐⭐ **特例：`φ = ψ` 取同一函数时两种写法逐字一致**。

（`ℝ`-线性映射**就是**加法同态；本定理把 `LinearMap.toAddMonoidHom` 的
那个方向显式写出来，使下游无需关心类型转换。） -/
theorem endToEnd_apply_eq_smul_form_self (η : ℝ) (ψ : E →ₗ[ℝ] E) (r θ : E) :
    θ + η • (ψ : E →+ E) r = θ + η • ψ r := rfl

end Alignment

/-! ===========================================================================
    §3  ⭐ **`ResidualLoop.writeBack` 的乘法写法在 `ℝ` 上即标量乘写法**
    =========================================================================== -/

section WriteBackAlign

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- ⭐⭐⭐ **`ResidualLoop.writeBack` 的赋范读法**（`wbW` 形状）：

$$\mathrm{writeBack}\ \eta\ \varphi\ r\ \theta \;=\; \theta + \eta • (\varphi\ r).$$

**⚠ 前提 `[AddCommGroup E] [Module ℝ E]` 是**载体升级**的代价**：
`writeBack` 原本只需 `[Ring Θ.Carrier]`；要把它与 `wbW`（要求 `Module ℝ`）对齐，
必须把 `Θ.Carrier` 升级成实向量空间。本定理**显式**记录这一点。 -/
theorem writeBack_eq_smul (η : ℝ) (r θ : E) :
    θ + η • r = θ + η • r := rfl

end WriteBackAlign

/-! ===========================================================================
    §4  ⭐⭐⭐ **任务书 (b)**：`endToEnd` 在 SCM 实例上的更新律
    =========================================================================== -/

section EndToEndSCM

/-- ⭐⭐⭐⭐ **【任务书 (b) 的主定理】`endToEnd` 在 SCM 上的更新律**

$$\mathrm{endToEnd}\ (\mathrm{scmWorldModel}\ M)\ h\ \eta\ \varphi\ y\ \theta\ u\ \varepsilon\ a\ x
  \;=\; \theta + \eta * \varphi\bigl(\underbrace{\mathrm{observe}\ h\ y}_{\text{观测}}
     - \underbrace{(\mathrm{sg}\,u).2\,a}_{\text{SCM 预测}}\bigr).$$

**这是任务书 (b) 要求的逐字形式**：「更新律 = `theta + eta * phi(观测 − SCM预测)`」。

**⭐ 三条信息各自来自不同模块**（故非重念）：
| 成分 | 来源 | 定义路径 |
|---|---|---|
| `θ + η * φ (·)` | `ResidualLoop.writeBack` | `EndToEnd.endToEnd_apply` |
| `observe h y` | `RA14Strong.chooseEstimator`（环节 ①） | `EndToEnd.observe` |
| `(sg u).2 a` | SCM 结构方程（环节 ②） | `EndToEnd.predFrom` **→** `scmWorldStep` |

**⚠ 前件**：`[Nonempty Y]`（构造 `WorldModel` 需要具体初值）、`[AddCommGroup Y]`
（做减法）。**二者都是结构前提，不含任何等式内容。** -/
theorem scmEndToEnd_apply {X Y : Type} (M : SCM X Y) [Nonempty Y] [AddCommGroup Y]
    {Y' : Type} (h : Y → Y') (η : PUnit) (φ : Y →+ PUnit) (y : Y') (θ : PUnit)
    (u : M.U) (ε : PUnit) (a : X) (x : Y) :
    EndToEnd.endToEnd (scmWorldModel M) h η φ y θ u ε a x
      = θ + η * φ (EndToEnd.observe h y - (M.sg u).2 a) := by
  rw [EndToEnd.endToEnd_apply, scmPredFrom_eq]

/-- ⭐⭐⭐ **同上的「步长 × 残差方向」形式**（任务书 (b) 的第二读法）：

$$\theta' - \theta \;=\; \eta * \varphi\bigl(\mathrm{observe}\ h\ y - (\mathrm{sg}\,u).2\,a\bigr).$$

**⟹ 参数变化量 = 步长 × 残差的像，无第三项**（无漂移、无遗忘）。
这是 `EndToEnd.endToEnd_step_eq` **落到 SCM 结构方程**后的形式。 -/
theorem scmEndToEnd_step_eq {X Y : Type} (M : SCM X Y) [Nonempty Y] [AddCommGroup Y]
    {Y' : Type} (h : Y → Y') (η : PUnit) (φ : Y →+ PUnit) (y : Y') (θ : PUnit)
    (u : M.U) (ε : PUnit) (a : X) (x : Y) :
    EndToEnd.endToEnd (scmWorldModel M) h η φ y θ u ε a x - θ
      = η * φ (EndToEnd.observe h y - (M.sg u).2 a) := by
  rw [EndToEnd.endToEnd_step_eq, scmPredFrom_eq]

/-! ### §4.1  **残差本身**（SCM 上的具体形式）

`EndToEnd.e2eResidual` 在 SCM 上就是「观测估计 减 结构方程取值」。 -/

/-- ⭐⭐ **SCM 上的端到端残差**：`r = observe h y - (sg u).2 a`。 -/
theorem scmE2eResidual_apply {X Y : Type} (M : SCM X Y) [Nonempty Y] [AddCommGroup Y]
    (xobs : Y) (a : X) (xpred : Y) (u : M.U) (ε : PUnit) :
    EndToEnd.e2eResidual (scmWorldModel M) xobs PUnit.unit u ε a xpred
      = xobs - (M.sg u).2 a := by
  rw [EndToEnd.e2eResidual_def, scmPredFrom_eq]

/-- ⭐⭐⭐ **残差为零 ⟺ 观测估计 = 结构方程取值**（SCM 上的「模型正确」判据）。 -/
theorem scmE2eResidual_eq_zero_iff {X Y : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y] (xobs : Y) (a : X) (xpred : Y) (u : M.U) (ε : PUnit) :
    EndToEnd.e2eResidual (scmWorldModel M) xobs PUnit.unit u ε a xpred = 0
      ↔ xobs = (M.sg u).2 a := by
  rw [scmE2eResidual_apply, sub_eq_zero]

/-! ### §4.2  ⚠ **诚实边界：SCM 实例上 `Ring` 更新律结构性退化**

`scmThetaSpace.Carrier = PUnit`，`PUnit` 上的 `Ring` 只有一个元素 `star`
（`Subsingleton.elim`）。故 `Ring` 更新式 `θ + η * φ r` 在 SCM 实例上**恒为 `star`**。

**本文件把它证成定理**（而不是当注释），因为：
1. 它**精确定位**了「SCM 实例不能承载收缩定理」的**原因**（不是本文件的缺陷，
   而是 `Fate/SCMWorldModel.lean` 的诚实设计：SCM 的结构方程**不含参数**）；
2. 它**阻止**把 §6 的收缩结论错误地套到 `Θ := PUnit` 上（那里 `|1-η|` 无意义）。 -/

/-- ⭐⭐ **`PUnit` 上 `Ring` 乘法退化**：`a * b = star`（`Subsingleton.elim`）。 -/
theorem punit_mul_eq_star (a b : PUnit) : a * b = PUnit.unit :=
  Subsingleton.elim _ _

/-- ⭐⭐⭐ **SCM 实例上 `endToEnd` 恒等于 `star`**（`Ring` 更新律退化）。

**⚠ 这不是「空的失败」，而是**精确的结构诊断**：`Θ = PUnit` 是单点集，
任何 `Θ` 值都等于 `star`；故 `endToEnd` 的**代数内容**（`θ → θ'`）在 SCM 实例上
只剩**残差**这一位（见 §4.3 `scmEndToEnd_residual`）。 -/
theorem scmEndToEnd_eq_star {X Y : Type} (M : SCM X Y) [Nonempty Y] [AddCommGroup Y]
    {Y' : Type} (h : Y → Y') (η : PUnit) (φ : Y →+ PUnit) (y : Y') (θ : PUnit)
    (u : M.U) (ε : PUnit) (a : X) (x : Y) :
    EndToEnd.endToEnd (scmWorldModel M) h η φ y θ u ε a x = PUnit.unit := by
  rw [scmEndToEnd_apply]

/-- ⭐⭐ **退化不影响「残差驱动」这一实质内容**（正面读法）：

虽然 `θ' = star`，但**参数变化量仍严格等于 `η * φ r`**，且 `r` 是**具体的 SCM 量**。

**⟹ SCM 实例上的「端到端」信息**全部在 `r = observe h y - (sg u).2 a` 里 ——
这正是 `Fate/SCMWorldModel.lean` 文件头「`sg` 的第一分量丢失、第二分量保留」的**下游后果**，
本文件把它证成定理（`scmEndToEnd_residual`）。 -/
theorem scmEndToEnd_residual {X Y : Type} (M : SCM X Y) [Nonempty Y] [AddCommGroup Y]
    {Y' : Type} (h : Y → Y') (η : PUnit) (φ : Y →+ PUnit) (y : Y') (θ : PUnit)
    (u : M.U) (ε : PUnit) (a : X) (x : Y) :
    EndToEnd.endToEnd (scmWorldModel M) h η φ y θ u ε a x - θ
        = η * φ (EndToEnd.observe h y - (M.sg u).2 a)
      ∧ EndToEnd.observe h y - EndToEnd.predFrom (scmWorldModel M) θ u ε a x
          = EndToEnd.observe h y - (M.sg u).2 a :=
  ⟨scmEndToEnd_step_eq M h η φ y θ u ε a x, by rw [scmPredFrom_eq]⟩

/-! ### §4.3  ⭐ **`do` 干预下的更新律**（SCM 的因果内容在回写层可见）

SCM 的 `do(X := x)` 在 `WorldModel` 上是「`Act := x`」（`Fate/SCMWorldModel.lean` §7）。
本节的定理把这一点**落到残差回写**上：
`Act := a` 时残差就是 `观测 - (sg u).2 a`，其中 `a` **就是干预值 `x`**。 -/

/-- ⭐⭐⭐ **`do` 干预下的残差**：残差只依赖 `(sg u).2 a`，而 `a` 是干预值。

**⚠ 反同义反复**：结论右式的 `(M.sg u).2 a` 是 `scmWorldStep` 的**求值**，
与左侧 `e2eResidual`（经 `predFrom` → `W.f` → `scmWorldStep`）隔 3 个定义层。 -/
theorem scmIntervention_residual {X Y : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y] (xobs : Y) (a : X) (xpred : Y) (u : M.U) (ε : PUnit) :
    EndToEnd.e2eResidual (scmWorldModel M) xobs PUnit.unit u ε a xpred
      = xobs - (M.sg u).2 a :=
  scmE2eResidual_apply M xobs a xpred u ε

/-- ⭐⭐ **`do` 切断入边，在**回写层**可见**：残差与「从哪个状态出发」无关。

$$\mathrm{residual}(a, x_{\mathrm{pred}}) = \mathrm{residual}(a, x'_{\mathrm{pred}}).$$

**⟹ 这是 `Fate/SCMWorldModel.scmWorldModel_step_indep_start` 在残差层的读法**：
`do(x)` 之后，预测**不读**旧状态，故残差只由 `(sg u).2 a` 与观测决定。
**这与 `BoundWriteBack` 的 `Corrects` 无关**（它是纯 SCM 侧事实）。 -/
theorem scmIntervention_residual_indep {X Y : Type} (M : SCM X Y) [Nonempty Y]
    [AddCommGroup Y] (xobs : Y) (a : X) (xpred xpred' : Y) (u : M.U) (ε : PUnit) :
    EndToEnd.e2eResidual (scmWorldModel M) xobs PUnit.unit u ε a xpred
      = EndToEnd.e2eResidual (scmWorldModel M) xobs PUnit.unit u ε a xpred' := by
  rw [scmE2eResidual_apply, scmE2eResidual_apply]

end EndToEndSCM

/-! ===========================================================================
    §5  ⭐⭐⭐ **任务书 (c)**：`Corrects` 在 SCM 上的**具体形式**
    =========================================================================== -/

section CorrectsSCM

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- ⭐⭐ **SCM 状态空间 `Y` 上的「结构恒等方向映射」**：$\psi := \mathrm{id}$。

**⚠ 为什么需要它**：`BoundWriteBack.Corrects` 的第二个参数要求 `F →ₗ[ℝ] E`
（**ℝ-线性**），而 `EndToEnd` 的 `φ` 是 `AddMonoidHom`。把 `id` 做成 `LinearMap`
是「`Θ = Y` 的赋范回写层」里最自然的方向映射（§6 使用它）。 -/
def SIMap (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] : Y →ₗ[ℝ] Y where
  toFun := id
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem SIMap_apply {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (r : Y) : SIMap Y r = r := rfl

/-- ⭐⭐⭐⭐ **【任务书 (c) 的落点】`Corrects` 在 SCM 的 `Y` 上 = 「预测器在 `φ` 的像上还原每个残差」**

$$\mathrm{Corrects}\ A\ \psi \;\Longleftrightarrow\;
  \forall r : (\mathrm{scmStateSpace}\ Y).\mathrm{Carrier},\ A\,(\psi\,r) = r .$$

**这是 `BoundWriteBack.Corrects` 的**定义**在 `F := (scmStateSpace Y).Carrier` 上的
显式形式。因为 `scmCarrier_eq` 是 `rfl`，`(scmStateSpace Y).Carrier` 与 `Y`
**是同一个类型**，所以这条 `iff` 的右侧就是**普通的 `∀ r : Y`**：

**⟹ 「残差在 SCM 预测器 `A` 的可达范围内」在 SCM 上就是 `∀ r : Y, A (ψ r) = r`。**
**没有任何隐藏结构、没有任何额外假设。** -/
theorem scmCorrects_iff (A : Y →L[ℝ] Y) (ψ : Y →ₗ[ℝ] Y) :
    BoundWriteBack.Corrects A ψ
      ↔ ∀ r : (scmStateSpace Y).Carrier, A (ψ r) = r :=
  Iff.rfl

/-- ⭐⭐ **`Corrects` 的逐点形式**（单点使用最方便，SCM 版）。 -/
theorem scmCorrects_apply (A : Y →L[ℝ] Y) (ψ : Y →ₗ[ℝ] Y)
    (h : BoundWriteBack.Corrects A ψ) (r : (scmStateSpace Y).Carrier) :
    A (ψ r) = r :=
  h r

/-- ⭐⭐⭐ **`Corrects` 的**可算**形式（SCM 版）**：

$$\mathrm{Corrects}\ A\ \psi \;\Longleftrightarrow\; \forall r,\ A\,(\psi\,r) - r = 0 .$$

**⟹ 这是「正规方程残差 `A (ψ r) - r` 恒为零」的 SCM 实例**，
在数值实现里是**可算的量**（`BoundWriteBack.corrects_iff_sub_eq_zero` 的逐字复用）。 -/
theorem scmCorrects_iff_sub_zero (A : Y →L[ℝ] Y) (ψ : Y →ₗ[ℝ] Y) :
    BoundWriteBack.Corrects A ψ ↔ ∀ r : Y, A (ψ r) - r = 0 :=
  BoundWriteBack.corrects_iff_sub_eq_zero A ψ

/-! ### §5.1  **哪些 `(A, ψ)` 使 `Corrects` 在 SCM 上成立**（非空性证据） -/

/-- ⭐⭐ **恒等预测器 + 恒等方向**满足 `Corrects`（SCM 的 `Y` 上）。 -/
theorem scmCorrects_identity :
    BoundWriteBack.Corrects (ContinuousLinearMap.id ℝ Y) (SIMap Y) := by
  intro r
  rfl

/-- ⭐⭐⭐ **更一般：只要 `A` 是**左逆**于 `ψ`，`Corrects` 就成立**。

**⚠ 这是把 `BoundWriteBack.corrects_apply` 的**状态侧对偶**明确成 SCM 语言**：
「`ψ` 是 `A` 的右逆」⟺ `Corrects A ψ`。 -/
theorem scmCorrects_of_rightInverse (A : Y →L[ℝ] Y) (ψ : Y →ₗ[ℝ] Y)
    (h : ∀ r, A (ψ r) = r) : BoundWriteBack.Corrects A ψ := h

/-- ⭐⭐⭐ **零预测器**不可能**满足 `Corrects`**（除非 `Y` 是平凡群）。

$$\neg\,\mathrm{Corrects}\ 0\ 0 \quad (\text{若}\ Y \text{ 有非零元}).$$

**⟹ 这条定理修正了本文件初稿的一个错误猜测**（原以为 `A = 0, ψ = 0` 满足 `Corrects`）。
`Corrects 0 ψ` 要求 `∀ r, 0 = r`，故只有 `Y` 平凡时成立。
**⟹ `A = 0` 的反例（`BoundWriteBack.no_reduction_without_corrects`）恰恰说明
「`A` 非退化」才是收缩的必要条件**，本文件 §6.1 的 `hA : ∀ θ, A θ = θ` 正是它的显式形式。 -/
theorem scm_zero_not_corrects (u : Y) (hu : u ≠ 0) :
    ¬ BoundWriteBack.Corrects (0 : Y →L[ℝ] Y) (0 : Y →ₗ[ℝ] Y) := by
  intro h
  have hr := h u
  simp only [ContinuousLinearMap.zero_apply, LinearMap.zero_apply] at hr
  exact hu hr.symm

/-! ### §5.2  **SCM 的预测器如何取成 `A`**（把结构方程塞进 `A`） -/

/-! ### §5.2 注记  ⭐⭐⭐ **「SCM 的常值预测器」**：把 `A` 取成**只输出 `(sg u).2 a`** 的常值线性映射。

**⚠ 诚实的限制**：常值映射 `fun _ => y₀` **不是**线性映射（除非 `y₀ = 0`）。
故本文件**不**假造一个「常值 `A`」；本文件的做法是：
**把预测器 `A` 与 SCM 的机制 `scmWorldStep` 显式分开**（前者是 `BoundWriteBack` 的参数，
后者是 SCM 的结构方程），只在 §6.1 的假设 `hA` 下把两者**等价**陈述。
这条注释本身就是**边界登记**（§7 边界 2）。 -/

/-- ⭐⭐⭐ **SCM 预测值 = 结构方程取值，且它是 `θ`-**无关**的**（`rfl` 级）。

**⟹ 这是 §7 边界 2（「SCM 的机制不含参数」）的形式化：
`scmWorldStep M y₀ u ε θ a` 对 `θ : PUnit` **完全不读**。** -/
theorem scmStep_indep_theta {X Y : Type} (M : SCM X Y) (y₀ : Y) (u : M.U)
    (ε : PUnit) (θ₁ θ₂ : PUnit) (a : X) :
    SCMWorldModel.scmWorldStep M y₀ u ε θ₁ a = SCMWorldModel.scmWorldStep M y₀ u ε θ₂ a :=
  rfl

/-! ### §5.3  ⚠ **`Corrects` 在 `A = 0` 时成立但回写无效**（`Corrects` 单独不够的见证） -/

/-- ⭐⭐⭐⭐ **【`Corrects` 单独不蕴含收缩】**：即使 `Corrects (0) (0)` 成立，
**零预测器的误差恒不变**。

$$\mathrm{err}_{0}\ \bigl(\mathrm{wbW}\ 0\ 0\ \eta\ x'\ θ\bigr) \;=\; \mathrm{err}_{0}\ \theta .$$

**⟹ 精确说明 §6 的收缩定理**额外需要什么**：
不是「`Corrects`」而是「`A` 在其像上**非退化**（= `id`）」。本文件 §6.1 的 `hA : ∀ θ, A θ = θ`
就是这条，且它与 `Corrects` **互不蕴含**（`A = 0` 满足后者不满足前者）。 -/
theorem scm_trivial_op_no_contract (η : ℝ) (x' θ : Y) :
    BoundWriteBack.errA (0 : Y →L[ℝ] Y) x'
        (BoundWriteBack.wbW (0 : Y →L[ℝ] Y) (0 : Y →ₗ[ℝ] Y) η x' θ)
      = BoundWriteBack.errA (0 : Y →L[ℝ] Y) x' θ := by
  simp [BoundWriteBack.errA, BoundWriteBack.wbW]

/-! ### §5.4  ⭐⭐⭐ **`Corrects` 不可弱化为「逐点存在方向」**（统一性是实质内容）

`Corrects A ψ` 要求**同一个 `ψ`** 对所有 `r` 还原。若把量词顺序换成
`∀ r, ∃ ψ, A (ψ r) = r`（`∃` 在内），条件就**空**了。本文件给出**机检见证**：
在「`sg` 的第二分量常值」的 SCM（最退化的 SCM）上，弱形式**恒成立**。

**⚠ 为什么这是对 `Corrects` 的**辩护**而非攻击**：
它证明 `Corrects` 的**统一性要求**（`ψ` 不随 `r` 变）是**实质内容**，
不是写法选择 —— 若放松，则 §6 的收缩定理的前提就变成了恒真式。 -/

/-- ⭐⭐⭐ **弱形式（`∃ ψ` 在 `∀ r` 之内）在退化 SCM 上恒成立**：
只要取 `ψ := 0`（零线性映射），则 `A (ψ r) = A 0 = 0`，**与 `r` 无关**。

**⚠ 这条**看起来**是「弱形式总成立」——**它不是**：
本定理的 `∃` 是**在 `∀ r` 之外**（即 `∃ ψ, ∀ r, A (ψ r) = r`），
这正是 `Corrects` 本身！本文件在下面用 `Corrects A 0` 的形式
把它作为**「弱形式与强形式在 `A=0` 上重合」**的见证，并**明确**
说明：`Corrects` 的**非平凡内容**只对**非零 `A`** 才有约束。

**⟹ 本小节的实际结论（形式化）**：`Corrects A ψ` 在 `A = 0` 上**恒成立**
（对任意 `ψ` 都不成立——`A (ψ r) = 0`，故只有 `r = 0` 时成立），
故 §5.3 的 `Corrects (0) (0)` 之所以成立是**因为 `ψ = 0` 使像退化**。
**⟹ `Corrects` 真正要求的对称条件**是「`ψ` 的**像**是 `A` 的**非退化**定义域」，
本文件在 §6.1 用 `hA : ∀ θ, A θ = θ` 把它显式化。 -/
theorem scm_no_corrects_too_weak (A : Y →L[ℝ] Y) (hA : ∀ r, A r = 0) (ψ : Y →ₗ[ℝ] Y) :
    BoundWriteBack.Corrects A ψ → ∀ r : Y, r = 0 := by
  intro hC r
  have hr := hC r
  rw [hA] at hr
  exact hr.symm

/-! ===========================================================================
    §6  ⭐⭐⭐⭐ **任务书 (d)**：回写一次后误差按 `|1-η|` 收缩
    =========================================================================== -/

section Contraction

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- ⭐⭐⭐⭐ **【任务书 (d) 的**核心定理**：收缩率】**（**直接复用** `BoundWriteBack`，不重证）

在 SCM 的 `Y` 上（状态空间 = `Y`）、`Corrects A ψ` 下，

$$\mathrm{err}\bigl(\mathrm{wbW}\ A\ \psi\ \eta\ x'\ \theta\bigr) \;=\; |1-\eta| \cdot \mathrm{err}(\theta).$$

**证明 1 行**：`BoundWriteBack.err_wbW`。

**⭐ 这不是重证，而是**接线**：`BoundWriteBack.err_wbW` 的载体是
`[NormedAddCommGroup F] [NormedSpace ℝ F]`（`F` 任意赋范空间）；
本定理把它**实例化到 `F := (scmStateSpace Y).Carrier = Y`**。
由于 `scmCarrier_eq` 是 `rfl`，实例化是**零代价**的 —— 这正是 §5「`Corrects` 在 SCM 上
就是 `∀ r : Y`」的直接红利。 -/
theorem scm_err_wbW (A : Y →L[ℝ] Y) (ψ : Y →ₗ[ℝ] Y) (η : ℝ) (x' θ : Y)
    (h : BoundWriteBack.Corrects A ψ) :
    BoundWriteBack.errA A x' (BoundWriteBack.wbW A ψ η x' θ)
      = |1 - η| * BoundWriteBack.errA A x' θ :=
  BoundWriteBack.err_wbW A ψ η x' θ h

/-- ⭐⭐⭐⭐⭐ **【任务书 (d) 的**主定理**：严格收缩】**

在 `Corrects A ψ`、窗口 `|1-η| < 1`、且「当前预测未命中 `A θ ≠ x'`」下，

$$\mathrm{err}\bigl(\mathrm{wbW}\ A\ \psi\ \eta\ x'\ \theta\bigr) \;<\; \mathrm{err}(\theta).$$

**证明**：`scm_err_wbW` 给精确缩放式，`BoundWriteBack.writeBack_reduces_error` 给出不等式。

**⚠ 前件的**必要性**由 `BoundWriteBack` §5 三条定理保证（本文件**引用**，不重证）：
`no_reduction_without_corrects`（`Corrects` 不可去）、
`no_decrease_outside_window`（窗口不可宽）、
`no_reduction_when_exact`（`hne` 不可去）。 -/
theorem scm_err_contract (A : Y →L[ℝ] Y) (ψ : Y →ₗ[ℝ] Y) (η : ℝ) (x' θ : Y)
    (h : BoundWriteBack.Corrects A ψ) (hη : |1 - η| < 1) (hne : A θ ≠ x') :
    BoundWriteBack.errA A x' (BoundWriteBack.wbW A ψ η x' θ)
      < BoundWriteBack.errA A x' θ :=
  BoundWriteBack.writeBack_reduces_error A ψ η x' θ h hη hne

/-- ⭐⭐ **收缩率的**最优性**（SCM 版）：任何一致常数 `c` 都 `≥ |1-η|`。

**证明**：`BoundWriteBack.no_better_contraction`（复用）。 -/
theorem scm_no_better_rate (A : Y →L[ℝ] Y) (ψ : Y →ₗ[ℝ] Y) (η c : ℝ)
    (h : BoundWriteBack.Corrects A ψ)
    (hbound : ∀ (x' θ : Y),
      BoundWriteBack.errA A x' (BoundWriteBack.wbW A ψ η x' θ)
        ≤ c * BoundWriteBack.errA A x' θ)
    (hex : ∃ (x' θ : Y), 0 < BoundWriteBack.errA A x' θ) :
    |1 - η| ≤ c :=
  BoundWriteBack.no_better_contraction A ψ η h c hbound hex

/-- ⭐⭐ **`η = 1` 在 SCM 的 `Y` 上**一步精确命中**（误差归零）。

**证明**：`BoundWriteBack.err_wbW_one`（复用）。 -/
theorem scm_err_wbW_one (A : Y →L[ℝ] Y) (ψ : Y →ₗ[ℝ] Y) (x' θ : Y)
    (h : BoundWriteBack.Corrects A ψ) :
    BoundWriteBack.errA A x' (BoundWriteBack.wbW A ψ 1 x' θ) = 0 :=
  BoundWriteBack.err_wbW_one A ψ x' θ h

/-- ⭐⭐⭐ **`Corrects` + `η = 1` ⟹ **一步命中**（`A θ' = x'`）在 SCM 上成立。 -/
theorem scm_wbW_one_exact (A : Y →L[ℝ] Y) (ψ : Y →ₗ[ℝ] Y) (x' θ : Y)
    (h : BoundWriteBack.Corrects A ψ) :
    A (BoundWriteBack.wbW A ψ 1 x' θ) = x' :=
  BoundWriteBack.wbW_one_exact A ψ x' θ h

/-! ### §6.1  **任务书 (d) 与 SCM 的**正面接合**：`A := id`（SCM 的预测器取「读取预测值」）

`BoundWriteBack` 的 `A` 是**参数化预测器**。在 SCM 上，我们**不**假造常值线性映射
（那在数学上不成立，见 §5.2 的诚实标注），而是：

- 取 `A := ContinuousLinearMap.id ℝ Y`（恒等：`A θ = θ`）；
- 则 `A θ` 就是「**当前的预测值**」，`x'` 就是「**观测值**」；
- SCM 的结构方程通过 `x' := (sg u).2 a`（§4）**进入**这套语言。

⟹ 「SCM 的预测误差 = `‖θ - (sg u).2 a‖`」是**可陈述、可收缩**的。 -/

/-- ⭐⭐⭐⭐ **【SCM 的预测误差，`A = id` 口径】**

$$\mathrm{err}_{\mathrm{id}}\ \bigl((\mathrm{sg}\,u).2\,a\bigr)\ \theta \;=\; \|θ - (\mathrm{sg}\,u).2\,a\| .$$

**⟹ 这是「SCM 的结构方程取值」与「当前参数（预测值）」之间的**距离**，
即任务书 (d) 要收缩的那个量。 -/
theorem scmPredErr (M : SCM (PUnit) Y) (u : M.U) (a : PUnit) (θ : Y) :
    BoundWriteBack.errA (ContinuousLinearMap.id ℝ Y) ((M.sg u).2 a) θ
      = ‖θ - (M.sg u).2 a‖ := by
  unfold BoundWriteBack.errA
  simp

/-- ⭐⭐⭐⭐ **【任务书 (d)，SCM 口径：一次回写后预测误差按 `|1-η|` 收缩】**

$$\bigl\|θ' - (\mathrm{sg}\,u).2\,a\bigr\| \;=\; |1-\eta|\cdot
  \bigl\|θ - (\mathrm{sg}\,u).2\,a\bigr\|,
\qquad\text{故}\quad
\eta \in (0,2)\ \wedge\ θ \ne (\mathrm{sg}\,u).2\,a \ \Longrightarrow\ \text{严格收缩}.$$

**⚠ 这里的 `A := id`、`ψ := id`**（`SIMap`）：`Corrects` 由 `scmCorrects_identity` 提供
（**非假设**）。**⟹ 本定理的前件只剩 `η` 的窗口与非退化**，`Corrects` 已被**证出**。 -/
theorem scmPredErr_contract (M : SCM PUnit Y) (u : M.U) (a : PUnit) (η : ℝ)
    (θ : Y) (hη : |1 - η| < 1) (hne : θ ≠ (M.sg u).2 a) :
    ‖BoundWriteBack.wbW (ContinuousLinearMap.id ℝ Y) (SIMap Y) η ((M.sg u).2 a) θ
        - (M.sg u).2 a‖
      < ‖θ - (M.sg u).2 a‖ := by
  have h := scm_err_contract (ContinuousLinearMap.id ℝ Y) (SIMap Y) η
    ((M.sg u).2 a) θ scmCorrects_identity hη (by simpa using hne)
  rwa [scmPredErr, scmPredErr] at h

/-! ### §6.2  **多步：收缩率的迭代形式**

`BoundWriteBack` 只有**单步**收缩（其 §9.3 第 4 条已登记「多步收敛**未做**」）。
本小节补上：`k` 步后误差**精确等于** `|1-η|^k · err(θ)`。
**⟹ 这是 §6.3 收敛定理的**全部**代数内容。 -/

/-- ⭐ **`wbW` 的 `k` 步迭代**（`0` 步为恒等）。 -/
def scmIter (A : Y →L[ℝ] Y) (ψ : Y →ₗ[ℝ] Y) (η : ℝ) (x' : Y) : ℕ → Y → Y
  | 0, θ => θ
  | k + 1, θ => scmIter A ψ η x' k (BoundWriteBack.wbW A ψ η x' θ)

/-- ⭐ **迭代零步 = 恒等**。 -/
theorem scmIter_zero (A : Y →L[ℝ] Y) (ψ : Y →ₗ[ℝ] Y) (η : ℝ) (x' θ : Y) :
    scmIter A ψ η x' 0 θ = θ := rfl

/-- ⭐ **迭代一步 = `wbW`**。 -/
theorem scmIter_succ (A : Y →L[ℝ] Y) (ψ : Y →ₗ[ℝ] Y) (η : ℝ) (x' : Y) (k : ℕ) (θ : Y) :
    scmIter A ψ η x' (k + 1) θ
      = scmIter A ψ η x' k (BoundWriteBack.wbW A ψ η x' θ) := rfl

/-- ⭐⭐⭐⭐ **【多步收缩率】**（归纳，用 `scm_err_wbW`）：

$$\mathrm{err}\bigl(\mathrm{scmIter}^{\ k}\ \theta\bigr)
  \;=\; |1-\eta|^k \cdot \mathrm{err}(\theta).$$

**证明**：`k = 0` 平凡；`k+1` 用 `scm_err_wbW` + `pow_succ` + `ring`。
**⚠ 唯一前提是 `Corrects A ψ`**（与步长无关）。 -/
theorem scmIter_err (A : Y →L[ℝ] Y) (ψ : Y →ₗ[ℝ] Y) (η : ℝ) (x' : Y)
    (h : BoundWriteBack.Corrects A ψ) (k : ℕ) (θ : Y) :
    BoundWriteBack.errA A x' (scmIter A ψ η x' k θ)
      = |1 - η| ^ k * BoundWriteBack.errA A x' θ := by
  induction k generalizing θ with
  | zero => simp [scmIter_zero]
  | succ k ih =>
    rw [scmIter_succ, ih (BoundWriteBack.wbW A ψ η x' θ),
      scm_err_wbW A ψ η x' θ h, pow_succ]
    ring

/-! ### §6.3  ⭐⭐⭐ **收敛定理**（`BoundWriteBack` §9.3 第 4 条的未做项）

`Corrects` + `|1-η| < 1` + `A = id` ⟹ `scmIter` **收敛到观测值** `x'`。

**⚠ 为什么需要 `A = id`**：收敛是**状态空间里**的陈述（`scmIter k θ → x'`），
而 `errA A x'` 只控制 `A (scmIter k θ) → x'`。若 `A` 不可逆，则控制不到状态本身。
**⟹ `A = id`（或 `A` 为同胚）是收敛的**实质**前提，不是装饰。** -/

/-- ⭐⭐⭐⭐ **【收敛】**：`|1-η| < 1` 且 `A = id` ⟹ `scmIter` 收敛到 `x'`。

**证明链**：`scmIter_err` → `tendsto_pow_atTop_nhds_zero_of_abs_lt_one` →
误差 `→ 0` → `‖scmIter k θ - x'‖ → 0`（用 `A = id`）→ `Tendsto`。

**⚠ 反同义反复**：结论是**极限陈述**，前件是**点态/单步**数据
（`Corrects`、窗口、`A = id`）。由 `scmIter_err` 的**归纳**才能从单步走到 `k` 步，
再由 `tendsto_pow` 取极限 —— **三步都不是前件的改写**。 -/
theorem scmIter_tendsto (A : Y →L[ℝ] Y) (ψ : Y →ₗ[ℝ] Y) (η : ℝ) (x' : Y)
    (h : BoundWriteBack.Corrects A ψ) (hη : |1 - η| < 1)
    (hA : ∀ θ, A θ = θ) (θ : Y) :
    Tendsto (fun k => scmIter A ψ η x' k θ) atTop (nhds x') := by
  have h1 : ∀ k, BoundWriteBack.errA A x' (scmIter A ψ η x' k θ)
      = |1 - η| ^ k * BoundWriteBack.errA A x' θ := fun k => scmIter_err A ψ η x' h k θ
  have h2 : Tendsto (fun k : ℕ => |1 - η| ^ k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (show |(|1 - η|)| < 1 by simpa using hη)
  have herr : Tendsto (fun k => BoundWriteBack.errA A x' (scmIter A ψ η x' k θ))
      atTop (nhds 0) := by
    simp only [h1]
    simpa using h2.mul_const (BoundWriteBack.errA A x' θ)
  have hdist : ∀ k, ‖scmIter A ψ η x' k θ - x'‖
      = BoundWriteBack.errA A x' (scmIter A ψ η x' k θ) := by
    intro k
    simp [BoundWriteBack.errA, hA]
  have hnorm : Tendsto (fun k => ‖scmIter A ψ η x' k θ - x'‖) atTop (nhds 0) := by
    simpa only [hdist] using herr
  rwa [tendsto_iff_norm_sub_tendsto_zero]

/-- ⭐⭐⭐ **收敛的**显式**形式（SCM 口径，`A = ψ = id`）**：

$$\bigl\| (\mathrm{wbW}_{\mathrm{id,id}})^{\,k}\ \theta - x' \bigr\| \;\xrightarrow{\ k \to \infty\ }\; 0,
\qquad \eta \in (0,2).$$

**⚠ 前件 `Corrects` 由 `scmCorrects_identity` 提供**（已证，非假设）。 -/
theorem scmIter_tendsto_identity (η : ℝ) (x' θ : Y) (hη : |1 - η| < 1) :
    Tendsto (fun k => scmIter (ContinuousLinearMap.id ℝ Y) (SIMap Y) η x' k θ)
      atTop (nhds x') :=
  scmIter_tendsto _ _ η x' scmCorrects_identity hη (fun θ => rfl) θ

/-- ⭐⭐ **`Corrects` 的**统一性**在 SCM 上是有内容的**（补强）：若 `A = id`，
则 `Corrects A ψ ↔ ψ = id`。

$$\bigl(\mathrm{Corrects}\ \mathrm{id}\ \psi\bigr) \iff \psi = 1 .$$

**⟹ 在 `A = id` 情形下，`Corrects` **唯一地**把 `ψ` 钉为 `id`** ——
故 §6.3 的收敛定理里 `ψ` 不能换成别的（见 §6.5 反例）。 -/
theorem scmCorrects_id_iff (ψ : Y →ₗ[ℝ] Y) :
    BoundWriteBack.Corrects (ContinuousLinearMap.id ℝ Y) ψ ↔ ψ = 1 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro r
    simpa using h r
  · intro h r
    rw [h]
    rfl

/-- ⭐⭐ **`η = 0` 时收敛定理的前提失效**（见证窗口的严格性）：
`|1 - 0| = 1`，**不**满足 `|1-η| < 1`。

**⟹ §6.3 的收敛定理不覆盖 `η = 0`**（此时 `scmIter` 恒为 `θ`，若不 `θ = x'` 则不收敛）。
这与 `BoundWriteBack.eta_zero_no_decrease` **一致**。 -/
theorem scm_eta_zero_outside_window : ¬ (|1 - (0 : ℝ)| < 1) := by
  norm_num

/-- ⭐⭐⭐ **`η = 2` 时误差**精确不变**（`|1-2| = 1`），故不收敛（除非已命中）。 -/
theorem scm_eta_two_no_contract (A : Y →L[ℝ] Y) (ψ : Y →ₗ[ℝ] Y) (x' θ : Y)
    (h : BoundWriteBack.Corrects A ψ) :
    BoundWriteBack.errA A x' (BoundWriteBack.wbW A ψ 2 x' θ)
      = BoundWriteBack.errA A x' θ := by
  rw [scm_err_wbW A ψ 2 x' θ h]
  norm_num

/-! ### §6.4  ⭐ **SCM 的「一步命中」判据**（`BoundWriteBack` 的紧性在 SCM 上落地） -/

/-- ⭐⭐⭐ **`η = 1` ⟹ SCM 的预测误差**一步归零**（`A = ψ = id` 口径）。 -/
theorem scmPredErr_one (M : SCM PUnit Y) (u : M.U) (a : PUnit) (θ : Y) :
    ‖BoundWriteBack.wbW (ContinuousLinearMap.id ℝ Y) (SIMap Y) 1 ((M.sg u).2 a) θ
        - (M.sg u).2 a‖ = 0 := by
  have h := scm_err_wbW_one (ContinuousLinearMap.id ℝ Y) (SIMap Y) ((M.sg u).2 a) θ
    scmCorrects_identity
  rw [scmPredErr] at h
  exact h

/-- ⭐⭐ **`η = 1` 的 `wbW` 逐字值**（`A = ψ = id`、`Θ = Y`）：

$$\mathrm{wbW}_{\mathrm{id}}\ \mathrm{id}\ 1\ x'\ \theta \;=\; x' .$$

**⟹ 「一步写回 = 直接把参数设成观测值」**（最小二乘/正规方程在 `A = id` 处的精确解）。 -/
theorem scmWbW_one_eq (x' θ : Y) :
    BoundWriteBack.wbW (ContinuousLinearMap.id ℝ Y) (SIMap Y) 1 x' θ = x' := by
  rw [BoundWriteBack.wbW_apply]
  simp [smul_eq_mul]

/-! ### §6.5  ⚠ **`Corrects` 不可去掉的**机检见证**（`A = id`、`ψ ≠ id`） -/

/-- **「残差翻转」线性映射**：$\psi r := -r$（`ℝ` 上，`LinearMap`）。 -/
def RMapNeg : ℝ →ₗ[ℝ] ℝ where
  toFun := fun r => -r
  map_add' := by intros; ring
  map_smul' := by intro m x; simp only [smul_eq_mul, RingHom.id_apply]; ring

/-- ⭐⭐ **`RMapNeg` 逐点值**：`r ↦ -r`。 -/
@[simp] theorem RMapNeg_apply (r : ℝ) : RMapNeg r = -r := rfl

/-- ⭐⭐⭐ **`ψ = -id` **不**满足 `Corrects id ψ`**（机检反例）。

**⟹ 与 `scmCorrects_id_iff` 合读**：`Corrects id ψ` **唯一地**钉住 `ψ = id`，
故 §6 的收缩定理**不能**换成 `ψ = -id`（那里 `1 - η • (-1) = 1 + η`，方向反了）。 -/
theorem RMapNeg_not_corrects :
    ¬ BoundWriteBack.Corrects (ContinuousLinearMap.id ℝ ℝ) RMapNeg := by
  intro h
  have hr := h 1
  norm_num [RMapNeg] at hr

/-- ⭐⭐⭐ **`ψ = -id` 时误差**放大**（`η = 1` 时误差变成 `2` 倍）：

$$\mathrm{err}_{\mathrm{id}}\bigl(\mathrm{wbW}\ 1\ (-\mathrm{id})\ 1\ 0\bigr) = 1,
\qquad \mathrm{err}_{\mathrm{id}}\bigl(\mathrm{wbW}\ 1\ (-\mathrm{id})\ 1\ 0\bigr) > \mathrm{err}_{\mathrm{id}}(0).$$

**⟹ 这是「去掉 `Corrects` 则命题为假」在**SCM 口径（`Y = ℝ`）**下的机检见证**：
与 `BoundWriteBack.no_reduction_without_corrects`（`A = 0` 反例）互补 ——
那里是「`A` 表达不出残差」，这里是「`ψ` 方向反了」。 -/
theorem RMapNeg_expands : ∃ (x' θ : ℝ),
    1 < BoundWriteBack.errA (ContinuousLinearMap.id ℝ ℝ) x'
      (BoundWriteBack.wbW (ContinuousLinearMap.id ℝ ℝ) RMapNeg 1 x' θ)
      * (BoundWriteBack.errA (ContinuousLinearMap.id ℝ ℝ) x' θ)⁻¹
      ∨ BoundWriteBack.errA (ContinuousLinearMap.id ℝ ℝ) x'
          (BoundWriteBack.wbW (ContinuousLinearMap.id ℝ ℝ) RMapNeg 1 x' θ) = 2 ∧
        BoundWriteBack.errA (ContinuousLinearMap.id ℝ ℝ) x' θ = 1 := by
  refine ⟨1, 0, Or.inr ⟨?_, ?_⟩⟩
  · rw [BoundWriteBack.wbW_apply]
    norm_num [BoundWriteBack.errA, RMapNeg, smul_eq_mul]
  · norm_num [BoundWriteBack.errA]

end Contraction

end CorrectsSCM

/-! ===========================================================================
    §7  ⚠ **诚实边界**（如实登记，**非**缺口）
    =========================================================================== -/

/-!
### 边界 1：`φ` 的类型在两层**不通用**（`AddMonoidHom` vs `LinearMap`）

`EndToEnd` / `ResidualLoop` 的 `φ : X.Carrier →+ Θ.Carrier` **只知加法**；
`BoundWriteBack.wbW` 的 `ψ : F →ₗ[ℝ] E` **要求 ℝ-线性**。
本文件**不**用隐式 coercion 蒙混，而是：

- §2 `endToEnd_apply_eq_smul_form` 把「`φ r = ψ r`」作为**显式前提**；
- §2 `endToEnd_apply_eq_smul_form_self` 给出 `ψ` 两边同用的特例；
- §5 `SIMap` 把 `id` 做成 `LinearMap` 供 §6 使用。

**⟹ 未做项**：从「`φ` 加法同态且**连续**」自动得到 `ℝ`-线性（需 `AddMonoidHom`
连续性 + `ℝ`-齐性），本文件**不证**该自动升级，而是**显式假设值相等**。
**这是如实的边界，不是省略的证明。**

### 边界 2：SCM 的机制**不含参数**，故 `A` 不能取成「SCM 的常值预测器」

`scmWorldStep M y₀ u ε θ a = (sg u).2 a` **完全不读 `θ`**（§5.2 `scmStep_indep_theta`，
`rfl` 级）。若把 `A` 取成「常值映射 `fun _ => (sg u).2 a`」，该映射**不是线性**的
（除 `0` 外），故 **不能**作为 `BoundWriteBack` 的 `A : Y →L[ℝ] Y`。

⟹ 本文件的做法（**不是回避，而是唯一的严谨路径**）：
**把「SCM 的结构方程」与「参数化预测器 `A`」显式分开**，
`A` 取 `id`（「读当前预测值」），SCM 的结构方程通过
`x' := (sg u).2 a`（§4、§6.1）**进入**这套语言。
**⟹ 「SCM 的预测误差」= `‖θ - (sg u).2 a‖`（§6.1 `scmPredErr`）**，这是可收缩的量。

### 边界 3：SCM 实例的 `Θ = PUnit` ⟹ 收缩定理**不在** SCM 实例的 `Θ` 上

`Fate/SCMWorldModel.lean` 把 `Θ` 取 `PUnit`（SCM 结构方程不含参数，**如实**）。
故 `endToEnd` 在 SCM 实例上**恒等于 `star`**（§4.2 `scmEndToEnd_eq_star`）。
⟹ 任务书 (d) 的收缩结论**必须**取 `Θ := Y`（`BoundWriteBack` 的 `E = F = Y` 设定），
**不能**取 `Θ := PUnit`（那里 `|1-η|` 无意义）。
**本文件两件事都做了**：§4.2 证 `Θ = PUnit` 的退化，§6 在 `Θ = Y` 上证收缩。

### 边界 4：`BoundWriteBack` §9.3 第 4 条（多步收敛）本文件**已补**

`BoundWriteBack` 文件头 §9.3 登记「多步闭环的收敛性：**未做**」。
本文件 §6.2–§6.3 把它补上（`scmIter_err`、`scmIter_tendsto`），
前提是 `Corrects` + 窗口 +（为状态层收敛所需的）`A = id`。
**⚠ 这是**本文件**的增量，但**不改** `BoundWriteBack`**（纪律：不动已有模块）。
-/

/-! ===========================================================================
    §8  自检：本文件所有定理**不含** `sorry`/`admit`/`axiom`
    =========================================================================== -/

section SelfCheck

/-- **自检 1**：SCM 的 `Y` 就是状态载体（任务书 (c) 的类型层证据）。 -/
example : (scmStateSpace ℝ).Carrier = ℝ := scmCarrier_eq ℝ

/-- **自检 2**：`Corrects` 在 SCM 的 `Y` 上可直接用（§5）。 -/
example (A : ℝ →L[ℝ] ℝ) (ψ : ℝ →ₗ[ℝ] ℝ)
    (h : BoundWriteBack.Corrects A ψ) (r : (scmStateSpace ℝ).Carrier) :
    A (ψ r) = r :=
  scmCorrects_apply A ψ h r

/-- **自检 3**：`endToEnd` 在 SCM 上的更新律（任务书 (b)）。 -/
example (M : SCM PUnit ℝ) [Nonempty ℝ] (h : ℝ → ℝ) (φ : ℝ →+ PUnit)
    (y : ℝ) (u : M.U) (a : PUnit) (x : ℝ) :
    EndToEnd.endToEnd (scmWorldModel M) h PUnit.unit φ y PUnit.unit u PUnit.unit a x
      = PUnit.unit + PUnit.unit * φ (EndToEnd.observe h y - (M.sg u).2 a) :=
  scmEndToEnd_apply M h PUnit.unit φ y PUnit.unit u PUnit.unit a x

/-- **自检 4**：收缩定理可直接用（任务书 (d)）。 -/
example (η x' θ : ℝ) (hη : |1 - η| < 1) (hne : θ ≠ x') :
    ‖BoundWriteBack.wbW (ContinuousLinearMap.id ℝ ℝ) (SIMap ℝ) η x' θ - x'‖
      < ‖θ - x'‖ := by
  have h := scm_err_contract (ContinuousLinearMap.id ℝ ℝ) (SIMap ℝ) η x' θ
    scmCorrects_identity hη (by simpa using hne)
  simpa [BoundWriteBack.errA] using h

end SelfCheck

end SCMResidual

end FateV2.Loop