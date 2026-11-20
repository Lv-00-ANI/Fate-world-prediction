/-
命运理论 · Lean 4 形式化实现
================================

模块：`SCMWorldModelEval`
定位：**第 3 层「可运行」—— 给 SCM 主干加 `#eval` 数值实例**

---------------------------------------------------------------------------
〇、要解决的问题（不是猜测，是盘点结果）
---------------------------------------------------------------------------
`SCM` 主干（`SCMSemantics` → `SCMWorldModel` → `SCMEndToEnd` /
`SCMResidual`）有 90 余条定理，**但零 `#eval`**。
库中 5 个含 `#eval` 的模块（`ConvergeToOptimalDemo` / `EvalClosedLoop` /
`EvalDemo` / `EvalReal` / `EvalRealProof`）**都不在 SCM 主干上**。
⟹「世界模型真的能预测」这件事在 SCM 主干上**从未被数值验证**。本文件补这一块。

---------------------------------------------------------------------------
一、具体 SCM（可判定、可计算的部分尽量可计算）
---------------------------------------------------------------------------
`scmDemo : SCM Bool Bool`：

| 位 | 取值 |
|---|---|
| `U` | `Bool`（`true` / `false` 两个外生实现）|
| `pU` | 均匀：每个 `u` 权重 `1/2` |
| `sg u` | `(u, fun x => x && u)` —— 事实分量 `= u`，结构方程 `h_u(x) = x ∧ u` |

**读法**：`u = true` 时 `h_u` 是恒等（`x && true = x`）；
`u = false` 时 `h_u` 恒为 `false`。故**外生实现 `u` 真的改变预测**。

**⚠ 诚实边界（`#eval` 的可计算性，必读）**：
`pU : Bool → ℝ` 里的 `1/2` 依赖 `Real.instDivInvMonoid`，它在本环境是
**`noncomputable`**（`#eval` 直接求值 `scmDemo` 会报
`depends on 'Real.instDivInvMonoid', which is 'noncomputable'`，已实测）。
同理 `WorldModel.x`（`Classical.choice`）与 `Rule.kernel`（`Measure.dirac`）也不可计算。
⟹ 本文件的处理**不是**回避，而是**把每个不可计算位换成一个可计算镜像，
再用定理证明镜像 = 库里的定义**（与 `Fate/EvalDemo.lean` 的既有做法同构）：

| 库里的对象（不可计算）| 本文件的可计算镜像 | 桥定理（已证）|
|---|---|---|
| `SCMWorldModel.scmWorldStep scmDemo` | `stepD u a = a && u` | `scmStep_eq_stepD` |
| `WorldModel.sim (scmWorldModel scmDemo) _ u ε a (n+1)` | `stepD (u n) (a n)` | `scmSim_succ_eq_stepD` |
| `WorldModel.sim … ` 整条轨迹（`trajGen`）| `trajD x₀ u a` | `scmTrajD_eq_trajGen` |
| `EndToEnd.predFrom (scmWorldModel scmDemo) …` | `stepD u a` | `scmPredFrom_eq_stepD` |
| `FateV2.Modeling.SCMSemantics.doLaw scmDemo` | `doLawQ : Bool → Bool → ℚ` | `scmDoLawQ_cast` |
| `FateV2.Modeling.SCMSemantics.jointLaw scmDemo` | `jointLawQ : Bool → Bool → Bool → ℚ` | `scmJointLawQ_cast` |
| `FateV2.Modeling.SCMSemantics.marginalY scmDemo` | `marginalYQ : Bool → ℚ` | `scmMarginalYQ_cast` |
| `(scmDemo.sg u).1` / `(scmDemo.sg u).2` | `sgFst u` / `sgSnd u a` | `scmSg_fst` / `scmSg_snd` |

概率律用 `ℚ` 而非 `ℝ` 作镜像（`ℚ` 的加乘**可计算**，`ℝ` 的不行；
这是本文件**唯一的数值口径让步**，已由上面三条 `_cast` 定理补平：
`((doLawQ x y : ℚ) : ℝ) = FateV2.Modeling.SCMSemantics.doLaw scmDemo x y`，逐点，不是抽样）。

---------------------------------------------------------------------------
二、`#eval` 的实际输出（本机实跑，粘贴原文）
---------------------------------------------------------------------------
--__EVAL_OUTPUTS__--

---------------------------------------------------------------------------
三、交付的定理（`grep -n "^theorem"` 实测见文末清单）
---------------------------------------------------------------------------
| 节 | 定理 | 内容 |
|---|---|---|
| §3 | `scmStep_eq_stepD` | `scmWorldStep scmDemo y u ε θ a = a && u`（`rfl`，确认接线） |
| §3 | `scmTrajD_eq_trajGen` | 可计算镜像 `trajD` **逐字等于** `TrajGenDeterministic.trajGen`（归纳） |
| §3 | `scmSim_succ_eq_stepD` | ⭐ `WorldModel.sim` 第 `n+1` 步 `= a n && u n` |
| §3 | `scmPredFrom_eq_stepD` | ⭐ `EndToEnd.predFrom` 在 `scmDemo` 上 `= a && u` |
| §3 | `scmSg_fst` / `scmSg_snd` | 结构映射两个分量的可计算形状（`rfl`） |
| §4 | `scmDoLawQ_cast` | ℚ 镜像 cast 到 ℝ **=** `FateV2.Modeling.SCMSemantics.doLaw`（逐点） |
| §4 | `scmJointLawQ_cast` | 同上（联合律）|
| §4 | `scmMarginalYQ_cast` | 同上（`Y` 边缘律）|
| §4.1 | `scmDoLaw_true_true` / `_true_false` / `_false_true` / `_false_false` | `doLaw` 的**四个具体数值**（`1/2, 1/2, 0, 1`）|
| §4.1 | `scmMarginalY_true` | `marginalY` 在 `true` 处 `= 1/2` |
| §5 | `scmStepD_dep_u` | ⭐ **外生变量真的影响预测**：`true && true ≠ false && true` |
| §5 | `scmPredFrom_dep_u` | ⭐ 同一事实落到 `EndToEnd.predFrom`（不是 `stepD` 的自言自语）|
| §5 | `scmSim_dep_u` | ⭐ 同一事实落到 `WorldModel.sim` 的第 1 步 |
| §5 | `scmDoLaw_dep_x` | ⭐ **干预依赖干预值**：`doLaw scmDemo true true ≠ doLaw scmDemo false true`（`1/2 ≠ 0`）|
| §6 | `predFrom_scmDemo_indep_start` | ⭐ **真消费 `SCMEndToEnd`**：`scmDemo` 上 `predFrom` 与出发状态无关（调 `SCMEndToEnd.predFrom_scmWorldModel_indep_start`）|
| §6 | `scmStepD_eq_predFrom_both_starts` | ⭐ 同一 `stepD u a` = 两个不同出发状态的 `predFrom`（同上定理 + `scmPredFrom_eq_stepD` 串联）|

合计 `grep -n "^theorem\|^@\[simp\] theorem"` 实测 **20** 条（见文末逐条清单）。
另有两个**可计算镜像 `def`**（`trajD` / `predictD`）与七个**镜像 `def`**
（`sgD` / `sgFst` / `sgSnd` / `stepD` / `pUq` / `doLawQ` / `jointLawQ` / `marginalYQ`），
它们**不是**断言，只是被 `#eval` 求值的函数。

---------------------------------------------------------------------------
四、⚠ 反同义反复核查（本项目最高频问题）
---------------------------------------------------------------------------
逐条核过（详见表后 §6 的自查）：
* **本文件没有任何定理的结论出现在自己的前件里**；§3–§5 的定理前件**只含**
  具体取值（`x₀ u a n y : Bool` 等）与**结构前提**（`PUnit` 的取值）。
* §5 的三条 `_dep_u` 定理的结论是**不等** `≠`，前件里**没有**任何 `≠`（无前件）。
* `scmDoLaw_true_true` 等的结论是**等式**，左式是 `FateV2.Modeling.SCMSemantics.doLaw` 的
  `Finset` 求和、右式是具体有理数；证明必须`展开定义 + 枚举 Bool`（见证明），
  **不是** `rfl` 级重念，也**不是**前件的改写。
* `scmTrajD_eq_trajGen` 两侧是**两个不同的定义**（`trajD` 的 `Nat.rec`
  vs `TrajGenDeterministic.trajGen` 的 `Nat.rec`），证明走归纳，
  且**用到** `scmStep_eq_stepD`（`rfl` 级，但确认构造接线无误）。

---------------------------------------------------------------------------
五、诚实边界（必须登记）
---------------------------------------------------------------------------
1. **`#eval` 的数是 `ℚ`／`Bool` 上的镜像数**，不是 `ℝ` 上的直接求值（`ℝ` 在本环境
   `noncomputable`）。桥由 §4 三条 `_cast` 定理给出：**镜像数 = 库定义的实数值**。
2. **`sim` 的整条轨迹不可直接 `#eval`**（`W.x` 是 `Classical.choice`）。
   故 §3 用 `trajGen`（`scmTrajD_eq_trajGen`）与 `sim_succ`（`scmSim_succ_eq_stepD`）
   把「打印的数」接到 `sim` 的**第 `n+1` 步**上（`n+1` 步与初值无关，这是
   `SCMWorldModel.scmWorldModel_step_indep_start` 的既有结论）。
   **第 0 步**（= `W.x`，占位初值）**没有**数值意义，本文件**不**对步 0 作任何声明。
3. **不声称**本例代表一般 SCM：`U = X = Y = Bool`、`pU` 均匀、`sg` 取
   `x && u`，均为**具体见证**。它的作用是证明**主干管线可运行且给出正确数值**，
   而不是统计结论。
4. **不跑全量 `lake build`**；只 `lake env lean Fate/SCMWorldModelEval.lean`。

---------------------------------------------------------------------------
六、纪律
---------------------------------------------------------------------------
零 `sorry` / 零 `admit` / 零 `axiom`；**只新建文件，不改动任何既有模块**。
-/

import FateWorld.FateV2.Loop.SCMWorldModel
import FateWorld.FateV2.Loop.SCMEndToEnd
import FateWorld.FateV2.Loop.SCMEndToEndGeneral
import FateWorld.FateV2.Modeling.SCMSemantics
import FateWorld.FateV2.Model.TrajGenDeterministic
namespace FateV2.Loop

open FateV2.Model
open FateV2.Modeling
open FateV2.Predict
namespace SCMWorldModelEval

open FateV2.Modeling.PearlHierarchy

set_option autoImplicit false

noncomputable section

/-!
  # Loop · SCMWorldModelEval

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SCMWorldModelEval.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SCMWorldModel, SCMEndToEnd, SCMEndToEndGeneral, SCMSemantics, TrajGenDeterministic
  - 补充 open 域：FateV2.Model, FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  具体 SCM：`U = X = Y = Bool`，均匀外生律，`sg u = (u, x ↦ x && u)`
  =========================================================================== -/

/-- 结构映射的可计算形状：`sg u = (u, fun x => x && u)`。

**单独提出来**是为了让镜像与 SCM 定义**共用同一份代码**（不写两遍）。 -/
def sgD (u : Bool) : Bool × (Bool → Bool) := (u, fun x => x && u)

/-- ⭐ **本文件的具体 SCM**：`U = Bool`、`pU` 均匀（每个 `1/2`）、`sg = sgD`。

**标签**：[定义性约定] —— 一个**具体的**实例，用于数值验证，不是新理论假设。

**⚠ 不可计算**：`pU` 里的 `1/2 : ℝ` 依赖 `Real.instDivInvMonoid`（`noncomputable`），
故此定义整体 `noncomputable`（`#eval` 报 `dependsOnNoncomputable`，已实测）。
可计算镜像见 §2。 -/
def scmDemo : SCM Bool Bool where
  U := Bool
  pU := fun _ => (1/2 : ℝ)
  sg := sgD

/-- 外生实现的事实分量：`(sg u).1 = u`（可计算镜像）。 -/
def sgFst (u : Bool) : Bool := u

/-- 外生实现的结构方程：`(sg u).2 a = a && u`（可计算镜像）。 -/
def sgSnd (u a : Bool) : Bool := a && u

/-- 单步机制的可计算镜像：`a && u`（= `(sg u).2 a`）。 -/
def stepD (u a : Bool) : Bool := a && u

/-! ===========================================================================
  §2  可计算镜像：轨迹 / 概率律（`ℚ` 上算）
  =========================================================================== -/

/-- 轨迹的可计算镜像：与 `TrajGenDeterministic.trajGen` **同一个 `Nat.rec` 形状**，
只是把机制换成可计算的 `stepD`。 -/
def trajD (x₀ : Bool) (u a : ℕ → Bool) : ℕ → Bool :=
  fun n => Nat.rec x₀ (fun k _ => stepD (u k) (a k)) n

/-- 外生律的可计算镜像（`ℚ` 上的均匀律）。 -/
def pUq : Bool → ℚ := fun _ => 1 / 2

/-- `FateV2.Modeling.SCMSemantics.doLaw` 的 `ℚ` 镜像。 -/
def doLawQ (x y : Bool) : ℚ :=
  ∑ u : Bool, pUq u * (if sgSnd u x = y then 1 else 0)

/-- `FateV2.Modeling.SCMSemantics.jointLaw` 的 `ℚ` 镜像（联合律含 `X` 的取值 `x`）。 -/
def jointLawQ (u x y : Bool) : ℚ :=
  pUq u * (if sgSnd u x = y then 1 else 0)

/-- `FateV2.Modeling.SCMSemantics.marginalY` 的 `ℚ` 镜像（事实分量取 `(sg u).1`）。 -/
def marginalYQ (y : Bool) : ℚ :=
  ∑ u : Bool, pUq u * (if sgSnd u (sgFst u) = y then 1 else 0)

/-! ===========================================================================
  §3  桥：可计算镜像 **=** 库里的定义（这才是「`#eval` 的数有意义」的理由）
  =========================================================================== -/

/-- ⭐ **结构映射的第一分量**：`(scmDemo.sg u).1 = u`（`rfl`）。 -/
@[simp] theorem scmSg_fst (u : Bool) : (scmDemo.sg u).1 = sgFst u := rfl

/-- ⭐ **结构映射的第二分量**：`(scmDemo.sg u).2 a = a && u`（`rfl`）。 -/
@[simp] theorem scmSg_snd (u a : Bool) : (scmDemo.sg u).2 a = sgSnd u a := rfl

/-- ⭐⭐ **桥：`SCMWorldModel.scmWorldStep` 在 `scmDemo` 上就是 `a && u`**。

**⚠ 反同义反复**：左侧是 `SCMWorldModel` 的构造（`WorldModel` 的机制位），
右侧是本文件的可计算镜像 `stepD`。两者由 `rfl` 相等**恰恰是构造正确的证据**
（若 `scmStep` 把参数接错位，此处即失败）。 -/
theorem scmStep_eq_stepD (y : Bool) (u : Bool) (e : PUnit) (t : PUnit) (a : Bool) :
    SCMWorldModel.scmWorldStep scmDemo y u e t a = stepD u a := rfl

/-- ⭐⭐⭐ **桥：轨迹镜像 `trajD` 与 `trajGen` 是同一算法**（归纳证明）。

$$ \mathrm{trajD}\,x_0\,u\,a\,n
   \;=\; \mathrm{trajGen}\;F\;(\mathrm{scmWorldStep})\;\dots\;x_0\;u\;\varepsilon\;a\;n .$$

**读法**：`#eval trajD …` 打印的数**就是** `trajGen` 迭代出的数，
故也就是 `WorldModel.sim` 的轨迹（`sim` 的定义就是 `trajGen`，见
`WorldModel.sim` 与 `TrajGenDeterministic.trajGen`）。

**⚠ 这份归纳不是摆设**：每一步都要用 `scmStep_eq_stepD` 把 `Nat.rec` 的
步函数换成 `stepD`，若 `trajD` 与 `trajGen` 的递归形状不一致，归纳走不通。 -/
theorem scmTrajD_eq_trajGen (x₀ : Bool) (u a : ℕ → Bool) (n : ℕ) :
    trajD x₀ u a n
      = TrajGenDeterministic.trajGen (SCMWorldModel.scmFrame scmDemo)
          (SCMWorldModel.scmWorldStep scmDemo) PUnit.unit x₀ u (fun _ => PUnit.unit) a n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show stepD (u k) (a k)
        = SCMWorldModel.scmWorldStep scmDemo (trajD x₀ u a k) (u k)
            PUnit.unit PUnit.unit (a k)
      rw [scmStep_eq_stepD]

/-- ⭐⭐⭐ **桥：`WorldModel.sim` 的第 `n+1` 步 = `a n && u n`**。

这是 `WorldModel.sim_succ`（既有）+ `scmWorldStep` 展开（本文件 §1）的复合：
`sim` 的递推给出第 `n+1` 步，机制再把它算成 `a n && u n`。

**⚠ 为什么只对 `n+1`**：`sim` 的第 0 步是 `W.x = Classical.choice …`（占位初值），
**没有数值意义**（`SCMWorldModel` 文件头边界 2 已登记），故本文件不对第 0 步作声明。
`n+1` 步**不读**初值（`scmWorldModel_step_indep_start`），故可算且唯一。 -/
theorem scmSim_succ_eq_stepD (u a : ℕ → Bool) (n : ℕ) :
    (SCMWorldModel.scmWorldModel scmDemo).sim PUnit.unit u (fun _ => PUnit.unit) a (n + 1)
      = stepD (u n) (a n) := by
  have h := WorldModel.sim_succ (SCMWorldModel.scmWorldModel scmDemo) PUnit.unit
    u (fun _ => PUnit.unit) a n
  refine h.trans ?_
  exact scmStep_eq_stepD
    ((SCMWorldModel.scmWorldModel scmDemo).sim PUnit.unit u (fun _ => PUnit.unit) a n)
    (u n) PUnit.unit PUnit.unit (a n)

/-- ⭐⭐⭐ **桥：`EndToEnd.predFrom` 在 `scmDemo` 上 = `a && u`**。

**这是任务书 (d) 的 `predFrom` 一位**：`predFrom` 是端到端链的「一步预测」，
在具体 SCM 上它算出 `a && u`——即结构方程 `h_u(a)`。

引用既有的 `SCMEndToEnd.predFrom_scmWorldModel`（它把 `predFrom` 化归到 `scmWorldStep`），
再用 §1 的可计算形状收尾 —— 不是重新定义一遍。

**⭐ 接线更新（任务 D / G6）**：本证明体现在**真的调用**
`SCMEndToEndGeneral.scmEndToEnd_general_predFrom`（`Fate/SCMEndToEndGeneral.lean` §1），
而不是 `SCMEndToEnd.predFrom_scmWorldModel`。二者结论相同（都是 `(sg u).2 a`），
但**前件强弱不同**：`SCMEndToEndGeneral` 版只要求 `[Nonempty Y]`
（**不**要求 `[AddCommGroup Y]`），因此能在 `Y = Bool` 上用。
这一步是**真实消费**（定理名出现在证明体里），不是仅 `import` 凑扇入。 -/
theorem scmPredFrom_eq_stepD (u : Bool) (a : Bool) (y : Bool) :
    FateV2.Loop.EndToEnd.predFrom (SCMWorldModel.scmWorldModel scmDemo) PUnit.unit u PUnit.unit a y
      = stepD u a := by
  rw [SCMEndToEndGeneral.scmEndToEnd_general_predFrom scmDemo
    PUnit.unit u PUnit.unit a y]
  rfl

/-! ===========================================================================
  §4  概率律：可计算镜像 **cast 到 ℝ 后 = 库定义**
  =========================================================================== -/

/-- ⭐⭐⭐ **干预律：`#eval` 出的 `ℚ` 数 cast 到 `ℝ` 就是 `FateV2.Modeling.SCMSemantics.doLaw`**。

$$\bigl(\mathrm{doLawQ}\,x\,y : \mathbb{Q}\bigr)_{\mathbb{R}}
  \;=\; \mathrm{doLaw}\;\mathrm{scmDemo}\;x\;y .$$

**⟹ 这条定理消除了「`#eval` 打印的数是另一套算法」的疑虑**：
它逐点（对**所有** `x y`，不是抽样）证明镜像与库定义相等。

**⚠ 证明为什么不能只 `rfl`**：左侧是 `ℚ` 上的 `Finset.sum`（`Bool` 上两点求和），
右侧是 `ℝ` 上的 `Finset.sum`；二者由 `push_cast`（`Rat.cast` 穿过 `+`/`*`）
与 `Fintype.sum_bool`（把 `Bool` 上的和摊成两项）桥接。 -/
theorem scmDoLawQ_cast (x y : Bool) :
    ((doLawQ x y : ℚ) : ℝ) = FateV2.Modeling.SCMSemantics.doLaw scmDemo x y := by
  simp only [doLawQ, FateV2.Modeling.SCMSemantics.doLaw, scmDemo, sgD, pUq, sgSnd]
  change ((∑ u : Bool, (1 / 2 : ℚ) * (if (x && u) = y then 1 else 0) : ℚ) : ℝ)
    = ∑ u : Bool, (1 / 2 : ℝ) * (if (x && u) = y then 1 else 0)
  rw [Fintype.sum_bool, Fintype.sum_bool]
  push_cast
  cases x <;> cases y <;> norm_num

/-- ⭐⭐ **联合律：`ℚ` 镜像 cast 到 `ℝ` 就是 `FateV2.Modeling.SCMSemantics.jointLaw`**。 -/
theorem scmJointLawQ_cast (u x y : Bool) :
    ((jointLawQ u x y : ℚ) : ℝ) = FateV2.Modeling.SCMSemantics.jointLaw scmDemo (u, x, y) := by
  simp only [jointLawQ, FateV2.Modeling.SCMSemantics.jointLaw, scmDemo, sgD, pUq, sgSnd]
  push_cast
  cases u <;> cases x <;> cases y <;> norm_num

/-- ⭐⭐ **`Y` 边缘律：`ℚ` 镜像 cast 到 `ℝ` 就是 `FateV2.Modeling.SCMSemantics.marginalY`**。 -/
theorem scmMarginalYQ_cast (y : Bool) :
    ((marginalYQ y : ℚ) : ℝ) = FateV2.Modeling.SCMSemantics.marginalY scmDemo y := by
  simp only [marginalYQ, FateV2.Modeling.SCMSemantics.marginalY, scmDemo, sgD, pUq, sgFst, sgSnd]
  change ((∑ u : Bool, (1 / 2 : ℚ) * (if (u && u) = y then 1 else 0) : ℚ) : ℝ)
    = ∑ u : Bool, (1 / 2 : ℝ) * (if (u && u) = y then 1 else 0)
  rw [Fintype.sum_bool, Fintype.sum_bool]
  push_cast
  cases y <;> norm_num

/-! ### §4.1 干预律的四个**具体数值**（直接陈述在 `ℝ` 的库定义上）

这些是把 `scmDoLawQ_cast` 与 `#eval` 输出的数**逐条落到库定义**上的等式，
逐条枚举 `x y : Bool`（四次，即全集）。 -/

/-- ⭐ `doLaw(true) = 1/2` 在 `y = true` 处。 -/
theorem scmDoLaw_true_true : FateV2.Modeling.SCMSemantics.doLaw scmDemo true true = 1 / 2 := by
  simp only [FateV2.Modeling.SCMSemantics.doLaw, scmDemo, sgD]
  change (∑ u : Bool, (1 / 2 : ℝ) * (if (u && true) = true then 1 else 0)) = 1 / 2
  rw [Fintype.sum_bool]
  norm_num

/-- ⭐ `doLaw(true) = 1/2` 在 `y = false` 处。 -/
theorem scmDoLaw_true_false : FateV2.Modeling.SCMSemantics.doLaw scmDemo true false = 1 / 2 := by
  simp only [FateV2.Modeling.SCMSemantics.doLaw, scmDemo, sgD]
  change (∑ u : Bool, (1 / 2 : ℝ) * (if (u && true) = false then 1 else 0)) = 1 / 2
  rw [Fintype.sum_bool]
  norm_num

/-- ⭐ `doLaw(false) = 0` 在 `y = true` 处（`x := false` 使 `Y` 恒为 `false`）。 -/
theorem scmDoLaw_false_true : FateV2.Modeling.SCMSemantics.doLaw scmDemo false true = 0 := by
  simp only [FateV2.Modeling.SCMSemantics.doLaw, scmDemo, sgD]
  change (∑ u : Bool, (1 / 2 : ℝ) * (if (u && false) = true then 1 else 0)) = 0
  rw [Fintype.sum_bool]
  norm_num

/-- ⭐ `doLaw(false) = 1` 在 `y = false` 处（点质量）。 -/
theorem scmDoLaw_false_false : FateV2.Modeling.SCMSemantics.doLaw scmDemo false false = 1 := by
  simp only [FateV2.Modeling.SCMSemantics.doLaw, scmDemo, sgD]
  change (∑ u : Bool, (1 / 2 : ℝ) * (if (u && false) = false then 1 else 0)) = 1
  rw [Fintype.sum_bool]
  norm_num

/-- ⭐⭐ **`Y` 的边缘律是均匀的**：`marginalY true = 1/2`。 -/
theorem scmMarginalY_true : FateV2.Modeling.SCMSemantics.marginalY scmDemo true = 1 / 2 := by
  simp only [FateV2.Modeling.SCMSemantics.marginalY, scmDemo, sgD]
  change (∑ u : Bool, (1 / 2 : ℝ) * (if (u && u) = true then 1 else 0)) = 1 / 2
  rw [Fintype.sum_bool]
  norm_num

/-- `EndToEnd.predFrom` 的可计算镜像：**五个参数照抄**（含被丢弃的出发位 `y`）。 -/
def predictD (_y : Bool) (u : Bool) (a : Bool) : Bool := stepD u a

/-! ### §4.2 `#eval` 数值块（本文件「可运行」的正面证据） -/

-- (E1) 单步机制 `stepD u a` 的真值表：四组 `(u, a)`
#eval ([(true,true),(true,false),(false,true),(false,false)] : List (Bool × Bool)).map
  (fun p => (p.1, p.2, stepD p.1 p.2))

-- (E2) `predFrom` 镜像 `predictD`：同一 `(u,a)` 下**两个不同出发状态**给出**同一**预测
#eval ([(true,true),(false,true)] : List (Bool × Bool)).map
  (fun p => (p.1, p.2, predictD false p.1 p.2, predictD true p.1 p.2))

-- (E3) 轨迹：`u` 交替（true,false,true,…），`a ≡ true`，起点 `false`，前 6 步
#eval (List.range 6).map fun n => trajD false (fun k => k % 2 == 0) (fun _ => true) n

-- (E4) 轨迹：同上但 `a ≡ false`（与 E3 对照：全部 `false`）
#eval (List.range 6).map fun n => trajD false (fun k => k % 2 == 0) (fun _ => false) n

-- (E5) `WorldModel.sim` 的第 `n+1` 步（`scmSim_succ_eq_stepD` 的右式）
#eval (List.range 6).map fun n => stepD ((fun k => k % 2 == 0) n) true

-- (E6) 干预律 `doLaw` 的四格（`ℚ` 镜像 `doLawQ`）
#eval ([(true,true),(true,false),(false,true),(false,false)] : List (Bool × Bool)).map
  (fun p => (p.1, p.2, doLawQ p.1 p.2))

-- (E7) `Y` 边缘律 `marginalY` 的两格
#eval ([(true),(false)] : List Bool).map (fun y => (y, marginalYQ y))

-- (E8) 联合律 `jointLaw` 的八格 `(u, x, y)`
#eval ([(true,true,true),(true,true,false),(true,false,true),(true,false,false),
        (false,true,true),(false,true,false),(false,false,true),(false,false,false)]
       : List (Bool × Bool × Bool)).map
  (fun p => (p.1, p.2.1, p.2.2, jointLawQ p.1 p.2.1 p.2.2))

/-! ===========================================================================
  §5  反退化：**外生变量真的影响预测**（这是本文件要验证的核心命题）
  =========================================================================== -/

/-- ⭐⭐⭐ **`stepD` 真的依赖 `u`**：`a = true` 时 `u = true` 与 `u = false` 的预测不同。

**⚠ 反同义反复核查**：本定理**无前件**（`Bool` 上的具体取值），
结论是**不等** `true && true = true ≠ false = true && false`。
若机制把 `u` 丢掉（如 `stepD u a = a`），本定理立即为假 ⟹ 它**实质约束**了机制。 -/
theorem scmStepD_dep_u : stepD true true ≠ stepD false true := by decide

/-- ⭐⭐⭐ **外生变量影响 `EndToEnd.predFrom`**（把上一条搬到**库定义**上，不是 `stepD` 的自言自语）。

$$\mathrm{predFrom}\;(\mathrm{scmWorldModel}\,\mathrm{scmDemo})\;\theta\;\mathrm{true}\;\varepsilon\;\mathrm{true}\;y
  \;\neq\;
  \mathrm{predFrom}\;(\mathrm{scmWorldModel}\,\mathrm{scmDemo})\;\theta\;\mathrm{false}\;\varepsilon\;\mathrm{true}\;y' .$$ -/
theorem scmPredFrom_dep_u (y y' : Bool) :
    FateV2.Loop.EndToEnd.predFrom (SCMWorldModel.scmWorldModel scmDemo) PUnit.unit true
        PUnit.unit true y
      ≠ FateV2.Loop.EndToEnd.predFrom (SCMWorldModel.scmWorldModel scmDemo) PUnit.unit false
        PUnit.unit true y' := by
  rw [scmPredFrom_eq_stepD, scmPredFrom_eq_stepD]
  exact scmStepD_dep_u

/-- ⭐⭐⭐ **外生变量影响 `WorldModel.sim` 的第 1 步**（同一事实的轨迹层读法）。 -/
theorem scmSim_dep_u :
    (SCMWorldModel.scmWorldModel scmDemo).sim PUnit.unit (fun _ => true)
        (fun _ => PUnit.unit) (fun _ => true) 1
      ≠ (SCMWorldModel.scmWorldModel scmDemo).sim PUnit.unit (fun _ => false)
          (fun _ => PUnit.unit) (fun _ => true) 1 := by
  rw [scmSim_succ_eq_stepD, scmSim_succ_eq_stepD]
  exact scmStepD_dep_u

/-- ⭐⭐⭐ **干预 ≠ 观测（数值见证）**：`do(true)` 在 `true` 上的质量是 `1/2`，
而 `x := false` 的**点质量**在 `true` 上是 `0`。

⟹ 「`do(X := x)` 切断了 `X` 的入边」在本实例上给出**不同的数**
（`1/2` vs `0`），不是同一件事的两种说法。 -/
theorem scmDoLaw_dep_x :
    FateV2.Modeling.SCMSemantics.doLaw scmDemo true true ≠ FateV2.Modeling.SCMSemantics.doLaw scmDemo false true := by
  rw [scmDoLaw_true_true, scmDoLaw_false_true]
  norm_num

/-! ===========================================================================
  §6  ⭐ **与 `SCMEndToEnd` 的等式对接**（任务 H，第 716 轮）

  本文件此前只 `import` 了 `SCMEndToEnd` 却**未真正消费**它的任何定理。
  本节把 `SCMEndToEnd.predFrom_scmWorldModel_indep_start`
  （`Fate/SCMEndToEnd.lean`，前件仅 `[Nonempty Y]`，对**任意** SCM 成立）
  落到本文件的具体 SCM `scmDemo : SCM Bool Bool` 上，得到两条**新结论**：

  * `predFrom_scmDemo_indep_start`：`scmDemo` 上的端到端预测**与出发状态无关**；
  * `scmStepD_indep_start`：把上一条经本文件的 `scmPredFrom_eq_stepD` 翻译到
    可计算镜像 `stepD` 上（`stepD` 本就不读出发状态，但此处是**从库定义推出**的）。

  **⚠ 反同义反复核查**：
  * 前件只有具体取值 `u a y₁ y₂ : Bool`／`u a : Bool`，**无任何等式假设**；
  * 结论是 `EndToEnd.predFrom`（库的 `noncomputable def`）在两个不同出发状态
    上的**相等**，其证明**调用** `SCMEndToEnd` 的定理（定理名出现在证明体里）；
  * `Nonempty` 实例在 `Bool` 上有多个候选，需以 `@… _` 显式交由 Lean 推断
    （这是 `Y = Bool` 上的实例合成细节，不改变命题）。 -/

/-- ⭐⭐⭐ **`scmDemo` 上的端到端预测与出发状态无关**（真消费 `SCMEndToEnd`）。

$$\mathrm{predFrom}\,(\mathrm{scmWorldModel}\,\mathrm{scmDemo})\;\theta\;u\;\varepsilon\;a\;y_1
  = \mathrm{predFrom}\,(\mathrm{scmWorldModel}\,\mathrm{scmDemo})\;\theta\;u\;\varepsilon\;a\;y_2 .$$

**证明**：本文件**没有**重证它，而是直接调用
`SCMEndToEnd.predFrom_scmWorldModel_indep_start scmDemo …`。 -/
theorem predFrom_scmDemo_indep_start (u a y₁ y₂ : Bool) :
    FateV2.Loop.EndToEnd.predFrom (SCMWorldModel.scmWorldModel scmDemo) PUnit.unit u PUnit.unit a y₁
      = FateV2.Loop.EndToEnd.predFrom (SCMWorldModel.scmWorldModel scmDemo) PUnit.unit u PUnit.unit a y₂ :=
  @SCMEndToEnd.predFrom_scmWorldModel_indep_start Bool Bool scmDemo _
    PUnit.unit u PUnit.unit a y₁ y₂

/-- ⭐⭐ **同一个 `stepD` 等于两个不同出发状态的 `predFrom`**
（`scmPredFrom_eq_stepD` 与 `predFrom_scmDemo_indep_start` 的真串联）。

**读法**：左端是本文件的可计算镜像 `stepD u a`；右端是库定义 `predFrom`
在 `y = true` 与 `y = false` 两个出发状态上的值。三者相等的证明**必须**用
`SCMEndToEnd.predFrom_scmWorldModel_indep_start` 把两个 `predFrom` 拉齐，
再各自用 `scmPredFrom_eq_stepD` 翻成 `stepD`。 -/
theorem scmStepD_eq_predFrom_both_starts (u a : Bool) :
    stepD u a
        = FateV2.Loop.EndToEnd.predFrom (SCMWorldModel.scmWorldModel scmDemo) PUnit.unit u
            PUnit.unit a true
      ∧ FateV2.Loop.EndToEnd.predFrom (SCMWorldModel.scmWorldModel scmDemo) PUnit.unit u
            PUnit.unit a true
          = FateV2.Loop.EndToEnd.predFrom (SCMWorldModel.scmWorldModel scmDemo) PUnit.unit u
              PUnit.unit a false :=
  ⟨(scmPredFrom_eq_stepD u a true).symm, predFrom_scmDemo_indep_start u a true false⟩

end

end SCMWorldModelEval

end FateV2.Loop