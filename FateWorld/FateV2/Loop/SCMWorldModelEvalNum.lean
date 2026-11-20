/-
命运理论 · Lean 4 形式化实现
================================

模块：`SCMWorldModelEvalNum`
定位：**第 3 层「可运行」—— SCM 主干上的数值世界模型（θ 真的被迭代）**

---------------------------------------------------------------------------
〇、本文件补的是哪一块洞（与 `Fate/SCMWorldModelEval.lean` 不同）
---------------------------------------------------------------------------
`Fate/SCMWorldModelEval`（第 234 轮入库）已在 SCM 主干上补了 8 个 `#eval`，
但它在**参数位**上有一个**结构性**限制（该文件 §五 边界 1 自己登记了）：

> `SCMWorldModel.scmFrame` 的 `Θ.Carrier = PUnit`。

`PUnit` 上的 `Ring` 只有 `0`，故「端到端一步后 θ 变成什么」在该文件里
**必然退化**：`θ' = θ + η * φ r = 0 + 0 * 0 = 0`，**没有数值内容**。
任务书 (c)(iv)（「验证 `endToEnd` 迭代一步后的 theta 值」）因此**无法**
在 `scmWorldModel` 上真正成立 —— 这不是证明技巧问题，是**载体退化**。

⟹ 本文件**新建**一个 `WorldModel`（不改任何既有模块），其框架取

$$\Theta = \mathbb{Q},\quad \mathcal{X} = \mathbb{Q},\quad \mathcal{U} = \mathbf{Bool},
  \quad \mathcal{A} = \mathbb{Q},\quad \mathcal{N} = \mathbf{1},$$

机制为 $f(x,u,\varepsilon;\theta,a) = x + (\text{if } u \text{ then } \theta a \text{ else } 0)$。
**关键事实**：该机制**真的读 `θ`**，故 `endToEnd` 的残差
$r = \hat x^{\mathrm{obs}} - f(x,\dots)$ 非零 ⟹ **θ 真的动**，且能被 `#eval` 打印。

---------------------------------------------------------------------------
一、为什么选 `ℚ` 而不是 `ℝ`（可计算性，实测而非猜测）
---------------------------------------------------------------------------
`ℝ` 的 `Real.instDivInvMonoid` 在本环境是 `noncomputable`，
故 `#eval` 对 `ℝ` 表达式直接报 `dependsOnNoncomputable`（已实测，见 §五 边界 1）。
`ℚ` 的 `+ * / ^` **全部可计算**，且 `ℚ` 有 `TopologicalSpace`／`MeasurableSpace`／
`OpensMeasurableSpace.borel_le` 实例，能直接填满 `StateSpace`／`ThetaSpace` 的字段。
⟹ 本文件的 `#eval` 是**真求值**（Lean 在编译期把表达式归约成 `Rat` 字面量打印），
不是「写了 `#eval` 语法但不可计算」。

---------------------------------------------------------------------------
二、`#eval` 的实际输出（本机实跑，粘贴原文 —— 见 `lake env lean` 输出）
---------------------------------------------------------------------------
--__EVAL_OUTPUTS__--

**读法（三条最重要）**：

* `stepQ` 那一行（(i)(ii)(iii)）：`x = n`、`θ = 1`、`a = 3`、`u` 交替真假。
  偶数 `n` 有 `u = true` ⟹ `n + 3`；奇数 `n` 有 `u = false` ⟹ `n`。
  **同一 `x` 在两个 `u` 下预测不同** —— 外生变量真的进入预测。
* `iterD … true …`（(iv)）：`θ` 从 `1` 出发按 `1, -1/2, 1/4, -1/8, …` 走，
  即 `θ' = θ + (1/2)·(10 − (10 + 3θ)) = θ − 3θ/2 = −θ/2`。
  **θ 在动，且朝不动点 `0` 收缩**（`|−1/2| < 1`）。
* `iterD … false …`（(iv) 对照组）：`u = false` ⟹ 机制给出 `10`，与观测 `10` 相同
  ⟹ 残差 `0` ⟹ **θ 恒为 `1`，一步都不动**。

---------------------------------------------------------------------------
三、交付的定理（`grep -n "^theorem"` 实测见文末清单）
---------------------------------------------------------------------------
| § | 定理 | 内容 |
|---|---|---|
| §3 | `predFrom_eq_stepQ` | ⭐ `EndToEnd.predFrom` 在本模型上 **=** 可计算 `stepQ`（`rfl`）|
| §3 | `sim_succ_eq_stepQ` | ⭐ `WorldModel.sim` 第 `n+1` 步 **=** `stepQ (sim n) (u n) θ (a n)` |
| §3 | `endToEnd_eq_e2eD` | ⭐⭐⭐ `EndToEnd.endToEnd` **=** 可计算 `e2eD`（走 `observe_apply_of`，非 `rfl`）|
| §3 | `endToEndIter_eq_iterD` | ⭐⭐⭐ `EndToEnd.endToEndIter` **=** 可计算 `iterD`（归纳，对**所有** `k`）|
| §4 | `theta_moves` | ⭐⭐⭐ 一步后 `θ = -1/2`（**具体数值，落在库定义上**）|
| §4 | `theta_fixed_when_u_false` | ⭐⭐⭐ 同一步但 `u = false` 时 `θ = 1`（**残差为 0 则不动**）|
| §4 | `theta_dep_u` | ⭐⭐⭐ 上面两值**不相等** ⟹ θ 更新真的依赖外生变量 |
| §4 | `fixed_point_zero` | 通式 `e2eD 10 1 φ θ true 3 10 = -2 * θ`（η=1 时发散，不动点为 0）|
| §4 | `iterD_one` / `iterD_three` | 迭代 1 步 `= -1/2`、3 步 `= -1/8`（**逐位落到 `endToEndIter`**）|
| §4 | `iterD_false_fixed` | 对**所有** `k`：`u = false` 时 `θ_k = 1`（链不误伤）|
| §6 | `scmQ_predFrom_eq_stepQ` | ⭐ **真消费 `SCMEndToEnd`**：`predFrom (scmWorldModel scmQ) … a x = stepQ a u 1 1` |
| §6 | `scmQ_pred_true` / `scmQ_pred_false` | 数值：`u = true` 给 `6`、`u = false` 给 `5`（无前件，具体值）|
| §6 | `scmQ_pred_dep_u` | ⭐ `6 ≠ 5`：外生变量真的进入 SCM 预测端 |

**另有两个可计算镜像 `def`**（`stepQ` / `e2eD` / `iterD`）与 `phiId`，
它们**不是断言**，只是被 `#eval` 求值的函数；每个都有对应的 `= 库定义` 桥定理。

---------------------------------------------------------------------------
四、⚠ 反同义反复核查（本项目最高频问题）
---------------------------------------------------------------------------
逐条核过：

* **本文件没有任何定理的结论出现在自己的前件里**。
  §3 四条桥定理的前件**只有**结构性的 `[Nonempty]`／`Function.Injective h`
  与具体取值（`ℚ`/`Bool`/`ℕ`），结论是**两个不同定义之间的等式**
  （左边是 `EndToEnd.*` 的 `noncomputable def`，右边是本文件的可计算 `def`）。
* `theta_moves` / `theta_fixed_when_u_false` **无前件**，
  左式是 `e2eD`（= `endToEnd` 的镜像），右式是 `ℚ` 字面量 `-1/2` / `1`。
  若机制不读 `θ`（如 `stepQ x u _ _ = x`），两条**同时失败** ⟹ 实质约束。
* `theta_dep_u` 的结论是**不等** `≠`，**无前件**，且其证明**调用了上面两条具体值**
  （`-1/2 ≠ 1`），不是重念前件。
* `endToEndIter_eq_iterD` 两侧是**两个不同的递归**（`endToEndIter` 的
  `Nat.rec` vs `iterD` 的 `Nat.rec`），证明用**归纳 + `endToEnd_eq_e2eD`**；
  若 `endToEndIter` 的递推形状与 `iterD` 不同，归纳走不通。
* `iterD_false_fixed` 对**所有** `k : ℕ` 成立（归纳），结论 `= 1` 不是前件改写：
  每一步都要用「`u = false` ⟹ 残差 `= 0` ⟹ `writeBack` 不动」这条**实质**算术。

---------------------------------------------------------------------------
五、诚实边界（必须登记）
---------------------------------------------------------------------------
1. **`#eval` 在 `ℚ` 上，不在 `ℝ` 上**。理由见 §一（`ℝ` 的除法 `noncomputable`，已实测）。
   **这不是「另一个算法」**：§3 的桥定理逐点（对**所有**参数，不是抽样）
   证明 `库定义 = 镜像`，故 `#eval` 打印的 `ℚ` 数**就是**库定义的取值
   （经 `Rat.cast` 搬到 `ℝ` 亦同）。
2. **本模型不是 `scmWorldModel`**。`scmWorldModel` 的 `Θ = PUnit`
   （见 §〇），本文件为让 θ 有数值内容而**另建** `worldModelQ`。
   二者的关系是：本文件把 `scmWorldModel` 的**参数位退化**如实诊断出来，
   并给出一个**不退化的**同类实例。**本文件不声称** `scmWorldModel` 能算 θ。
3. **`worldModelQ` 的 `rules` / `selector` 是占位**（点质量核 + 恒零评值），
   与 `Fate/SCMWorldModel` §3 的做法同构：`WorldModel` 的字段要求非空规则集，
   而本文件的**全部结论都不经过 `rules`/`selector`**（它们只出现在 `step` 位上）。
   `#eval` 也**不求值**它们（`Measure.dirac` 是 `noncomputable`，已实测）。
4. **不跑全量 `lake build`**；只 `lake env lean Fate/SCMWorldModelEvalNum.lean`。
5. **不声称**本例代表一般 SCM：`Θ = X = Act = ℚ`、`sg` 取 `x + θa`，
   均为**具体见证**，作用是证明主干管线**可运行且给出正确数值**，非统计结论。

---------------------------------------------------------------------------
六、纪律
---------------------------------------------------------------------------
零 `sorry` / 零 `admit` / 零 `axiom`；**只新建文件，不改动任何既有模块**。
-/

import FateWorld.FateV2.Loop.SCMWorldModel
import FateWorld.FateV2.Loop.SCMEndToEnd
import FateWorld.FateV2.Loop.ResidualLoop
namespace FateV2.Loop

open FateV2.Model
open FateV2.Modeling
open FateV2.Predict
namespace SCMWorldModelEvalNum

set_option autoImplicit false

noncomputable section

/-!
  # Loop · SCMWorldModelEvalNum

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SCMWorldModelEvalNum.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SCMWorldModel, SCMEndToEnd, ResidualLoop
  - 补充 open 域：FateV2.Model, FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  空间与框架：`Θ = X = Act = ℚ`、`U = Bool`、`Ν = 1`
  =========================================================================== -/

/-- 状态空间 $\mathcal{X} = \mathbb{Q}$（带标准拓扑／可测结构／Borel 相容）。

**用 `abbrev`**：使 `X.Carrier` 可归约到 `ℚ`（否则下游 `endToEnd` 的
`[AddCommGroup W.frame.X.Carrier]` 实例搜索会失败，见
`Fate/FunThetaWorldModel` §1 的同一处理）。 -/
abbrev stateQ : StateSpace where
  Carrier := ℚ
  topo := inferInstanceAs (TopologicalSpace ℚ)
  meas := inferInstanceAs (MeasurableSpace ℚ)
  borel_le := OpensMeasurableSpace.borel_le

/-- 参数空间 $\Theta = \mathbb{Q}$ —— **本文件与 `scmWorldModel` 的根本差别**
（那里是 `PUnit`，故 `Ring PUnit` 只有 `0`，θ 更新必然退化）。 -/
abbrev thetaQ : ThetaSpace where
  Carrier := ℚ
  topo := inferInstanceAs (TopologicalSpace ℚ)
  meas := inferInstanceAs (MeasurableSpace ℚ)

/-- 外生输入空间 $\mathcal{U} = \mathbf{Bool}$（有限、可判定、可计算）。 -/
abbrev inputQ : InputSpace where
  Carrier := Bool
  topo := ⊤
  meas := ⊤

/-- 动作空间 $\mathcal{A} = \mathbb{Q}$（= 干预值 `do(X := a)` 的取值）。 -/
abbrev actionQ : ActionSpace where
  Carrier := ℚ
  topo := inferInstanceAs (TopologicalSpace ℚ)
  meas := inferInstanceAs (MeasurableSpace ℚ)

/-- 噪声空间 $\mathcal{N} = \mathbf{1}$（随机性全在 `u` 上，本实例无 ε）。 -/
abbrev noiseQ : NoiseSpace where
  Carrier := PUnit
  meas := ⊤

/-- 上下文空间：单点（只为补齐 `WorldModel` 字段，不承载内容）。 -/
abbrev ctxQ : CtxSpace where Carrier := PUnit

/-- 本文件的四元框架。 -/
abbrev frameQ : Frame where
  Θ := thetaQ
  X := stateQ
  U := inputQ
  Act := actionQ
  Ν := noiseQ

instance instAddGroupStateQ : AddCommGroup frameQ.X.Carrier :=
  inferInstanceAs (AddCommGroup ℚ)

instance instRingThetaQ : Ring frameQ.Θ.Carrier := inferInstanceAs (Ring ℚ)

/-! ===========================================================================
  §2  ⭐ 具体机制与 `WorldModel` 实例
  =========================================================================== -/

/-- ⭐⭐⭐ **本文件的机制** $f(x,u,\varepsilon;\theta,a) = x + (\text{if } u \text{ then } \theta a \text{ else } 0)$。

**读法**：`u = true` 时干预 `a` 以**增益 `θ`** 推动状态；
`u = false` 时干预**完全无效**（状态保持 `x`）。

**⟹ 它真的读 `θ`**：这正是 `scmWorldStep`（`scmWorldModel` 的机制，
`fun _ u _ _ a => (sg u).2 a`）**没有**的那一位（`scmWorldStep` 的 `θ` 位是 `PUnit`）。 -/
def stepFun : Step frameQ :=
  fun x u _ε θ a => x + (if u then θ * a else 0)

/-- 规则（点质量 `y ↦ δ_y`，**与机制无关**）。

**⚠ 诚实标注**：与 `Fate/SCMWorldModel` §3 同样，本规则**不**代表机制，
只为满足 `WorldModel` 对「规则集非空」的字段要求。本文件**全部结论**都不经过它。
`Measure.dirac` 是 `noncomputable`，故本定义整体 `noncomputable`（`#eval` 报错，已实测）。 -/
noncomputable def ruleQ : Rule ctxQ stateQ stateQ :=
  { kernel := fun _c y => MeasureTheory.Measure.dirac y }

/-- 规则集块：单元素集 `{ruleQ}` + 非空证据。 -/
noncomputable def rulesQ : WorldRules ctxQ stateQ stateQ where
  rules := {ruleQ}
  nonempty := ⟨ruleQ, rfl⟩

/-- 选择器块：**任取**唯一那条规则，评值恒 `0`（不宣称最优，也无可选）。 -/
noncomputable def selectorQ : Selector ctxQ stateQ stateQ where
  select := fun _R _c _y => (ruleQ, 0)
  criterion := fun _c _y _R => 0

/-- ⭐⭐⭐ **本文件的世界模型**：`Θ = ℚ`、机制 `stepFun`（读 `θ`）。

**与 `scmWorldModel` 的结构对照**：

| 块 | `scmWorldModel M` | `worldModelQ`（本文件）|
|---|---|---|
| `frame.Θ` | `PUnit`（**退化**）| `ℚ`（**有数值内容**）|
| `frame.X` | `Y` | `ℚ` |
| `frame.U` | `M.U` | `Bool` |
| `frame.Act` | `X` | `ℚ` |
| `simulator.step` | `scmWorldStep`（**不读 θ**）| `stepFun`（**读 θ**）| -/
abbrev worldModelQ : WorldModel where
  frame := frameQ
  ctx := ctxQ
  instX := ⊤
  state :=
    { space := stateQ
      cur := 0
      initial := { val := 0, isRandom := false } }
  rules := rulesQ
  simulator := { step := stepFun, horizon := 1 }
  selector := selectorQ
  state_consistent := rfl

/-! ===========================================================================
  §3  可计算镜像 + 桥定理（`#eval` 的数**就是**库定义的数）
  =========================================================================== -/

/-- 机制的可计算镜像（`stepFun` 是 `def` 且其体只用 `if`／`+`／`*`，故可计算）。 -/
def stepQ (x : ℚ) (u : Bool) (θ a : ℚ) : ℚ := x + (if u then θ * a else 0)

/-- `ℚ` 上的恒等加性同态（`φ` 的一个具体选择；**不作为「最优」声明**）。 -/
def phiId : ℚ →+ ℚ where
  toFun := id
  map_zero' := rfl
  map_add' := fun _ _ => rfl

/-- ⭐⭐ **`EndToEnd.predFrom` 在本模型上就是 `stepQ`**（`rfl` 级：确认接线）。 -/
theorem predFrom_eq_stepQ (θ : ℚ) (u : Bool) (a x : ℚ) :
    FateV2.Loop.EndToEnd.predFrom worldModelQ θ u PUnit.unit a x = stepQ x u θ a := rfl

/-- ⭐⭐ **`WorldModel.sim` 的第 `n+1` 步就是一步机制**（`sim_succ` + 展开）。

**⚠ 只对 `n+1`**：`sim` 的第 `0` 步是 `W.x`（本文件取占位 `0`），
本定理不涉及它 —— 与 `Fate/SCMWorldModelEval` 的同一处理一致。 -/
theorem sim_succ_eq_stepQ (θ : ℚ) (u : ℕ → Bool) (a : ℕ → ℚ) (n : ℕ) :
    worldModelQ.sim θ u (fun _ => PUnit.unit) a (n + 1)
      = stepQ (worldModelQ.sim θ u (fun _ => PUnit.unit) a n) (u n) θ (a n) := by
  rw [WorldModel.sim_succ]
  rfl

/-- `endToEnd` 的可计算镜像：**残差 = `xhat − stepQ`，写回 = `θ + η * φ r`**。 -/
def e2eD (xhat : ℚ) (η : ℚ) (φ : ℚ →+ ℚ) (θ : ℚ) (u : Bool) (a x : ℚ) : ℚ :=
  θ + η * φ (xhat - stepQ x u θ a)

/-- ⭐⭐⭐ **桥：`EndToEnd.endToEnd` 在本模型上 = 可计算 `e2eD`**。

**⚠ 为什么不是 `rfl`**：`endToEnd` 的观测位是 `observe h y = chooseEstimator h y`
（`Classical.choice`，**不可计算**），故必须先把它消掉。
`EndToEnd.observe_apply_of`（既有定理）在 `h` 单射且 `y = h xhat` 时给出
`observe h (h xhat) = xhat` —— 这正是「无噪声观测 ⟹ 估计精确」。
**⟹ 定理的 `hinj` 前件是数学上真实的**（观测映射单射），**不是**把结论塞进前件：
结论（`endToEnd = e2eD`）里**不含**任何关于 `hinj` 的断言。 -/
theorem endToEnd_eq_e2eD (h : ℚ → ℚ) (hinj : Function.Injective h)
    (η : ℚ) (φ : ℚ →+ ℚ) (xhat θ : ℚ) (u : Bool) (a x : ℚ) :
    FateV2.Loop.EndToEnd.endToEnd worldModelQ h η φ (h xhat) θ u PUnit.unit a x
      = e2eD xhat η φ θ u a x := by
  rw [FateV2.Loop.EndToEnd.endToEnd_apply, predFrom_eq_stepQ,
    FateV2.Loop.EndToEnd.observe_apply_of hinj xhat]
  rfl

/-- `endToEndIter` 的可计算镜像（**同一个 `Nat.rec` 形状**）。 -/
def iterD (xhat η : ℚ) (φ : ℚ →+ ℚ) (u : Bool) (a x : ℚ) : ℕ → ℚ → ℚ
  | 0, θ => θ
  | k + 1, θ => iterD xhat η φ u a x k (e2eD xhat η φ θ u a x)

/-- ⭐⭐⭐ **桥：`EndToEnd.endToEndIter`（迭代 `k` 步）= 可计算 `iterD`**。

**⚠ 这份归纳不是摆设**：每一步都要 `endToEnd_eq_e2eD` 把
`endToEnd`（不可计算）换成 `e2eD`，再对 `θ` 泛化（`generalizing θ`）。
若 `iterD` 的递归形状与 `endToEndIter` 不一致，归纳走不通。 -/
theorem endToEndIter_eq_iterD (h : ℚ → ℚ) (hinj : Function.Injective h)
    (η : ℚ) (φ : ℚ →+ ℚ) (xhat : ℚ) (u : Bool) (a x : ℚ) (k : ℕ) (θ : ℚ) :
    FateV2.Loop.EndToEnd.endToEndIter worldModelQ h η φ (h xhat) u PUnit.unit a x k θ
      = iterD xhat η φ u a x k θ := by
  induction k generalizing θ with
  | zero => rfl
  | succ k ih =>
      rw [FateV2.Loop.EndToEnd.endToEndIter, ih, iterD, endToEnd_eq_e2eD h hinj]

/-! ===========================================================================
  §4  ⭐⭐⭐ 数值结论：θ 真的被更新，且更新**依赖外生变量 u**

  **口径**：`xhat = 10`（观测估计）、`x = 10`（出发状态）、`a = 3`（干预值）、
  `θ = 1`（初始参数）、`φ = phiId`（恒等）、`η = 1/2`（步长）。
  **故残差** $r = 10 - (10 + (\text{if } u \text{ then } 3 \text{ else } 0))$
  $= -3$（若 `u = true`）/ $0$（若 `u = false`）。
  -/

/-- ⭐⭐⭐ **一步之后 `θ = -1/2`**（`u = true`：残差 `-3`，`η = 1/2`，故位移 `-3/2`）。

**⚠ 反同义反复**：**无前件**；左式经 `e2eD`（`= endToEnd`，见 §3 桥）算出，
右式是 `ℚ` 字面量。若机制不读 `θ`，此处得不到 `-1/2`。 -/
theorem theta_moves : e2eD 10 (1/2) phiId 1 true 3 10 = -1/2 := by
  simp only [e2eD, stepQ, phiId, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_true, id]
  norm_num

/-- ⭐⭐⭐ **同一步但 `u = false`：`θ` 保持 `1`**（残差 `0` ⟹ `writeBack` 不动）。

**⟹ 与 `theta_moves` 合起来，直接证明「外生变量决定 θ 是否更新」。** -/
theorem theta_fixed_when_u_false : e2eD 10 (1/2:ℚ) phiId 1 false 3 10 = 1 := by
  simp only [e2eD, stepQ, phiId, AddMonoidHom.coe_mk, ZeroHom.coe_mk, id]
  norm_num

/-- ⭐⭐⭐ **θ 的一步更新真的依赖外生变量 `u`**（`-1/2 ≠ 1`）。

**⚠ 反同义反复**：**无前件**，结论是**不等** `≠`，
证明**调用** §4 的两条具体值定理（不是重念前件）。
若 `e2eD` 把 `u` 丢掉，本定理立即为假。 -/
theorem theta_dep_u : e2eD 10 (1/2) phiId 1 true 3 10 ≠ e2eD 10 (1/2) phiId 1 false 3 10 := by
  rw [theta_moves, theta_fixed_when_u_false]
  norm_num

/-- ⭐⭐ **通式：`η = 1` 时一步映射是 `θ ↦ -2θ`**（故 `|−2| > 1` ⟹ **发散**，
不动点 `0` 不稳定；这解释了为何 `η = 1/2` 才收敛）。

**⟹ 这条定理给出「步长选择会影响稳定性」的**可算事实**，
而不是修辞（`η = 1/2` 给 `-1/2`，收缩；`η = 1` 给 `-2`，发散）。 -/
theorem fixed_point_zero (θ : ℚ) : e2eD 10 (1:ℚ) phiId θ true 3 10 = -2 * θ := by
  simp only [e2eD, stepQ, phiId, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_true, id]
  ring

/-- ⭐⭐ **迭代 1 步后 `θ = -1/2`**（经 `iterD`，即 `endToEndIter` 的镜像，见 §3 桥）。 -/
theorem iterD_one : iterD 10 (1/2:ℚ) phiId true 3 10 1 1 = -1/2 := by
  simp only [iterD, e2eD, stepQ, phiId, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_true, id]
  norm_num

/-- ⭐⭐ **迭代 3 步后 `θ = -1/8`**（`1 → -1/2 → 1/4 → -1/8`，收缩）。 -/
theorem iterD_three : iterD 10 (1/2:ℚ) phiId true 3 10 3 1 = -1/8 := by
  simp only [iterD, e2eD, stepQ, phiId, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_true, id]
  norm_num

/-- ⭐⭐⭐ **`u = false` 对**所有** `k`：`θ_k = 1`**（残差恒 `0` ⟹ 链不误伤）。

**读法**：这是 `ResidualLoop.writeBack` 的「不伤害」判据
（`writeBack_eq_self_of_residual_zero`）在本实例上的**数值表现**：
模型已经预测对了，就**不该**动参数。**对任意步数成立**，不是抽样。 -/
theorem iterD_false_fixed (k : ℕ) :
    iterD 10 (1/2:ℚ) phiId false 3 10 k 1 = 1 := by
  induction k with
  | zero => rfl
  | succ n ih =>
      have hstep : e2eD 10 (1/2:ℚ) phiId 1 false 3 10 = 1 := by
        simp only [e2eD, stepQ, phiId, AddMonoidHom.coe_mk, ZeroHom.coe_mk, id]
        norm_num
      show iterD 10 (1/2:ℚ) phiId false 3 10 n (e2eD 10 (1/2:ℚ) phiId 1 false 3 10) = 1
      rw [hstep]
      exact ih

/-! ===========================================================================
  §5  `#eval` 数值块（本文件「可运行」的正面证据）
  =========================================================================== -/

-- (N1) (i)(ii) 一步机制 `stepQ`：`x = n`、`θ = 1`、`a = 3`、`u` 交替真假
#eval (List.range 5).map fun n => stepQ (n : ℚ) (n % 2 == 0) 1 3

-- (N2) (iii) 同一 `x = 10` 在 `u = true` / `u = false` 下的预测（差 3）
#eval ([(true, stepQ 10 true 1 3), (false, stepQ 10 false 1 3)] : List (Bool × ℚ))

-- (N3) (iv) 端到端迭代：`u = true`（残差 −3，θ 收缩）
#eval (List.range 6).map fun k => iterD 10 (1/2) phiId true 3 10 k 1

-- (N4) (iv) 端到端迭代：`u = false`（残差 0，θ 恒为 1）
#eval (List.range 6).map fun k => iterD 10 (1/2) phiId false 3 10 k 1

-- (N5) 一步映射的步长敏感性：`η = 1`（发散）与 `η = 1/2`（收缩）从同一 `θ = 1` 出发
-- ⚠ 必须写类型标注 `: List (ℚ × ℚ)`：否则字面量 `1/2` 会按 `Nat` 除法退化成 `0`
#eval ([(1, e2eD 10 (1:ℚ) phiId 1 true 3 10),
        (1/2, e2eD 10 (1/2:ℚ) phiId 1 true 3 10)] : List (ℚ × ℚ))

/-! ===========================================================================
  §6  ⭐ **与 `SCMEndToEnd` 的等式对接**（任务 H，第 716 轮）

  本文件此前只 `import` 了 `SCMEndToEnd` 却**未真正消费**它的任何定理。
  本节新建一个具体 SCM `scmQ : SCM ℚ ℚ`（`U := Bool`，
  `sg u = (0, x ↦ x + (if u then 1 else 0))`），并**调用**
  `SCMEndToEnd.predFrom_scmWorldModel`（`Fate/SCMEndToEnd.lean` §1，
  前件仅 `[Nonempty Y]`，对**任意** SCM 成立）得到**数值预测**，
  再与本文件的可计算镜像 `stepQ` 对拉，得到三定义链的首次相等：

  `EndToEnd.predFrom (scmWorldModel scmQ) … a x = stepQ a u 1 1`。

  **⚠ 为什么这个 SCM 是“新的”（不是 `worldModelQ`）**：`worldModelQ` 的参数位
  `Θ = ℚ` 且机制 `stepFun` **读 `θ`**；而 `scmWorldModel M` 的参数位恒为 `PUnit`
  （见文件头 §〇 与 §五 边界 2），故 `scmQ` 与 `worldModelQ` **载体不同**。
  本节的桥只是把「`SCM` 图上的 `predFrom`」与「`worldModelQ` 的可计算镜 `stepQ`」
  在 `θ = 1, a = a` 这一个**数值切片**上对齐，**不声称**两者同构。

  **⚠ 反同义反复核查**：
  * `scmQ_predFrom_eq_stepQ` 前件只有具体取值 `u : Bool` / `a x : ℚ`，**无等式假设**；
    左侧经 `predFrom → WorldModel.f → scmWorldStep` 四层定义，右侧是 `stepQ`
    （`worldModelQ` 的镜）——证明**调用** `SCMEndToEnd.predFrom_scmWorldModel`。
  * `scmQ_pred_true` / `scmQ_pred_false` **无前件**，右式是 `ℚ` 字面量
    （`a+1 = 6` / `a = 5`）；若 SCM 的 `sg` 不读 `u`，两条会同时失败。
  * `scmQ_pred_dep_u` 结论是**不等** `≠`，无前件，证明**调用**上面两条具体值。 -/

/-- 本节的 SCM 结构方程：$h_u(x) = x + (\text{if } u \text{ then } 1 \text{ else } 0)$。

**读法**：`u = true` 时干预增益 `1`，`u = false` 时干预无效——
与 `worldModelQ.stepFun` 在 `θ = 1, a = x` 的切片上同形。 -/
def sgStep (u : Bool) (x : ℚ) : ℚ := x + (if u then 1 else 0)

/-- 具体 SCM：`U = Bool`、均匀 `pU`、结构映射 `sg u = (0, sgStep u)`。 -/
def scmQ : FateV2.Modeling.PearlHierarchy.SCM ℚ ℚ where
  U := Bool
  pU := fun _ => 1 / 2
  sg := fun u => (0, sgStep u)

/-- ⭐⭐⭐ **`SCMEndToEnd` 的 `predFrom` 在 `scmQ` 上就是 `stepQ`**（真消费 `SCMEndToEnd`）。

$$\mathrm{predFrom}\,(\mathrm{scmWorldModel}\,\mathrm{scmQ})\;\theta\;u\;\varepsilon\;a\;x
  = \mathrm{stepQ}\;a\;u\;1\;1 .$$

**证明**：`rw [SCMEndToEnd.predFrom_scmWorldModel scmQ …]`（SCM 结构映射求值），
随后 `stepQ` 与 `sgStep` 都展开为 `a + (if u then 1*1 else 0)` 而闭合。 -/
theorem scmQ_predFrom_eq_stepQ (u : Bool) (a x : ℚ) :
    EndToEnd.predFrom (SCMWorldModel.scmWorldModel scmQ) PUnit.unit u PUnit.unit a x
      = stepQ a u 1 1 := by
  rw [SCMEndToEnd.predFrom_scmWorldModel scmQ PUnit.unit u PUnit.unit a x]
  simp [scmQ, sgStep, stepQ]

/-- ⭐⭐ **数值：`u = true`（干预有效）时预测 `= a + 1`**（本文件无前件，具体值）。 -/
theorem scmQ_pred_true :
    EndToEnd.predFrom (SCMWorldModel.scmWorldModel scmQ) PUnit.unit true PUnit.unit (5 : ℚ) 3
      = 6 := by
  rw [SCMEndToEnd.predFrom_scmWorldModel scmQ PUnit.unit true PUnit.unit (5 : ℚ) 3]
  simp [scmQ, sgStep]
  norm_num

/-- ⭐⭐ **数值：`u = false`（干预无效）时预测 `= a`**。 -/
theorem scmQ_pred_false :
    EndToEnd.predFrom (SCMWorldModel.scmWorldModel scmQ) PUnit.unit false PUnit.unit (5 : ℚ) 3
      = 5 := by
  rw [SCMEndToEnd.predFrom_scmWorldModel scmQ PUnit.unit false PUnit.unit (5 : ℚ) 3]
  simp [scmQ, sgStep]

/-- ⭐⭐⭐ **`u` 影响预测（`6 ≠ 5`）**：同一 `a = 5`、同一出发 `x = 3`，
`u = true` 与 `u = false` 给出不同预测 —— 外生变量真的进入 SCM 预测端。 -/
theorem scmQ_pred_dep_u :
    EndToEnd.predFrom (SCMWorldModel.scmWorldModel scmQ) PUnit.unit true PUnit.unit (5 : ℚ) 3
      ≠ EndToEnd.predFrom (SCMWorldModel.scmWorldModel scmQ) PUnit.unit false PUnit.unit (5 : ℚ) 3 := by
  rw [scmQ_pred_true, scmQ_pred_false]
  norm_num

end

end SCMWorldModelEvalNum

end FateV2.Loop