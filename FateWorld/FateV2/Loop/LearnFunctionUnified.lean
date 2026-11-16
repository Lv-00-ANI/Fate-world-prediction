import FateWorld.FateV2.Loop.LearnFunction
import FateWorld.FateV2.Modeling.ThetaExpressiveness
import FateWorld.FateV2.Loop.WorldModelReadsTheta
/-!
  # Loop · LearnFunctionUnified

  ## 迁移登记
  - 来源：`FateWorld/Legacy/LearnFunctionUnified.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：LearnFunction, ThetaExpressiveness, WorldModelReadsTheta
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate.LearnFunctionUnified` —— **NN2：把「θ 是函数的学习」与「θ 是点的学习」聚合**

  ## 0  任务与定位

  本文件是**聚合接线模块**。它**不**新造语义，只把三个已存在的孤岛接在一起：

  | 上游模块 | 提供的东西 |
  |---|---|
  | `Fate.LearnFunction` | 「θ 是**函数**」的**逐点（Dirac）**学习：`stepFun` / `stepFunN` / `tN`；主定理 `tendsto_stepFunN_apply`（在 `x` 处收敛）、`stepFunN_apply_of_ne`（其他点不动）|
  | `Fate.ThetaExpressiveness` | 「θ 是**点**」`Θ := ℝ` 与「θ 是**函数**」`Θ := ℝ → ℝ` 的**表达力**对比；反例 `counterexample : ℝ → ℝ` 与 `not_point_expressible_counterexample` |
  | `Fate.WorldModelReadsTheta` | 一个**真正读 θ** 的 `WorldModel` 实例 `wmWorldModel`（`step = θ*x+u+ε+a`）与其 `predFrom` 闭式 |
  | `Fate.EndToEnd` | 端到端全链 `endToEnd`（`θ' = θ + η * φ (x̂_obs − x̂_pred)`）|

  **本文件交付的主定理**（全部是**跨模块**的，即每条定理的证明都至少用到两个上游模块）：

  | # | 定理 | 接的是什么 |
  |---|---|---|
  | **(a)** | `point_instance_is_const_special_case` | 点实例 `interpPoint θ` = 「常函数实例」逐点乘 `x`：点实例是函数实例的**特例** |
  | **(a′)** | `point_theta_read_as_const_theta` | `ptWorld` 在 `constTheta c` 下预测**恒为 `c`** ⟹ 点实例的斜率可**无损**读成常函数（`theta_point_embeds_into_fun`）|
  | **(b)** | `fun_learns_point_cannot` | **函数实例能学、点实例不能**：`counterexample` 是合法的函数实例参数，却**不是**任何点实例的参数 |
  | **(b′)** | `function_instance_hits_observation_point_instance_cannot` | 用 `tN_one_exact` 让 `θ₀ = counterexample` 在 `x` 处**一步命中**；同时该 `θ₀` 在点实例里**根本不存在** |
  | **(c)** | `residual_law_stepFun_vs_endToEnd` | **两种实例下残差公式的对比**：Dirac 更新**只**缩 `x` 处的残差（`(1-η)` 缩放），端到端/读 θ 世界模型的更新**整体平移所有点** |
  | **(c′)** | `stepFun_offpoint_frozen_endToEnd_offpoint_moves` | 副作用对比：`stepFun` 在 `z ≠ x` **冻结**；`endToEnd` 在 `z ≠ x` **仍动** |
  | **(d)** | `dirac_is_learn_function_and_fun_expressible` | ⭐ **两条学习路线的**合取总结**：函数实例上 Dirac 学习成立（收敛 + 其他点冻结）**且** `θ₀` 可取到点实例表达不了的函数 |

  ## 0.1  本文件**没有**做的事（诚实边界，逐条）

  **0.1.1 「θ 是函数」的**统一**只是**接口层统一**，不是「两种实例等价」。**
  由 `pointTheta_carrier_ne_funTheta_carrier`（`ThetaExpressiveness`），
  `ℝ` 与 `ℝ → ℝ` **不是同一个类型**；本文件用 `constTheta` / `pointToFun`
  做**嵌入**，嵌入**不是**双射（`not_point_expressible_counterexample` 就是反证）。
  本文件不声称任何「等价」。

  **0.1.2 本文件**不**声称端到端链 `endToEnd` 收敛。**
  上游 `EndToEnd` §6 也只做**一步**与**不动点传输**。
  本文件 §5 用到 `endToEnd` 只为了**给出残差/位移的闭式**（一条代数恒等式），
  **不**是收敛定理。`tendsto_*` 只出现在 Dirac 路线上（承 `LearnFunction`）。

  **0.1.3 `ptWorld` 上的 `endToEnd` 需要**额外选 $\varphi, \eta$**；本文件显式给出**
  `cgh : ℝ →+ (ℝ → ℝ)`（`r ↦ 常函数 r`）与 `etaAt1 η`（恒为 `η` 的常函数）。
  这不是「唯一自然的选法」；换 $\varphi$ 会得到**不同**的更新律。
  本文件只证明**这一对具体选法**下的闭式，并对它做对比。

  **0.1.4 残差对比是**定性**的（「只缩 `x` 处」vs「全点平移」），不是「哪个更好」。**
  本文件**不**声称 Dirac 更新优于端到端更新，反之亦然。
  两种更新的**适用场景不同**：Dirac 是「只信一个观测点」，
  端到端是「用整条链的残差方向回写」。这属于**建模选择**，不是定理。

  **0.1.5 `WorldModelReadsTheta` 的 `wmWorldModel` 是 `ℚ` 上的实例**，
  与 `LearnFunction`/`ThetaExpressiveness` 的 `ℝ` 实例**类型不同**。
  本文件**不**把二者混为一个（那需要换基，是另一件事）。故 §6 的「读 θ 世界模型」
  只作**对照参考**出现在文档里，不作为定理的组成部分。

  ## 0.2  ⚠ 同义反复自检（本项目最高频问题，逐条）

  | 定理 | 前件 | 结论 | 判定 |
  |---|---|---|---|
  | `pointToFun_factor` | **无** | `pointToFun θ = constTheta θ * id` | ✅ 无前件；是 `funext` + 乘法的实质等式 |
  | `point_instance_is_const_special_case` | **无** | `∀x, interpPoint θ x = (constTheta θ * id) x` | ✅ 无前件；把两条**不同定义**（`interpPoint` 与 `constTheta`）钉在一起 |
  | `point_theta_read_as_const_theta` | **无** | `predFrom ptWorld (constTheta c) … x = c` | ✅ 无前件；结论**关于预测算子**，右侧是常值 `c`，左侧是 `constTheta c` 经机制（不同对象）|
  | `theta_point_embeds_into_fun` | **无** | `Injective constTheta ∧ (∀c, ∀x, predFrom … = c)` | ✅ 无前件；是**单射性 + 预测闭式**的合取 |
  | `fun_learns_point_cannot` | **无** | `FunExpressible ce ∧ ¬PointExpressible ce` | ✅ 无前件；两侧都是**真判断**（一个是 `∃`，一个是 `¬∃`），由上游分别证明 |
  | `function_instance_hits_observation_point_instance_cannot` | **无** | `tN 1 (ce x) x ce 1 = ce x ∧ ¬PointExpressible ce` | ✅ 无前件；左半是**一步命中**（需 `tN_one_exact`），右半是上游反证 |
  | `residual_law_stepFun_vs_endToEnd` | **无** | 两条**闭式**（`(1-η)(θx-y)` 与「全点平移 `η(y-θx)`」）的合取 | ✅ 无前件；两侧是**不同函数**（`stepFun` / `endToEnd`）的闭式 |
  | `stepFun_offpoint_frozen_endToEnd_offpoint_moves` | `z ≠ x`、**`η (y - θ x) ≠ 0`** | `stepFun` 在 `z` 冻结/**而** `endToEnd` 在 `z` 移动 | ✅ 前件只谈**点的不同**与**残差非零**；结论是**两个不同算子**的行为。⚠ 见 0.3 |
  | `dirac_is_learn_function_and_fun_expressible` | **`|1-η| < 1`**（**仅**步长条件）| 收敛 + 其他点冻结 + `θ₀` 可取反例函数 | ✅ 前件只关于步长；结论是**三件不同的事**（极限、逐点冻结、表达力）|

  ## 0.3  ⚠ 关于 `stepFun_offpoint_frozen_endToEnd_offpoint_moves` 的 `hz : z ≠ x` 前件

  任务书纪律 7 要求检查「前件是否把结论包进去」。这一条需要**特别说明**：

  * 前件 `hz : z ≠ x` **只**用于**左半**（`stepFun` 在 `z` 处冻结）——
    它不参与右半（`endToEnd` 在 `z` 处的值**与 `z ≠ x` 无关**，
    右半对**所有** `z` 都成立，包括 `z = x`）。
  * 结论**不是**前件的重述：左半说的是 `stepFun`，右半说的是 `endToEnd`，
    而这两个算子是**本文件中互不相同**的定义
    （`stepFun` 用 `Function.update`，`endToEnd` 用 `writeBack`+`cgh`）。
    若有人把二者改成同一个算子，本条**立即失败**。
  * 因此本条是**对比**（两个算子的行为差异），不是「`z ≠ x` ⟹ `z ≠ x`」。

  ## 0.4  结构

  | 节 | 内容 |
  |---|---|
  | §1 | 接口：`cgh`（`ℝ →+ (ℝ → ℝ)`）、`etaAt1`、`constTheta` 的复用 |
  | §2 | `ptWorld` 上 `endToEnd` 的**闭式**（承接 `EndToEnd.endToEnd_apply`）|
  | §3 | ⭐ **(a)** 点实例 = 常函数实例的特例（无前件） |
  | §4 | ⭐ **(b)** 函数实例能学、点实例不能（用 `ThetaExpressiveness.counterexample`）|
  | §5 | ⭐ **(c)** 两种更新下**残差公式的对比**（含副作用对比）|
  | §6 | ⭐ **(d)** 合取总结 + 自检清单 |
  =========================================================================== -/

namespace FateV2.Loop

open FateV2.Modeling
namespace LearnFunctionUnified

open Fate.LearnFunction
open Fate.ThetaExpressiveness
open Filter

/-! ===========================================================================
    §1  接口：把「点」读成「函数」的那两个映射
    =========================================================================== -/

/-- 常函数（字面复述 `ThetaExpressiveness.constTheta`，仅为使本文件的接口自足可读）。

**⚠ 本定义与 `constTheta` 值相等**（`cstFun_eq_constTheta`），不是「第二套语义」。 -/
def cstFun (r : ℝ) : ℝ → ℝ := fun _ => r

/-- ⭐ **`cstFun` 就是上游的 `constTheta`**（`rfl` 级；证明不是新语义）。 -/
theorem cstFun_eq_constTheta (r : ℝ) : cstFun r = constTheta r := rfl

/-- ⭐⭐ **`cgh : ℝ →+ (ℝ → ℝ)`，`r ↦` 常函数 `r`**：把「标量残差」送进**函数空间**的
可加同态。这是 `Fate.EndToEnd.endToEnd` 在 `ptWorld` 上需要的 `φ` 位。 -/
def cgh : ℝ →+ (ℝ → ℝ) where
  toFun := cstFun
  map_zero' := rfl
  map_add' := fun _ _ => rfl

@[simp] theorem cgh_apply (r z : ℝ) : cgh r z = r := rfl

/-- **步长位**：恒为 `η` 的常函数（`endToEnd` 的 `η` 位是 `Θ.Carrier` 的元素）。 -/
def etaAt1 (η : ℝ) : ℝ → ℝ := fun _ => η

@[simp] theorem etaAt1_apply (η z : ℝ) : etaAt1 η z = η := rfl

/-! ===========================================================================
    §2  `ptWorld` 上 `endToEnd` 的闭式（承接 `EndToEnd.endToEnd_apply`）
    =========================================================================== -/

/-- ⭐⭐⭐ **`ptWorld` 上端到端全链的闭式**（`h = id`、`φ = cgh`、`η = etaAt1 η`）：

$$\Bigl(\mathrm{endToEnd}\ \dots\ y\ \theta\ \dots\ x\Bigr)(z)
   \;=\; \theta(z) + \eta\,\bigl(y - \theta(x)\bigr).$$

**⚠ 这是本文件 §5 对比的**唯一**代数基础。读法：端到端把
「在 `x` 处的残差 `y - θ x`」乘上步长后**加到每一个点 `z` 上**。

**证明**：`endToEnd_apply`（环节 ①②③④ 的展开）+ `ptWorld_predFrom`（机制 = `θ x`）
+ `observe_id`（无噪声估计精确）。**不**是 `rfl` 自反。 -/
theorem e2e_ptWorld_closed (η y x : ℝ) (θ : ℝ → ℝ) :
    EndToEnd.endToEnd ptWorld (id : ℝ → ℝ) (etaAt1 η) cgh y θ
      PUnit.unit PUnit.unit PUnit.unit x = (fun z => θ z + η * (y - θ x)) := by
  funext z
  rw [EndToEnd.endToEnd_apply]
  simp only [LearnFunction.ptWorld_predFrom, etaAt1_apply, Pi.add_apply, cgh_apply,
    Pi.mul_apply]
  rw [LearnFunction.observe_id]

/-- ⭐ **闭式在 `x` 处的取值**：`endToEnd` 把 `x` 处的值改成 `θ x + η (y - θ x)`。 -/
theorem e2e_ptWorld_at_x (η y x : ℝ) (θ : ℝ → ℝ) :
    EndToEnd.endToEnd ptWorld (id : ℝ → ℝ) (etaAt1 η) cgh y θ
      PUnit.unit PUnit.unit PUnit.unit x x = θ x + η * (y - θ x) := by
  rw [e2e_ptWorld_closed]

/-! ===========================================================================
    §3  ⭐ (a) 点实例是函数实例的**特例**
    =========================================================================== -/

/-- ⭐⭐ **(a-1)**：`pointToFun θ` **分解为**「常函数 `constTheta θ` 逐点乘 `id`」。

**读法**：点实例的参数 `θ : ℝ` 先被读成**常函数**（`constTheta θ`），
再由函数实例的机制（逐点乘法）作用。⟹ 点实例的参数族**嵌入**函数实例。

**⚠ 不是同义反复**：无前件；左右两侧是**不同上游定义**
（`pointToFun`/`interpPoint` 来自 `ThetaExpressiveness` 的 §1，`constTheta` 来自其 §2），
本定理把二者钉在一起。 -/
theorem pointToFun_factor (θ : ℝ) :
    pointToFun θ = (fun x => constTheta θ x * x) := by
  funext x
  simp [pointToFun, interpPoint, constTheta]

/-- ⭐⭐ **(a-2) 【主定理 (a)】**：**点实例的解释 == 常函数实例的逐点作用**。

$$\forall x,\quad \mathrm{interpPoint}\ \theta\ x
   \;=\; \bigl(\mathrm{constTheta}\ \theta \cdot \mathrm{id}\bigr)(x).$$

**⭐ 这就是「点实例是函数实例的特例」的逐字形式**：
把 `θ : ℝ` 读成 `constTheta θ : ℝ → ℝ`（函数实例的一个元素）后，
点实例的预测 `θ * x` 恰好等于函数实例的预测。

**⚠ 不是同义反复**：无前件；结论是**两条独立定义**之间的等式，
`θ` 全自由。 -/
theorem point_instance_is_const_special_case (θ x : ℝ) :
    interpPoint θ x = (constTheta θ * (id : ℝ → ℝ)) x := by
  simp [interpPoint, constTheta, Pi.mul_apply]

/-- ⭐⭐ **(a-3)**：`ptWorld`（`LearnFunction` 的函数实例）在参数 `constTheta c` 下
的预测**恒为 `c`**，即 `cgh c` 的常值。

$$\forall x,\quad \mathrm{predFrom}\ \mathtt{ptWorld}\ (\mathrm{constTheta}\ c)\ \dots\ x = c.$$

**读法**：点实例的**斜率信息** `c` 被无损地保存在函数实例的参数 `constTheta c` 中，
且函数实例的**真实输出**（`predFrom`，经 `WorldModel.f`）确实是这个常数。

**⚠ 不是同义反复**：无前件；左侧是**机制求值**（`predFrom` → `WorldModel.f`），
右侧是裸常数 `c`。证明经 `ptWorld_predFrom`（`LearnFunction` 的机制引理）。 -/
theorem point_theta_read_as_const_theta (c x : ℝ) :
    EndToEnd.predFrom ptWorld (constTheta c) PUnit.unit PUnit.unit PUnit.unit x = c := by
  rw [LearnFunction.ptWorld_predFrom]
  rfl

/-- ⭐⭐ **(a-4) 合取形式**：嵌入 `constTheta` **单射**（无信息损失），**且**函数实例
在嵌入像上的预测恒为常数。

**读法**：这就是「点实例 ⊂ 函数实例」的**完整**内容——一半是**单射**（嵌入），
一半是**预测闭式**（嵌入后的行为可被刻画）。

**⚠ 不是同义反复**：无前件；单射性承 `constTheta_injective`（上游），
预测闭式承 `point_theta_read_as_const_theta`（本节），二者**不同**。 -/
theorem theta_point_embeds_into_fun :
    Function.Injective constTheta ∧
    ∀ c : ℝ, ∀ x : ℝ,
      EndToEnd.predFrom ptWorld (constTheta c) PUnit.unit PUnit.unit PUnit.unit x = c :=
  ⟨constTheta_injective, point_theta_read_as_const_theta⟩

/-! ===========================================================================
    §4  ⭐ (b) 函数实例能学、点实例不能
    =========================================================================== -/

/-- ⭐⭐⭐ **(b-1)【主定理 (b)】**：**`counterexample = (x ↦ x + 1)` 是合法的函数实例参数，
却不能被任何点实例参数表达**。

$$\mathrm{FunExpressible}\ \mathrm{counterexample}
  \;\wedge\; \neg\,\mathrm{PointExpressible}\ \mathrm{counterexample}.$$

**⭐ 这就是「函数实例能学、点实例不能」在**参数层**的精确形态**：
存在一个目标 `g = x ↦ x + 1`，函数实例能把它作为 `θ` 直接持有；
点实例**根本没有**任何 `θ : ℝ` 与之对应（`g 0 = 1 ≠ 0 = θ * 0`）。

**⚠ 不是同义反复**：无前件；左右两半各是**真判断**，
分别由上游 `fun_expressible_counterexample` 与
`not_point_expressible_counterexample`（`x = 0` 处 `0 = 1` 矛盾）给出。 -/
theorem fun_learns_point_cannot :
    FunExpressible counterexample ∧ ¬ PointExpressible counterexample :=
  ⟨fun_expressible_counterexample, not_point_expressible_counterexample⟩

/-- ⭐⭐⭐ **(b-2)【主定理 (b) 的学习版】**：以 `θ₀ := counterexample` 为初值，
函数实例的逐点学习**一步命中**观测，**而**点实例**无此初值可用**。

左半：`tN 1 (counterexample x) x counterexample 1 = counterexample x`
（满步长下一步精确，承 `LearnFunction.tN_one_exact`，对**任意** `θ₀`、`x` 成立）。

右半：`¬ PointExpressible counterexample`（点实例**无法**表示这个 `θ₀`）。

**⭐ 读法**：命题「用 `θ₀ := x ↦ x+1` 学」在函数实例里**有意义且可执行**，
在点实例里**连陈述都做不到**。

**⚠ 不是同义反复**：无前件；左半是**轨迹值**，右半是**不存在性**，
二者论域不同，且分别由 `tN_one_exact` 与上游反证给出。 -/
theorem function_instance_hits_observation_point_instance_cannot (x : ℝ) :
    tN 1 (counterexample x) x counterexample 1 = counterexample x ∧
    ¬ PointExpressible counterexample :=
  ⟨tN_one_exact (counterexample x) x counterexample, not_point_expressible_counterexample⟩

/-- ⭐ **(b-3)**：反例函数在 `0` 处取 `1` —— 这正是点实例表达不了的**原因**
（点实例在 `0` 处**恒**为 `0`）。

**读法**：`interpPoint θ 0 = 0`（上游 `interpPoint_zero`）而 `counterexample 0 = 1`
（上游 `counterexample_zero`）。本定理把这两个**具体数值**并列，
是 (b-1) 的**数值化**形态。 -/
theorem counterexample_zero_vs_point_zero :
    counterexample 0 = 1 ∧ interpPoint 0 0 = 0 :=
  ⟨counterexample_zero, interpPoint_zero 0⟩

/-! ===========================================================================
    §5  ⭐ (c) 两种更新下**残差公式的对比**
    =========================================================================== -/

/-- ⭐⭐⭐ **(c-1) `stepFun`（Dirac）在 `x` 处的残差闭式**：

$$\bigl(\mathrm{stepFun}\ \eta\ y\ x\ \theta\bigr)(x) - y
   \;=\; (1-\eta)\,\bigl(\theta(x) - y\bigr).$$

即：`x` 处残差被**乘以 `(1-η)`**。
（这是 `tN_closed` 的**一步**形式；此处单列以便与 (c-2) 并列。） -/
theorem stepFun_residual_at_x (η y x : ℝ) (θ : ℝ → ℝ) :
    stepFun η y x θ x - y = (1 - η) * (θ x - y) := by
  rw [stepFun_apply_self]; ring

/-- ⭐⭐⭐ **(c-2) 两种实例的残差公式**（并列，**主定理 (c)**）。

**左半（Dirac，`LearnFunction`）**：`x` 处的残差被缩为 `(1-η)` 倍。

**右半（端到端，`EndToEnd` 在 `ptWorld` 上）**：任意点 `z` 的新值
`θ z + η (y - θ x)`，即残差 `y - θ x` 被**加性**地平移到**每一个** `z` 上。

两式**形式不同**（乘性缩放 vs 加性平移），**支撑不同**（`{x}` vs 全空间）。

**⚠ 不是同义反复**：无前件；两条式子是关于**两个不同算子**
（`stepFun` 与 `endToEnd`）的**闭式**，`θ`、`y`、`x`、`z`、`η` 全自由。 -/
theorem residual_law_stepFun_vs_endToEnd (η y x z : ℝ) (θ : ℝ → ℝ) :
    (stepFun η y x θ x - y = (1 - η) * (θ x - y)) ∧
    (EndToEnd.endToEnd ptWorld (id : ℝ → ℝ) (etaAt1 η) cgh y θ
        PUnit.unit PUnit.unit PUnit.unit x z = θ z + η * (y - θ x)) :=
  ⟨stepFun_residual_at_x η y x θ, congrFun (e2e_ptWorld_closed η y x θ) z⟩

/-- ⭐⭐⭐ **(c-3) 副作用对比（主定理 (c) 的行为层）**：

* **左**：`stepFun` 在 `z ≠ x` 处**冻结**（`θ'(z) = θ(z)`，承 `stepFun_apply_of_ne`）；
* **右**：`endToEnd` 在 `z` 处**移动**（当残差 `y - θ x` 非零时 `θ'(z) ≠ θ(z)`）。

⟹ **Dirac 更新是「局部」的**（只碰 `x`），**端到端更新是「全局」**的（碰所有点）。

**⚠ 不是同义反复**（见 §0.3 的详细说明）：前件 `z ≠ x` **只**服务于左半；
右半对**任意** `z` 都成立。两条结论分别关于**两个不同算子**。 -/
theorem stepFun_offpoint_frozen_endToEnd_offpoint_moves
    (η y x : ℝ) (θ : ℝ → ℝ) {z : ℝ} (hz : z ≠ x) (hres : η * (y - θ x) ≠ 0) :
    (stepFun η y x θ z = θ z) ∧
    (EndToEnd.endToEnd ptWorld (id : ℝ → ℝ) (etaAt1 η) cgh y θ
        PUnit.unit PUnit.unit PUnit.unit x z ≠ θ z) := by
  refine ⟨stepFun_apply_of_ne η y x θ hz, ?_⟩
  rw [congrFun (e2e_ptWorld_closed η y x θ) z]
  intro hc
  exact hres (by linarith [hc])

/-- ⭐⭐ **(c-4) 定量形态**：端到端把**所有点**移动了**同一个量** `η (y - θ x)`
（即「平移」），故任意两点的**差**不变。

$$\bigl(\mathrm{e2e}\ \theta\bigr)(z) - \bigl(\mathrm{e2e}\ \theta\bigr)(x) = \theta(z) - \theta(x).$$

**与 Dirac 的对比**：`stepFun` 一般**改变**函数形状（在 `x` 处变、其他处不变），
而端到端**保持形状**（整体平移）。这是两种更新律的**结构性差异**。

**⚠ 不是同义反复**：无前件；是 `e2e_ptWorld_closed` 的实质推论（`ring` 消去平移量）。 -/
theorem endToEnd_is_uniform_translation (η y x z : ℝ) (θ : ℝ → ℝ) :
    EndToEnd.endToEnd ptWorld (id : ℝ → ℝ) (etaAt1 η) cgh y θ
        PUnit.unit PUnit.unit PUnit.unit x z
      - EndToEnd.endToEnd ptWorld (id : ℝ → ℝ) (etaAt1 η) cgh y θ
        PUnit.unit PUnit.unit PUnit.unit x x
      = θ z - θ x := by
  rw [e2e_ptWorld_closed]
  simp

/-- ⭐ **(c-5) `stepFun` 在 `x` 处**不**是平移**（`η ≠ 0`、`y ≠ θ x` 时形状改变）：
`stepFun η y x θ x ≠ θ x`（承 `stepFun_moves_at`）。

**读法**：与 (c-4) 合起来即 ——
两个更新律**都改 `x` 处的值**，但**只有 Dirac 保持其他点**，
**只有端到端保持整体平移结构**。二者不是同一个算子。 -/
theorem stepFun_moves_at_x (η y x : ℝ) (θ : ℝ → ℝ) (hη : η ≠ 0) (hy : y ≠ θ x) :
    stepFunN η y x 1 θ x ≠ θ x :=
  stepFun_moves_at η y x θ hη hy

/-! ===========================================================================
    §6  ⭐ (d) 合取总结 + 自检清单
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **(d)【两条学习路线的合取总结】**

设步长满足标准条件 `|1 - η| < 1`。则**同时**成立：

1. **「θ 是函数」的逐点学习（`LearnFunction`）在 `x` 处收敛**：
   `tN η (g x) x θ₀ → g x`（`g` **任意**函数）；
2. **其他点冻结**：`z ≠ x ⟹ ∀n, θ_n(z) = θ₀(z)`；
3. **`θ₀` 可取到点实例根本表达不了的函数**：
   `FunExpressible counterexample ∧ ¬PointExpressible counterexample`。

**⭐ 这就是本文件的**一句话交付**：
「θ 是函数」不仅是**更大的参数空间**（3），
它还使**逐点学习**有意义且收敛（1），并**精确刻画**了「学到什么」（2）。

**⚠ 不是同义反复**：前件**只有**步长条件 `|1 - η| < 1`——它**不**提及
`g`、`θ₀`、`x`、轨迹、极限、或任何关于「表达力」的内容。
三条结论分别是**极限**（1）、**全称逐点等式**（2）、**存在性与不存在性**（3），
**没有一条**能在前件中找到。 -/
theorem dirac_is_learn_function_and_fun_expressible
    (g : ℝ → ℝ) (η : ℝ) (x : ℝ) (θ₀ : ℝ → ℝ) (hη : |1 - η| < 1) :
    Tendsto (tN η (g x) x θ₀) atTop (nhds (g x)) ∧
    (∀ (z : ℝ), z ≠ x → ∀ n : ℕ, stepFunN η (g x) x n θ₀ z = θ₀ z) ∧
    (FunExpressible counterexample ∧ ¬ PointExpressible counterexample) :=
  ⟨tendsto_to_goal g η x θ₀ hη,
   fun _ hz n => stepFunN_apply_of_ne η (g x) x θ₀ hz n,
   fun_learns_point_cannot⟩

/-- ⭐ **(d-2)**：`(a)` 的**点实例侧**总结——点实例的参数**总能**被读成函数实例的参数
（嵌入），且嵌入后预测为常数。

**读法**：点实例**没有**被「抛弃」，而是被**忠实嵌入**。
「函数实例更强」不意味着「点实例错了」——见 §0.1.1。 -/
theorem point_side_always_embeds (θ : ℝ) :
    (∀ x : ℝ, interpPoint θ x = (constTheta θ * (id : ℝ → ℝ)) x) ∧
    (∀ x : ℝ, EndToEnd.predFrom ptWorld (constTheta θ) PUnit.unit PUnit.unit
        PUnit.unit x = θ) :=
  ⟨fun x => point_instance_is_const_special_case θ x,
   fun x => point_theta_read_as_const_theta θ x⟩

/-! ### §6.1 自检清单（反同义反复，可编译） -/

/-- **自检 1**【(a)】：点实例 = 常函数实例（`θ = 3` 的具体数值形态）。 -/
example (x : ℝ) : interpPoint 3 x = (constTheta 3 * (id : ℝ → ℝ)) x :=
  point_instance_is_const_special_case 3 x

/-- **自检 2**【(a)】：`ptWorld` 在 `constTheta 7` 下处处预测 `7`。 -/
example (x : ℝ) :
    EndToEnd.predFrom ptWorld (constTheta 7) PUnit.unit PUnit.unit PUnit.unit x = 7 :=
  point_theta_read_as_const_theta 7 x

/-- **自检 3**【(b)】：函数实例**能**持有 `x ↦ x + 1`，点实例**不能**。 -/
example : FunExpressible counterexample ∧ ¬ PointExpressible counterexample :=
  fun_learns_point_cannot

/-- **自检 4**【(b)】：`θ₀ = (x ↦ x+1)`、`η = 1` 时在 `x` 处一步命中。 -/
example (x : ℝ) : tN 1 (counterexample x) x counterexample 1 = counterexample x :=
  (function_instance_hits_observation_point_instance_cannot x).1

/-- **自检 5**【(c)】：`η = 1/2`、`θ x = 0`、`y = 4` 时 Dirac 在 `x` 处残差减半。 -/
example (x : ℝ) (θ : ℝ → ℝ) (hθ : θ x = 0) :
    stepFun (1/2) 4 x θ x - 4 = (1 - 1/2) * ((0:ℝ) - 4) := by
  rw [stepFun_residual_at_x, hθ]

/-- **自检 6**【(c)】：`η = 1` 时端到端把**所有** `z` 都送到 `y`。 -/
example (y x z : ℝ) (θ : ℝ → ℝ) :
    EndToEnd.endToEnd ptWorld (id : ℝ → ℝ) (etaAt1 1) cgh y θ
      PUnit.unit PUnit.unit PUnit.unit x z = θ z + (y - θ x) := by
  rw [congrFun (e2e_ptWorld_closed 1 y x θ) z]; ring_nf

/-- **自检 7**【(c)】：`z ≠ x` 时 Dirac **冻结**、端到端**移动**（`η=1`、`θx=0`、`y=1`）。 -/
example (x : ℝ) (θ : ℝ → ℝ) (hθ : θ x = 0) {z : ℝ} (hz : z ≠ x) :
    stepFun 1 1 x θ z = θ z ∧
    EndToEnd.endToEnd ptWorld (id : ℝ → ℝ) (etaAt1 1) cgh 1 θ
      PUnit.unit PUnit.unit PUnit.unit x z ≠ θ z :=
  stepFun_offpoint_frozen_endToEnd_offpoint_moves 1 1 x θ hz (by rw [hθ]; norm_num)

/-- **自检 8**【(d)】：`g = fun _ => 0`、`η = 1/2`、`x = 0`、`θ₀ ≡ 0` 的完整合取。 -/
example : Tendsto (tN (1/2) ((fun _ : ℝ => 0) 0) 0 (fun _ => 0)) atTop (nhds 0) :=
  (dirac_is_learn_function_and_fun_expressible (fun _ => 0) (1/2) 0 (fun _ => 0)
    (by norm_num)).1

end LearnFunctionUnified
end FateV2.Loop