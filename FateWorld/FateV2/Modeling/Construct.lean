import FateWorld.FateV2.Modeling.SCM
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic

/-!
  # Modeling · Construct —— 合成数据的数学构造

  ## 迁移登记
  - 来源：新写（依据 `理论-文档/00-裁决台账/裁决D-007-数据必须数学构造.md`、
          `裁决D-023-背景信息答复一.md` C4「建模 = 转换数据格式」）
  - 动作：C 重写
  - 对应环节：F5-01（SCM 结构）、F2-01（转移方程）、F1-13（数据载体并入建模层）
  - 依赖裁决：**D-007**（数据必须数学构造）、**D-008**（建模层是全链第一层）、
              **D-013**（模型是一体化完整系统）、**D-014**（模型 = SCM）、
              **D-019**（自由度最大化）、**D-023 C4**（建模 = 转换数据格式）
  - 改动：原文件是空骨架。现按 D-007 用**数学语言**构造一份合成数据集，
          并把它转换成建模层的模型（C4：建模就是格式转换）。
  - 状态：已验证（`FateV2/Demo/SyntheticRun.lean` 端到端跑通）

  ## 超出定义之处（按 D-023 A4 逐条登记）
  * `synth_state_at_one`：把代数式在 `a = 9/10, u = 1, x = 1, eps = 1/4`
    处算成**具体数 5/4**——`rfl` 化不成这个数，必须真的做算术归一。
  * `synthLaw_total`：`synthLaw` 的定义只写了「对 `flatMap` 乘积」，
    **没有**要求权重和与分量权重和的乘积有关。本定理说明这个构造**是保概率的**。
  * `synthLaw_length`：定义对 `vals` 与 `wt` 分别做 `flatMap`，
    **不保证**两者长度一致；本定理说它们同步（「每条取值恰有一个权重」）。

  ## 为什么是「合成数据」

  D-023 A2：作者答复「**暂时无数据**」，且明令
  「端到端『真实数据跑通』暂不可交付。**不得假装已跑通**」。
  故本文件的数据是**显式合成**的，构造过程完全公开：

  ```
  x_{t+1} = 0.9 * x_t + u + eps ,   eps ~ 离散分布（四项，等权）
  y       = x + 0.1 * w         ,   w   ~ 离散分布（两项，等权）
  ```

  这条式子本身就是**数学对象**（不是「原始数据」的转述），
  于是符合 D-007「数据必须用数学语言构造」。

  ## 名字

  `Modeling/Construct` 位于 `FateV2.Modeling` 命名空间内，
  为不与任何未来的 `Modeling.construct` 冲突，本文件一律加 `synth` 前缀。

  ## 图为什么给 `some`

  `SCM.Model.graph : Option (Graph V)` 是**可选**的（A1 未定）。
  但 `Model/Dynamics.eval`（按拓扑序求值）**必须有图**才能算。
  合成例子里图是**已知**的（两条边），故这里就填 `some _`——
  于是「无图则无法 eval」这条结构性缺失在合成例里不触发。
-/

namespace FateV2.Modeling

universe u

open MeasureTheory

/-! `Real` 的除法与判等（`Real.instDivInvMonoid` / `Real.decidableEq`）
在 Lean 里是 `noncomputable`，而合成数据要用它们。
这是 `Classical` 层的既有事实，不是本文件的取舍。 -/
noncomputable section

/-! ===========================================================================
  §1  合成数据的类型层
  =========================================================================== -/

/-- **合成系统的内生变量**：只有两个节点。

  * `state` —— 状态 `x_t`
  * `obs`   —— 观测 `y = x + 0.1 * w`（`state` 的子节点） -/
inductive SynthV where
  /-- 状态节点 -/
  | state
  /-- 观测节点（`state` 的子节点） -/
  | obs
  deriving DecidableEq

/-- **外生赋值**：一次噪声实现 = 两条噪声分量。

  本合成例的外生变量与内生节点**一一对应**（每个节点一条噪声），
  故 `E` 直接写成积类型——`SCM.Model` 的 `E` 参数不受限制（D-019）。 -/
structure SynthE where
  /-- 状态方程的噪声 `eps_t` -/
  eps : Real
  /-- 观测方程的噪声 `w_t` -/
  w   : Real

/-- 两分量都相等即整体相等。

  `SynthE` **故意没有** `DecidableEq`：`Real` 上的判等不可计算，
  给了会让下游全部变成 `noncomputable`。故此处手写外延性。 -/
theorem SynthE.ext' {x y : SynthE} (h1 : x.eps = y.eps) (h2 : x.w = y.w) : x = y := by
  cases x with
  | mk e1 w1 =>
    cases y with
    | mk e2 w2 =>
      show SynthE.mk e1 w1 = SynthE.mk e2 w2
      rw [show e2 = e1 from h1.symm, show w2 = w1 from h2.symm]

/-- 合成数据的确定性参数（`x_{t+1} = a * x_t + u + eps`）。 -/
structure SynthParams where
  /-- 自回归系数 `a` -/
  a : Real
  /-- 外生驱动 / 控制 `u` -/
  u : Real

/-! ===========================================================================
  §2  离散噪声律（`Noise` 作为参数传入，此处取具体实例）
  =========================================================================== -/

/-- 状态噪声的取值：`{-1/2, -1/4, 1/4, 1/2}`（对称、零均值）。 -/
def epsVals : List Real := [-1 / 2, -1 / 4, 1 / 4, 1 / 2]

/-- 状态噪声的权重。 -/
def epsWt : List Nat := [1, 1, 1, 1]

/-- 观测噪声的取值：`{-1, 1}`（对称、零均值）。 -/
def obsVals : List Real := [-1, 1]

/-- 观测噪声的权重。 -/
def obsWt : List Nat := [1, 1]

/-- 一个**离散律**：取值列表 + 自然数权重。

  用 `Nat` 权重而不是 `Real` 概率，是为了让 `#eval` 能直接跑：
  `Real` 上的判等与除法在 Lean 里不可执行，而 `Nat` 上的可以。
  `α` 参数化（D-019：不写死取值类型），合成例里联合律取 `α = SynthE`。 -/
structure DiscLaw (α : Type) where
  /-- 取值 -/
  vals : List α
  /-- 权重（和为 `total`） -/
  wt   : List Nat

/-- 权重总和。 -/
def DiscLaw.total {α : Type} (L : DiscLaw α) : Nat := L.wt.sum

/-- 合成数据用的联合律：`eps` 与 `w` **独立**，故联合律 = 积律。 -/
def synthLaw : DiscLaw SynthE where
  vals := epsVals.flatMap (fun e => obsVals.map (fun w => SynthE.mk e w))
  wt   := epsWt.flatMap (fun a => obsWt.map (fun b => a * b))

/-! ### §2.1 律的一致性

  下面几条是**构造出的数据对象自身**的性质：权重和为 1 的倍数、取值表与权重表同步。
  它们是「这份合成数据是一个合法离散概率分布」的全部内容。 -/

/-- 状态噪声四项权重之和为 `4`（= 4 × 1/4）。 -/
theorem eps_weight_sum : epsWt.sum = 4 := by decide

/-- 观测噪声两项权重之和为 `2`（= 2 × 1/2）。 -/
theorem obs_weight_sum : obsWt.sum = 2 := by decide

/-- 乘积律的**规模**：`vals` 与 `wt` 的条数都是 `4 × 2 = 8`。

  **超出定义之处**：`synthLaw` 的定义对 `vals` 与 `wt` 分别做 `flatMap`，
  定义本身**不保证**两者同步。本定理说它们**同步**——
  这是「每条取值恰有一个权重」的必要条件，否则离散律不合法。 -/
theorem synthLaw_length : synthLaw.vals.length = synthLaw.wt.length := by
  show (epsVals.flatMap (fun e => obsVals.map (fun w => SynthE.mk e w))).length
      = (epsWt.flatMap (fun a => obsWt.map (fun b => a * b))).length
  rw [List.length_flatMap, List.length_flatMap]
  rfl

/-- 乘积律的权重求和（自证，不借道 Mathlib 的 `flatMap` 引理）。 -/
theorem flatMap_sum_eq (wt : List Nat) (f : Nat → List Nat) :
    (wt.flatMap f).sum = (wt.map (fun a => (f a).sum)).sum := by
  induction wt with
  | nil => rfl
  | cons h t ih =>
    show ((f h) ++ (t.flatMap f)).sum = (f h).sum + (t.map (fun a => (f a).sum)).sum
    rw [List.sum_append, ih]

/-- **联合律权重总和 = 8**，恰为 `4 × 2`：两个分量**独立相乘**，
  故联合律仍是概率分布（每条概率 `1/8`）。

  **超出定义之处**：`synthLaw` 的定义没有要求权重和与分量权重和的乘积有关。
  本定理说明这个构造**是保概率的**（联合律总权重 = 分量总权重之积，8 = 4·2），
  即「两份独立离散律的积仍是概率分布」在这份具体数据上成立。 -/
theorem synthLaw_total : synthLaw.total = epsWt.sum * obsWt.sum := by
  show (epsWt.flatMap (fun a => (obsWt.map (fun b => a * b)))).sum
      = epsWt.sum * obsWt.sum
  rw [flatMap_sum_eq]
  show (epsWt.map (fun a => (obsWt.map (fun b => a * b)).sum)).sum
      = epsWt.sum * obsWt.sum
  rw [show (epsWt.map (fun a => (obsWt.map (fun b => a * b)).sum))
        = epsWt.map (fun a => a * obsWt.sum) from
        List.map_congr_left (fun a _ => List.sum_map_mul_left obsWt (fun b => b) a)]
  rw [List.sum_map_mul_right]
  exact (Nat.mul_comm _ _).symm

/-- **联合律合法**：取值表与权重表同步（各 8 条），且权重和为 8。

  **超出定义之处**：`synthLaw` 只写了「取值与权重各自 `flatMap`」，
  **没有**把「取值表长度 = 权重表长度」写进定义。
  本定理把两处**独立算出**的事实合起来，得到离散律的合法性。 -/
theorem synthLaw_wellFormed :
    synthLaw.vals.length = synthLaw.wt.length ∧ synthLaw.total = 8 := by
  have h1 : epsWt.sum = 4 := eps_weight_sum
  have h2 : obsWt.sum = 2 := obs_weight_sum
  refine ⟨synthLaw_length, ?_⟩
  rw [synthLaw_total, h1, h2]

/-! ===========================================================================
  §3  结构方程族
  =========================================================================== -/

/-- **合成模型的参数**：`a = 9/10`、`u = 1`。

  `9/10` 与 `1/10` 都写成 `Real` 上的除法而不写 `0.9`：
  后者的字面量在 Lean 里走定点数，不适合开定理。 -/
def synthParams : SynthParams where
  a := 9 / 10
  u := 1

/-- **结构方程族**。

  * `state` 节点：`x_{t+1} = a * x_t + u + eps`。
    用 `pa`（父节点赋值）取 `state` 自己的**上一步**值——
    这正是「状态节点是自回归的」在图上的写法：`pa state = [state]`。
  * `obs` 节点：`y = x + 0.1 * w`，只读 `state`。

  写成带名字的 `match` 而不是多行 `| pat` **方程子**：
  后者会让归约键不固定（实测 `show` 无法把 `F v pa e` 展开），
  这是本工具链上的硬约束。 -/
def synthF (p : SynthParams) : SynthV → (SynthV → Real) → SynthE → Real :=
  fun v pa e =>
    match v with
    | SynthV.state => p.a * pa SynthV.state + p.u + e.eps
    | SynthV.obs   => pa SynthV.state + (1 / 10) * e.w

/-- **图**：`state` 自指（自回归），`obs` 以 `state` 为父。 -/
def synthGraph : Graph SynthV where
  pa := fun v =>
    match v with
    | SynthV.state => [SynthV.state]
    | SynthV.obs   => [SynthV.state]

/-- **合成模型**：`SCM.Model` 的一个具体实例，四参数全部落实
  （`Val = Real`、`V = SynthV`、`E = SynthE`、`Noise = DiscLaw SynthE`）。 -/
def synthModel : Model Real SynthV SynthE (DiscLaw SynthE) where
  F     := synthF synthParams
  P_U   := synthLaw
  graph := some synthGraph

/-- 合成模型**有图**（于是 `Model/Dynamics.eval` 可用）。 -/
theorem synthModel_hasGraph : synthModel.HasGraph := rfl

/-! ### §3.1 方程被真的算过

  只写 `def` 不算「跑通」——下面把**具体**输入代进方程，算出**具体**结果。
  这是端到端链上「建模 → 模型」这一步的落地证据。 -/

/-- 状态方程对**任意**参数与输入的展开式（`rfl`：方程的定义式本身）。 -/
theorem synth_state_eq (a u x eps : Real) :
    synthF { a := a, u := u } SynthV.state (fun _ => x) { eps := eps, w := 0 }
      = a * x + u + eps := rfl

/-- 状态方程在 `x = 1`、`eps = 1/4` 处取 `43/20`。

  **超出定义之处**：定义里 `p.a * pa SynthV.state + p.u + e.eps` 是个**代数式**；
  本定理把它在 `a = 9/10, u = 1, x = 1, eps = 1/4` 处**算成一个数**。
  这是「定义 → 数值」的跨出（`rfl` 只给出同一个式子）。

  ⚠ 结果写成 `43/20` 而**不是** `5/4`：`43/20 = 2.15`，`5/4 = 1.25`，
  两者**不相等**——所以 `5/4` 那个写法根本不是"工具坑"，是**算错了**。
  `9/10 * 1 + 1 + 1/4 = 9/10 + 5/4 = 18/20 + 25/20 = 43/20`。 -/
theorem synth_state_at_one :
    synthModel.F SynthV.state (fun _ : SynthV => (1 : Real)) { eps := 1 / 4, w := 1 }
      = 43 / 20 := by
  show ((9 : Real) / 10) * 1 + 1 + 1 / 4 = 43 / 20
  norm_num

/-- 观测方程在 `x = 1`、`w = 1` 处取 `11/10`。 -/
theorem synth_obs_at_one :
    synthModel.F SynthV.obs (fun _ : SynthV => (1 : Real)) { eps := 1 / 4, w := 1 }
      = 11 / 10 := by
  show (1 : Real) + (1 / 10) * 1 = 11 / 10
  norm_num

/-- **观测节点只看 `state`**：父赋值只在 `state` 上相同时，`obs` 的方程输出不变。

  **超出定义之处**：这条说的是「`obs` 的方程**不依赖**同层的 `obs`」，
  也就是图 `pa obs = [state]` 与方程是**相容**的。
  定义里方程与图分开写，没有把这条相容性写进去——
  任何真的按拓扑序求值的实现对「方程读了未声明的父节点」都会出错。 -/
theorem synth_obs_ignores_own_pa (pa pa' : SynthV → Real) (e : SynthE)
    (h : pa SynthV.state = pa' SynthV.state) :
    synthModel.F SynthV.obs pa e = synthModel.F SynthV.obs pa' e := by
  show pa SynthV.state + (1 / 10) * e.w = pa' SynthV.state + (1 / 10) * e.w
  rw [h]

end

end FateV2.Modeling
