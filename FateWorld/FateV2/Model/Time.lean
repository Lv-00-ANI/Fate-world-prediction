import FateWorld.FateV2.Model.State

/-!
  # Model · Time —— 时间分层（当前点 + 机制）

  ## 迁移登记
  - 来源：新写
  - 动作：C 重写
  - 对应环节：F2-01（转移方程）、F2-12（随机转移核）
  - 依赖裁决：**D-023 D2**（作者答复：「时间**暂时分层**」「当前点 + 机制」分层；
              `Entity × Time` 方案暂不用）
  - 改动：原文件空骨架。
  - 状态：已验证

  ## 时间分层的准确含义（D2 的落点）

  两种写法：

  | 写法 | 形状 | 问题 |
  |---|---|---|
  | ❌ `Entity × Time` | 状态里存 `(实体, 时刻)` 对 | 时刻被塞进**状态**，于是「同一实体两个时刻」是两个不同状态，轨迹不再是函数 |
  | ✅ **分层**（本文件） | `Now`（当前点）+ `Mechanism`（机制/动力学） | 时刻只在**索引**里出现；状态与机制各自是一层，演化 = 两层的联合更新 |

  于是「轨迹」= `Nat → State`（索引是时刻），而**机制**不是状态的一部分，
  它是把 `State → State` 的映射。这样：

  * 机制可以**不随**状态改变（`Mechanism` 与 `State` 解耦）——D-013 的「一体化」
  * 回写（`Loop/WriteBack`）改的是**机制**，不是当前点——这正是「闭环」的语义

  ## 超出定义之处
  * `Trajectory.step_succ`：轨迹的第 `n+1` 步恰是第 `n` 步经机制演化一步
    （定义 `step` 用的是 `n+1` 的递归式；本定理把它写成 `Nat.succ` 形式，
    使下游可以按「一步」推理而不是按递归式推理）。
  * `Trajectory.step_zero`：零点不被机制触碰。
-/

namespace FateV2.Model

universe u

/-! ===========================================================================
  §1  两层
  =========================================================================== -/

/-- **时间索引**：本批取离散时间（`Nat`）。

  D2：「暂时分层」⟹ 时间**只**出现在索引里，不进入状态。
  连续时间 / 事件时间将来另给实例，不改变本文件的结论。 -/
abbrev Time : Type := Nat

/-- **机制层**：把当前点送到下一当前点。

  注意它**不吃时刻**——机制本身是时间齐次的（时变机制由 `Mechanism` 的
  取值为函数族来表达，那是 D-019 允许的实例，不改结构）。 -/
abbrev Mechanism (Val : Type u) (V : Type u) : Type u :=
  WholeState Val V → WholeState Val V

/-- **两层的时间片**：当前点 + 机制。 -/
structure Slice (Val : Type u) (V : Type u) where
  /-- 当前点（内生赋值） -/
  now : WholeState Val V
  /-- 机制（动力学） -/
  mech : Mechanism Val V

/-- **轨迹**：时刻 → 当前点。

  「机制」不进轨迹——它是轨迹的**生成规则**。 -/
abbrev Trajectory (Val : Type u) (V : Type u) : Type u := Time → WholeState Val V

/-- **按机制生成轨迹**：`tr 0 = s₀`，`tr (n+1) = mech (tr n)`。 -/
def Trajectory.step (mech : Mechanism Val V) (s₀ : WholeState Val V) :
    Trajectory Val V
  | 0 => s₀
  | n + 1 => mech (Trajectory.step mech s₀ n)

/-! ===========================================================================
  §2  轨迹的基本事实
  =========================================================================== -/

/-- **零点不被机制触碰**：`tr 0 = s₀`。 -/
theorem Trajectory.step_zero {Val V : Type u} (mech : Mechanism Val V)
    (s₀ : WholeState Val V) : Trajectory.step mech s₀ 0 = s₀ := rfl

/-- **后一步恰是一步演化**。

  **超出定义之处**：`Trajectory.step` 的定义是**递归式**（`n + 1` 分支里再递归）；
  这条定理把 `n+1` 的形态固定成「`n` 的结果再过一次 `mech`」，
  使下游可以按「一步」而不是按递归式推理（`Nat.succ` 与 `n + 1` 的
  书写形式在本工具链下并不总自动统一）。 -/
theorem Trajectory.step_succ {Val V : Type u} (mech : Mechanism Val V)
    (s₀ : WholeState Val V) (n : Time) :
    Trajectory.step mech s₀ n.succ = mech (Trajectory.step mech s₀ n) := by
  cases n with
  | zero => rfl
  | succ k => rfl

/-- **两层的时间片走一步**：机制作用于当前点。 -/
def Slice.tick {Val V : Type u} (sl : Slice Val V) : Slice Val V where
  now := sl.mech sl.now
  mech := sl.mech

/-- 走一步之后，**机制不变**。

  **超出定义之处**：这是「时间分层」的核心副产品——
  `Slice.tick` 的定义里 `mech := sl.mech` 只是搬运；本定理把它读成
  「演化**只**动当前点，不动机制」，于是「机制由回写单独修改」
  （`Loop/WriteBack`）与「状态由演化推进」是**两条正交的作用通道**。
  没有这条，回写的语义会和演化缠在一起。 -/
theorem Slice.tick_mech {Val V : Type u} (sl : Slice Val V) :
    sl.tick.mech = sl.mech := rfl

/-- 走一步之后，当前点恰是机制作用的结果。 -/
theorem Slice.tick_now {Val V : Type u} (sl : Slice Val V) :
    sl.tick.now = sl.mech sl.now := rfl

/-- **连走 `n` 步** 的时间片序列（按索引递归，不按结构递归）。 -/
def Slice.iter {Val V : Type u} (sl : Slice Val V) : Time → Slice Val V
  | 0 => sl
  | n + 1 => (Slice.iter sl n).tick

/-- `Slice.iter` 的 `n+1` 步展开。

  **超出定义之处**：定义按索引递归，`n+1` 分支写的是 `(iter n).tick`；
  本定理把它固定成可重写的形式（避免下游被 `Nat.rec` 的原始形态卡住）。 -/
theorem Slice.iter_succ {Val V : Type u} (sl : Slice Val V) (n : Time) :
    Slice.iter sl (n + 1) = (Slice.iter sl n).tick := rfl

/-- **连走 `n` 步之后机制不变**（「机制与状态正交」的迭代版）。

  **超出定义之处**：`Slice.iter` 只递归 `tick`，定义里没有把「机制不变」
  单列；本定理把它抽出来单独可用——下游（回写层）需要它把
  「演化」与「机制修改」两条通道分开推理。 -/
theorem Slice.iter_mech {Val V : Type u} (sl : Slice Val V) :
    ∀ n : Time, (Slice.iter sl n).mech = sl.mech
  | 0 => rfl
  | n + 1 => by
    show (Slice.iter sl n).tick.mech = sl.mech
    rw [Slice.tick_mech, Slice.iter_mech sl n]

/-- **连走 `n` 步的当前点 = `Trajectory.step mech s₀ n`**。

  **超出定义之处**：`Slice.tick`/`Slice.iter` 与 `Trajectory.step` 是
  **两套独立的索引递归**，定义本身不说它们一致；
  本定理把它们接起来——于是「按时间片推进」与「按轨迹索引推进」
  是同一件事，下游可以任选一侧推理。 -/
theorem Slice.iter_now {Val V : Type u} (sl : Slice Val V) :
    ∀ n : Time, (Slice.iter sl n).now = Trajectory.step sl.mech sl.now n
  | 0 => rfl
  | n + 1 => by
    have hmech : (Slice.iter sl n).mech = sl.mech := Slice.iter_mech sl n
    show (Slice.iter sl n).tick.now = sl.mech (Trajectory.step sl.mech sl.now n)
    rw [Slice.tick_now, hmech, Slice.iter_now sl n]

end FateV2.Model
