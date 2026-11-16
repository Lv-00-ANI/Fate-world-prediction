/-
命运理论 · `#eval` 数值预测演示（世界模型最小实例）
=====================================================

模块：`EvalDemo`
上游：`Fate.WorldModel`（`WorldModel`, `WorldModel.sim`, `WorldModel.sim_zero`,
　　　`WorldModel.sim_succ`, `WorldModel.x`, `WorldModel.f`）、
　　　`Fate.TrajGenDeterministic`（`trajGen`）。

---------------------------------------------------------------------------
⚠ 本文件的修复记录（P0 修复批次，如实说明）
---------------------------------------------------------------------------
本文件原 `import Fate.WorldModelMinimal`，但该模块**已被移出 `Fate/`**
（现存于 `_quarantine/WorldModelMinimal.lean`，且其 `zWorldModel_sim_two`
一条定理本身编译不过），故 `.lake/build/lib/lean/Fate/WorldModelMinimal.olean`
不存在，导致本文件报唯一错误
`object file ... of module Fate.WorldModelMinimal does not exist`。

**修复方式（只改 import 与证明，不改任何定理陈述）**：
本文件**不再**依赖那个被隔离的模块，而是**在文件内**用可用模块
（`Fate.WorldModel` / `Fate.TrajGenDeterministic`）**重建**同一个最小实例
（状态空间 `Bool`、参数/输入/动作/噪声均为单点 `PUnit`、机制 `!x`、初值 `false`）。
重建所用的每个定义与 `_quarantine/WorldModelMinimal.lean` 的对应定义**逐字同构**
（`minFrame`、`stepFlip`、`minimalWorldModel`），故本文件所证的数值与语义
与原设计**完全一致**。§3 的 `evalTraj_eq_sim` 等定理陈述**一字未改**。

---------------------------------------------------------------------------
本文件做什么（一句话）
---------------------------------------------------------------------------
用最小实例，**真正跑一次 `#eval`**：输入一个状态，算出下一步状态，**打印结果**，
并**证明** `#eval` 算出的数值与理论上算的**完全一致**（`rfl` / `decide` / 归纳）。

---------------------------------------------------------------------------
为什么 `#eval` 不能直接作用在 `minimalWorldModel.sim` 上（诚实标注）
---------------------------------------------------------------------------
`minimalWorldModel` 的 `Rule` 块含 `Measure`（`MeasureTheory.Measure.dirac`），
故 `minimalWorldModel` 是 `noncomputable`，`#eval` 直接对其求值会报
`depends on 'minimalWorldModel', which is 'noncomputable'`。

**解决办法（不引入任何 `sorry`／`axiom`）**：
`WorldModel.sim` 的定义就是
`TrajGenDeterministic.trajGen W.frame W.simulator.step θ W.x u ε a`，
而 `trajGen` 本身**是构造性的（`Nat.rec`，可计算）**。
故我们直接对**可计算的** `trajGen` 求值——`trajGen minFrame stepFlip PUnit.unit false u ε a`，
并**证明**它 `= minimalWorldModel.sim ...`（本文件 `evalTraj_eq_sim`，`rfl` 级）。
于是「`#eval` 打印的数」与「世界模型语义的数」是**同一个数**，不是两套算法。

---------------------------------------------------------------------------
零 `sorry` / 零 `admit` / 零 `axiom`（自检）
---------------------------------------------------------------------------
本文件所有 `#eval` 皆为具体的计算指令；所有定理皆为已证：
`rfl`、`decide`、及对 `TrajGenDeterministic.trajGen` 的归纳。无占位、无新增假设。
-/

import FateWorld.FateV2.Predict.WorldModel
import FateWorld.FateV2.Model.TrajGenDeterministic
namespace FateV2.Loop

open FateV2.Model
open FateV2.Modeling
open FateV2.Predict
namespace EvalDemo

noncomputable section

/-!
  # Loop · EvalDemo

  ## 迁移登记
  - 来源：`FateWorld/Legacy/EvalDemo.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：WorldModel, TrajGenDeterministic
  - 补充 open 域：FateV2.Model, FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §0  最小实例的重建（逐字同构于 `_quarantine/WorldModelMinimal.lean`）

    说明：这些定义与 `WorldModelMinimal` 的同名定义**同构**，
    此处重建只为消除对**已被隔离模块**的依赖；不修改任何已有模块。
    =========================================================================== -/

/-- 最小状态空间：`Bool`（两态），离散拓扑 / 离散可测。 -/
def minX : StateSpace where
  Carrier := Bool
  topo := ⊤
  meas := ⊤
  borel_le := le_top

/-- 最小参数空间：单点 `PUnit`。 -/
def minΘ : ThetaSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 最小外生输入空间：单点。 -/
def minU : InputSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 最小动作空间：单点。 -/
def minAct : ActionSpace where
  Carrier := PUnit
  topo := ⊤
  meas := ⊤

/-- 最小噪声空间：单点。 -/
def minN : NoiseSpace where
  Carrier := PUnit
  meas := ⊤

/-- 最小上下文空间。 -/
def minC : CtxSpace where
  Carrier := PUnit

/-- **最小四元框架**。 -/
def minFrame : Frame where
  Θ := minΘ
  X := minX
  U := minU
  Act := minAct
  Ν := minN

attribute [local instance] StateSpace.topo StateSpace.meas ThetaSpace.topo
  ThetaSpace.meas InputSpace.topo InputSpace.meas ActionSpace.topo
  ActionSpace.meas NoiseSpace.meas

/-- 规则 **R**：核为点质量 `δ_x`。 -/
def ruleStay : Rule minC minX minX where
  kernel := fun _c x => MeasureTheory.Measure.dirac x

/-- **最小规则集** `𝓡 = {R}`。 -/
def minRules : Rules minC minX minX := {ruleStay}

/-- 最小规则集**非空**。 -/
theorem minRules_nonempty : minRules.Nonempty :=
  ⟨ruleStay, Set.mem_singleton ruleStay⟩

/-- **规则集块**。 -/
def minWorldRules : WorldRules minC minX minX where
  rules := minRules
  nonempty := minRules_nonempty

/-- **最小机制 `f`（翻转）**。 -/
def stepFlip : Step minFrame :=
  fun x _u _ε _θ _a => !x

/-- **模拟器块**：机制 `stepFlip`，窗口 `Tmax = 2` 步。 -/
def minSimulator : WorldSimulator minFrame where
  step := stepFlip
  horizon := 2

/-- **最小选择器**：`select` 恒返回首条规则 `R`，评值 `0`。 -/
def minSelector : Selector minC minX minX where
  select := fun _R _c _x => (ruleStay, 0)
  criterion := fun _c _x _R => 0

/-- **最小世界模型**：四部分齐备、状态空间对齐。 -/
def minimalWorldModel : WorldModel where
  frame := minFrame
  ctx := minC
  instX := ⊤
  state := { space := minX, cur := false, initial := { val := false, isRandom := false } }
  rules := minWorldRules
  simulator := minSimulator
  selector := minSelector
  state_consistent := rfl

/-! ===========================================================================
    §1  可计算轨迹：把 `minimalWorldModel.sim` 的四部分用**具体值**喂进去
    =========================================================================== -/

/-- 最小实例的**可计算轨迹**：起点 `x₀ = false`（= `minimalWorldModel.x`），
机制 `stepFlip`（= `minimalWorldModel.f`），参数/动作固定为单点 `PUnit.unit`，
噪声/外生输入取常值 `PUnit.unit`。

**这就是 `#eval` 的对象**——它是 `trajGen` 的直接实例化，`Nat.rec` 定义，**可计算**。 -/
def evalTraj (n : ℕ) : Bool :=
  TrajGenDeterministic.trajGen minFrame stepFlip PUnit.unit false
    (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => PUnit.unit) n

/-- 单步**下一状态**函数（可计算模型）：`next b = !b`（机制 `stepFlip` 的裸读法）。 -/
def nextState (b : Bool) : Bool := !b

/-! ===========================================================================
    §2  `#eval`：真正的数值预测（打印结果）
    =========================================================================== -/

/-! **`#eval` 一：从状态 `false` 出发的轨迹前 5 步（打印真值）。**

预期：`false, true, false, true, false`（奇偶翻转）。 -/
#eval evalTraj 0
#eval evalTraj 1
#eval evalTraj 2
#eval evalTraj 3
#eval evalTraj 4

/-! **`#eval` 二：单步「下一状态」预测（输入状态 → 下一步状态）。** -/
#eval nextState false
#eval nextState true

/-! **`#eval` 三：最小的 `Traj` 读法（前 5 步一次性打印成表）。** -/
#eval (List.map evalTraj [0, 1, 2, 3, 4])

/-! ===========================================================================
    §3  证明：`#eval` 的结果与理论一致
    =========================================================================== -/

/-- ⭐ **可计算轨迹 = 世界模型语义的轨迹**（`rfl` 级等式）。

`WorldModel.sim` 的定义正是 `trajGen W.frame W.simulator.step θ W.x u ε a`；
对 `minimalWorldModel`，`W.frame = minFrame`、`W.simulator.step = stepFlip`、
`W.x = false`（均为定义性，`state_consistent := rfl`），故两端**定义相等**。

于是「`#eval evalTraj n` 打印的数」与「`minimalWorldModel.sim` 语义的数」
是**同一个项**——这就是「`#eval` 结果与理论一致」的**最强制形式**。 -/
theorem evalTraj_eq_sim (n : ℕ) :
    evalTraj n
      = minimalWorldModel.sim PUnit.unit (fun _ => PUnit.unit)
          (fun _ => PUnit.unit) (fun _ => PUnit.unit) n :=
  rfl

/-- ⭐ **`#eval` 打印的首步 = 理论值**：`evalTraj 0 = false`（与 `#eval` 第一行一致）。 -/
theorem evalTraj_zero : evalTraj 0 = false := rfl

/-- ⭐ **`#eval` 打印的第 1 步 = 理论值**：`evalTraj 1 = true`。 -/
theorem evalTraj_one : evalTraj 1 = true := rfl

/-- ⭐ **`#eval` 打印的第 2 步 = 理论值**：`evalTraj 2 = false`。 -/
theorem evalTraj_two : evalTraj 2 = false := rfl

/-- **`decide` 版本的一致性证据**：`evalTraj 3` 与 `true` 可判定相等。 -/
theorem evalTraj_three_decide : evalTraj 3 = true := by decide

/-- **`decide` 版本**：`evalTraj 4 = false`。 -/
theorem evalTraj_four_decide : evalTraj 4 = false := by decide

/-! ### §3.1  全称形式：对**一切** `n`，可计算轨迹的闭式（奇偶翻转）

`trajGen` 递推为 `x₀ = false`、`x_{n+1} = !x_n`。
故**全称**：`n` 为偶数时 `false`、`n` 为奇数时 `true`。
这比「逐步 `#eval`」更强——它覆盖整个窗口，不只前 5 步。 -/

/-- 辅助引理：`evalTraj` 的递推式（`trajGen` 的 `succ` 读法，`rfl`）。 -/
theorem evalTraj_succ (n : ℕ) : evalTraj (n + 1) = !evalTraj n := rfl

/-- ⭐⭐ **全称闭式（值的）**：一切 `n`，`evalTraj n` 恰为「`n` 为奇数」
（`decide (n % 2 = 1)`）。

这覆盖了 `#eval` 所验的有限步，并把结论**推广到全窗口**（四层标准之「最优性全称」）。
证明：对 `n` 归纳，用递推 `evalTraj (n+1) = !evalTraj n` 与 `n % 2` 的奇偶律（`omega`）。 -/
theorem evalTraj_eq_decide_odd (n : ℕ) : evalTraj n = decide (n % 2 = 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [evalTraj_succ, ih]
    by_cases hk : k % 2 = 0
    · have h1 : ¬ (k % 2 = 1) := by omega
      have h2 : (k + 1) % 2 = 1 := by omega
      rw [decide_eq_false h1, decide_eq_true h2]; rfl
    · have h1 : k % 2 = 1 := by omega
      have h2 : ¬ (k + 1) % 2 = 1 := by omega
      rw [decide_eq_true h1, decide_eq_false h2]; rfl

/-- ⭐⭐ **全称闭式（等，布尔读法）**：一切 `n`，`evalTraj n = true ↔ n` 为奇数。

由 `evalTraj_eq_decide_odd` 直接得到。 -/
theorem evalTraj_true_iff (n : ℕ) : evalTraj n = true ↔ n % 2 = 1 := by
  rw [evalTraj_eq_decide_odd]
  exact decide_eq_true_iff

/-! ===========================================================================
    §4  单步「下一状态」= 机制 `f` 的投影（`rfl`）
    =========================================================================== -/

/-- ⭐ **单步预测一致**：`nextState b` 恰是 `minimalWorldModel` 的机制 `f` 作用在 `b` 上。 -/
theorem nextState_eq_f (b : Bool) :
    nextState b = minimalWorldModel.f b PUnit.unit PUnit.unit PUnit.unit PUnit.unit :=
  rfl

/-- ⭐ **世界模型的「下一步状态」投影 = 可计算下一状态**：
从当前状态 `minimalWorldModel.x = false` 出发，一步后为 `true`。 -/
theorem next_of_x : nextState minimalWorldModel.x = true := rfl

/-- **`#eval` 打印的轨迹前两步**被一条定理完全钉住：`evalTraj 0 = false ∧ evalTraj 1 = true`。 -/
theorem evalTraj_first_two : evalTraj 0 = false ∧ evalTraj 1 = true :=
  ⟨evalTraj_zero, evalTraj_one⟩

end

end EvalDemo
end FateV2.Loop