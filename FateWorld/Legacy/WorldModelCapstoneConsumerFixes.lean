/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.WorldModelCapstoneConsumerFixes`
任务：**【审计 R96 / C8 修复】** 消除 `Fate.WorldModelCapstoneConsumer` 中 C8 的
同义反复，换为**真有信息**的收缩率定理。

---------------------------------------------------------------------------
## 0  被修的是什么（实测）
---------------------------------------------------------------------------
`Fate/WorldModelCapstoneConsumer.lean` 的原 C8
（`capstone_closedLoopWorld_contraction_interface`，:167 附近）结论为

    0 ≤ OptimalEta.c W.η  ∧  OptimalEta.c W.η < 1  ∧  |1 - W.η| = OptimalEta.c W.η

而 `OptimalEta.c η` **按定义**就是 `|1 - η|`（`Fate/OptimalEta.lean:91`：
`def c (η : ℝ) : ℝ := |1 - η|`）。`ClosedLoopWorld` 的字段 `window`
（`Fate/WorldModelCapstone.lean:159`）正是 `|1 - W.η| < 1`。

于是原 C8 的三条结论逐字就是：
* 结论 2 `c W.η < 1` ＝ 前件 `W.window : |1 - W.η| < 1` 经 `rfl` 展开；
* 结论 3 `|1 - W.η| = c W.η` ＝ `rfl`；
* 结论 1 `0 ≤ c W.η` ＝ `abs_nonneg`。

即**前件经定义展开 = 结论**，零信息量，违反作者纪律第 7 条。

⚠ **本文件不修改** `Fate/WorldModelCapstoneConsumer.lean`（纪律 2：不改已有模块）。
原 C8 仍在原文件中；**应由维护者删除**。本文件提供它的**替代**，并在 §4 登记
「原 C8 应删除」。这样修复可被独立验证，同时不触碰任何既有模块。

---------------------------------------------------------------------------
## 1  替代定理：真跨模块的收缩率定理
---------------------------------------------------------------------------
新定理 `capstone_closedLoopWorld_contraction_rate` 把 `ClosedLoopWorld` 的
步长 `W.η` 真正喂进 `ThetaConvergence` 的**学习轨迹** `thetaN`，结论为三合一：

1. **精确 n 步误差界**：`|θ_n - θ*| = c W.η ^ n · |θ₀ - θ*|`；
2. **误差收敛到 0**：`|θ_n - θ*| → 0`（经 `c^n → 0` 乘常数，用
   `tendsto_pow_atTop_nhds_zero_iff`）；
3. **单调界**：`|θ_n - θ*| ≤ |θ₀ - θ*|` 对每步成立。

### 为什么这**不是**同义反复（纪律 7 自查）
* 前件只有 `W : ClosedLoopWorld E F`（字段：`corrects`、`window : |1-W.η|<1`、
  `drift_nonneg`）以及设计点非零 `hx : x ≠ 0`。
* 结论讲的是 **`ThetaConvergence.thetaN W.η …` 这一轨迹对象**——它在
  `ClosedLoopWorld` 的定义里**根本不出现**（`ClosedLoopWorld` 不含任何 `thetaN`）。
* 因此结论不可能是前件的定义展开：需要真正把 `lin_contraction_eq_c`（闭式）
  与 `tendsto_pow_atTop_nhds_zero_iff`（极限）应用上去。
* 已用探针核实（§3）：对 (1)(2) 两条结论，`simp [OptimalEta.c, thetaN]` 与
  `linarith [W.window]` 均**证不出**（会落到 `sorry`），必须走上述数学。
  而原 C8 的 `c W.η < 1` 段落可以 `simpa [OptimalEta.c] using W.window` 直接得到
  ——这就是同义反复与否的**实测分界**。

---------------------------------------------------------------------------
## 2  诚实边界
---------------------------------------------------------------------------
* 本文件**只新增**，**不修改**任何已有模块，**不删除**原 C8（纪律 2）。
  删除原 C8 的动作留给维护者；本文件 §4 明确登记该待办。
* `thetaN` 需 `x ≠ 0`（`ThetaConvergence.thetaN_closed` 的前提），故本定理
  也带 `hx : x ≠ 0`——这是**结构性前件**，不含任何结论。
* 零 `sorry` / 零 `admit` / 零 `axiom`。
* 本文件不跑全量 `lake build`；仅以 `lake env lean` 单文件验证。
-/

import FateWorld.Legacy.WorldModelCapstone
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic

namespace Fate

namespace WorldModelCapstoneConsumerFixes

universe u

open Filter Topology
open scoped Topology

variable {E : Type u} {F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ===========================================================================
    §3  收缩率 `c^n → 0`（真用 `tendsto_pow_atTop_nhds_zero_iff`）
    =========================================================================== -/

/-- ⭐⭐ **`ClosedLoopWorld` 的收缩因子序列 `c(W.η)^n → 0`**。

证明用到 Mathlib 的 `tendsto_pow_atTop_nhds_zero_iff`
（`Tendsto (r^n) → 0 ↔ |r| < 1`），配合 `|c η| = c η`（因 `c η ≥ 0`）
把 `W.window : |1 - W.η| < 1`（即 `c W.η < 1`）转成所需不等式的 `|·|` 形式。

**前件自查**：唯一前件是 `W.window`，结论是**极限等式**（`Tendsto … → 0`），
不是 `W.window` 的逐字复制——`window` 是 `|1-W.η|<1`，结论是序列极限，
需经 `iff` 引理与 `abs_of_nonneg` 才能得到。 -/
theorem closedLoopWorld_c_rate_tendsto_zero
    (W : WorldModelCapstone.ClosedLoopWorld E F) :
    Tendsto (fun n : ℕ => OptimalEta.c W.η ^ n) atTop (nhds 0) := by
  rw [tendsto_pow_atTop_nhds_zero_iff,
    abs_of_nonneg (OptimalEta.c_nonneg W.η)]
  exact W.window

/-! ===========================================================================
    §4  替代 C8：把 `W.η` 喂进学习轨迹，给出误差界与收敛
    =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【替代 C8】`ClosedLoopWorld` 的步长驱动 `ThetaConvergence` 的收敛率**。

设 `W : ClosedLoopWorld E F` 是一个（带收缩窗的）闭环世界，`x ≠ 0` 为设计点。
则对**任意**真值 `θ*` 与初值 `θ₀`，学习轨迹 `θ_n := thetaN W.η θ* x θ₀ n` 满足

1. **精确 n 步误差界** `|θ_n - θ*| = c W.η ^ n · |θ₀ - θ*|`；
2. **误差 → 0**：`|θ_n - θ*| → 0`；
3. **单调界** `|θ_n - θ*| ≤ |θ₀ - θ*|`（每步误差不增大）。

**⭐ 为何非同义反复（纪律 7，逐条）**：
* 前件：`W`（字段 `corrects` / `window : |1-W.η|<1` / `drift_nonneg`）与 `x ≠ 0`。
* 结论：三条都关于 `ThetaConvergence.thetaN W.η …`——这把 `W.η` 送进**另一个
  模块**（`ThetaConvergence`）的迭代，`ClosedLoopWorld` 定义中**无 `thetaN`**。
* 证明分别调用 `WorldModelCapstone.lin_contraction_eq_c`（闭式）、
  `§3` 的 `c^n → 0` 乘常数（取极限）、`pow_le_one₀` + `nlinarith`（单调界）。
  三条都不是 `W.window` 的 `rfl` 展开（§3 探针已实测证不出）。 -/
theorem capstone_closedLoopWorld_contraction_rate
    (W : WorldModelCapstone.ClosedLoopWorld E F)
    (θstar x θ₀ : ℝ) (hx : x ≠ 0) :
    -- (1) 精确 n 步误差界
    (∀ n : ℕ, |ThetaConvergence.thetaN W.η θstar x θ₀ n - θstar|
        = OptimalEta.c W.η ^ n * |θ₀ - θstar|)
    -- (2) 误差收敛到 0
    ∧ Tendsto (fun n : ℕ =>
        |ThetaConvergence.thetaN W.η θstar x θ₀ n - θstar|) atTop (nhds 0)
    -- (3) 单调界：每步误差不超过初误差
    ∧ (∀ n : ℕ, |ThetaConvergence.thetaN W.η θstar x θ₀ n - θstar|
        ≤ |θ₀ - θstar|) := by
  have hbase := closedLoopWorld_c_rate_tendsto_zero W
  refine ⟨?_, ?_, ?_⟩
  · -- (1) 直接由 Capstone 的闭式
    intro n
    exact WorldModelCapstone.lin_contraction_eq_c W.η θstar x θ₀ hx n
  · -- (2) c^n → 0 乘常数 |θ₀-θ*|，再改写回误差
    have h : Tendsto (fun n : ℕ => OptimalEta.c W.η ^ n * |θ₀ - θstar|)
        atTop (nhds (0 * |θ₀ - θstar|)) := hbase.mul_const _
    rw [zero_mul] at h
    refine h.congr (fun n => ?_)
    exact (WorldModelCapstone.lin_contraction_eq_c W.η θstar x θ₀ hx n).symm
  · -- (3) c^n ≤ 1（因 0 ≤ c < 1）乘非负 |θ₀-θ*|
    intro n
    rw [WorldModelCapstone.lin_contraction_eq_c W.η θstar x θ₀ hx n]
    have h2 : OptimalEta.c W.η ^ n ≤ 1 :=
      pow_le_one₀ (OptimalEta.c_nonneg W.η) (le_of_lt W.window)
    have h3 : (0:ℝ) ≤ |θ₀ - θstar| := abs_nonneg _
    nlinarith

/-! ===========================================================================
    §5  维护者待办登记（如实）
    =========================================================================== -/

/-!
### §5.1 应删除的原 C8

`Fate/WorldModelCapstoneConsumer.lean` 中的
`capstone_closedLoopWorld_contraction_interface` 应被删除（或替换为对本章
`capstone_closedLoopWorld_contraction_rate` 的转发）。本文件按纪律 2 未改动它。

其消费关系（`WorldModelCapstone.Consumer` 的 L3 见证）可改为指向本文件的
新定理：本文件 §4 的新定理**签名里出现** `WorldModelCapstone.ClosedLoopWorld`
（真 L3，删掉 Capstone 则签名不合法），且结论**不是**同义反复。

### §5.2 本文件消费的 Capstone 声明（可 grep 核对）

| Capstone 声明 | 用在哪 | 位置 |
|---|---|---|
| `ClosedLoopWorld`（`structure`） | 本章两定理的**参数类型** | 类型签名（L3）|
| `lin_contraction_eq_c` | §4 结论 (1)(2)(3) | 证明体 |
| `ClosedLoopWorld.window`（字段） | §3、§4 | 证明体 |

### §5.3 未做项

* **未**把新定理接进 `Fate.WorldModelCapstoneConsumer` 的其它定理（不改已有模块）。
* **未**处理审计提到的更上游问题（Consumer 自身扇入为 0，即「终点无人使用」）。
  本文件只修 C8 的同义反复这一条，如审计任务范围所述。
-/

end WorldModelCapstoneConsumerFixes

end Fate
