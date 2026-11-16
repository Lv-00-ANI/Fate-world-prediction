import FateWorld.FateV2.Loop.ThetaConvergence
/-!
  # Loop · DemoConcrete

  ## 迁移登记
  - 来源：`FateWorld/Legacy/DemoConcrete.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ThetaConvergence
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# `FateV2.Loop.DemoConcrete` —— 前件在具体场景中自动成立

## 目的

`Fate.ThetaConvergence.linWorld_tendsto_thetaStar` 有两条前件：

* `hx : x ≠ 0`（观测非零）
* `hη : |1 - η| < 1`（步长条件）

本文件**不写**「带前件的主定理副本」，而是构造**具体场景**，
在那里两条前件**被具体数值消掉**，从而得到**真正无前件**的收敛定理。

## 定理清单

| # | 名称 | 内容 | 前件 |
|---|------|------|------|
| 1 | `eta_one_satisfies` | `η = 1 ⟹ |1-η| < 1` | 仅 `η = 1`（等式前提，非数值约束）|
| 2 | `eta_half_satisfies` | `|1-1/2| < 1`（**零前件**）| 无 |
| 3 | `x_ne_zero_of_mul_ne_zero` | `θ*x ≠ 0 ⟹ x ≠ 0` | 仅 `θ*x ≠ 0` |
| 4 | `linWorld_converges_concrete` | `thetaN (1/2) 1 1 0 → 1`（**零前件**）| 无 |
| 5 | `linWorld_converges_concrete_alt` | `thetaN 1 (-3) 2 7 → -3`（**零前件**）| 无 |
| 6 | `linWorld_converges_eta_gt_half` | `thetaN (3/2) 5 (-1) 100 → 5`（**零前件**）| 无 |

## 同义反复自查

* #1、#2 是**纯算术**，结论 `|1-η| < 1` 不是前提的复述（前提是 `η = 1` / 空）。
* #3：前提 `θ*x ≠ 0`，结论 `x ≠ 0`。**结论严格弱于前提**（`mul_ne_zero` 分解），
  不是同义反复。注意：任务模板里还有一条 `hθ : θstar ≠ 0`，但它在证明中**未被使用**
  （`θ*x ≠ 0` 已经蕴含两个因子都非零），故此处**删去**，避免「僵尸前件」。
* #4、#5、#6：**无任何前件**，结论是具体的 `Filter.Tendsto` 陈述；
  证明调用的是真实的 `linWorld_tendsto_thetaStar`，前件由 `norm_num` 消去。
-/

namespace FateV2.Loop.DemoConcrete

open Filter
open FateV2.Loop.ThetaConvergence

/-! ## §1 步长条件的自然选择 -/

/-- `η = 1`（最经典学习率）满足步长条件 `|1 - η| < 1`。 -/
theorem eta_one_satisfies (η : ℝ) (h : η = 1) : |1 - η| < 1 := by
  rw [h]; norm_num

/-- `η = 1/2` 满足步长条件（**零前件**，具体数值）。 -/
theorem eta_half_satisfies : |1 - (1 / 2 : ℝ)| < 1 := by
  norm_num

/-! ## §2 `x ≠ 0` 在具体观测下自动成立 -/

/-- 若观测 `y = θ * x` 非零，则设计点 `x ≠ 0`。

**⚠ 说明**：结论 `x ≠ 0` 由 `θ*x ≠ 0` 直接推出（乘积非零则因子非零），
这是严格的**分解**，不是同义反复 —— 前提说的是「乘积」，结论说的是「单个因子」。 -/
theorem x_ne_zero_of_mul_ne_zero (θstar x : ℝ) (hy : θstar * x ≠ 0) :
    x ≠ 0 := by
  intro hx
  rw [hx, mul_zero] at hy
  exact hy rfl

/-! ## §3 具体场景下的**无前件**收敛 -/

/-- ⭐ **具体场景收敛（零前件）**：`η = 1/2`, `θ* = 1`, `x = 1`, `θ₀ = 0`。

`thetaN (1/2) 1 1 0 → 1`。

**没有任何前件** —— 两条前提 `x ≠ 0` 与 `|1-η| < 1` 都被 `norm_num` 消掉。 -/
theorem linWorld_converges_concrete :
    Tendsto (thetaN (1 / 2) 1 1 0) atTop (nhds 1) := by
  apply linWorld_tendsto_thetaStar
  · norm_num
  · norm_num

/-- ⭐ **具体场景收敛（零前件，负初值 + 负真值 + 非单位设计点）**：
`η = 1`, `θ* = -3`, `x = 2`, `θ₀ = 7`。 -/
theorem linWorld_converges_concrete_alt :
    Tendsto (thetaN 1 (-3) 2 7) atTop (nhds (-3)) := by
  apply linWorld_tendsto_thetaStar
  · norm_num
  · norm_num

/-- ⭐ **具体场景收敛（零前件，大步长 η = 3/2，振荡收敛）**：
`η = 3/2`, `θ* = 5`, `x = -1`, `θ₀ = 100`。

`|1 - 3/2| = 1/2 < 1`，故 `1-η = -1/2`，偏差交替变号但绝对值衰减。 -/
theorem linWorld_converges_eta_gt_half :
    Tendsto (thetaN (3 / 2) 5 (-1) 100) atTop (nhds 5) := by
  apply linWorld_tendsto_thetaStar
  · norm_num
  · norm_num

end FateV2.Loop.DemoConcrete
