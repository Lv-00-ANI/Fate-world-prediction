import FateWorld.FateV2.Loop.EndToEndPipelineBridge
import FateWorld.FateV2.Loop.PipelineTendstoGen
/-!
  # Loop · EndToEndConvergence

  ## 迁移登记
  - 来源：`FateWorld/Legacy/EndToEndConvergence.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：EndToEndPipelineBridge, PipelineTendstoGen
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# 端到端迭代的收敛（`EndToEndConvergence`）

## 本模块证明什么

`Fate/EndToEndPipelineBridge.lean` 已把 `EndToEnd.endToEndIter`（含
`observe`／`predFrom`／减法／`writeBack` 四环节的端到端链）与
`PipelineTendstoGen.pipelineNGen` 在 `linWorld` 上**逐点**接上：

```
linWorld_endToEndIter_eq_pipelineNGen :
  endToEndIter linWorld … n θ₀ = pipelineNGen η θstar θ₀ n
```

`Fate/PipelineTendstoGen.lean` 又独立给出 `pipelineNGen η θstar θ₀ n → θstar`。
本模块把两者**复合**，得到本项目的**第一条「端到端收敛」定理**：

1. `linWorld_endToEndIter_tendsto` —— `endToEndIter … n θ₀ → θstar`（`nhds θstar`）。
2. `linWorld_endToEndIter_deviation_tendsto_zero` —— 偏差 `θₙ - θ* → 0`。
3. `linWorld_endToEndIter_error_band` —— 任意 `ε > 0` 有 `ε`-`N` 误差带。

## 诚实边界（必读）

- **只在 `linWorld` 上**：一般 `W` 的 `endToEnd` 一步对 `θ` 不是 ℝ-仿射的
  （见 `EndToEndPipelineBridge` 的诚实边界），故等价与收敛只在 `linWorld` 上成立。
- **非循环**：前件只有 `x ≠ 0` 与步长条件 `|1 - η| < 1`（关于 `η`、`x` 的代数条件），
  结论是 `Tendsto` 语句。前件**不含**任何 `Tendsto`／极限形式。
- 零 `sorry` / 零 `admit` / 零 `axiom` / 零 `?_`。
-/

namespace FateV2.Loop

open FateV2.Modeling
namespace EndToEndConvergence

open FateV2.Loop.EndToEnd
open FateV2.Loop.ThetaConvergence
open FateV2.Loop.EndToEndPipelineBridge
open PipelineTendstoGen
open Filter
open scoped Topology

/-! ===========================================================================
  §1  ⭐⭐⭐ 端到端迭代收敛（核心）
  =========================================================================== -/

/-- ⭐⭐⭐ **【端到端迭代收敛】**

左端是 `EndToEnd.endToEndIter`（端到端链：观测 → 预测 → 残差 → 写回，迭代 `n` 步），
右端是 `nhds θstar`。

**证明**：把函数列换成 `pipelineNGen η θstar θ₀`（由
`EndToEndPipelineBridge.linWorld_endToEndIter_eq_pipelineNGen` 逐点相等），
再用 `PipelineTendstoGen.pipeline_tendsto_gen`（在 `V := ℝ` 上，
`ℕ`-幂 `(1-η)^n → 0` 给出极限）。

**⚠ 非循环**：前件为 `x ≠ 0` 与 `|1 - η| < 1`（代数条件），
结论为 `Tendsto … (nhds θstar)`；前件没有把结论包进去。 -/
theorem linWorld_endToEndIter_tendsto (η θstar x θ₀ : ℝ)
    (hx : x ≠ 0) (hη : |1 - η| < 1) :
    Tendsto
      (fun n => endToEndIter linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
      atTop (nhds θstar) := by
  have hfuneq :
      (fun n => endToEndIter linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
      = (fun n => pipelineNGen η θstar θ₀ n) := by
    funext n
    exact linWorld_endToEndIter_eq_pipelineNGen η θstar x θ₀ hx n
  rw [hfuneq]
  exact pipeline_tendsto_gen η θstar x θ₀ hx hη

/-! ===========================================================================
  §2  ⭐⭐ 推论：偏差趋于 0
  =========================================================================== -/

/-- ⭐⭐ **【偏差趋于 0】** 端到端迭代值与 `θstar` 的偏差趋于 `0`。

由 §1 与 `Tendsto.sub_const` 直接得到。 -/
theorem linWorld_endToEndIter_deviation_tendsto_zero (η θstar x θ₀ : ℝ)
    (hx : x ≠ 0) (hη : |1 - η| < 1) :
    Tendsto
      (fun n => endToEndIter linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀ - θstar)
      atTop (nhds 0) := by
  have h := linWorld_endToEndIter_tendsto η θstar x θ₀ hx hη
  have h2 : Tendsto
      (fun n => endToEndIter linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀ - θstar)
      atTop (nhds (θstar - θstar)) :=
    h.sub_const θstar
  simpa using h2

/-! ===========================================================================
  §3  ⭐⭐ 误差带（ε-N 形式）
  =========================================================================== -/

/-- ⭐⭐ **【误差带】** 对任意 `ε > 0`，存在 `N`，使所有 `n ≥ N` 时
端到端迭代值与 `θstar` 的距离 `< ε`。

证明：由 §1 的 `Tendsto` 与 `Metric.tendsto_atTop`（`ℝ` 上的 `nhds = 𝓝` 由距离给出）。 -/
theorem linWorld_endToEndIter_error_band (η θstar x θ₀ : ℝ)
    (hx : x ≠ 0) (hη : |1 - η| < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      |endToEndIter linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀ - θstar| < ε := by
  have h := linWorld_endToEndIter_tendsto η θstar x θ₀ hx hη
  have hd := linWorld_endToEndIter_deviation_tendsto_zero η θstar x θ₀ hx hη
  rw [Metric.tendsto_atTop] at hd
  obtain ⟨N, hN⟩ := hd ε hε
  exact ⟨N, fun n hn => by
    have := hN n hn
    simpa [Real.dist_eq] using this⟩

end EndToEndConvergence
end FateV2.Loop