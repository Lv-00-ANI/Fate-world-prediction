/-
  ============================================================================
  命运理论 · **G3 接入：一般版 `pipelineTendstoGen` 与 ℝ 特化版的一致性**
  ============================================================================

  ## 0  为什么本文件单独存在（⚠ 必读）

  任务 C 要求「在 `WorldModelPipeline` 里**新增**一条定理
  `pipeline_tendsto_gen_specializes`，证明取 `V := ℝ` 回落到原版」。

  **⚠ 直接写进 `Fate/WorldModelPipeline.lean` 会造成循环 import**：
  `Fate/PipelineTendstoGen.lean` 的首行就是 `import Fate.WorldModelPipeline`
  （它需要 `thetaN` / `linWorld` / `pipelineN` 等来陈述「ℝ 回落」）。
  若反过来让 `WorldModelPipeline` import `PipelineTendstoGen`，则
  `WorldModelPipeline → PipelineTendstoGen → WorldModelPipeline` 成环，
  Lean 会加载**陈旧的 `.olean`** 并在其上重编译，产生
  「`pipelinePredict_eq` has already been declared」等一整屏
  `already declared` 错误 —— **即破坏构建**（本项目历史教训之一）。

  **⟹ 本文件的处置**：新建本模块（不修改任何既有文件），
  **在 `Fate.WorldModelPipeline` 命名空间内**声明该定理，
  于是它的**全限定名正是**
  `Fate.WorldModelPipeline.pipeline_tendsto_gen_specializes`
  —— 与「写进 `WorldModelPipeline`」在**名称与语义上完全等价**，
  且依赖方向 `本文件 → PipelineTendstoGen → WorldModelPipeline` 是**无环**的。

  ## 1  本文件做了什么（只有两条定理）

  | 定理 | 内容 |
  |---|---|
  | `pipelineN_eq_pipelineNGen` | ℝ-管线轨迹 `pipelineN … = pipelineNGen …`（`V := ℝ`）|
  | `pipeline_tendsto_gen_specializes` ⭐ | 取 `V := ℝ` 调 `pipelineTendstoGen`，得 `pipeline_tendsto` 的同一陈述 |

  **本文件不重证收敛**：收敛由
  `Fate.PipelineTendstoGen.pipeline_tendsto_gen`（其证明用 `pipelineNGen_closed`
  + `(1-η)^n → 0`）提供；本文件只做「轨迹对齐 + 结论搬运」。

  ## 2  ⚠ 前件是否把结论包进去（纪律 7 自查）

  * `pipelineN_eq_pipelineNGen`：前件 `hx : x ≠ 0`（关于**设计点**的假设），
    结论是**两条不同定义**的轨迹在一切 `n` 上相等。前件**不提**任何轨迹取值。**非同义反复。**
  * `pipeline_tendsto_gen_specializes`：前件 `hx : x ≠ 0` 与 `hη : |1 - η| < 1`
    分别讲**设计点**与**步长**；结论讲「轨迹的极限点 = `θstar`」。前件中**不存在**
    形如 `Tendsto … θstar` 的语句，也不存在关于 `pipelineN` 取值的等式。**非同义反复。**

  纪律：零 `sorry` / 零 `admit` / 零 `axiom`。
  ============================================================================
-/

import FateWorld.Legacy.PipelineTendstoGen

namespace Fate

namespace WorldModelPipeline

open Fate.EndToEnd
open Fate.ThetaConvergence

/-! ===========================================================================
    §1  ⭐⭐⭐ 桥：ℝ-管线轨迹 = 一般版轨迹（`V := ℝ`）
    =========================================================================== -/

/-- ⭐⭐⭐ **【桥：`ℝ`-管线轨迹 = 一般版轨迹（`V := ℝ`）】**

$$\mathrm{pipelineN}\ \mathrm{linWorld}\ \mathrm{id}\ \eta\ \bigl(\tfrac1x\cdot\mathrm{id}\bigr)
    (\theta^* x)\ \dots\ x\ n\ \theta_0
  \;=\; \mathrm{pipelineNGen}\ \eta\ \theta^*\ \theta_0\ n .$$

**⭐ 证明走两条既有结果把两侧归一到同一 `fstep` 迭代**：

1. `PipelineTendstoGen.pipelineNGen_real_eq_fstep`：
   `pipelineNGen η θ* θ₀ n = (fstep η θ*)^[n] θ₀`（一般版在 `V := ℝ` 上就是 `fstep` 迭代）；
2. `ThetaConvergence.thetaN_eq_iterate`：
   `thetaN η θ* x θ₀ n = (fstep η θ*)^[n] θ₀`，而 `pipelineN` 在 `linWorld` 上
   **就是** `thetaN`（`pipelineN_eq_iter` + `thetaN` 的定义，二者均 `rfl` 级）。

故两侧相等。**本定理不涉及任何极限**，只是轨迹的逐点对齐。

**⚠ 不是同义反复**：前件 `hx : x ≠ 0` 是设计点假设，结论断言的是
**两个不同定义**（六环管线 vs 仿射收缩迭代）在**一切 `n`** 上相等；
前件**没有**提到任何一侧的取值。 -/
theorem pipelineN_eq_pipelineNGen (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    pipelineN linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀
      = PipelineTendstoGen.pipelineNGen η θstar θ₀ n := by
  rw [PipelineTendstoGen.pipelineNGen_real_eq_fstep,
    ← Fate.ThetaConvergence.thetaN_eq_iterate η θstar x θ₀ hx n]
  rfl

/-! ===========================================================================
    §2  ⭐⭐⭐⭐ 主结论：一般版取 `V := ℝ` 回落
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【G3 与特化版的一致性】**：一般版主定理取 `V := ℝ` **即回落**。

**陈述**（与 `Fate.WorldModelPipeline.pipeline_tendsto` **逐字同形**）：

$$x \ne 0 \;\wedge\; |1-\eta| < 1 \;\Longrightarrow\;
  \mathrm{Tendsto}\ \bigl(n \mapsto \mathrm{pipelineN}\ \dots\ n\ \theta_0\bigr)
  \ \mathrm{atTop}\ (\mathcal N\ \theta^*) .$$

**⭐ 证明就是「取 `V := ℝ` 调用 `PipelineTendstoGen.pipeline_tendsto_gen`」**：

```lean
exact (PipelineTendstoGen.pipeline_tendsto_gen (V := ℝ) η θstar x θ₀ hx hη).congr
  (fun n => (pipelineN_eq_pipelineNGen η θstar x θ₀ hx n).symm)
```

即：一般版给出 `(n ↦ pipelineNGen η θ* θ₀ n) → θ*`，
本文件的桥把 `pipelineNGen` 换成 `pipelineN` —— 于是得到 `pipeline_tendsto`
所陈述的**同一命题**。**故一般版与本特化版是同一命题的两个形态，而非两个不同命题。**

**⚠ 不是同义反复**：前件 `hx : x ≠ 0`、`hη : |1 - η| < 1` 分别讲**设计点**与
**步长**；结论讲**轨迹的极限点 = `θstar`**。前件中**不存在**任何形如
`Tendsto … θstar` 的语句（也没有关于 `pipelineN` 取值的等式）。
收敛性来自 `PipelineTendstoGen.pipelineNGen_closed`（闭式
`θ_n − θ* = (1−η)^n • (θ₀ − θ*)`）配 `(1−η)^n → 0`，
而 `hη` 仅用于保证该标量幂趋于 0。 -/
theorem pipeline_tendsto_gen_specializes (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hη : |1 - η| < 1) :
    Filter.Tendsto
      (fun n : ℕ => pipelineN linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
      Filter.atTop (nhds θstar) :=
  (PipelineTendstoGen.pipeline_tendsto_gen (V := ℝ) η θstar x θ₀ hx hη).congr
    (fun n => (pipelineN_eq_pipelineNGen η θstar x θ₀ hx n).symm)

/-! ===========================================================================
    §3  ⭐ 自检：上述定理与原版 `pipeline_tendsto` **陈述一致**（可直接互替）
    =========================================================================== -/

/-- **自检 1**：`pipeline_tendsto_gen_specializes` 与既有 `pipeline_tendsto`
给出**同一结论**——本文件的新定理可作为其直接替代（互替检验）。 -/
example (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (hη : |1 - η| < 1) :
    Filter.Tendsto
      (fun n : ℕ => pipelineN linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
      Filter.atTop (nhds θstar) :=
  pipeline_tendsto_gen_specializes η θstar x θ₀ hx hη

/-- **自检 2**：反过来，原版 `pipeline_tendsto` 也满足本文件的结论类型
（两个方向都通过，说明**不是**本文件私自加强了命题）。 -/
example (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (hη : |1 - η| < 1) :
    Filter.Tendsto
      (fun n : ℕ => pipelineN linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
      Filter.atTop (nhds θstar) :=
  pipeline_tendsto η θstar x θ₀ hx hη

/-- **自检 3**：桥的具体数值实例 —— `η = 1/2, θ* = 3, x = 2, θ₀ = 0` 时，
第 `5` 步的 ℝ-管线值 `= 3 - (1/2)^5 · 3`，与一般版一致。 -/
example :
    pipelineN linWorld (id : ℝ → ℝ) (1/2)
        (((1 / (2:ℝ))) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        ((3:ℝ) * 2) PUnit.unit PUnit.unit PUnit.unit (2:ℝ) 5 0
      = PipelineTendstoGen.pipelineNGen (1/2) (3:ℝ) 0 5 :=
  pipelineN_eq_pipelineNGen (1/2) 3 2 0 (by norm_num) 5

end WorldModelPipeline

end Fate
