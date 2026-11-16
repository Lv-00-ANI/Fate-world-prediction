import FateWorld.FateV2.Loop.EndToEnd
import FateWorld.FateV2.Loop.PipelineTendstoGen
import FateWorld.FateV2.Loop.ThetaConvergence
/-!
  # Loop · EndToEndPipelineBridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/EndToEndPipelineBridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：EndToEnd, PipelineTendstoGen, ThetaConvergence
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# 端到端迭代与管线迭代的结构等价（`EndToEndPipelineBridge`）

## 本模块证明什么

`Fate/PipelineTendstoGen.lean` §1 的注释原文声称：

> 「结构完全同 `ThetaConvergence.thetaN`（后者 = `endToEndIter`），
>   只是把标量域 `ℝ` 换成任意 `V`。」

本模块把这句话从**注释里的类比**升级为**机器检查的定理**：

1. `endToEndIter_eq_iterate` —— 对**任意** `W`，`endToEndIter` 就是
   端点函数 `fun s => endToEnd … s …` 的 `Function.iterate`。
2. `linStep_eq_gstep` —— 在 `linWorld` 上、`x ≠ 0` 时，一步
   `endToEnd …` 精确等于 `PipelineTendstoGen.gstep η θstar`。
3. `linWorld_endToEndIter_eq_pipelineNGen` —— 由此
   `endToEndIter … n θ₀ = pipelineNGen η θstar θ₀ n`，
   即两条原本完全没连的链**在多步上逐点相等**。
4. `linWorld_pipelineNGen_closed` —— 该等式的推论：偏差按 `(1-η)^n` 缩放，
   把 `PipelineTendstoGen.pipelineNGen_closed` 落到 `endToEndIter` 上。

## 诚实边界（必读）

**只证 `linWorld` 上的重写。** 原因是一般 `W` 上
`endToEnd` 的环节 ② 为 `predFrom W θ u ε a x = W.f x u ε θ a`，
而 `W.f` 是任意 `Step`（`WorldModel.simulator.step`），对 `θ` 的依赖
**不是 ℝ-仿射的**。因此「`endToEnd` 的一步 = `gstep`」对一般 `W` 是**假**的：
缺口不是「忘了连」，而是「结构不同」。`linWorld`（机制 `θ * x`、
方向映射 `(1/x) • id`）是该结构相同的**唯一已实例化落点**，
本模块在它上面把等价证死。

- 不声称一般 `W` 上一阶等价（见上）。
- 不声称收敛——收敛已在 `Fate.ThetaConvergence` 中独立给出。
- 零 `sorry` / 零 `admit` / 零 `axiom` / 零 `?_`。
-/

namespace FateV2.Loop

open FateV2.Predict
namespace EndToEndPipelineBridge

open FateV2.Loop.EndToEnd
open FateV2.Loop.ThetaConvergence
open PipelineTendstoGen

/-! ===========================================================================
  §1  ⭐ `endToEndIter` = 一步函数的 `Function.iterate`（**任意** `W`）
  =========================================================================== -/

/-- ⭐⭐⭐ **【迭代 = 端点函数的 `Nat.iterate`】，对任意 `W` 成立。**

`endToEndIter` 的定义是 `Nat.rec`（先作用再递推）。本定理把它对齐到标准的
`Function.iterate`：
$$\mathrm{endToEndIter}\ \dots\ n\ \theta
   = \bigl(\lambda s.\ \mathrm{endToEnd}\ \dots\ s\ \dots\bigr)^{[n]}\ \theta .$$

**⭐ 这是与 `pipelineNGen := (gstep η θstar)^[n] θ₀` 结构对齐的第一步**：
右端正是 `Nat.iterate` 的形状，故只要「一步函数相等」，多步就相等。

**⚠ 非循环**：左端是 `EndToEnd` 的 `Nat.rec` 定义，右端是 Mathlib 的
`Function.iterate`（独立定义）。等式内容是**两套独立迭代语义的对接**。 -/
theorem endToEndIter_eq_iterate (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier]
    {Y : Type v} [Nonempty W.frame.X.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (n : ℕ) (θ : W.frame.Θ.Carrier) :
    endToEndIter W h η φ y u ε a x n θ
      = (fun s => endToEnd W h η φ y s u ε a x)^[n] θ := by
  induction n generalizing θ with
  | zero => rfl
  | succ k ih =>
    rw [endToEndIter_succ, ih (endToEnd W h η φ y θ u ε a x), Function.iterate_succ_apply]

/-! ===========================================================================
  §2  ⭐ `linWorld` 上的一步 = `gstep`
  =========================================================================== -/

/-- ⭐⭐ **`linWorld` 上 `endToEnd` 的一步函数**（把 `θ` 之外的全部参数固定）。 -/
noncomputable abbrev linStep (η θstar x : ℝ) : ℝ → ℝ :=
  fun θ => endToEnd linWorld (id : ℝ → ℝ) η
    (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
    (θstar * x) θ PUnit.unit PUnit.unit PUnit.unit x

/-- ⭐⭐⭐ **【`linWorld` 上 `endToEnd` 的一步 = `gstep`】**

$$f(\theta) = (1-\eta)\theta + \eta\,\theta^* = \mathrm{gstep}\ \eta\ \theta^*\ \theta .$$

**⭐ 这就是 `PipelineTendstoGen.lean` §1 注释所**断言的**结构等价**在
`linWorld` 上的**证明**：左端是 `EndToEnd` 的端到端一步（经 `x ≠ 0`
归一化后的真更新律），右端是 `PipelineTendstoGen.gstep`。

**⚠ 非循环**：前件只有 `x ≠ 0`（保证 `1/x` 存在）。
结论「`linStep η θstar x = gstep η θstar`」不是任何前件的重述：
`linStep` 里含 `observe`、`predFrom`、减法、`writeBack` 四个环节，
`gstep` 只有 `(1-η)•θ + η•θstar`。二者相等是**代数事实**。 -/
theorem linStep_eq_gstep (η θstar x : ℝ) (hx : x ≠ 0) :
    linStep η θstar x = gstep η θstar := by
  funext θ
  simp only [linStep, gstep, smul_eq_mul]
  rw [linWorld_endToEnd_step η θ θstar x hx]

/-! ===========================================================================
  §3  ⭐⭐⭐ 主定理：`endToEndIter` = `pipelineNGen`（`linWorld` 上）
  =========================================================================== -/

/-- ⭐⭐⭐ **【端到端 `n` 步 = 管线 `n` 步】**

$$\mathrm{endToEndIter}\ \mathrm{linWorld}\ \dots\ n\ \theta_0
   \;=\; \mathrm{pipelineNGen}\ \eta\ \theta^*\ \theta_0\ n .$$

**⭐ 这是本模块的顶点**：`RuleDrivesEndToEnd`／`EndToEnd` 与
`PipelineTendstoGen` 两条链此前**互不 import**，本定理把它们**逐点**接上。

**证明链**：§1 `endToEndIter = (fun s => endToEnd … s …)^[n]`
→ §2 `linStep = gstep` → `pipelineNGen` 的定义。 -/
theorem linWorld_endToEndIter_eq_pipelineNGen (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (n : ℕ) :
    endToEndIter linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀
      = pipelineNGen η θstar θ₀ n := by
  rw [endToEndIter_eq_iterate]
  change (linStep η θstar x)^[n] θ₀ = pipelineNGen η θstar θ₀ n
  rw [linStep_eq_gstep η θstar x hx]
  rfl

/-! ===========================================================================
  §4  ⭐⭐ 推论：偏差按 `(1-η)^n` 缩放（把 `pipelineNGen_closed` 落到 `endToEndIter`）
  =========================================================================== -/

/-- ⭐⭐ **【`endToEndIter` 的偏差闭式】**

$$\theta_n - \theta^* = (1-\eta)^n\,(\theta_0 - \theta^*) .$$

由 §3 的 `linWorld_endToEndIter_eq_pipelineNGen` 与
`PipelineTendstoGen.pipelineNGen_closed` 合并得到。 -/
theorem linWorld_endToEndIter_closed (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    endToEndIter linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀ - θstar
      = (1 - η)^n * (θ₀ - θstar) := by
  rw [linWorld_endToEndIter_eq_pipelineNGen η θstar x θ₀ hx n, pipelineNGen_closed]
  rw [smul_eq_mul]

end EndToEndPipelineBridge
end FateV2.Loop