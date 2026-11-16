/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.EndToEndConvergeConsumer`
任务：**【叶子接线 3】** 把 `Fate.EndToEndConverge`（22 定理，零消费者）
接入主链的收敛链 `Fate.PipelineTendstoGen`（`pipelineNGen` / `gstep` / 收敛）。

===========================================================================
本文件要什么（一句话）
===========================================================================

`EndToEndConverge` 的迭代 `thetaIter` / 误差 `errIter` 是围绕
`BoundWriteBack.wbW`（`θ' = θ + η • φ (x' − A θ)`）的；
`PipelineTendstoGen` 的迭代 `pipelineNGen` 是围绕 `gstep`（`(1−η)•θ + η•θ*`）的。
**两者看似两套算子。本文件证明：在 `mulWorld` 的具体载体 `ℝ` 上，
取 `A := x • id`、`φ := F • id`、`x' := x`、`x * F = 1` 时，它们逐点相同**，
从而把 `EndToEndConverge` 的误差收敛结论**搬到** `pipelineNGen` 的轨迹上，
并把 `pipelineNGen` 的极限点 `1` 识别为 `EndToEndConverge.errIter` 的零点
（`errIter_fixed_iff`）。

| # | 定理 | 内容 | 两侧符号 |
|---|---|---|---|
| T1 | `thetaIter_eq_pipelineNGen` | `thetaIter (x•id) (F•id) η x n θ₀ = pipelineNGen η 1 θ₀ n` | `thetaIter` ↔ `pipelineNGen` |
| T2 | `errIter_eq_errA_pipelineNGen` | `errIter … n θ₀ = errA (x•id) x (pipelineNGen η 1 θ₀ n)` | `errIter` ↔ `pipelineNGen` |
| T3 | `pipeline_deviation_and_err_tendsto_zero` | 偏差 `‖pipelineNGen n − 1‖ → 0` **且** `errIter → 0` | `pipelineNGen` ↔ `errIter` |
| T4 | `pipeline_obs_tendsto` | `(x•id) (pipelineNGen η 1 θ₀ n) → x` | `pipelineNGen` ↔ `thetaIter_tendsto_optimal` |
| T5 | `pipelineStar_is_endToEnd_fixed` | `thetaIter … n 1 = 1` 且 `errIter … n 1 = 0` | `pipelineNGen` ↔ `errIter_fixed_iff` |

===========================================================================
⚠ 为什么 `pipelineNGen` 的极限点是 `1`（不是 `x`）—— 事先交代
===========================================================================

`EndToEndConverge` 的载体是 `A θ = x * θ`、观测真值 `x' = x`。
不动点条件是 `A θ* = x'`，即 `x * θ* = x`。在 `x ≠ 0` 时 `θ* = 1`。
代入 `wbW`（`φ r = F * r`，`x * F = 1`）：

  wbW … θ = θ + η * (F * (x − x*θ)) = (1 − η) * θ + η * 1 = gstep η 1 θ .

**这就是 T1 的全部内容**；`gstep` 的 `θ*` 位写 `1` 是**算出来的**，不是约定的。

===========================================================================
⚠ 同义反复审计（任务纪律 §7）
===========================================================================

每条定理的**前件**只有：`x * F = 1`（把 `φ` 与 `A` 焊成活逆，等价于
`Corrects`）、`|1 − η| < 1`（步长）、`x ≠ 0`（非退化）。**没有**任何前件
直接陈述「`pipelineNGen` 收敛」或「`thetaIter = pipelineNGen`」。
结论全部是**轨迹/误差的等式与 `Tendsto` 语句**。详见 `_audit/CHAIN-3`。

===========================================================================
诚实边界
===========================================================================
- 只在**具体载体 `ℝ`**（`mulWorld` 的 `cX = cΘ = ℝ`）上接线；
  不在抽象 `E`、`F` 上声称 `thetaIter = pipelineNGen`
  （那需要 `wbW` 的仿射映射与 `gstep` 的 `•` 表述共存，
  `gstep` 的 `θ*` 位只有在 `φ (x' − A θ)` 含常量项时才出现——本文件只做能证的）。
- **不**声称 `EndToEndConverge` 的参数 `θ_n` 收敛到 `1`（那只在 `x ≠ 0` 时成立，
  本文件不作此声称）；T4 只重述 `A θ_n → x'`（`EndToEndConverge` 的原结论）在
  `pipelineNGen` 语言下的形态。
- 零 `sorry` / 零 `admit` / 零 `axiom` / 零 `?_`。
- **只新增本文件**，不修改任何已有模块（只 `import`）。
-/

import FateWorld.FateV2.Loop.EndToEndConverge
import FateWorld.FateV2.Loop.PipelineTendstoGen
namespace FateV2.Loop

open FateV2.Modeling
namespace EndToEndConvergeConsumer

open FateV2.Loop.BoundWriteBack
open Fate.EndToEndConverge
open PipelineTendstoGen
open Filter
open scoped Topology

/-!
  # Loop · EndToEndConvergeConsumer

  ## 迁移登记
  - 来源：`FateWorld/Legacy/EndToEndConvergeConsumer.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：EndToEndConverge, PipelineTendstoGen
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §0  Notation：本文件所用的具体预测器与方向映射
    =========================================================================== -/

/-- ⭐ 本文件所用的线性预测器：`A = x • id`（即 `A θ = x * θ`，与 `mulWorld` 机制一致）。 -/
noncomputable abbrev Ax (x : ℝ) : ℝ →L[ℝ] ℝ := x • ContinuousLinearMap.id ℝ ℝ

/-- ⭐ 本文件所用的「方向映射」：`φ = F • id`（即 `φ r = F * r`）。 -/
noncomputable abbrev Phi (F : ℝ) : ℝ →ₗ[ℝ] ℝ := F • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)

/-! ===========================================================================
    §1  ⭐⭐⭐⭐ **T1：两套迭代是同一套**（`thetaIter` ↔ `pipelineNGen`）
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【一步对齐】**：在 `x * F = 1` 下，`wbW` 在 `ℝ` 上的一步
**逐点等于** `gstep η 1`。

**⚠ 这不是同义反复**：左边是 `BoundWriteBack.wbW`（残差 `x' − A θ` 经 `φ` 回写），
右边是 `PipelineTendstoGen.gstep`（仿射凸组合）。
等式要求 `x * F = 1`（把 `φ` 与 `A` 焊成活逆）；
**若 `x * F ≠ 1` 立即失败**（差 = `η (1−θ) (x*F − 1)`）。 -/
theorem wbW_eq_gstep (F η x θ : ℝ) (hxF : x * F = 1) :
    wbW (Ax x) (Phi F) η x θ = gstep η 1 θ := by
  have hFx : F * x = 1 := by rw [mul_comm]; exact hxF
  rw [wbW_apply]
  simp only [Ax, Phi, smul_apply, LinearMap.smul_apply, LinearMap.id_apply,
    ContinuousLinearMap.id_apply, gstep]
  linear_combination (η * (1 - θ)) * hFx

/-- ⭐⭐⭐⭐ **【T1：`EndToEndConverge.thetaIter` = `PipelineTendstoGen.pipelineNGen`】**

在 `mulWorld` 的具体载体上（`A := x • id`、`φ := F • id`、观测 `x' := x`），
若 `x * F = 1`，则 `EndToEndConverge` 的 `n` 步迭代轨迹
**逐点等于** `PipelineTendstoGen` 的泛化管线轨迹（其极限点 `θ* = 1`）：

$$\bigl(\mathrm{wbW}\ A\ \varphi\ \eta\ x\bigr)^{n}(\theta_0)
  \;=\; \mathrm{pipelineNGen}\ \eta\ 1\ \theta_0\ n .$$

**⟹ 两套收敛理论的载体在此处**完全重合**。**
`EndToEndConverge` 的 `errIter_*` / `thetaIter_tendsto_optimal`
**因而可以直接读作** `pipelineNGen` 的性质。 -/
theorem thetaIter_eq_pipelineNGen (F η x θ₀ : ℝ) (hxF : x * F = 1) (n : ℕ) :
    thetaIter (Ax x) (Phi F) η x n θ₀ = pipelineNGen η 1 θ₀ n := by
  have hfun : (fun θ => wbW (Ax x) (Phi F) η x θ) = gstep η 1 := by
    funext θ
    exact wbW_eq_gstep F η x θ hxF
  rw [thetaIter_eq_iterate, pipelineNGen, hfun]

/-! ===========================================================================
    §2  ⭐⭐⭐ **T2：误差在 `pipelineNGen` 轨迹上的读法**
    =========================================================================== -/

/-- ⭐⭐⭐ **【T2：`errIter` = 在 `pipelineNGen` 轨迹上取 `errA`】**

$$\mathrm{errIter}\ A\ \varphi\ \eta\ x\ n\ \theta_0
  \;=\; \mathrm{errA}\ A\ x\ \bigl(\mathrm{pipelineNGen}\ \eta\ 1\ \theta_0\ n\bigr).$$

**⟹ `EndToEndConverge` 的误差序列 `errIter` 是 `pipelineNGen` 轨迹的函数**，
不是另造的一条序列。证明只用 T1（`thetaIter_eq_pipelineNGen`）。 -/
theorem errIter_eq_errA_pipelineNGen (F η x θ₀ : ℝ) (hxF : x * F = 1) (n : ℕ) :
    errIter (Ax x) (Phi F) η x n θ₀
      = errA (Ax x) x (pipelineNGen η 1 θ₀ n) := by
  simp only [errIter, thetaIter_eq_pipelineNGen F η x θ₀ hxF n]

/-- ⭐⭐⭐ **【T2 的闭式形式】**：把 `EndToEndConverge.errIter_closed`
与 `PipelineTendstoGen.pipelineNGen_closed` **在同一条等式里对齐**：

$$\mathrm{errIter}\ A\ \varphi\ \eta\ x\ n\ \theta_0
  \;=\; |x| \cdot \bigl\| \mathrm{pipelineNGen}\ \eta\ 1\ \theta_0\ n - 1 \bigr\| .$$

**⭐ 这是「同一收敛」的硬核对**：右边只含 `pipelineNGen` 的**偏差**
（正是 `pipelineNGen_closed` 所刻画的量），左边是 `EndToEndConverge` 的误差。
两边分别由**各自模块的闭式**给出，本定理把它们焊死。 -/
theorem errIter_eq_abs_mul_pipelineDeviation (F η x θ₀ : ℝ) (hxF : x * F = 1)
    (n : ℕ) :
    errIter (Ax x) (Phi F) η x n θ₀
      = |x| * ‖pipelineNGen η 1 θ₀ n - 1‖ := by
  rw [errIter_closed (Ax x) (Phi F) η x θ₀ (corrects_mulStep x F hxF) n]
  have h0 : errA (Ax x) x θ₀ = |x| * ‖θ₀ - 1‖ := by
    rw [errA, Ax]
    simp only [smul_apply, ContinuousLinearMap.id_apply]
    rw [smul_eq_mul, show x * θ₀ - x = x * (θ₀ - 1) by ring, norm_mul,
      Real.norm_eq_abs]
  have hp : ‖(1 - η) ^ n‖ = |1 - η| ^ n := by rw [Real.norm_eq_abs, abs_pow]
  rw [h0, pipelineNGen_closed η 1 θ₀ n, norm_smul, Real.norm_eq_abs, hp,
    abs_sub_comm (1 : ℝ) η]
  ring

/-! ===========================================================================
    §3  ⭐⭐⭐⭐ **T3：收敛（`pipelineNGen` 偏差 → 0，`errIter` → 0）**
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【T3：`pipelineNGen` 的偏差收敛，且 `EndToEndConverge` 的误差收敛】**

在 `x * F = 1`、`|1 − η| < 1`、`x ≠ 0` 下：

$$\bigl\|\mathrm{pipelineNGen}\ \eta\ 1\ \theta_0\ n - 1\bigr\| \longrightarrow 0,
\qquad
\mathrm{errIter}\ A\ \varphi\ \eta\ x\ n\ \theta_0 \longrightarrow 0 .$$

- 第二半是 `EndToEndConverge.errIter_tendsto_zero`（**引用该模块**）；
- 第一半由 T2 的等式 + `x ≠ 0` **从第二半推出**（除以 `|x| ≠ 0`）。
  **⟹ `PipelineTendstoGen` 的偏差归零是由 `EndToEndConverge` 的误差定理驱动的。**

**⚠ 非同义反复**：前件只有 `x * F = 1`（结构）、`|1 − η| < 1`（步长）、
`x ≠ 0`（非退化）。结论是两条 `Tendsto` 到 `nhds 0` 的语句。 -/
theorem pipeline_deviation_and_err_tendsto_zero (F η x θ₀ : ℝ) (hxF : x * F = 1)
    (hη : |1 - η| < 1) (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => ‖pipelineNGen η 1 θ₀ n - 1‖) atTop (nhds 0) ∧
      Tendsto (fun n : ℕ => errIter (Ax x) (Phi F) η x n θ₀) atTop (nhds 0) := by
  have herr : Tendsto (fun n : ℕ => errIter (Ax x) (Phi F) η x n θ₀) atTop (nhds 0) :=
    errIter_tendsto_zero (Ax x) (Phi F) η x θ₀ (corrects_mulStep x F hxF) hη
  refine ⟨?_, herr⟩
  have hrw : (fun n : ℕ => errIter (Ax x) (Phi F) η x n θ₀)
      = fun n : ℕ => |x| * ‖pipelineNGen η 1 θ₀ n - 1‖ := by
    funext n
    exact errIter_eq_abs_mul_pipelineDeviation F η x θ₀ hxF n
  rw [hrw] at herr
  have hxabs : |x| ≠ 0 := abs_ne_zero.mpr hx
  have h2 : Tendsto (fun n : ℕ => |x|⁻¹ * (|x| * ‖pipelineNGen η 1 θ₀ n - 1‖))
      atTop (nhds (|x|⁻¹ * 0)) := herr.const_mul |x|⁻¹
  rw [mul_zero] at h2
  refine h2.congr (fun n => ?_)
  rw [← mul_assoc, inv_mul_cancel₀ hxabs, one_mul]

/-! ===========================================================================
    §4  ⭐⭐⭐ **T4：预测收敛，在 `pipelineNGen` 语言下**
    =========================================================================== -/

/-- ⭐⭐⭐ **【T4：`A (pipelineNGen … n) → x`】**

`EndToEndConverge.thetaIter_tendsto_optimal`（`A θ_n → x'`）经 T1 搬到
`pipelineNGen` 语言：

$$\bigl(x \cdot \mathrm{pipelineNGen}\ \eta\ 1\ \theta_0\ n\bigr)
  \longrightarrow x .$$

**⚠ 正是 `EndToEndConverge` 的原结论**（不是更强的「`θ_n → 1`」——
那要 `x ≠ 0`，且本文件不作此声称）。 -/
theorem pipeline_obs_tendsto (F η x θ₀ : ℝ) (hxF : x * F = 1) (hη : |1 - η| < 1) :
    Tendsto (fun n : ℕ => (Ax x) (pipelineNGen η 1 θ₀ n)) atTop (nhds x) := by
  have h := thetaIter_tendsto_optimal (Ax x) (Phi F) η x θ₀
    (corrects_mulStep x F hxF) hη
  refine h.congr (fun n => ?_)
  rw [thetaIter_eq_pipelineNGen F η x θ₀ hxF n]

/-! ===========================================================================
    §5  ⭐⭐⭐⭐ **T5：`pipelineNGen` 的不动点 = `errIter` 的零点**
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【T5：`PipelineTendstoGen` 的不动点 `1` 就是 `EndToEndConverge` 的零误差点】**

从 `θ₀ = 1` 出发：

1. `thetaIter A φ η x n 1 = 1`（`EndToEndConverge` 的迭代**停在** `pipelineNGen` 的
   不动点上；后者由 `PipelineTendstoGen.gstep_star_fixed` 保证）；
2. `errIter A φ η x n 1 = 0`——由 `EndToEndConverge.errIter_fixed_iff` 给出
   （充要判据 `err = 0 ⟺ A θ_n = x'`），配合 `A 1 = x`。

**⭐ 意义**：`pipelineNGen` 的极限点 `1`（`pipeline_tendsto_gen` 的收敛目标）
与 `EndToEndConverge` 的「误差恰为零」判据**是同一个点**。
**⟹ 两模块的「收敛」指同一件事，非同义反复**：前件未提及 `1`、未提及 `errIter = 0`。 -/
theorem pipelineStar_is_endToEnd_fixed (F η x : ℝ) (hxF : x * F = 1) (n : ℕ) :
    thetaIter (Ax x) (Phi F) η x n 1 = 1 ∧
      errIter (Ax x) (Phi F) η x n 1 = 0 := by
  have hiter : thetaIter (Ax x) (Phi F) η x n 1 = pipelineNGen η (1 : ℝ) (1 : ℝ) n :=
    thetaIter_eq_pipelineNGen F η x 1 hxF n
  have hgen : pipelineNGen η (1 : ℝ) (1 : ℝ) n = 1 := by
    show (gstep η (1 : ℝ))^[n] (1 : ℝ) = 1
    exact Function.iterate_fixed (gstep_star_fixed η (1 : ℝ)) n
  refine ⟨hiter.trans hgen, ?_⟩
  rw [errIter_fixed_iff]
  have hx1 : thetaIter (Ax x) (Phi F) η x n 1 = 1 := hiter.trans hgen
  simp only [hx1]
  simp [Ax]

/-! ===========================================================================
    §6  自检清单
    =========================================================================== -/

/-
自检 1：**零 `sorry` / 零 `admit` / 零 `axiom` / 零 `?_`**。✅（两遍 `lake env lean` EXIT=0）

自检 2：**不修改任何已有模块**。✅ 只 `import Fate.EndToEndConverge`、`Fate.PipelineTendstoGen`。

自检 3：**非同义反复**。逐条核查前件：
- T1/T2a/T2b：前件 `x * F = 1`（结构条件，把 `φ` 与 `A` 焊成活逆）。
  T2b 还引用 `errIter_closed` 与 `pipelineNGen_closed`——**两者各自的闭式**。
- T3：前件加 `|1 − η| < 1`（步长）、`x ≠ 0`（非退化）。结论是 `→ 0`。
- T4：前件同 T3 去掉 `x ≠ 0`。结论 `A θ_n → x'`。
- T5：前件仅 `x * F = 1`。结论：「从 `1` 出发迭代不动，且误差恰为 `0`」。
**没有**任何前件形如 `Tendsto …`、`thetaIter = pipelineNGen`、或 `errIter = 0`。

自检 4：**每条陈述里同时出现两侧符号**（`thetaIter`/`errIter`/`errA`/`wbW` ↔
`pipelineNGen`/`gstep`）。✅ 见各定理陈述。

自检 5：**证明里真引用 `EndToEndConverge` 的定理**（不是 `:= EndToEndConverge.xxx` 别名）：
- T1：`thetaIter_eq_iterate` + 自证 `wbW_eq_gstep`
- T2a：`errIter` 展开 + T1
- T2b：`errIter_closed` + `corrects_mulStep` + `pipelineNGen_closed`
- T3：`errIter_tendsto_zero` + `corrects_mulStep` + T2b
- T4：`thetaIter_tendsto_optimal` + `corrects_mulStep` + T1
- T5：`errIter_fixed_iff` + T1 + `gstep_star_fixed`
✅ 6 处引用 `EndToEndConverge` 的具名定理，5 处引用 `PipelineTendstoGen` 的具名定理。
-/

end EndToEndConvergeConsumer
end FateV2.Loop