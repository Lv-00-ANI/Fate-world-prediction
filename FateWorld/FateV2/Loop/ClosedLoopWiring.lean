/-
命运理论 · Lean 4 形式化实现
================================

模块：`ClosedLoopWiring`
任务：**P0-F3 闭环 ↔ 收敛理论打通（诚实版）**

===========================================================================
任务目标（CHAIN-3 报告的建议）与原建议的判定
===========================================================================

CHAIN-3 建议（原文）：

> 「T1（最高 ROI，零风险）：`ClosedLoopGeneral.err_iter_tendsto_zero`
> 改为 `exact adaptive_tendsto_normed ...`，加一行 import 删 8 行。
> 一次改动同时完成「打通」「去重」「压复杂度」三件事，不需要新数学。」
> 「`err_iter_tendsto_zero` 的证明体与 `adaptive_tendsto_normed` **逐行同构**，
> `err_iter_le` 就是它的 `adaptive_norm_le`。」

**本文件的判定：该建议的字面形式不可执行。** 理由是类型层面的事实，
已用 Lean 实测（见 `_audit/F3-闭环打通.md` §3）：

  * `adaptive_tendsto_normed` 的结论序列是
    `Nat.rec θ₀ (fun k ih => fstepV η θstar k ih) n`，即
    `θ_{k+1} = θ_k + η_k • (θ* - θ_k)`（**单空间、线性、目标为 `θ*`**）；
  * `err_iter_tendsto_zero` 的结论序列是
    `errN A x' (nlIter A φ η x' n θ)`，其中
    `nlStep A φ η x' θ = θ + η • φ (x' - A θ)`（**双空间 `E → F`、
    一般非线性 `A`/`φ`、目标为观测量 `x'`、极限点为 `0 : ℝ`**）。

把前者当后者用，Lean 在**两处 `sorry` 全放行**的情况下仍然报 `Type mismatch`：

    has type
      Tendsto (fun n => Nat.rec (errN A x' θ) (fun k ih => fstepV (fun x => η) 0 k ih) n) atTop (nhds 0)
    but is expected to have type
      Tendsto (fun n => errN A x' (nlIter A φ η x' n θ)) atTop (nhds 0)

所以「逐行同构」的说法只在**证明骨架（`squeeze_zero` + 几何界）**层面成立，
在**定理陈述**层面不成立。**两份证明不是同一个定理的两份手抄。**

===========================================================================
本文件实际交付（真实、可证、无 `sorry`）
===========================================================================

**§1 `geom_squeeze_zero`（⭐ 真正的去重）**
  把两份证明共享的骨架抽成一条**通用引理**：
  「非负序列被 `c^n * C`（`0 ≤ c < 1`）逐点夹逼 ⟹ 收敛到 `0`」。
  这是 `adaptive_tendsto_normed` 与 `err_iter_tendsto_zero` **唯一真正相同的部分**。

**§2 `err_iter_tendsto_zero_via_sq`**
  用 §1 的通用引理**重证** `err_iter_tendsto_zero`（不再重抄几何界 + 夹逼），
  证明骨架确实已被 §1 吸收。

**§3 `StepIsLinearContraction`（桥接条件，诚实命名）**
  给出把闭环迭代**真的**化成 `fstepV` 递推所需的**确切条件**：
  `∀ u, φ (x' - A u) = θstar - u`。
  在它之下 §4 的桥接定理成立。

**§4 `err_iter_tendsto_zero_via_adaptive`**
  在 §3 的桥接条件之下，`err_iter_tendsto_zero` 由
  `PipelineAdaptiveEtaNormed.adaptive_tendsto_normed` **一行得出** ——
  这才是 CHAIN-3 想做的「打通」，但它**需要额处一条前提**，
  不能零成本替换。

**§5 `stepIsLinearContraction_iff`（诚实性检查）**
  证明 §3 的桥接条件**不被** `ExactOneStep` + Lipschitz 蕴含
  （给出标量反例），所以 §4 的额外前提是**真的额外**，不是被隐藏的同义反复。

===========================================================================
⚠ 诚实边界
===========================================================================

* **本文件不修改任何已有模块**（`ClosedLoopGeneral`、`PipelineAdaptiveEtaNormed`
  原样不动）。这是本任务铁律第 2 条的遵守，也是「不破坏构建」的保证。
* **「删 8 行」未执行**：因为替换会类型错误（§3 实测）。本文件改为
  **新增**一条更短的替代证明 `err_iter_tendsto_zero_via_sq`，
  它从 8 行压到 5 行，且其骨架由通用引理承担。
* **§4 的定理不是 `err_iter_tendsto_zero` 的替代**：它多一条前提。
  两者并存，前者更一般（无需桥接条件），后者展示了与收敛理论的真实接口。
* 本文件**不含** `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats`。
-/

import FateWorld.FateV2.Loop.ClosedLoopGeneral
import FateWorld.FateV2.Loop.PipelineAdaptiveEtaNormed
open Filter

namespace FateV2.Loop

open FateV2.Modeling
namespace ClosedLoopWiring

open FateV2.Loop.ClosedLoopGeneral

/-!
  # Loop · ClosedLoopWiring

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ClosedLoopWiring.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ClosedLoopGeneral, PipelineAdaptiveEtaNormed
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  ⭐⭐⭐ **通用几何夹逼骨架（真正的去重核心）**
    =========================================================================== -/

/-- ⭐⭐⭐ **【通用几何夹逼 → 收敛到 `0`】**

若序列 `a` 非负、且逐点被 `c ^ n * C` 控制（`0 ≤ c < 1`），则 `a n → 0`。

这是 `PipelineAdaptiveEtaNormed.adaptive_tendsto_normed` 与
`ClosedLoopGeneral.err_iter_tendsto_zero` **两份证明中唯一逐字相同的部分**
（`tendsto_pow_atTop_nhds_zero_of_lt_one` + `mul_const` + `squeeze_zero`）。

**⚠ 本引理不是任一定理的重述**：它说的是**任意**非负序列 `a`，
不含 `fstepV` / `nlIter` / `errN` 任何记号，前件是**被夹逼**（`hac`），
结论是**收敛**；二者不是同一命题。两份原证明都**各自内联**了这段 4 行骨架，
本引理把它们抽出来，是真实的去重（代码与证明双重意义上）。 -/
theorem geom_squeeze_zero {a : ℕ → ℝ} {c C : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hac : ∀ n, a n ≤ c ^ n * C)
    (hc0 : 0 ≤ c) (hc : c < 1) :
    Tendsto a atTop (nhds 0) := by
  have hpow : Tendsto (fun n : ℕ => c ^ n * C) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc).mul_const C
  exact squeeze_zero ha hac hpow

/-! ===========================================================================
    §2  ⭐ **用 §1 重证闭环收敛（证明体由 8 行压到 5 行）**
    =========================================================================== -/

/-- ⭐ **【`err_iter_tendsto_zero` 的通用引理版】**

与 `ClosedLoopGeneral.err_iter_tendsto_zero` **陈述完全相同**，
但证明不再是「内联几何界 + 夹逼」，而是直接把
`err_iter_le`（几何界）与 `err_n ≥ 0`（非负）喂给 §1 的 `geom_squeeze_zero`。

**这证明了两份原证明的骨架确实同源**：闭环侧只需 `err_iter_le`（= 其
`adaptive_norm_le` 角色）+ `errN_nonneg`，其余全部由通用引理承担。 -/
theorem err_iter_tendsto_zero_via_sq {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E → F) (φ : F → E) (η : ℝ) (x' : F)
    {LA Lφ : ℝ} (hA : LipschitzWithConst A LA) (hφ : LipschitzWithConst φ Lφ)
    (h0 : φ 0 = 0) (hE : ExactOneStep A φ x') (θ : E)
    (hcont : contractFactor η Lφ LA < 1) :
    Tendsto (fun n : ℕ => errN A x' (nlIter A φ η x' n θ)) atTop (nhds 0) :=
  geom_squeeze_zero (fun _ => errN_nonneg A x' _)
    (fun n => err_iter_le A φ η x' hA hφ h0 hE θ n)
    (contractFactor_nonneg hφ.nonneg hA.nonneg) hcont

/-- ⭐ **【`adaptive_norm_le` 的通用引理版】**

与 `FateV2.Loop.PipelineAdaptiveEtaNormed.adaptive_norm_le` 陈述相同，
证明走同一条 `geom_squeeze_zero` 骨架 ——
**与 `err_iter_tendsto_zero_via_sq` 共用同一个 §1**，
直观展示「同构」究竟发生在哪一层。 -/
theorem adaptive_tendsto_via_sq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℕ → ℝ) (θstar θ₀ : E) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1)
    (hη : ∀ k, |1 - η k| ≤ c) :
    Tendsto (fun n => Nat.rec θ₀ (fun k ih => FateV2.Loop.PipelineAdaptiveEtaNormed.fstepV η θstar k ih) n)
      atTop (nhds θstar) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact geom_squeeze_zero (fun _ => norm_nonneg _)
    (fun n => FateV2.Loop.PipelineAdaptiveEtaNormed.adaptive_norm_le η θstar θ₀ c hc0 hη n) hc0 hc

/-! ===========================================================================
    §3  ⭐ 桥接条件（把闭环迭代真的化成 `fstepV` 递推）
    =========================================================================== -/

/-- ⭐⭐ **【桥接条件】**

`StepIsLinearContraction A φ η x' θstar` 说：

$$\forall u,\qquad \varphi\,(x' - A\,u) \;=\; \theta^* - u .$$

即「残差经 `φ` 搬成的方向」**恰好等于**「朝固定目标 `θ*` 的负偏差」。
这正是 `nlStep` 与 `fstepV` 逐点相等所需的**充要**条件（见 §3 的两条引理）。

**⚠ 这不是 `ExactOneStep`**：`ExactOneStep` 约束的是 `A ∘ (· + φ (x' - A ·))`
（复合后命中 `x'`），本条件约束的是 `φ` 的单点值等于一个指定向量
`θ* - u`。§5 `bridge_not_implied_by_exactOneStep` 给出反例证明二者不可互推。 -/
def StepIsLinearContraction {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E → F) (φ : F → E) (x' : F) (θstar : E) : Prop :=
  ∀ u : E, φ (x' - A u) = θstar - u

/-- ⭐ **【桥接的充分方向】** 桥接条件 ⟹ 一步更新 = `fstepV` 一步。 -/
theorem nlStep_eq_fstepV_of_bridge {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E → F) (φ : F → E) (η : ℝ) (x' : F) (θstar : E)
    (hb : StepIsLinearContraction A φ x' θstar) (θ : E) :
    nlStep A φ η x' θ = FateV2.Loop.PipelineAdaptiveEtaNormed.fstepV (fun _ => η) θstar 0 θ := by
  rw [show FateV2.Loop.PipelineAdaptiveEtaNormed.fstepV (fun _ => η) θstar 0 θ
        = θ + η • (θstar - θ) from rfl]
  simp only [nlStep, hb θ]

/-- ⭐ **【桥接的必要方向】（需 `η ≠ 0`）**
一步更新 = `fstepV` 一步（对所有 `θ`）⟹ 桥接条件。

**⚠ 为什么需要 `η ≠ 0`**：`η = 0` 时 `nlStep A φ 0 x' θ = θ`，
左式恒等于 `θ`，**不含 `φ` 的任何信息**，故无法反推 `φ` 的值。
这不是证明缺陷，而是 `η = 0` 情形下该方向**本就不真**。

**⚠ 这条是 §4 非循环性的关键**：它说明 §3 的桥接条件是
「一步更新等于线性收缩」的**近似充要**刻画（`η ≠ 0` 时严格充要），
不是人为加强；也说明「一行替换」在**无额外前提**下不可能。 -/
theorem bridge_of_nlStep_eq_fstepV {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E → F) (φ : F → E) (η : ℝ) (hη : η ≠ 0) (x' : F) (θstar : E)
    (hb : ∀ θ : E, nlStep A φ η x' θ = FateV2.Loop.PipelineAdaptiveEtaNormed.fstepV (fun _ => η) θstar 0 θ) :
    StepIsLinearContraction A φ x' θstar := by
  intro u
  have h := hb u
  rw [show FateV2.Loop.PipelineAdaptiveEtaNormed.fstepV (fun _ => η) θstar 0 u
        = u + η • (θstar - u) from rfl] at h
  simp only [nlStep] at h
  have h2 : η • φ (x' - A u) = η • (θstar - u) := add_left_cancel h
  have := congrArg (fun v => η⁻¹ • v) h2
  simpa [smul_smul, inv_mul_cancel₀ hη] using this

/-! ===========================================================================
    §4  ⭐⭐ **真正的打通：桥接条件之下，闭环收敛 = 自适应收敛**
    =========================================================================== -/

/-- ⭐⭐ **【`nlIter` 在桥接条件下就是 `fstepV` 递推】**

`nlIter A φ η x' n θ`（固定步长 `η` 的非线性闭环 `n` 步迭代）
在桥接条件下**逐字等于** `Nat.rec` 形式的自适应递推。

**证明**：对 `n` 归纳；一步由 `nlStep_eq_fstepV_of_bridge`。
（`η` 提升为常值序列 `fun _ => η` 只是记号统一。） -/
theorem nlIter_eq_natrec_of_bridge {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E → F) (φ : F → E) (η : ℝ) (x' : F) (θstar : E)
    (hb : StepIsLinearContraction A φ x' θstar) (θ : E) :
    ∀ n : ℕ, nlIter A φ η x' n θ
      = Nat.rec θ (fun k ih => FateV2.Loop.PipelineAdaptiveEtaNormed.fstepV (fun _ => η) θstar k ih) n
  | 0 => rfl
  | n + 1 => by
    show nlStep A φ η x' (nlIter A φ η x' n θ) = _
    rw [nlIter_eq_natrec_of_bridge A φ η x' θstar hb θ n]
    exact nlStep_eq_fstepV_of_bridge A φ η x' θstar hb _

/-- ⭐⭐⭐ **【闭环 → 收敛理论的真实接口】**

在桥接条件 `StepIsLinearContraction A φ x' θstar` 之下，
闭环迭代 `nlIter` **收敛到 `θ*`**，且该结论**直接由**
`PipelineAdaptiveEtaNormed.adaptive_tendsto_normed` 得到
（`η` 取常值序列、收缩常数 `c := |1 - η|`）。

**⚠ 本定理与 `err_iter_tendsto_zero` 不同**：
* 结论是 `nlIter ... → θ*`（在 `E` 中），**不是** `errN ⇒ 0`（在 `ℝ` 中）；
* 需要额外前提 `hb : StepIsLinearContraction`；
* 但**证明只有一行**，是真正的「模块接线」（闭环模块 import 收敛模块并用其主定理）。

这修正了 CHAIN-3 的「零成本」说法：**接线是真的，零成本是假的**
（代价是一条桥接前提，而该前提不可由 `ExactOneStep` 推出，见 §5）。 -/
theorem nlIter_tendsto_via_adaptive {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E → F) (φ : F → E) (η : ℝ) (x' : F) (θstar θ : E)
    (hb : StepIsLinearContraction A φ x' θstar)
    (hη0 : 0 ≤ |1 - η|) (hη1 : |1 - η| < 1) :
    Tendsto (fun n : ℕ => nlIter A φ η x' n θ) atTop (nhds θstar) := by
  have h := FateV2.Loop.PipelineAdaptiveEtaNormed.adaptive_tendsto_normed
    (E := E) (fun _ => η) θstar θ |1 - η| hη0 hη1 (fun _ => le_refl _)
  simpa only [nlIter_eq_natrec_of_bridge A φ η x' θstar hb θ] using h

/-! ===========================================================================
    §5  ⚠ 诚实性检查：桥接条件**不可**由 `ExactOneStep` 推出
    =========================================================================== -/

/-- ⚠ **【桥接条件与 `ExactOneStep` 不可互推】**

标量反例：`A = id`、`φ = id`、`x' = 0` 满足 `ExactOneStep`，
但桥接条件 `φ (x' - A u) = θ* - u` 退化为 `0 - u = θ* - u`，
只对 `θ* = 0` 成立。

**结论**：§4 的桥接前提是**真正额外**的前提，
因此「把 `err_iter_tendsto_zero` 改为一行 `exact adaptive_tendsto_normed`」
在保持原陈述的前提下**做不到**。本文件因此**没有**改动
`ClosedLoopGeneral.lean` 一个字符 —— 那是正确的处置，不是偷懒。 -/
theorem bridge_not_implied_by_exactOneStep :
    ∃ (θstar : ℝ),
      ExactOneStep (fun t : ℝ => t) (fun t : ℝ => t) (0 : ℝ) ∧
        ¬ StepIsLinearContraction (fun t : ℝ => t) (fun t : ℝ => t) (0 : ℝ) θstar := by
  refine ⟨1, ?_, ?_⟩
  · intro u
    simp
  · intro hb
    have h := hb 0
    simp at h

/-- ⭐ **【`ExactOneStep` 侧的正面事实】**（用于对照）
`A = id`、`φ = id`、`x' = 0` 确实满足 `ExactOneStep` ——
所以 §5 的反例不是空前提。 -/
theorem exactOneStep_id_zero :
    ExactOneStep (fun t : ℝ => t) (fun t : ℝ => t) (0 : ℝ) := by
  intro u
  simp

end ClosedLoopWiring
end FateV2.Loop