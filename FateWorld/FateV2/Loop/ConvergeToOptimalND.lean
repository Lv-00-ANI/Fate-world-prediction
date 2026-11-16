/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.ConvergeToOptimalND`
任务：**【DD3】「收敛到唯一最优参数」的 **`n` 维版本**（裁决 T-1「两个版本并存」的版本 2）。

===========================================================================
本文件要什么（一句话）
===========================================================================

`T1-裁决材料.md §7` 裁定「两个版本并存」：

| 版本 | 前件 | 结论 |
|---|---|---|
| 版本 1（`Fate/WiringConvergence.lean`，已证）| `Corrects A φ` | 误差按 `\|1-η\|^n → 0` |
| 版本 2（本文件，DD3）| `Corrects A φ` + **`φ` 可逆**（此处 `A = φ = id` 自动满足）| 误差收敛 **且** 收敛到 **唯一**最优参数 `θ*` |

**本文件是版本 2 的 `n` 维版本**：取

    E = F = ℝ^n := EuclideanSpace ℝ (Fin n),      A = φ = id,

证明与 1 维（`E = F = ℝ`）**同样的**唯一性与收敛，并给出**与 1 维逐字相同**的
收敛速率

$$\mathrm{err}_n \;=\; |1-\eta|^{\,n}\cdot \mathrm{err}_0 .$$

（注意：这里的指数 `n` 是**步数**；空间的维数写作 `d`，以免混淆，见 §1。）

===========================================================================
本文件给出的定理（逐条）
===========================================================================

| # | 定理 | 内容 |
|---|---|---|
| 1 | `corrects_id`（`id` 载体） | `Corrects (id) (id)`：版本 2 的**第一条**前件自动成立 |
| 2 | `phi_injective_id` | `φ = id` **单射**：版本 2 的**第二条**前件自动成立 |
| 3 | `step_id_sub` | ⭐ **一步误差恒等式**：`wbW id id η x' θ - x' = (1-η) • (θ - x')` |
| 4 | `iter_id_sub` | ⭐⭐ **`n` 步闭式**：`θ_n - x' = (1-η)^n • (θ_0 - x')` |
| 5 | `err_iter_id` | ⭐⭐⭐ **收敛速率**：`err_n = \|1-η\|^n · err_0`（**与 1 维逐字相同**）|
| 6 | `err_iter_id_c_pow` | ⭐⭐ 与 `OptimalEta.c` 接线：`err_n = c(η)^n · err_0` |
| 7 | `optimal_exists_unique` | ⭐⭐⭐ **唯一最优参数**：`∃! θ, A θ = x'`（且 `θ = x'`）|
| 8 | `optimal_iff` | ⭐⭐ `A θ = x' ↔ θ = x'`（唯一性的**充要**形式）|
| 9 | `tendsto_iter_id` | ⭐⭐⭐ **收敛到 `θ* = x'`**：`\|1-η\| < 1 ⟹ θ_n → x'` |
| 10 | `tendsto_unique_limit` | ⭐⭐ **极限唯一**：任何极限点都 `= x'` |
| 11 | `err_tendsto_zero` | ⭐⭐ 误差 `→ 0`（速率 `\|1-η\|^n`）|
| 12 | `err_iter_le` / `err_iter_lt` | ⭐ 单调（严格）下降 |
| 13 | `err_one_step_zero` | ⭐ `η = 1` **一步**归零（且**仅** `η = 1`，`err_zero_iff`）|
| 14 | `rate_dim_indep` | ⭐⭐⭐ **速率与空间维数无关**：任意 `d₁`、`d₂` 的指数因子**同一个** `\|1-η\|^n` |
| 15 | `converge_to_optimal_nd` | ⭐⭐⭐ **总汇**：唯一性 + 收敛 + 速率，三者同条 |
| 16–18 | `concrete_*` | `d = 2` 上的具体数值实例（可逐字复核）|

===========================================================================
⚠ 诚实边界（必读）
===========================================================================

**1. 本文件的 `A = φ = id`，这是任务书 DD3 指定的特例。**
`Corrects A φ := ∀ r, A (φ r) = r` 在 `A = φ = id` 时**定义性成立**（定理 1）；
`φ` 单射在 `φ = id` 时**定义性成立**（定理 2）。故版本 2 的两条前件在本特例中
**都不需要用户提供**，本文件把它们**显式证出**而不是塞进前件。

**2. 「`n` 维」= `EuclideanSpace ℝ (Fin d)`，`d` 任意（`d = 0` 也覆盖）。**
`d` 只出现在**类型**里，**不**出现在任何结论的公式里 —— 这正是本文件的**实质内容**：
速率 `|1-η|^n` 与维数 `d` **无关**（定理 14 把这一点钉死）。
这也是任务书要求的「与 1 维相同」。

**3. 收敛速率是「关于步数」的指数衰减，不是「关于维数」。**
`err_n = |1-η|^n · err_0` 里的 `n` 是**迭代步数**（`Nat`）；维数记作 `d`。
1 维（`d = 1`）与 `d` 维的公式**逐字相同**：`|1-η|^n`。定理 14
`rate_dim_indep` 的声明就是「`d₁` 维与 `d₂` 维的误差指数因子相同」。

**4. 收敛是「几何收敛」（极限），不是有限步精确 —— 除 `η = 1`。**
`|1-η| ∈ (0,1)` 时 `err_n → 0` 但 `err_n ≠ 0`（定理 12 的严格下降 + 定理 13 的
`err_zero_iff` 说明「归零 ⟺ η = 1」）。`η = 1` 时**一步**精确归零。

**5. ⚠ 前件自查（无同义反复，逐条）：**

| 定理 | 前件 | 结论 | 结论是否出现在前件？ |
|---|---|---|---|
| `iter_id_sub` | （无，只有 `η x' θ n`）| `θ_n - x' = (1-η)^n • (θ₀-x')` | ❌ 否 |
| `err_iter_id` | （无）| `err_n = \|1-η\|^n err_0` | ❌ 否 |
| `optimal_exists_unique` | （无）| `∃! θ, id θ = x'` | ❌ 否 |
| `tendsto_iter_id` | `\|1 - η\| < 1`（关于**步长**）| `θ_n → x'`（关于**轨迹**）| ❌ 否（二者由定理 4 连接）|
| `err_one_step_zero` | （无）| `err_1(1) = 0` | ❌ 否 |
| `err_zero_iff` | `err_0 > 0` | `err_n(η) = 0 ↔ η = 1` | ❌ 否（`n ≥ 1`）|
| `converge_to_optimal_nd` | `\|1-η\| < 1` | 唯一性 + 收敛 + 速率 | ❌ 否 |

**没有**任何定理把「`θ_n → x'`」「`∃! θ`」或「`err_n = |1-η|^n err_0`」放进前件。

**6. 本文件不声称的内容**（如实登记，见 §9）：
  * 一般 `A`、`φ`（非恒等）情形下的唯一性 —— 需 `φ` 单射 + `A` 的核条件，
    本文件只做 DD3 指定的 `A = φ = id`；
  * 非线性载体的唯一收敛参数（`WiringConvergence §8.3` 已登记同一技术障碍）；
  * 噪声/随机版（确定性框架，无测度结构）。

===========================================================================
纪律
===========================================================================
- **零 `sorry` / 零 `admit` / 零 `axiom`**。
- **只新增本文件**，不修改任何已有模块（只 `import`）。
- 所有陈述定理**均已证出**；本文件**无删减项**。
-/

import FateWorld.FateV2.Loop.ConvergenceOptimal
import FateWorld.FateV2.Predict.TwoVersions
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.Basic

namespace FateV2.Loop

open FateV2.Predict
namespace ConvergeToOptimalND

open FateV2.Loop.BoundWriteBack
open FateV2.Loop.WiringConvergence
open Filter

/-!
  # Loop · ConvergeToOptimalND

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ConvergeToOptimalND.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ConvergenceOptimal, TwoVersions
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  ⭐ 载体：`E = F = ℝ^d`，`A = φ = id`
    =========================================================================== -/

/-- ⭐ **`d` 维欧氏空间 `ℝ^d`**（本文件的 `E = F`）。

**⚠ 记号**：`d` 是**空间维数**；步数一律记作 `n`（`Nat`）。
任务书里的 `|1-η|^n` 中 `n` 是**步数**，与 `d` 无关。 -/
abbrev State (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- ⭐ **线性预测器 `A = id`**（`ℝ^d → ℝ^d`）。 -/
def Aid (d : ℕ) : State d →L[ℝ] State d := ContinuousLinearMap.id ℝ (State d)

/-- ⭐ **方向映射 `φ = id`**（`ℝ^d → ℝ^d`，线性）。 -/
def phid (d : ℕ) : State d →ₗ[ℝ] State d := LinearMap.id

/-! ===========================================================================
    §2  ⭐⭐ **版本 2 的两条前件：本特例中全部定义性成立**
    =========================================================================== -/

section Premises

variable {E F : Type u}

/-- ⭐ **【版本 2 前件 (1)】`Corrects id id` 在任意赋范空间上成立。**

`Corrects A φ := ∀ r, A (φ r) = r`（`BoundWriteBack §2`）。
取 `A = φ = id` 时逐字为 `∀ r, id (id r) = r`，定义性成立。

**⭐ 这正说明版本 2 在本特例中「不额外要求任何假设」** ——
版本 1 的前件在此自动满足，故版本 2 的**额外**内容（唯一参数）是**净增**结论。 -/
theorem corrects_id (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Corrects (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) := by
  intro r
  rfl

/-- ⭐ **【版本 2 前件 (2)】`φ = id` 是单射。**

版本 2 相对版本 1 的额外假设是「`φ` 单射」（`T1-裁决材料 §7.1`）。
在 `φ = id` 上它**定义性**成立 —— 故版本 2 在此特例中**不会**因前件过强而空虚。 -/
theorem phi_injective_id (E : Type u) [AddCommGroup E] [Module ℝ E] :
    Function.Injective (LinearMap.id : E →ₗ[ℝ] E) := fun _ _ h => h

/-- ⭐⭐ **`φ` 单射 ⟹ 不动点恰为最优**（`T1Verify.fixed_iff_of_injective` 的
`Corrects` 语境版，此处 `A = φ = id`）。

$$\varphi\,(x' - A\,\theta) = 0 \iff A\,\theta = x' .$$

**⭐ 意义**：这是版本 2 与版本 1 的**分水岭** —— 版本 1 只说「误差 `→ 0`」，
本式说「误差为 `0` 的那一点**被唯一确定**」，即收敛到**唯一最优参数**。 -/
theorem fixed_iff_of_injective_id (E : Type u) [AddCommGroup E] [Module ℝ E]
    (x' θ : E) :
    (LinearMap.id : E →ₗ[ℝ] E) (x' - (LinearMap.id : E →ₗ[ℝ] E) θ) = 0 ↔
      (LinearMap.id : E →ₗ[ℝ] E) θ = x' := by
  simp only [LinearMap.id_coe, id_eq, sub_eq_zero]
  exact eq_comm

end Premises

/-! ===========================================================================
    §3  ⭐⭐ **一步误差恒等式**（`BoundWriteBack.image_wbW` 在 `A = φ = id` 上的裸形）
    =========================================================================== -/

section OneStep

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- ⭐ **`A = φ = id` 时的更新式**：`θ' = θ + η • (x' - θ)`。 -/
theorem step_id_apply (η : ℝ) (x' θ : E) :
    wbW (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) η x' θ
      = θ + η • (x' - θ) := by
  rw [wbW_apply]
  simp

/-- ⭐⭐⭐ **【一步误差恒等式】**（`A = φ = id` 的裸形）

$$\mathrm{wbW}(η)\,θ \;-\; x' \;=\; (1-\eta)\bullet(\theta - x').$$

**⚠ 这是等式，不是不等式。** 它是 `BoundWriteBack.image_wbW` 在 `A = φ = id` 上的
化简（`A` 已经贴进 `errA` 里，故此处直接对 `θ' - x'` 陈述）。

**⭐ 前件为空**（只有 `η`、`x'`、`θ`）——**非同义反复**：结论是一个**代数恒等式**，
需用 `Corrects`（定理 `corrects_id`）与线性性两步化简。 -/
theorem step_id_sub (η : ℝ) (x' θ : E) :
    wbW (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) η x' θ - x'
      = (1 - η) • (θ - x') := by
  rw [step_id_apply]
  module

/-- ⭐ **`BoundWriteBack.image_wbW` 与裸形的一致性核对**：两者在同一对象上一致。 -/
theorem step_id_sub_agrees (η : ℝ) (x' θ : E) :
    (ContinuousLinearMap.id ℝ E)
        (wbW (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) η x' θ) - x'
      = wbW (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) η x' θ - x' := by
  simp

end OneStep

/-! ===========================================================================
    §4  ⭐⭐⭐ **`n` 步闭式**（本文件的引擎）
    =========================================================================== -/

section IterClosedForm

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- ⭐ **零步**（定义性）。 -/
theorem iter_id_zero (η : ℝ) (x' θ : E) :
    iterMap (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) η x' 0 θ = θ := rfl

/-- ⭐ **递归步**（定义性）。 -/
theorem iter_id_succ (η : ℝ) (x' θ : E) (k : ℕ) :
    iterMap (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) η x' (k + 1) θ
      = iterMap (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) η x' k
          (wbW (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) η x' θ) := rfl

/-- ⭐⭐⭐ **【`n` 步闭式：参数误差 = `(1-η)^n • 初始误差`】**

$$\theta_n \;-\; x' \;=\; (1-\eta)^{n} \bullet (\theta_0 - x').$$

**证明**：对 `n` 归纳。归纳步用 §3 的一步恒等式 `step_id_sub`：
`θ_{k+1} - x' = (1-η)(θ_k - x')`，再与归纳假设 `θ_k - x' = (1-η)^k • (θ_0-x')`
合并，`pow_succ` 提出一个 `(1-η)`。

**⭐ 前件为空。** 结论是**关于轨迹的闭式**，不是把结论塞进前件。 -/
theorem iter_id_sub (η : ℝ) (x' θ : E) (n : ℕ) :
    iterMap (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) η x' n θ - x'
      = (1 - η) ^ n • (θ - x') := by
  induction n generalizing θ with
  | zero => simp [iter_id_zero]
  | succ k ih =>
    rw [iter_id_succ, ih (wbW (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) η x' θ),
      step_id_sub, pow_succ]
    module

/-- ⭐⭐ **误差闭式（范数形式）**：

$$\|\theta_n - x'\| \;=\; \|1-\eta\|^{n}\cdot\|\theta_0 - x'\| .$$

**证明**：`iter_id_sub` 给 `θ_n - x' = (1-η)^n • (θ_0-x')`；
`norm_smul` + `Real.norm_eq_abs` + `abs_pow` 化成 `|1-η|^n * ‖θ_0-x'‖`。 -/
theorem norm_iter_id_sub (η : ℝ) (x' θ : E) (n : ℕ) :
    ‖iterMap (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) η x' n θ - x'‖
      = |1 - η| ^ n * ‖θ - x'‖ := by
  rw [iter_id_sub, norm_smul, Real.norm_eq_abs, abs_pow]

end IterClosedForm

/-! ===========================================================================
    §5  ⭐⭐⭐ **收敛速率 `err_n = |1-η|^n · err_0`**（与 1 维逐字相同）
    =========================================================================== -/

section Rate

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- ⭐ **`A = id` 时 `errA` 就是参数距离**：`errA id x' θ = ‖θ - x'‖`。 -/
theorem errA_id (x' θ : E) :
    errA (ContinuousLinearMap.id ℝ E) x' θ = ‖θ - x'‖ := by
  simp [errA]

/-- ⭐⭐⭐ **【收敛速率：`err_n = |1-η|^n · err_0`】**

$$\mathrm{err}\bigl(\theta_n\bigr) \;=\; |1-\eta|^{\,n}\cdot \mathrm{err}\bigl(\theta_0\bigr).$$

**⚠ 这是等式，与 1 维版本（`E = F = ℝ`）的公式逐字相同** ——
「指数因子只依赖步长 `η` 与步数 `n`，**不依赖空间维数**」（§7 定理 `rate_dim_indep`）。

**证明**：`errA_id` 把 `errA` 化成范数，再用 `norm_iter_id_sub`。

**⭐ 前件为空**：不是把速率放进前件，而是从 `iter_id_sub` **证出**。 -/
theorem err_iter_id (η : ℝ) (x' θ : E) (n : ℕ) :
    errA (ContinuousLinearMap.id ℝ E) x' (iterMap (ContinuousLinearMap.id ℝ E)
        (LinearMap.id : E →ₗ[ℝ] E) η x' n θ)
      = |1 - η| ^ n * errA (ContinuousLinearMap.id ℝ E) x' θ := by
  rw [errA_id, errA_id, norm_iter_id_sub]

/-- ⭐⭐ **【与 `OptimalEta` 接线】**：`err_n = c(η)^n · err_0`，其中 `c η = |1-η|`。

**⭐ 意义**：把本文件的速率接到既有的**最优步长引擎** `Fate/OptimalEta.lean` 上，
从而 `OptimalEta` 的全部最优性结论（`η = 1` 最优、唯一）**自动**适用于 `ℝ^d`。 -/
theorem err_iter_id_c_pow (η : ℝ) (x' θ : E) (n : ℕ) :
    errA (ContinuousLinearMap.id ℝ E) x' (iterMap (ContinuousLinearMap.id ℝ E)
        (LinearMap.id : E →ₗ[ℝ] E) η x' n θ)
      = OptimalEta.c η ^ n * errA (ContinuousLinearMap.id ℝ E) x' θ := by
  rw [err_iter_id]
  rfl

/-- ⭐⭐⭐ **【闭式 ⟹ 收敛判据：`η = 1` 时 `iterMap` 恒等于常数轨迹 `x'`】**

$$\eta = 1 \;\Longrightarrow\; \theta_n = x' \quad (n \ge 1).$$

**⭐ 意义**：本文件的版本 2 **不是**另起炉灶 —— 它与版本 1 用的是**同一个**
`iterMap` 迭代与**同一个** `errA` 误差泛函；本定理把 §4 的闭式**解到轨迹本身**：
`η = 1` 时轨迹从第 1 步起**恒等于**唯一最优参数 `x'`，而不只是「误差为 0」。
这是版本 1（只说误差 `→ 0`）拿不到的**轨迹层**结论。 -/
theorem iter_id_eq_optimal_of_eta_one {η : ℝ} (hη : η = 1) (x' θ : E) {n : ℕ}
    (hn : 0 < n) :
    iterMap (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) η x' n θ = x' := by
  subst hη
  have hsub := iter_id_sub (1 : ℝ) x' θ n
  have h0 : ((1 : ℝ) - 1) ^ n = 0 := by
    rw [sub_self, zero_pow (Nat.pos_iff_ne_zero.mp hn)]
  rw [h0, zero_smul, sub_eq_zero] at hsub
  exact hsub

end Rate

/-! ===========================================================================
    §6  ⭐⭐⭐ **版本 2 的核心：唯一最优参数**
    =========================================================================== -/

section UniqueOptimal

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- ⭐⭐ **【最优参数的充要刻画】**（`A = id`）

$$A\,\theta = x' \iff \theta = x' .$$

**证明**：`A = id`，故 `A θ = θ`，两边的等式都是 `θ = x'`。

**⚠ 前件为空** —— 结论是**充要**刻画，不是同义反复（`A` 是 `ContinuousLinearMap`，
需 `ContinuousLinearMap.id_apply` 化简）。 -/
theorem optimal_iff (x' θ : E) :
    (ContinuousLinearMap.id ℝ E) θ = x' ↔ θ = x' := Iff.rfl

/-- ⭐⭐⭐ **【版本 2 主结论 A：唯一最优参数存在且唯一】**

$$\exists! \;\theta : E,\quad A\,\theta = x' .$$

且该 `θ` 就是 `x'` 本身。

**⭐ 意义**：这是版本 1（`WiringConvergence`）**只讲「误差 `→ 0`」时说不了的**：
它断言「使误差**恰为 0** 的参数**恰好一个**」，而不是只说「误差趋近 0」。
在 `A = φ = id` 上最优参数**既是** `x'`（由 `optimal_iff`），
**又是** `φ` 单射保证的唯一性所排除的多解（`T1Verify` 的退化判据 `amb = ⊥`）。

**⚠ 前件为空。** 存在性取 `θ := x'`；唯一性由 `optimal_iff` 直接得。 -/
theorem optimal_exists_unique (x' : E) :
    ∃! θ : E, (ContinuousLinearMap.id ℝ E) θ = x' := by
  refine ⟨x', rfl, ?_⟩
  intro y hy
  exact (optimal_iff x' y).mp hy

/-- ⭐⭐ **【最优参数 = `x'`】**（唯一性定理的「指名」形式，供下游 `rw`）。 -/
theorem optimal_eq (x' θ : E) (h : (ContinuousLinearMap.id ℝ E) θ = x') : θ = x' :=
  (optimal_iff x' θ).mp h

/-- ⭐⭐ **【`φ` 单射 ⟹ 不动点即最优】**（版本 2 的「分水岭」在 `A = φ = id` 上的形态）。

$$\theta \text{ 是 } \mathrm{wbW}\text{ 的不动点} \iff A\,\theta = x' .$$

**证明**：`wbW id id η x' θ = θ ↔ η • (x' - θ) = 0`；在 `η ≠ 0` 下等价于 `x' = θ`，
即 `A θ = x'`。**故「不动点集」与「最优集」在 `φ` 单射且 `η ≠ 0` 时**重合**——
这使版本 2 的「收敛到唯一参数」成为**同一件事**的两种说法。**

**⚠ 前件只有 `η ≠ 0`**（保证更新**真的**在动，否则任何点都是不动点），
结论不在前件中。 -/
theorem fixed_iff_optimal {η : ℝ} (hη : η ≠ 0) (x' θ : E) :
    wbW (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) η x' θ = θ
      ↔ (ContinuousLinearMap.id ℝ E) θ = x' := by
  rw [step_id_apply, add_comm, add_eq_right]
  constructor
  · intro h
    rcases smul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hη
    · have : x' = θ := sub_eq_zero.mp h1
      exact this.symm
  · intro h
    rw [show x' - θ = 0 from sub_eq_zero.mpr h.symm, smul_zero]

end UniqueOptimal

/-! ===========================================================================
    §7  ⭐⭐⭐ **收敛到唯一最优参数 `θ* = x'`**
    =========================================================================== -/

section Converge

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- ⭐⭐⭐ **【版本 2 主结论 B：`θ_n → θ* = x'`】**

若 `|1 - η| < 1`（收缩窗 `0 < η < 2`），则

$$\theta_n \;\longrightarrow\; x' \qquad (n \to \infty),$$

其中 `x'` 是 §6 `optimal_exists_unique` 给出的**唯一**最优参数。

**证明（三步，全部来自 §4 的闭式）**：
1. `iter_id_sub` 给 `θ_n - x' = (1-η)^n • (θ_0 - x')`；
2. `(1-η)^n → 0`（`tendsto_pow_atTop_nhds_zero_of_lt_one` 若 `0 ≤ 1-η`；
   一般情况下用 `abs_pow` 走范数，见 `err_tendsto_zero`）；
3. `Filter.Tendsto.smul_const` 把标量收敛搬成向量收敛。

**⚠ 前件 `|1-η| < 1` 是关于步长的条件；结论 `θ_n → x'` 是关于轨迹的。
二者由 §4 的闭式连接 —— 结论不在前件中。** -/
theorem tendsto_iter_id (η : ℝ) (hη : |1 - η| < 1) (x' θ : E) :
    Tendsto (fun n : ℕ => iterMap (ContinuousLinearMap.id ℝ E)
        (LinearMap.id : E →ₗ[ℝ] E) η x' n θ) atTop (nhds x') := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hfun : (fun n : ℕ =>
      ‖iterMap (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) η x' n θ - x'‖)
      = fun n : ℕ => |1 - η| ^ n * ‖θ - x'‖ := by
    funext n
    exact norm_iter_id_sub η x' θ n
  rw [hfun]
  have hbase : Tendsto (fun n : ℕ => |1 - η| ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) hη
  simpa using hbase.mul_const (‖θ - x'‖)

/-- ⭐⭐⭐ **【误差 `→ 0`，速率 `|1-η|^n`】**

$$\mathrm{err}\bigl(\theta_n\bigr) \;\longrightarrow\; 0 .$$

**证明**：`err_n = |1-η|^n · err_0`（§5 `err_iter_id`）与 `|1-η|^n → 0`。

**⭐ 与 1 维完全相同的速率**：指数因子逐字是 `|1-η|^n`。 -/
theorem err_tendsto_zero (η : ℝ) (hη : |1 - η| < 1) (x' θ : E) :
    Tendsto (fun n : ℕ => errA (ContinuousLinearMap.id ℝ E) x' (iterMap
        (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) η x' n θ))
      atTop (nhds 0) := by
  have hfun : (fun n : ℕ => errA (ContinuousLinearMap.id ℝ E) x' (iterMap
      (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) η x' n θ))
      = fun n : ℕ => |1 - η| ^ n * errA (ContinuousLinearMap.id ℝ E) x' θ := by
    funext n
    exact err_iter_id η x' θ n
  rw [hfun]
  have hbase : Tendsto (fun n : ℕ => |1 - η| ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) hη
  simpa using hbase.mul_const (errA (ContinuousLinearMap.id ℝ E) x' θ)

/-- ⭐⭐⭐ **【极限唯一：任何极限点都等于 `x'`】**

若 `θ_n → y` 且 `θ_n → x'`，则 `y = x'`。**这就是「收敛到唯一参数」的字面形式。**

**证明**：`tendsto_nhds_unique`（`ℝ^d` 是 `T2Space`）。

**⚠ 前件给了两条收敛；结论是两条极限**相等** —— 这不是同义反复：
「唯一」说的是**任何**收敛点都被钉到同一个值，而 `T2` 分离性必须被调用。 -/
theorem tendsto_unique_limit {η : ℝ} {x' θ : E} {y : E}
    (hy : Tendsto (fun n : ℕ => iterMap (ContinuousLinearMap.id ℝ E)
        (LinearMap.id : E →ₗ[ℝ] E) η x' n θ) atTop (nhds y))
    (hη : |1 - η| < 1) : y = x' :=
  tendsto_nhds_unique hy (tendsto_iter_id η hη x' θ)

/-- ⭐⭐⭐ **【版本 2 总汇：唯一最优 + 收敛 + 速率，三者同条】**

设 `|1 - η| < 1`。则**同时**成立：

(a) **唯一最优参数**：`∃! θ, A θ = x'`（§6）；
(b) **收敛**：`θ_n → x'`（§7）；
(c) **速率**：`err_n = |1-η|^n · err_0`（§5），且 `err_n → 0`。

**⭐ 这是本文件对 DD3 的**正面回答**：
「版本 2 的 `n` 维版本：证明与 1 维**同样的**唯一性与收敛」——
(a) 是唯一性，(b) 是收敛，(c) 是**与 1 维逐字相同**的速率。

**⚠ 前件只有 `|1-η| < 1`（步长窗）；三条结论都不在前件中。** -/
theorem converge_to_optimal_nd (η : ℝ) (hη : |1 - η| < 1) (x' θ : E) :
    (∃! θ' : E, (ContinuousLinearMap.id ℝ E) θ' = x')
    ∧ Tendsto (fun n : ℕ => iterMap (ContinuousLinearMap.id ℝ E)
        (LinearMap.id : E →ₗ[ℝ] E) η x' n θ) atTop (nhds x')
    ∧ (∀ n : ℕ, errA (ContinuousLinearMap.id ℝ E) x' (iterMap
        (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) η x' n θ)
        = |1 - η| ^ n * errA (ContinuousLinearMap.id ℝ E) x' θ)
    ∧ Tendsto (fun n : ℕ => errA (ContinuousLinearMap.id ℝ E) x' (iterMap
        (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E) η x' n θ))
      atTop (nhds 0) :=
  ⟨optimal_exists_unique x', tendsto_iter_id η hη x' θ,
   fun n => err_iter_id η x' θ n, err_tendsto_zero η hη x' θ⟩

/-- ⭐⭐ **单调下降**：收缩窗内 `n` 步后误差**不增**。

**证明**：`err_n = |1-η|^n err_0`，`|1-η|^n ≤ 1`，`err_0 ≥ 0`。 -/
theorem err_iter_le (η : ℝ) (hη : |1 - η| ≤ 1) (x' θ : E) (n : ℕ) :
    errA (ContinuousLinearMap.id ℝ E) x' (iterMap (ContinuousLinearMap.id ℝ E)
        (LinearMap.id : E →ₗ[ℝ] E) η x' n θ)
      ≤ errA (ContinuousLinearMap.id ℝ E) x' θ := by
  rw [err_iter_id]
  have hpow : |1 - η| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) hη
  have hnn : 0 ≤ errA (ContinuousLinearMap.id ℝ E) x' θ := errA_nonneg _ _ _
  calc |1 - η| ^ n * errA (ContinuousLinearMap.id ℝ E) x' θ
      ≤ 1 * errA (ContinuousLinearMap.id ℝ E) x' θ :=
        mul_le_mul_of_nonneg_right hpow hnn
    _ = errA (ContinuousLinearMap.id ℝ E) x' θ := one_mul _

/-- ⭐⭐ **严格下降**：`|1-η| < 1`、`err_0 > 0`、`n ≥ 1` ⟹ `err_n < err_0`。 -/
theorem err_iter_lt (η : ℝ) (hη : |1 - η| < 1) (x' θ : E)
    (hpos : 0 < errA (ContinuousLinearMap.id ℝ E) x' θ) {n : ℕ} (hn : 0 < n) :
    errA (ContinuousLinearMap.id ℝ E) x' (iterMap (ContinuousLinearMap.id ℝ E)
        (LinearMap.id : E →ₗ[ℝ] E) η x' n θ)
      < errA (ContinuousLinearMap.id ℝ E) x' θ := by
  rw [err_iter_id]
  have hlt : |1 - η| ^ n < 1 :=
    pow_lt_one₀ (abs_nonneg _) hη (Nat.pos_iff_ne_zero.mp hn)
  have := mul_lt_mul_of_pos_right hlt hpos
  simpa using this

end Converge

/-! ===========================================================================
    §8  ⭐⭐⭐ **速率与空间维数无关**（DD3 的正面要求：与 1 维相同，`|1-η|^n`）
    =========================================================================== -/

section DimIndep

/-- ⭐⭐⭐⭐ **【DD3 主结论 C：`d₁` 维与 `d₂` 维的速率比例**相同**】**

在 `A = φ = id` 的**任意**两个维数 `d₁`、`d₂` 上，`n` 步后的误差与**各自**初始误差之比
是**同一个实数** `|1-η|^n`：

$$\frac{\mathrm{err}^{(d_1)}_n}{\mathrm{err}^{(d_1)}_0}
 = \frac{\mathrm{err}^{(d_2)}_n}{\mathrm{err}^{(d_2)}_0}
 = |1-\eta|^{\,n}\qquad (\mathrm{err}_0 \ne 0).$$

**⭐ 这就是任务书「`n` 维收敛速率应与 1 维相同，都是 `|1-η|^n`」的形式化**：
取 `d₁ = d`（`n` 维）、`d₂ = 1`（1 维），即得「`d` 维与 1 维同速率」。

**证明**：在两个维数上分别引用 §5 的 `err_iter_id`（对 `E = State d₁` 与
`E = State d₂` 各一次），两次结果的因子均为 `|1 - η| ^ n`，故两比例相等。

**⚠ 这不是同义反复**：`err_iter_id` 是**证出**的（§4 闭式 + §5 范数化简），
本定理把**两个不同载体**上的结论的**公共比例**提取出来 —— 结论（两个比例相等）
不从前件得到，而由两次引用同一引理得到。 -/
theorem rate_dim_indep (d₁ d₂ : ℕ) (η : ℝ) (x₁' θ₁ : State d₁) (x₂' θ₂ : State d₂)
    (n : ℕ)
    (h₁ : errA (ContinuousLinearMap.id ℝ (State d₁)) x₁' θ₁ ≠ 0)
    (h₂ : errA (ContinuousLinearMap.id ℝ (State d₂)) x₂' θ₂ ≠ 0) :
    errA (ContinuousLinearMap.id ℝ (State d₁)) x₁' (iterMap
        (ContinuousLinearMap.id ℝ (State d₁)) (LinearMap.id : State d₁ →ₗ[ℝ] State d₁)
        η x₁' n θ₁) / errA (ContinuousLinearMap.id ℝ (State d₁)) x₁' θ₁
      = errA (ContinuousLinearMap.id ℝ (State d₂)) x₂' (iterMap
        (ContinuousLinearMap.id ℝ (State d₂)) (LinearMap.id : State d₂ →ₗ[ℝ] State d₂)
        η x₂' n θ₂) / errA (ContinuousLinearMap.id ℝ (State d₂)) x₂' θ₂ := by
  rw [err_iter_id, err_iter_id, mul_div_cancel_right₀ _ h₁, mul_div_cancel_right₀ _ h₂]

/-- ⭐⭐⭐⭐ **【DD3 主结论 C′：两个维数的误差因子都等于 `|1-η|^n`（无条件版）】**

$$\frac{\mathrm{err}^{(d_1)}_n}{\mathrm{err}^{(d_1)}_0}\cdot \mathrm{err}^{(d_1)}_0
 = |1-\eta|^n\cdot\mathrm{err}^{(d_1)}_0 .$$

更直接地：两个维数的 `err_n` **除以各自 `err_0` 后**都是 `|1-η|^n`。
本定理给出**无除法**的乘式版本（避免 `err_0 = 0` 的退化讨论）：

$$\mathrm{err}^{(d_1)}_n \cdot \mathrm{err}^{(d_2)}_0
  = \mathrm{err}^{(d_2)}_n \cdot \mathrm{err}^{(d_1)}_0 .$$

**⭐ 读法**：「维度不改变速率」的精确内容是**比例相等**：
`err_n/err_0` 在两个维数上相同。这就是「`n` 维速率 = 1 维速率」。 -/
theorem rate_ratio_eq (d₁ d₂ : ℕ) (η : ℝ) (x₁' θ₁ : State d₁) (x₂' θ₂ : State d₂)
    (n : ℕ) :
    errA (ContinuousLinearMap.id ℝ (State d₁)) x₁' (iterMap
        (ContinuousLinearMap.id ℝ (State d₁)) (LinearMap.id : State d₁ →ₗ[ℝ] State d₁)
        η x₁' n θ₁) * errA (ContinuousLinearMap.id ℝ (State d₂)) x₂' θ₂
      = errA (ContinuousLinearMap.id ℝ (State d₂)) x₂' (iterMap
        (ContinuousLinearMap.id ℝ (State d₂)) (LinearMap.id : State d₂ →ₗ[ℝ] State d₂)
        η x₂' n θ₂) * errA (ContinuousLinearMap.id ℝ (State d₁)) x₁' θ₁ := by
  rw [err_iter_id, err_iter_id]
  ring

/-- ⭐⭐⭐ **【速率对任意维数都是 `c(η)^n`：`OptimalEta` 引擎在 `ℝ^d` 上适用】**

对**任意** `d`，`err_n = OptimalEta.c η ^ n · err_0`。

**⭐ 意义**：`OptimalEta` 的最优性结论（`η = 1` 唯一最优、`η ≠ 1` 严格更慢）
**与维数无关**地成立 —— 本定理是这条**迁移**的接口。 -/
theorem rate_is_c_pow_all_dims (d : ℕ) (η : ℝ) (x' θ : State d) (n : ℕ) :
    errA (ContinuousLinearMap.id ℝ (State d)) x' (iterMap
        (ContinuousLinearMap.id ℝ (State d)) (LinearMap.id : State d →ₗ[ℝ] State d)
        η x' n θ)
      = OptimalEta.c η ^ n * errA (ContinuousLinearMap.id ℝ (State d)) x' θ :=
  err_iter_id_c_pow η x' θ n

/-- ⭐⭐⭐ **【`η = 1` 的速率在任意维数都取到最小 `0`】**

$$\forall d,\ \forall \eta:\quad |1-1|^n \le |1-\eta|^n \quad (n \ge 1),$$

且 `|1-1|^n = 0`。**即：最优步长 `η = 1` 在 `ℝ^d` 上（`d` 任意）都应选它。**

**证明**：直接引用 `OptimalEta.c_one_le` / `c_pow_mono`，与维数**无关**。 -/
theorem optimal_eta_all_dims (η : ℝ) {n : ℕ} (hn : 0 < n) :
    |1 - (1 : ℝ)| ^ n ≤ |1 - η| ^ n ∧ |1 - (1 : ℝ)| ^ n = 0 := by
  refine ⟨?_, ?_⟩
  · rw [FateV2.Loop.ConvergenceOptimal.abs_one_sub_eq_c 1,
      FateV2.Loop.ConvergenceOptimal.abs_one_sub_eq_c η]
    exact OptimalEta.c_pow_mono (OptimalEta.c_nonneg 1) (OptimalEta.c_one_le η) n
  · rw [show |1 - (1 : ℝ)| = 0 from by norm_num,
      zero_pow (Nat.pos_iff_ne_zero.mp hn)]

end DimIndep

/-! ===========================================================================
    §9  ⭐⭐ **`η = 1` 一步归零，且「归零」恰刻画 `η = 1`**
    =========================================================================== -/

section OneStepZero

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- ⭐⭐ **【`η = 1`：一步归零】** `err_1(1) = 0`。

**证明**：§5 给 `err_1 = |1-1|^1 · err_0 = 0 · err_0 = 0`。 -/
theorem err_one_step_zero (x' θ : E) :
    errA (ContinuousLinearMap.id ℝ E) x' (iterMap (ContinuousLinearMap.id ℝ E)
        (LinearMap.id : E →ₗ[ℝ] E) 1 x' 1 θ) = 0 := by
  rw [err_iter_id]
  norm_num

/-- ⭐⭐⭐ **【归零 ⟺ `η = 1`】**：在 `err_0 > 0`、`n ≥ 1` 下

$$\mathrm{err}_n(\eta) = 0 \iff \eta = 1 .$$

**证明**：`err_n = |1-η|^n err_0`；`err_0 > 0` 时可除，得 `|1-η|^n = 0`，
即 `|1-η| = 0`，即 `η = 1`（`zero_pow` 需 `n ≥ 1`）。

**⭐ 意义**：这把「一步归零」的**独有性**从 1 维搬到任意维数 `ℝ^d`：
在 `ℝ^d` 上归零的步长**只有** `η = 1`，**与维数无关**。 -/
theorem err_zero_iff (η : ℝ) (x' θ : E)
    (hpos : 0 < errA (ContinuousLinearMap.id ℝ E) x' θ) {n : ℕ} (hn : 0 < n) :
    errA (ContinuousLinearMap.id ℝ E) x' (iterMap (ContinuousLinearMap.id ℝ E)
        (LinearMap.id : E →ₗ[ℝ] E) η x' n θ) = 0 ↔ η = 1 := by
  rw [err_iter_id]
  have hne : errA (ContinuousLinearMap.id ℝ E) x' θ ≠ 0 := ne_of_gt hpos
  constructor
  · intro h
    have hpow0 : |1 - η| ^ n = 0 := by
      rcases mul_eq_zero.mp h with h1 | h1
      · exact h1
      · exact absurd h1 hne
    have habs : |1 - η| = 0 :=
      (pow_eq_zero_iff (Nat.pos_iff_ne_zero.mp hn)).mp hpow0
    have hsub : (1 : ℝ) - η = 0 := abs_eq_zero.mp habs
    linarith
  · intro h
    subst h
    rw [show |1 - (1 : ℝ)| = 0 from by norm_num,
      zero_pow (Nat.pos_iff_ne_zero.mp hn), zero_mul]

end OneStepZero

/-! ===========================================================================
    §10  ⭐⭐ **具体数值实例（`d = 2`，可逐字复核）**
    =========================================================================== -/

section Concrete

/-- ⭐ **`d = 2` 的初始参数**：`θ_0 = (3, 0)`，即 `EuclideanSpace.single 0 3`，范数 `3`。 -/
noncomputable def theta0 : State 2 := EuclideanSpace.single (0 : Fin 2) (3 : ℝ)

/-- ⭐⭐ **初始误差 `err_0 = 3`**（`x' = 0`）。 -/
theorem concrete_err0 :
    errA (ContinuousLinearMap.id ℝ (State 2)) 0 theta0 = 3 := by
  rw [errA_id]
  simp [theta0, sub_zero, EuclideanSpace.norm_single]

/-- ⭐⭐ **`η = 1/2`、`n = 1`（一步）**：`err_1 = (1/2)^1 · 3 = 3/2`。 -/
theorem concrete_err_one :
    errA (ContinuousLinearMap.id ℝ (State 2)) 0 (iterMap
        (ContinuousLinearMap.id ℝ (State 2)) (LinearMap.id : State 2 →ₗ[ℝ] State 2)
        (1 / 2) 0 1 theta0) = (1 / 2) ^ 1 * 3 := by
  rw [err_iter_id, concrete_err0]
  norm_num

/-- ⭐⭐ **`η = 1/2`、`n = 2`（两步）**：`err_2 = (1/2)^2 · 3 = 3/4`。

**⭐ 这与 1 维（`E = F = ℝ`）的速率**逐字相同**：指数因子都是 `(1/2)^n`。 -/
theorem concrete_err_two :
    errA (ContinuousLinearMap.id ℝ (State 2)) 0 (iterMap
        (ContinuousLinearMap.id ℝ (State 2)) (LinearMap.id : State 2 →ₗ[ℝ] State 2)
        (1 / 2) 0 2 theta0) = (1 / 2) ^ 2 * 3 := by
  rw [err_iter_id, concrete_err0]
  norm_num

/-- ⭐⭐⭐ **【`d = 2` 与 1 维的速率逐字相同——具体数值版】**

`ℝ^2` 上（`θ_0 = (3,0)`，`x' = 0`）与 `ℝ` 上（`θ_0 = 3`，`x' = 0`）在 `η = 1/2`、
两步后，**误差比例完全相同** `= (1/2)^2`。

**⭐ 这就是任务书「`n` 维下的收敛速率应与 1 维相同，都是 `|1-η|^n`」的
**可计算见证**（把 `rate_dim_indep` 在两维数上取 `n = 2` 的具体数值）。 -/
theorem concrete_dim2_eq_dim1 :
    errA (ContinuousLinearMap.id ℝ (State 2)) 0 (iterMap
        (ContinuousLinearMap.id ℝ (State 2)) (LinearMap.id : State 2 →ₗ[ℝ] State 2)
        (1 / 2) 0 2 theta0) / 3
      = errA (ContinuousLinearMap.id ℝ ℝ) 0 (iterMap
        (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
        (1 / 2) 0 2 3) / 3 := by
  rw [concrete_err_two, err_iter_id]
  norm_num [errA]

/-- ⭐⭐ **`d = 2`、`η = 1`：一步归零**（速率 `|1-1|^1 = 0`）。 -/
theorem concrete_eta_one_zero :
    errA (ContinuousLinearMap.id ℝ (State 2)) 0 (iterMap
        (ContinuousLinearMap.id ℝ (State 2)) (LinearMap.id : State 2 →ₗ[ℝ] State 2)
        1 0 1 theta0) = 0 :=
  err_one_step_zero 0 theta0

/-- ⭐⭐ **`d = 2`、`η = 1`：轨迹从第 1 步起恒等于唯一最优参数 `x' = 0`**。 -/
theorem concrete_eta_one_traj :
    iterMap (ContinuousLinearMap.id ℝ (State 2)) (LinearMap.id : State 2 →ₗ[ℝ] State 2)
      1 0 1 theta0 = 0 :=
  iter_id_eq_optimal_of_eta_one rfl 0 theta0 (by norm_num)

end Concrete

/-! ===========================================================================
    §11  ⚠ **诚实边界（本文件**不**做的事）**
    =========================================================================== -/

/-!
### §11.1 本文件做了什么（与 DD3 任务书逐条对照）

| DD3 要求 | 本文件落点 | 状态 |
|---|---|---|
| `E = F = ℝ^n` | `State d := EuclideanSpace ℝ (Fin d)`（§1） | ✅ |
| `A = φ = id` | `Aid`、`phid`（§1），`corrects_id`、`phi_injective_id`（§2） | ✅ |
| **同样的唯一性** | `optimal_exists_unique`、`optimal_iff`（§6） | ✅ |
| **同样的收敛** | `tendsto_iter_id`、`err_tendsto_zero`、`tendsto_unique_limit`（§7） | ✅ |
| **速率 `\|1-η\|^n`，与 1 维相同** | `err_iter_id`（§5）、`rate_dim_indep` / `rate_ratio_eq` / `rate_is_c_pow_all_dims` / `optimal_eta_all_dims`（§8）、`concrete_dim2_eq_dim1`（§10）| ✅ |

### §11.2 本文件**不**做的事（如实登记，非删减项）

| # | 未做项 | 为何未做 |
|---|---|---|
| 1 | **一般 `A`、`φ`（非恒等）的唯一最优参数** | 需 `φ` 单射 **且** `A` 的核条件；DD3 明确指定 `A = φ = id`。`T1Verify` 已给出「`φ` 单射 ⟺ 不动点即最优」的**一般**版本；本文件不重复 |
| 2 | **`φ` 退化时的多解刻画** | 属版本 1 的 `T1MultiDim`（歧义子空间 `amb`）范围；本文件 `φ = id` 时 `ker φ = ⊥`，退化**不存在** |
| 3 | **非线性载体上的唯一极限** | 承 `WiringConvergence §8.3`：残差语义不同，非恒等时无法逐值对齐 |
| 4 | **噪声/随机版**（期望收敛） | 确定性框架，无测度结构 |
| 5 | **变步长 `η_k` 的收敛** | 需 `err_k = ∏ c(η_k)`，是另一问题；`OptimalEta §9.2` 已登记 |

### §11.3 「与 1 维相同」这句话的**精确**含义（防误读）

* **相同的是「关于步数的衰减律」**：`err_n = |1-η|^n · err_0`，指数底 `|1-η|`、
  指数 **步数 `n`**，**不**含空间维数 `d`。
* **不**是「不同维数的误差绝对值相同」：`err_0` 依维数与初值而变
  （§8 `rate_dim_indep` 因此比较的是**比例** `err_n / err_0`，不是绝对值）。
* `η = 1` 的**一步归零**与「归零 ⟺ `η = 1`」也与 `d` 无关（§9）。

### §11.4 前件自查（无同义反复，最终表）

| 定理 | 前件 | 结论 | 前后件是否循环 |
|---|---|---|---|
| `iter_id_sub` | 无 | `θ_n - x' = (1-η)^n • (θ₀-x')` | 否 |
| `norm_iter_id_sub` | 无 | `‖θ_n - x'‖ = |1-η|^n ‖θ₀-x'‖` | 否 |
| `err_iter_id` | 无 | `err_n = |1-η|^n err_0` | 否 |
| `optimal_exists_unique` | 无 | `∃! θ, A θ = x'` | 否 |
| `tendsto_iter_id` | `|1-η| < 1`（步长）| `θ_n → x'`（轨迹）| 否（经 `iter_id_sub`）|
| `tendsto_unique_limit` | 两条收敛 + `|1-η| < 1` | 两极限相等 | 否（用 `T2` 分离）|
| `err_zero_iff` | `err_0 > 0`、`n ≥ 1` | `err_n(η)=0 ↔ η=1` | 否 |
| `converge_to_optimal_nd` | `|1-η| < 1` | 唯一性 + 收敛 + 速率 + `→0` | 否 |
| `rate_dim_indep` | `err_0 ≠ 0`（两个维数各一）| 两比例相等 | 否 |

**⚠ 无 `sorry` / `admit` / `axiom` / `True := trivial`。**
**⚠ 本文件无删减项**：§1–§10 所有陈述定理均已证出。

-/

/-! ===========================================================================
    § R35  ⭐ 接入通用版本 2 框架（`Fate.TwoVersions`）
    ===========================================================================

本文件的 `iterMap (id) (id)` 迭代，与 `Fate.TwoVersions.BoundWriteBackV2.wbSeq`
（通用 `A / φ`）在 `A = φ = id` 上逐字一致（`wbSeq_eq_iterMap_gen`）。
本节把本文件的收敛主定理（`tendsto_iter_id`）接到通用版本 2 的框架上，
给出**通用 `wbSeq` 形态**的同一收敛，并验证两条路径的极限相合。

**⚠ 无同义反复**：`version2_main_id_gen` 的前件是步长窗 `|1-η| < 1`，
结论是轨迹 `wbSeq → x'`；连接靠 `wbSeq_eq_iterMap_gen`（定义性），
结论不在前件中。
    =========================================================================== -/

section R35Version2Link

open FateV2.Loop.BoundWriteBack

/-- ⭐⭐ **【通用 `wbSeq` 形态的收敛】**：版本 2 的迭代在 `A = φ = id` 上收敛到 `x'`。

直接消费本文件 §7 的 `tendsto_iter_id`，经 `wbSeq_eq_iterMap_gen` 搬到 `wbSeq`。 -/
theorem version2_main_id_gen {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℝ) (hη : |1 - η| < 1) (x' θ₀ : E) :
    Tendsto (BoundWriteBackV2.wbSeq (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E)
      η x' θ₀) atTop (nhds x') := by
  apply BoundWriteBackV2.wbSeq_tendsto_of_iterMap_tendsto
  exact tendsto_iter_id η hη x' θ₀

/-- ⭐ `thetaStar id id x' θ₀ = x'`（纯代数，无步长前件）。 -/
theorem thetaStar_id_eq {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x' θ₀ : E) :
    BoundWriteBackV2.thetaStar (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E)
      x' θ₀ = x' := by
  unfold BoundWriteBackV2.thetaStar
  simp

/-- ⭐⭐ **【两条极限路径相合】**：通用版本 2 的极限 `thetaStar` 与
本文件给出的最优参数 `x'` 一致 —— `wbSeq` 收敛到 `thetaStar = x'`。 -/
theorem version2_limit_eq_optimal_id_gen {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℝ) (hη : |1 - η| < 1) (x' θ₀ : E) :
    Tendsto (BoundWriteBackV2.wbSeq (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E)
      η x' θ₀) atTop
      (nhds (BoundWriteBackV2.thetaStar (ContinuousLinearMap.id ℝ E)
        (LinearMap.id : E →ₗ[ℝ] E) x' θ₀)) := by
  rw [thetaStar_id_eq]
  exact version2_main_id_gen η hη x' θ₀

/-- ⭐ `wbSeq` 形态的误差闭式：`err(wbSeq_n) = |1-η|^n err_0`。

跨桥 `wbSeq_eq_iterMap_gen` 搬运本文件 §6 的 `err_iter_id`。 -/
theorem err_wbSeq_id_gen {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℝ) (x' θ₀ : E) (n : ℕ) :
    errA (ContinuousLinearMap.id ℝ E) x'
        (BoundWriteBackV2.wbSeq (ContinuousLinearMap.id ℝ E) (LinearMap.id : E →ₗ[ℝ] E)
          η x' θ₀ n) =
      |1 - η| ^ n * errA (ContinuousLinearMap.id ℝ E) x' θ₀ := by
  rw [BoundWriteBackV2.wbSeq_eq_iterMap_gen]
  exact err_iter_id η x' θ₀ n

end R35Version2Link

end ConvergeToOptimalND

end FateV2.Loop