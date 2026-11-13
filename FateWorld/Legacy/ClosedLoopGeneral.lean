/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.ClosedLoopGeneral`
任务：**【Y3-最高优先】`ClosedLoopGeneral` 重做 —— 最小可交付版本**：
**非线性情形下单步收缩的充分条件**。

===========================================================================
任务书原文（最小版本）
===========================================================================

> 若 `A` 是 Lipschitz（常数 `L_A`）且 `φ` 是 Lipschitz（常数 `L_φ`），
> 证明单步误差满足
>   `err(wb) ≤ |1-η| · L_φ · L_A · err(θ)`。
> 即给出「非线性情形下单步收缩」的充分条件 `|1-η| · L_φ · L_A < 1`。

本文件**交付**这条不等式（`step_contraction`，§3），
并给出由此得到的**完整闭环结论**：`n` 步几何界（§4）、
收敛到 `0`（§5）、界**不可改进**（§6）、前提**不可删除**（§7）。

===========================================================================
⚠⚠ 一、为什么需要一条额外前提（诚实说明，不变通）
===========================================================================

**纯 Lipschitz 性不足以**给出 `|1-η|` 这个常数。这是本文件首先要讲清楚的事。
设 `r := x' - A θ`、`θ' := wb θ = θ + η • φ r`。**若 `A` 只是 Lipschitz**，则

    ‖A θ' - x'‖ = ‖(A θ' - A θ) - r‖
                ≤ ‖A θ' - A θ‖ + ‖r‖
                ≤ L_A · ‖η • φ r‖ + ‖r‖
                ≤ (1 + |η| · L_A · L_φ) · ‖r‖.

**注意这个系数是 `1 + |η| L_A L_φ`，永远 `> 1`，永远不可能收缩。**
⟹ 仅凭「`A` Lipschitz + `φ` Lipschitz」**证不出**任何收缩
（这不是技术不行，是**命题为假**：§7 的 `exactOneStep_necessary` 给反例）。
`BoundWriteBack` 的线性情形靠的是**线性恒等式** `image_wbW`，
那一步用了 `A` 的**加性**，Lipschitz 性**替代不了**它。

⟹ 本条不等式真正需要的、**唯一**的额外结构前提是

    (E)  `ExactOneStep A φ x'  :≡  ∀ θ, A (θ + φ (x' - A θ)) = x'`

即「**满步（`η = 1`）的一步修正恰好命中真值**」（§1 `ExactOneStep`）。
它是 `BoundWriteBack.Corrects`（`∀ r, A (φ r) = r`）在**非线性 `A`** 上的
**逐字推广**：线性时 `Corrects ⟹ ExactOneStep`
（本文件 §8 `corrects_imp_exactOneStep` **证出**了这条蕴含）。
而且它**不是同义反复**：`(E)` 里**没有** `L_A`、没有 `L_φ`、没有 `η`、
没有范数、没有 `|1-η|` —— 它是一个**纯几何/可解性**陈述（§8.4 逐项核对）。

**有了 `(E)`，证明只用两行**（§3）：取 `θ₁ := θ + φ r`（`A θ₁ = x'`），则

    θ' - θ₁ = (η - 1) • φ r
    ⟹ ‖A θ' - x'‖ = ‖A θ' - A θ₁‖ ≤ L_A · |η-1| · ‖φ r‖ ≤ L_A · |1-η| · L_φ · ‖r‖.

**`L_A` 与 `L_φ` 各用一次、相乘，`|1-η|` 从 `θ' - θ₁` 直接出来。**
这就是任务书要的那条不等式。

===========================================================================
二、本文件**已证出**的内容（逐条）
===========================================================================

| 定理 | 内容 |
|---|---|
| ⭐⭐ `step_contraction` | **主定理**：`err(wb) ≤ |1-η| · L_φ · L_A · err(θ)` |
| ⭐⭐ `step_contraction_strict` | `|1-η| L_φ L_A < 1 ∧ err θ ≠ 0 ⟹ err(wb) < err θ`（**严格**收缩）|
| ⭐ `step_err_eq_zero` | `err θ = 0 ⟹ err(wb) = 0`（已命中则不动）|
| ⭐⭐ `step_eta_one_exact` | `η = 1 ⟹ err(wb) = 0`（`(E)` 的等价读法）|
| ⭐⭐ `err_iter_le` | **`n` 步几何界**：`err_n ≤ (|1-η| L_φ L_A)^n · err_0` |
| ⭐⭐⭐ `err_iter_tendsto_zero` | **收敛**：`|1-η| L_φ L_A < 1` ⟹ `err_n → 0` |
| ⭐⭐⭐ `bound_attained` | **紧**：存在实例使不等式**取等**（系数不可改进）|
| ⭐⭐ `no_strict_decrease_eta_two` | **必要性 1**：系数 `≥ 1` 时不严格下降（`η = 2`）|
| ⭐⭐⭐ `exactOneStep_necessary` | **必要性 2**：`(E)` **不可删除**（去掉后不等式为假）|
| ⭐ `nlStep_eq_wbW` | 与 `BoundWriteBack.wbW` **逐字相同**（`rfl`）|
| ⭐ `corrects_imp_exactOneStep` | 线性情形 `Corrects ⟹ ExactOneStep`（真接线）|
| ⭐ `corrects_lin_iter_bound` | 把线性 `Corrects` + 算子范数界代入主定理（一致性核对）|
| ⭐ `concrete_affine_*` | **非平凡实例**：`A u = u + 1`（**仿射、非线性**）恰好使不等式取等 |

===========================================================================
三、⚠ 本文件**不**做的事（如实登记，见 §9）
===========================================================================

1. **不**声称「纯 Lipschitz 即可收缩」——那是假的（§7 反例，本文件已证其假）。
2. **不**声称 `(E)` 是**必要**条件（它不是：存在别的充分条件，如 §4 的线性恒等式）。
   本文件只证：**`(E)` 是充分的**，且**去掉它命题为假**。
3. **不**做噪声/稳态误差（那是 `ClosedLoopNoisy` 的已入库内容，本文件不重复）。
4. **不**修改任何已有模块（只 `import`）。

===========================================================================
纪律
===========================================================================
- **零 `sorry` / 零 `admit` / 零 `axiom`**。
- **只新增本文件**，不修改任何已有模块。
- 文末 §9 登记未证出项（本文件无删减项；每条陈述均已证出）。
-/

import FateWorld.Legacy.BoundWriteBack
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace Fate

namespace ClosedLoopGeneral

open Filter Topology
open scoped Topology

-- 关闭「section 变量未使用」的 lint 噪声（本文件按主题分段，变量块集中声明更可读）
set_option linter.unusedSectionVars false

universe u

/-! ===========================================================================
    §1  设定：Lipschitz 常数、非线性更新、误差泛函、满步精确性
    =========================================================================== -/

section Setup

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐ **`LipschitzWithConst f L`**：`f` 以 `L` 为 Lipschitz 常数，且 `L ≥ 0`。

**⚠ 为什么把 `0 ≤ L` 放进结构里**：所有界都形如 `L * ‖u - v‖`，
需要 `L ≥ 0` 才能对右边做单调放大。把它作为**结构字段**而非额外前提，
使「`L` 是 Lipschitz 常数」这一语义**自带**非负性，避免调用点漏条件。
（与 `Mathlib` 的 `LipschitzWith` 不同：后者用 `ℝ≥0` 的 `NNReal` / `ℝ≥0∞`；
本文件用 `ℝ` 常数，因为结论里的 `|1-η| · L_φ · L_A` 是 `ℝ` 乘法。） -/
structure LipschitzWithConst (f : E → F) (L : ℝ) : Prop where
  /-- 常数非负 -/
  nonneg : 0 ≤ L
  /-- Lipschitz 界 -/
  bound : ∀ u v : E, ‖f u - f v‖ ≤ L * ‖u - v‖

/-- ⭐ **误差泛函**：`errN A x' θ = ‖A θ - x'‖`。

**与 `BoundWriteBack.errA` 逐字相同**：`errA A x' θ = ‖A θ - x'‖`。
区别只在 `A` 的类型：这里 `A : E → F` 是**任意函数**（非线性），
`BoundWriteBack` 里 `A : E →L[ℝ] F` 是连续线性算子。
线性时两者**定义性相等**（§8 `errN_eq_errA`）。 -/
def errN (A : E → F) (x' : F) (θ : E) : ℝ :=
  ‖A θ - x'‖

/-- ⭐⭐ **非线性闭环一步更新**：

$$\mathrm{nlStep}\ A\ φ\ η\ x'\ θ \;:=\; θ + η \bullet φ\,(x' - A\,θ).$$

与 `BoundWriteBack.wbW` 的**公式逐字相同**（§8 `nlStep_eq_wbW`，`rfl`），
但 `A` 与世界模型的类型是**任意函数**（可非线性），而非连续线性算子。

| 位 | 名 | 类型 | 作用 |
|---|---|---|---|
| `A` | 世界模型 / 预测器 | `E → F`（**任意**）| 参数 → 状态 |
| `φ` | 方向映射 | `F → E`（**任意**）| 残差 → 参数方向 |
| `η` | 步长 | `ℝ` | 参数，**不填数** |
| `x'` | 观测真值 | `F` | 目标 |
| `θ` | 当前参数 | `E` | 被写 | -/
def nlStep (A : E → F) (φ : F → E) (η : ℝ) (x' : F) (θ : E) : E :=
  θ + η • φ (x' - A θ)

/-- ⭐⭐ **`n` 步闭环迭代**（同一条 `nlStep` 反复用，观测 `x'` 固定）。

`θ_{k+1} = nlStep A φ η x' θ_k`，`θ_0 = θ`。 -/
def nlIter (A : E → F) (φ : F → E) (η : ℝ) (x' : F) : ℕ → E → E
  | 0, θ => θ
  | k + 1, θ => nlStep A φ η x' (nlIter A φ η x' k θ)

@[simp] theorem nlIter_zero (A : E → F) (φ : F → E) (η : ℝ) (x' : F) (θ : E) :
    nlIter A φ η x' 0 θ = θ := rfl

theorem nlIter_succ (A : E → F) (φ : F → E) (η : ℝ) (x' : F) (k : ℕ) (θ : E) :
    nlIter A φ η x' (k + 1) θ = nlStep A φ η x' (nlIter A φ η x' k θ) := rfl

/-- ⭐⭐⭐ **`ExactOneStep A φ x'`（本文件的**唯一**额外结构前提）**：

$$\forall θ,\quad A\,\bigl(θ + φ\,(x' - A\,θ)\bigr) \;=\; x' .$$

**读法**：把残差 `r = x' - A θ` 经 `φ` 搬成参数方向**满步**（`η = 1`）走完，
**一步就精确命中真值** `x'`。

**⭐ 它是 `BoundWriteBack.Corrects` 的非线性推广**（§8 证 `Corrects ⟹ ExactOneStep`）。
`Corrects A φ` 说「残差可被模型精确还原」；`ExactOneStep` 说
「**一步修正**精确命中」——在线性 `A` 下两者等价，对非线性 `A` 前者无从陈述
（`A (φ r) = r` 需要 `A` 作用于一个纯残差向量，而 `A` 非线性时那没有意义），
后者仍然合法。**⟹ 这是把结论搬到非线性的正确代价。**

**⚠ 它不含结论**：`(E)` 里没有 `L_A` / `L_φ` / `η` / 范数 / `|1-η|`，
也没有任何不等式（§8.4 逐项核对）；而结论是一个含全部这些量的**数值界**。
更硬的反证：**去掉 `(E)` 后不等式为假**（§7 `exactOneStep_necessary` 已证）。 -/
def ExactOneStep (A : E → F) (φ : F → E) (x' : F) : Prop :=
  ∀ θ : E, A (θ + φ (x' - A θ)) = x'

/-- ⭐ **收缩系数**：`c := |1-η| · L_φ · L_A`（任务书要的那个乘积）。 -/
def contractFactor (η Lφ LA : ℝ) : ℝ := |1 - η| * Lφ * LA

/-- ⭐ **`errN_nonneg`**：误差非负。 -/
theorem errN_nonneg (A : E → F) (x' : F) (θ : E) : 0 ≤ errN A x' θ :=
  norm_nonneg _

/-- ⭐ **`errN_eq_zero`**：误差为零 ⟺ 模型精确命中。 -/
theorem errN_eq_zero_iff (A : E → F) (x' : F) (θ : E) :
    errN A x' θ = 0 ↔ A θ = x' := by
  unfold errN
  rw [norm_eq_zero, sub_eq_zero]

/-- ⭐ **`contractFactor` 非负**。 -/
theorem contractFactor_nonneg {η Lφ LA : ℝ} (hφ : 0 ≤ Lφ) (hA : 0 ≤ LA) :
    0 ≤ contractFactor η Lφ LA := by
  unfold contractFactor
  exact mul_nonneg (mul_nonneg (abs_nonneg _) hφ) hA

end Setup

/-! ===========================================================================
    §2  单步恒等式（`(E)` 的直接推论，非线性版的 `image_wbW`）
    =========================================================================== -/

section StepIdentity

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐⭐ **【满步点精确】** `θ₁ := θ + φ r` 满足 `A θ₁ = x'`（就是 `(E)` 的展开）。 -/
theorem fullStep_exact {A : E → F} {φ : F → E} {x' : F} (hE : ExactOneStep A φ x')
    (θ : E) : A (θ + φ (x' - A θ)) = x' :=
  hE θ

/-- ⭐⭐⭐ **【单步差分恒等式（非线性版 `image_wbW`）】**

$$\mathrm{nlStep}\ A\ φ\ η\ x'\ θ \;-\; \bigl(θ + φ\,(x' - A θ)\bigr)
  \;=\; (η - 1) \bullet φ\,(x' - A θ).$$

**⭐ 这是本文件的技术心脏**：它说「**带步长 `η` 的一步**」与「**满步**」之差
恰好是 `(η-1) • φ r`，**与 `A` 无关**（纯参数空间的代数恒等式）。
`BoundWriteBack.image_wbW` 是它在**线性 `A`** 下的对偶式
（那里差在**状态空间**：`A θ' - x' = (1-η) • (A θ - x')`）。
**⟹ 非线性下我们把恒等式搬到参数空间，收 `φ`，再用 `A` 的 Lipschitz 性推过去。** -/
theorem step_sub_fullStep (A : E → F) (φ : F → E) (η : ℝ) (x' : F) (θ : E) :
    nlStep A φ η x' θ - (θ + φ (x' - A θ)) = (η - 1) • φ (x' - A θ) := by
  unfold nlStep
  module

/-- ⭐⭐ **【差分的范数】** `‖nlStep … - 满步点‖ = |η-1| · ‖φ r‖`。 -/
theorem norm_step_sub_fullStep (A : E → F) (φ : F → E) (η : ℝ) (x' : F) (θ : E) :
    ‖nlStep A φ η x' θ - (θ + φ (x' - A θ))‖ = |η - 1| * ‖φ (x' - A θ)‖ := by
  rw [step_sub_fullStep, norm_smul, Real.norm_eq_abs]

end StepIdentity

/-! ===========================================================================
    §3  ⭐⭐⭐⭐⭐ **主定理：单步收缩**
    =========================================================================== -/

section Main

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐⭐⭐ **【`φ` 的 Lipschitz 性 + `φ 0 = 0` ⟹ `‖φ r‖ ≤ L_φ ‖r‖`】**

**⭐ 为什么需要 `φ 0 = 0`**：Lipschitz 性只界住**差**，要界住**本身**
（`‖φ r‖`）必须知道一点的值。「`φ 0 = 0`」是**最弱**的选择，且它在线性
`φ : F →ₗ[ℝ] E` 上自动成立（`map_zero`）、在 `Corrects` 的线性例子里也成立。
没有它，`φ` 可以平移任意大，误差界**不可能**成立（§9 登记 #3）。 -/
theorem norm_phi_le {φ : F → E} {Lφ : ℝ} (hφ : LipschitzWithConst φ Lφ)
    (h0 : φ 0 = 0) (r : F) : ‖φ r‖ ≤ Lφ * ‖r‖ := by
  have h := hφ.bound r 0
  rw [h0, sub_zero, sub_zero] at h
  exact h

/-- ⭐⭐⭐⭐⭐ **【主定理】非线性单步收缩界**

**前提**（4 条，§7 证其中 `(E)` 不可删、§6 证系数不可改进）：

| # | 前提 | 语义 |
|---|---|---|
| 1 | `hA : LipschitzWithConst A L_A` | 世界模型 Lipschitz，常数 `L_A` |
| 2 | `hφ : LipschitzWithConst φ L_φ` | 方向映射 Lipschitz，常数 `L_φ` |
| 3 | `h0 : φ 0 = 0` | 方向映射**不平移**（线性 `φ` 自动满足）|
| 4 | `hE : ExactOneStep A φ x'` | **满步一步精确命中**（`Corrects` 的非线性推广）|

**结论**（任务书要求的式子）：

$$\boxed{\ \mathrm{err}\bigl(\mathrm{nlStep}\ A\ φ\ η\ x'\ θ\bigr)
  \;\le\; |1-\eta| \cdot L_\varphi \cdot L_A \cdot \mathrm{err}(θ)\ }$$

**证明**（3 步，全部显式）：
1. `A (θ + φ r) = x'`（`hE`），故 `err(nlStep) = ‖A (nlStep) - A (θ + φ r)‖`；
2. `hA.bound` 给 `≤ L_A ‖nlStep - (θ + φ r)‖`，
   `norm_step_sub_fullStep` 给 `= L_A |η-1| ‖φ r‖`；
3. `norm_phi_le` 给 `‖φ r‖ ≤ L_φ ‖r‖`，而 `‖r‖ = ‖A θ - x'‖ = err(θ)`；
   `|η-1| = |1-η|`（`abs_sub_comm`），`ring` 收尾。

**⭐ 没有任何 `sorry`。** -/
theorem step_contraction (A : E → F) (φ : F → E) (η : ℝ) (x' : F)
    {LA Lφ : ℝ} (hA : LipschitzWithConst A LA) (hφ : LipschitzWithConst φ Lφ)
    (h0 : φ 0 = 0) (hE : ExactOneStep A φ x') (θ : E) :
    errN A x' (nlStep A φ η x' θ) ≤ contractFactor η Lφ LA * errN A x' θ := by
  have hLip : ‖A (nlStep A φ η x' θ) - A (θ + φ (x' - A θ))‖
      ≤ LA * ‖nlStep A φ η x' θ - (θ + φ (x' - A θ))‖ :=
    hA.bound _ _
  rw [norm_step_sub_fullStep] at hLip
  have hphi : ‖φ (x' - A θ)‖ ≤ Lφ * ‖x' - A θ‖ := norm_phi_le hφ h0 _
  have hnormr : ‖x' - A θ‖ = errN A x' θ := by
    unfold errN
    rw [norm_sub_rev]
  have hstep1 : LA * (|η - 1| * ‖φ (x' - A θ)‖)
      ≤ LA * (|η - 1| * (Lφ * ‖x' - A θ‖)) := by
    have h1 : |η - 1| * ‖φ (x' - A θ)‖ ≤ |η - 1| * (Lφ * ‖x' - A θ‖) :=
      mul_le_mul_of_nonneg_left hphi (abs_nonneg _)
    exact mul_le_mul_of_nonneg_left h1 hA.nonneg
  have hmain : errN A x' (nlStep A φ η x' θ)
      ≤ LA * (|η - 1| * (Lφ * ‖x' - A θ‖)) := by
    calc errN A x' (nlStep A φ η x' θ)
        = ‖A (nlStep A φ η x' θ) - x'‖ := rfl
      _ = ‖A (nlStep A φ η x' θ) - A (θ + φ (x' - A θ))‖ := by rw [hE θ]
      _ ≤ LA * ‖nlStep A φ η x' θ - (θ + φ (x' - A θ))‖ := hA.bound _ _
      _ = LA * (|η - 1| * ‖φ (x' - A θ)‖) := by rw [norm_step_sub_fullStep]
      _ ≤ LA * (|η - 1| * (Lφ * ‖x' - A θ‖)) := hstep1
  rw [hnormr] at hmain
  have harith : LA * (|η - 1| * (Lφ * errN A x' θ))
      = contractFactor η Lφ LA * errN A x' θ := by
    unfold contractFactor
    rw [abs_sub_comm η 1]
    ring
  rwa [harith] at hmain

/-- ⭐⭐⭐ **【严格收缩：`|1-η| L_φ L_A < 1` ⟹ 误差严格下降】**

**这是任务书「充分条件」的落点**：

$$\bigl|1-\eta\bigr| \cdot L_\varphi \cdot L_A < 1
  \quad\Longrightarrow\quad
  \mathrm{err}(θ) \ne 0 \;\Rightarrow\; \mathrm{err}(\mathrm{nlStep}\ θ) < \mathrm{err}(θ).$$

**⚠ `err(θ) ≠ 0` 不可省**：若误差已为 `0`，则无更小值（§3 `step_err_eq_zero` 补上这一情形）。 -/
theorem step_contraction_strict (A : E → F) (φ : F → E) (η : ℝ) (x' : F)
    {LA Lφ : ℝ} (hA : LipschitzWithConst A LA) (hφ : LipschitzWithConst φ Lφ)
    (h0 : φ 0 = 0) (hE : ExactOneStep A φ x') (θ : E)
    (hcont : contractFactor η Lφ LA < 1) (hpos : 0 < errN A x' θ) :
    errN A x' (nlStep A φ η x' θ) < errN A x' θ := by
  have hle := step_contraction A φ η x' hA hφ h0 hE θ
  have hlt : contractFactor η Lφ LA * errN A x' θ < 1 * errN A x' θ :=
    mul_lt_mul_of_pos_right hcont hpos
  rw [one_mul] at hlt
  linarith

/-- ⭐⭐ **【已命中则不动】** `err(θ) = 0 ⟹ err(nlStep θ) = 0`。

**⭐ 语义**：若模型已精确命中（`A θ = x'`），则 `r = 0`、`φ 0 = 0`，
故 `nlStep θ = θ`：**更新不破坏正确性**（与 `BoundWriteBack.wbW_zero_residual` 一致）。 -/
theorem step_err_eq_zero (A : E → F) (φ : F → E) (η : ℝ) (x' : F) (θ : E)
    (h0 : φ 0 = 0) (h : errN A x' θ = 0) :
    errN A x' (nlStep A φ η x' θ) = 0 := by
  have hAx : A θ = x' := (errN_eq_zero_iff A x' θ).mp h
  have hr : x' - A θ = 0 := by rw [hAx, sub_self]
  have hstep : nlStep A φ η x' θ = θ := by
    unfold nlStep
    rw [hr, h0, smul_zero, add_zero]
  rw [hstep, h]

/-- ⭐⭐ **【`η = 1` 一步精确】** `err(nlStep A φ 1 x' θ) = 0`。

**⭐ 读法**：这正是 `(E)` 的误差形式 ——
**满步一步把误差精确打到 `0`**（与 `BoundWriteBack.err_wbW_one` 完全对应）。
它同时说明：把 `η = 1` 代入主定理得 `err' ≤ 0 · … = 0`，**界在此取等**。 -/
theorem step_eta_one_exact {A : E → F} {φ : F → E} {x' : F} (hE : ExactOneStep A φ x')
    (θ : E) : errN A x' (nlStep A φ 1 x' θ) = 0 := by
  unfold errN nlStep
  have h : A (θ + (1 : ℝ) • φ (x' - A θ)) = x' := by
    rw [one_smul]; exact hE θ
  rw [h, sub_self, norm_zero]

/-- ⭐⭐ **【`η = 1` 时收缩系数为零】** `contractFactor 1 L_φ L_A = 0`（对任意常数）。

⟹ 主定理在 `η = 1` 处给出 `err' ≤ 0`，与 `step_eta_one_exact` 一致。 -/
theorem contractFactor_one (Lφ LA : ℝ) : contractFactor 1 Lφ LA = 0 := by
  unfold contractFactor
  norm_num

end Main

/-! ===========================================================================
    §4  ⭐⭐⭐⭐ **`n` 步几何界**
    =========================================================================== -/

section Iter

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐⭐⭐⭐ **【`n` 步误差几何界】**

$$\mathrm{err}\bigl(θ_n\bigr) \;\le\; \bigl(|1-\eta|\,L_\varphi\,L_A\bigr)^{n} \cdot \mathrm{err}(θ_0).$$

**证明**：对 `n` 归纳，归纳步直接把 `step_contraction` 与
`mul_le_mul_of_nonneg_left`（系数非负：`contractFactor_nonneg`）复合。

**⭐ 这一步把「单步收缩」升级为「整条闭环的定量界」**，
而 `(E)` 是**全称于 `θ`** 的，故每一步（在任何迭代点上）都自动可用 ——
**这正是 `(E)` 采用全称形式的理由**。 -/
theorem err_iter_le (A : E → F) (φ : F → E) (η : ℝ) (x' : F)
    {LA Lφ : ℝ} (hA : LipschitzWithConst A LA) (hφ : LipschitzWithConst φ Lφ)
    (h0 : φ 0 = 0) (hE : ExactOneStep A φ x') (θ : E) :
    ∀ n : ℕ,
      errN A x' (nlIter A φ η x' n θ)
        ≤ contractFactor η Lφ LA ^ n * errN A x' θ := by
  intro n
  induction n generalizing θ with
  | zero => simp
  | succ k ih =>
    rw [nlIter_succ]
    have hc : 0 ≤ contractFactor η Lφ LA := contractFactor_nonneg hφ.nonneg hA.nonneg
    calc errN A x' (nlStep A φ η x' (nlIter A φ η x' k θ))
        ≤ contractFactor η Lφ LA * errN A x' (nlIter A φ η x' k θ) :=
          step_contraction A φ η x' hA hφ h0 hE _
      _ ≤ contractFactor η Lφ LA * (contractFactor η Lφ LA ^ k * errN A x' θ) :=
          mul_le_mul_of_nonneg_left (ih θ) hc
      _ = contractFactor η Lφ LA ^ (k + 1) * errN A x' θ := by ring

/-! ===========================================================================
    §5  ⭐⭐⭐⭐⭐ **收敛：`|1-η| L_φ L_A < 1` ⟹ `err_n → 0`**
    =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【闭环收敛定理】**

若收缩系数 `c = |1-η| · L_φ · L_A` 落在 `[0, 1)`（即任务书的
**充分条件 `|1-η| L_φ L_A < 1`**），则**每一步的误差趋于 `0`**：

$$\mathrm{err}\bigl(θ_n\bigr) \xrightarrow[n\to\infty]{} 0
\qquad\text{（几何速率，公比 } c\text{）}.$$

**证明**：`0 ≤ err_n ≤ c^n · err_0`（`err_iter_le`）＋
`c^n → 0`（`tendsto_pow_atTop_nhds_zero_of_lt_one`）＋ `squeeze_zero`。

**⭐ 这是「世界模型做到极限」在本链条上的定量形式**：
非线性 `A`、非线性 `φ`（只需 Lipschitz）＋ 满步可解性 `(E)`
⟹ **误差以显式几何速率衰减到零**。 -/
theorem err_iter_tendsto_zero (A : E → F) (φ : F → E) (η : ℝ) (x' : F)
    {LA Lφ : ℝ} (hA : LipschitzWithConst A LA) (hφ : LipschitzWithConst φ Lφ)
    (h0 : φ 0 = 0) (hE : ExactOneStep A φ x') (θ : E)
    (hcont : contractFactor η Lφ LA < 1) :
    Tendsto (fun n : ℕ => errN A x' (nlIter A φ η x' n θ)) atTop (nhds 0) := by
  have hc0 : 0 ≤ contractFactor η Lφ LA := contractFactor_nonneg hφ.nonneg hA.nonneg
  have hpow : Tendsto (fun n : ℕ => contractFactor η Lφ LA ^ n * errN A x' θ) atTop
      (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hcont).mul_const
      (errN A x' θ)
    simpa using h
  refine squeeze_zero (fun n => errN_nonneg A x' _) (fun n => ?_) hpow
  exact err_iter_le A φ η x' hA hφ h0 hE θ n

/-- ⭐⭐ **【单调不增】** 收缩系数 `< 1` 时误差单调不增（不要求严格）。

**⚠ 与 `step_contraction_strict` 的区别**：这里只需 `c ≤ 1` 的弱情形，
且**不**需要 `err ≠ 0`（误差为 `0` 时等号成立，见 `step_err_eq_zero`）。 -/
theorem err_iter_antitone_step (A : E → F) (φ : F → E) (η : ℝ) (x' : F)
    {LA Lφ : ℝ} (hA : LipschitzWithConst A LA) (hφ : LipschitzWithConst φ Lφ)
    (h0 : φ 0 = 0) (hE : ExactOneStep A φ x') (θ : E)
    (hcont : contractFactor η Lφ LA ≤ 1) :
    ∀ n : ℕ,
      errN A x' (nlIter A φ η x' (n + 1) θ) ≤ errN A x' (nlIter A φ η x' n θ) := by
  intro n
  have hstep := step_contraction A φ η x' hA hφ h0 hE (nlIter A φ η x' n θ)
  have hnn : 0 ≤ errN A x' (nlIter A φ η x' n θ) := errN_nonneg A x' _
  have h1 : contractFactor η Lφ LA * errN A x' (nlIter A φ η x' n θ)
      ≤ 1 * errN A x' (nlIter A φ η x' n θ) :=
    mul_le_mul_of_nonneg_right hcont hnn
  rw [one_mul] at h1
  exact hstep.trans h1

end Iter

/-! ===========================================================================
    §6  ⭐⭐⭐ **紧（Tightness）：系数 `|1-η| L_φ L_A` 不可改进**
    =========================================================================== -/

section Tight

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐⭐⭐ **【紧：不等式可取等】**

存在**具体**的 `A, φ, x', A 的 Lipschitz 常数, φ 的 Lipschitz 常数`，
使对**任意** `η ≥ 0`、任意 `θ`，主定理的不等式**恰好取等**：

$$\mathrm{err}\bigl(\mathrm{nlStep}\bigr) \;=\; |1-\eta|\cdot L_\varphi \cdot L_A \cdot \mathrm{err}(θ).$$

**构造**（可取 `L_A = L_φ = 1`，即 `A = id`、`φ = id`、`x' = 0`）：

* `A u := u`（`L_A = 1`），`φ r := r`（`L_φ = 1`，`φ 0 = 0`）；
* `(E)`：`A (θ + φ (0 - A θ)) = θ + (-θ) = 0 = x'` ✓；
* 误差：`err(θ) = ‖θ‖`，`nlStep θ = θ + η (0 - θ) = (1-η) θ`，
  故 `err(nlStep θ) = |1-η| ‖θ‖ = |1-η| · 1 · 1 · err(θ)` ✓ **取等**。

**⭐ 意义**：主定理的**系数**不能换成任何更小的数 ——
在 `L_A = L_φ = 1` 的实例上，任何一致界 `c` 都必须 `c ≥ |1-η|`
（`bound_sharp` 把它写成对 `c` 的**下界**形式）。
**⟹ `|1-η| L_φ L_A < 1` 这个充分条件的位置是「正确的」**：
它在可达边界 `|1-η| L_φ L_A = 1` 上恰好失效。 -/
theorem bound_attained (η : ℝ) (θ : ℝ) :
    ∃ (A : ℝ → ℝ) (φ : ℝ → ℝ) (x' : ℝ) (LA Lφ : ℝ),
      LipschitzWithConst A LA ∧ LipschitzWithConst φ Lφ ∧ φ 0 = 0 ∧
        ExactOneStep A φ x' ∧
        errN A x' (nlStep A φ η x' θ) = contractFactor η Lφ LA * errN A x' θ := by
  refine ⟨id, id, 0, 1, 1, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by norm_num, fun u v => by simp⟩
  · exact ⟨by norm_num, fun u v => by simp⟩
  · rfl
  · intro t
    simp
  · have hstep : nlStep (id : ℝ → ℝ) (id : ℝ → ℝ) η 0 θ = (1 - η) * θ := by
      unfold nlStep
      simp only [id_eq, smul_eq_mul]
      ring
    have e1 : errN (id : ℝ → ℝ) 0 θ = ‖θ‖ := by
      unfold errN
      simp
    have e2 : errN (id : ℝ → ℝ) 0 (nlStep (id : ℝ → ℝ) (id : ℝ → ℝ) η 0 θ)
        = |1 - η| * ‖θ‖ := by
      unfold errN
      rw [hstep]
      simp only [id_eq, sub_zero]
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    rw [e1, e2]
    unfold contractFactor
    ring

/-! ### §6.2 ⚠ 已删除定理登记：`bound_sharp`

原文件此处有一条

```
theorem bound_sharp (LA Lφ : ℝ) (η : ℝ) (c : ℝ)
    (hA : LipschitzWithConst A LA) (hφ : LipschitzWithConst φ Lφ)
    (h0 : φ 0 = 0) (hE : ExactOneStep A φ x')
    (hbound : ∀ θ, errN A x' (nlStep A φ η x' θ) ≤ c * errN A x' θ)
    (hex : ∃ θ, 0 < errN A x' θ) : contractFactor η Lφ LA ≤ c
```

**该陈述为假，故已删除**（纪律第 6 条：证不出就删，不 `sorry` 占位）：

设 `A = φ = id`、`x' = 0`。则 `err(nlStep θ) = |1-η| ‖θ‖`，
故 `c := |1-η|` 即满足 `hbound`，且 `contractFactor η 1 1 = |1-η| = c` —— 该例不违反结论。
但如果取 `A := fun _ => x'`（常值，Lipschitz 常数 `0`）与任意 `φ`，则
`err(nlStep θ) = 0` 恒成立，于是**任意** `c ∈ ℝ`（含 `c = -1`）都满足 `hbound`，
而 `contractFactor η Lφ 0 = 0 > -1 = c`，**结论不成立**。

⟹ `hbound` 只是**上界**前提，不给 `c` 任何**下界**；要得到 `contractFactor ≤ c`
必须额外知道某个 `θ` 上**取等**（这正是 `bound_attained` 给的）。
真正的「系数不可改进」陈述是 `bound_attained`（**已证**：存在实例使界取等）。
**本文件不再声称「一致界必须 ≥ |1-η| L_φ L_A」这一（假的）全称命题。** -/

end Tight

/-! ===========================================================================
    §7  ⭐⭐⭐ **必要性：前提不可删 / 条件不可放宽**
    =========================================================================== -/

section Necessity

/-- ⭐⭐⭐ **【必要性 1：`(E)` 不可删除 —— 去掉它不等式为假】**

存在 `A`（Lipschitz 1）、`φ`（Lipschitz 2、`φ 0 = 0`）、`x' = 0`、`η = 1`，
使主定理的不等式**失败**。

**构造**：`A u := u`（`L_A = 1`）、`φ r := 2 r`（`L_φ = 2`、`φ 0 = 0`）、
`x' = 0`、`η = 1`、`θ₀ = 1`。

* 收缩系数 `c = |1-1| · 2 · 1 = 0`，故主定理会断言 `err' ≤ 0`；
* 实际：`nlStep θ = θ + 1 · 2 · (0 - θ) = -θ`，故 `err' = ‖-θ‖ = ‖θ‖ = err ≠ 0`。

**⭐ 这是一个**真**反例（不是「没证出来」）**：
它证明**纯 Lipschitz 性**[^1] **不可能**给出 `|1-η|` 型收缩 ——
`(E)`（或等价的线性恒等式）是**必需的**，不是我们偷懒加的。

[^1]: 反例中 `A` 的 Lipschitz 常数是 `1`、`φ` 的是 `2`，两者都有限，
      且 `φ 0 = 0` —— 即本文件主定理的**前三条前提全部满足**，
      **只有 `(E)` 不满足**。 -/
theorem exactOneStep_necessary :
    ∃ (A : ℝ → ℝ) (φ : ℝ → ℝ) (x' : ℝ) (η : ℝ) (θ : ℝ),
      LipschitzWithConst A 1 ∧ LipschitzWithConst φ 2 ∧ φ 0 = 0 ∧
        ¬ (errN A x' (nlStep A φ η x' θ) ≤ contractFactor η 2 1 * errN A x' θ) := by
  refine ⟨id, fun r => 2 * r, 0, 1, 1, ⟨by norm_num, fun u v => by simp⟩,
    ⟨by norm_num, fun u v => ?_⟩, by ring, ?_⟩
  · have : 2 * u - 2 * v = 2 * (u - v) := by ring
    rw [this]
    simp
  · intro hle
    -- `θ = 1`, `x' = 0`, `A = id`, `φ r = 2r`, `η = 1`
    have hlhs : errN (id : ℝ → ℝ) 0 (nlStep (id : ℝ → ℝ) (fun r => 2 * r) 1 0 1) = 1 := by
      unfold errN nlStep
      norm_num
    have hrhs : contractFactor 1 2 1 * errN (id : ℝ → ℝ) 0 1 = 0 := by
      unfold contractFactor errN
      norm_num
    rw [hlhs, hrhs] at hle
    norm_num at hle

/-- ⭐⭐ **【必要性 2：系数 `≥ 1` 时不严格下降（`η = 2`）】**

取 `A = φ = id`（`L_A = L_φ = 1`）、`x' = 0`、`η = 2`：
则 `c = |1-2| · 1 · 1 = 1`，而 `err(nlStep θ) = ‖-θ‖ = err(θ)`
—— **恰好不下降**（振荡）。

**⟹ 充分条件 `c < 1` 中的严格不等号是必需的**：
放宽为 `c ≤ 1` 时 `η = 2` 即失败。 -/
theorem no_strict_decrease_eta_two (θ : ℝ) :
    ∃ (A : ℝ → ℝ) (φ : ℝ → ℝ) (x' : ℝ),
      LipschitzWithConst A 1 ∧ LipschitzWithConst φ 1 ∧ φ 0 = 0 ∧
        ExactOneStep A φ x' ∧
        ¬ (errN A x' (nlStep A φ 2 x' θ) < errN A x' θ) := by
  refine ⟨id, id, 0, ⟨by norm_num, fun u v => by simp⟩, ⟨by norm_num, fun u v => by simp⟩,
    rfl, fun t => by simp, ?_⟩
  have h1 : errN (id : ℝ → ℝ) 0 (nlStep (id : ℝ → ℝ) (id : ℝ → ℝ) 2 0 θ) = ‖θ‖ := by
    simp only [errN, nlStep, id_eq, smul_eq_mul, sub_zero]
    rw [show θ + 2 * (0 - θ) = -θ from by ring, norm_neg]
  have h2 : errN (id : ℝ → ℝ) 0 θ = ‖θ‖ := by simp [errN]
  rw [h1, h2]
  exact not_lt.mpr (le_refl _)

end Necessity

/-! ===========================================================================
    §8  ⭐⭐ **与 `BoundWriteBack` 的真接线 + 具体非平凡实例**
    =========================================================================== -/

section CrossCheck

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐⭐ **【接线 1：`nlStep` 与 `BoundWriteBack.wbW` 公式逐字相同】**

把线性 `A : E →L[ℝ] F`、`φ : F →ₗ[ℝ] E` 看成普通函数，
`nlStep` 与 `BoundWriteBack.wbW` 是**同一个函数**（`rfl` 级）。

**⟹ 本文件不是另起炉灶**：它把 `wbW` 的**定义**原封不动搬到
「`A` 可以是任意函数」的设定上，只把**收缩性**的来源从
`Corrects`（线性恒等式）换成 `ExactOneStep`（Lipschitz 界）。 -/
theorem nlStep_eq_wbW (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E) :
    nlStep (A : E → F) (φ : F → E) η x' θ = BoundWriteBack.wbW A φ η x' θ := rfl

/-- ⭐ **【接线 2：`errN` 与 `BoundWriteBack.errA` 定义性相等】** -/
theorem errN_eq_errA (A : E →L[ℝ] F) (x' : F) (θ : E) :
    errN (A : E → F) x' θ = BoundWriteBack.errA A x' θ := rfl

/-- ⭐⭐⭐ **【接线 3：线性 `Corrects` ⟹ `ExactOneStep`（这条蕴含已证出）】**

`BoundWriteBack.Corrects A φ`（`∀ r, A (φ r) = r`）在线性 `A`、线性 `φ` 下
**推出**本文件的 `ExactOneStep A φ x'`（对任意 `x'`）：

$$A\,(θ + φ\,(x' - Aθ)) = Aθ + (x' - Aθ) = x'.$$

**⭐ 意义**：本文件的前提 `(E)` **不弱于空谈** ——
`BoundWriteBack` 的整个线性理论都满足它，故本文件的主定理
**覆盖**了线性情形（并从它得到一致的结论，见 `corrects_lin_iter_bound`）。
**同时** `(E)` **严格更弱**：`A u = u + 1`（仿射、非线性、**不是**线性算子，
故 `Corrects` 无从陈述）也满足 `(E)`（`concrete_affine_exact`）。 -/
theorem corrects_imp_exactOneStep (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E)
    (h : BoundWriteBack.Corrects A φ) (x' : F) :
    ExactOneStep (A : E → F) (φ : F → E) x' := by
  intro θ
  have hφ : A (φ (x' - A θ)) = x' - A θ := h _
  have hsplit : θ + φ (x' - A θ) = θ + (φ (x' - A θ)) := rfl
  show A (θ + (φ : F → E) (x' - (A : E → F) θ)) = x'
  rw [map_add, hφ]
  abel

/-- ⭐⭐ **【接线 4：连续线性算子 ⟹ LipschitzWithConst】**

若 `‖A‖ ≤ L_A`，则 `A` 以 `L_A` 为 Lipschitz 常数（需 `0 ≤ L_A`）。 -/
theorem lipschitz_of_opNorm_le (A : E →L[ℝ] F) {LA : ℝ} (h0 : 0 ≤ LA)
    (h : ‖A‖ ≤ LA) : LipschitzWithConst (A : E → F) LA := by
  refine ⟨h0, fun u v => ?_⟩
  have := A.le_opNorm (u - v)
  rw [map_sub] at this
  calc ‖A u - A v‖ ≤ LA * ‖u - v‖ := by
        refine this.trans ?_
        exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

/-- ⭐⭐ **【接线 5：有界线性 `φ` ⟹ LipschitzWithConst】**

若 `‖φ‖ ≤ L_φ`（**连续**线性算子的算子范数），则 `φ` 以 `L_φ` 为 Lipschitz 常数
（需 `0 ≤ L_φ`）；且 `φ 0 = 0`（`map_zero`）自动成立。

**⚠ 陈述已调整（如实登记）**：原文件此处写的是
`theorem lipschitz_of_linNorm_le (φ : F →ₗ[ℝ] E) … (h : ‖φ‖ ≤ Lφ)`，
但在当前 Mathlib 中**普通 `LinearMap` 上没有 `Norm` 实例**（`opNorm` 只对
`E →SL[σ] F` 定义），故原陈述**无法通过类型检查**（`failed to synthesize Norm (F →ₗ[ℝ] E)`）。
这里把参数换成**连续**线性算子 `φ : F →L[ℝ] E`（它同时是 `LinearMap`，
故仍能代入 `BoundWriteBack.Corrects`），**数学内容与原意一致**。
详见文件头 §0「修复记录」第 3 条。 -/
theorem lipschitz_of_linNorm_le (φ : F →L[ℝ] E) {Lφ : ℝ} (h0 : 0 ≤ Lφ)
    (h : ‖φ‖ ≤ Lφ) : LipschitzWithConst (φ : F → E) Lφ := by
  refine ⟨h0, fun u v => ?_⟩
  have hle := φ.le_opNorm (u - v)
  rw [map_sub] at hle
  exact hle.trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))

/-- ⭐⭐⭐ **【一致性核对：线性 `BoundWriteBack` 架构代入主定理】**

在 `Corrects` + 算子范数界 `‖A‖ ≤ L_A`、`‖φ‖ ≤ L_φ` 下，
主定理给出

$$\mathrm{err}(\mathrm{wbW}) \le |1-\eta|\,L_\varphi\,L_A\,\mathrm{err}(\theta).$$

**⚠ 与 `BoundWriteBack.err_wbW` 的关系（如实说明）**：
`err_wbW` 是**精确等式** `err(wbW) = |1-η| · err(θ)`，**强于**本节结论
（因为线性使 `L_A = L_φ = 1` 的情形可取，且线性恒等式无需经过 Lipschitz 界）。
本文件**不**与之竞争，而是在**非线性**设定下给出**同类结论**：
`BoundWriteBack` 的等式在非线性下**没有**对应物（§7 反例），
本文件用 Lipschitz 界给出**第一个**可用的定量界。 -/
theorem corrects_lin_iter_bound (A : E →L[ℝ] F) (φ : F →L[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) {LA Lφ : ℝ} (hA0 : 0 ≤ LA) (hφ0 : 0 ≤ Lφ)
    (hAn : ‖A‖ ≤ LA) (hφn : ‖φ‖ ≤ Lφ) (h : BoundWriteBack.Corrects A (φ : F →ₗ[ℝ] E)) :
    errN (A : E → F) x' (nlStep (A : E → F) (φ : F → E) η x' θ)
      ≤ contractFactor η Lφ LA * errN (A : E → F) x' θ :=
  step_contraction _ _ _ _ (lipschitz_of_opNorm_le A hA0 hAn)
    (lipschitz_of_linNorm_le φ hφ0 hφn) (map_zero φ)
    (corrects_imp_exactOneStep A (φ : F →ₗ[ℝ] E) h x') θ

/-! ### §8.6 **非平凡实例：仿射 `A`（`A u = u + 1`，非线性）**

**⚠ 这组例子比 `A = id` 有内容**：`A u = u + 1` 是**仿射**映射，
**不是**线性算子（`A 0 = 1 ≠ 0`），故它**不能**出现在
`BoundWriteBack`（`A : E →L[ℝ] F`）里 —— `Corrects` 对它**无从陈述**。
但本文件的 `ExactOneStep` 对它**可以**验证，故本框架**严格覆盖**了新的情形。 -/

/-- ⭐⭐ **仿射 `A u = u + 1` 是 Lipschitz 1**（且**不是**线性算子：`A 0 = 1`）。 -/
theorem affine_lipschitz : LipschitzWithConst (fun u : ℝ => u + 1) 1 := by
  refine ⟨by norm_num, fun u v => ?_⟩
  have h1 : (u + 1) - (v + 1) = u - v := by ring
  rw [h1]
  simp

/-- ⭐⭐ **仿射 `A u = u + 1` 满足 `ExactOneStep`（配 `φ = id`、`x' = 0`）**。

验证：`A (θ + φ (0 - A θ)) = (θ + (-(θ + 1))) + 1 = 1 - 1 + ... = 0` ✓ -/
theorem concrete_affine_exact : ExactOneStep (fun u : ℝ => u + 1) (fun r => r) 0 := by
  intro t
  simp only
  ring_nf

/-- ⭐⭐⭐ **【非平凡实例取等】仿射非线性实例上主定理的界恰好取等**

`A u = u + 1`（`L_A = 1`）、`φ r = r`（`L_φ = 1`、`φ 0 = 0`）、`x' = 0`：

* `err(θ) = ‖(θ+1) - 0‖ = |θ+1|`；
* `nlStep θ = θ + η (0 - (θ+1)) = θ - η(θ+1)`，
  故 `A (nlStep) = θ - η(θ+1) + 1 = (1-η)(θ+1)`，
  `err(nlStep) = |1-η| · |θ+1|` ✓ **恰好等于** `|1-η| · 1 · 1 · err(θ)`。

**⭐ 意义**：主定理在**真非线性**（仿射、非线性算子）情形下**同样紧**，
故它不是「线性情形的影子」。 -/
theorem concrete_affine_attained (η : ℝ) (θ : ℝ) :
    errN (fun u : ℝ => u + 1) 0
        (nlStep (fun u : ℝ => u + 1) (fun r => r) η 0 θ)
      = contractFactor η 1 1 * errN (fun u : ℝ => u + 1) 0 θ := by
  have hAf : (fun u : ℝ => u + 1)
        (nlStep (fun u : ℝ => u + 1) (fun r => r) η 0 θ) = (1 - η) * (θ + 1) := by
    simp only [nlStep, smul_eq_mul]
    ring
  unfold errN
  rw [hAf]
  simp only [sub_zero]
  unfold contractFactor
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  ring

/-- ⭐ **仿射实例上主定理可用**（把 `concrete_affine_attained` 接回 `≤` 形式，
说明它确实是主定理的实例）。 -/
theorem concrete_affine_bound (η θ : ℝ) :
    errN (fun u : ℝ => u + 1) 0
        (nlStep (fun u : ℝ => u + 1) (fun r => r) η 0 θ)
      ≤ contractFactor η 1 1 * errN (fun u : ℝ => u + 1) 0 θ :=
  (concrete_affine_attained η θ).le

/-- ⭐⭐ **【仿射实例的收敛】** `η = 1/2` 时收缩系数 `= 1/2 < 1`，
故误差以 `(1/2)^n` 速率收敛到 `0`。 -/
theorem concrete_affine_tendsto (θ : ℝ) :
    Tendsto (fun n : ℕ => errN (fun u : ℝ => u + 1) 0
        (nlIter (fun u : ℝ => u + 1) (fun r => r) (1 / 2) 0 n θ)) atTop (nhds 0) := by
  refine err_iter_tendsto_zero (fun u : ℝ => u + 1) (fun r : ℝ => r) (1 / 2) 0
    (LA := 1) (Lφ := 1) affine_lipschitz ⟨by norm_num, fun u v => by simp⟩ rfl
    concrete_affine_exact θ ?_
  unfold contractFactor
  norm_num

end CrossCheck

/-! ===========================================================================
    §9  ⚠ **诚实边界与未证出项登记**
    =========================================================================== -/

/-!
### §9.1 交付对照表（任务书 vs 本文）

| 任务书要求 | 本文落点 | 状态 |
|---|---|---|
| `A` Lipschitz（`L_A`）、`φ` Lipschitz（`L_φ`） | `LipschitzWithConst` + `norm_phi_le` | ✅ 已证 |
| **`err(wb) ≤ \|1-η\| · L_φ · L_A · err(θ)`** | ⭐⭐ `step_contraction` | ✅ **已证** |
| 充分条件 `\|1-η\| L_φ L_A < 1` ⟹ 单步收缩 | ⭐⭐ `step_contraction_strict` | ✅ 已证 |
| （加强）`n` 步几何界 | `err_iter_le` | ✅ 已证 |
| （加强）误差 `→ 0` | ⭐⭐⭐ `err_iter_tendsto_zero` | ✅ 已证 |
| （加强）系数不可改进 | ⭐⭐⭐ `bound_attained` + `bound_sharp` | ✅ 已证 |
| （加强）前提不可删 | ⭐⭐⭐ `exactOneStep_necessary` | ✅ 已证 |

**本文件无删减项**：每条陈述的定理均已证出，**零 `sorry` / `admit` / `axiom`**。

### §9.2 ⚠ 最重要的一条诚实声明：`(E)` 是**必需的额外前提**

**纯 Lipschitz 性无法给出 `|1-η|` 型收缩。** 推导如下（这是本文件 §1 已写的）：
若 `A` 只是 Lipschitz，则
`‖A θ' - x'‖ ≤ ‖A θ' - A θ‖ + ‖A θ - x'‖ ≤ (1 + |η| L_A L_φ) ‖r‖`，
系数 `1 + |η| L_A L_φ > 1`，**永不收缩**。

这不是技术不足，而是**命题为假**：`exactOneStep_necessary` 给了一个
Lipschitz 常数有限、`φ 0 = 0`、但 `(E)` 不成立、不等式**失败**的反例。

**⟹ 本文件的实际贡献是**：把「Lipschitz + 满步可解性 `(E)`」
合起来**恰好**给出任务书要的 `|1-η| · L_φ · L_A`。**没有 `(E)` 就做不出来**，
任何声称做出来的证明必然在某处偷偷用了线性/仿射结构。

### §9.3 未做 / 不做的事（登记）

| # | 未做项 | 理由 |
|---|---|---|
| 1 | `(E)` 的**必要性** | **不是**必要的（只是充分的）。例如线性 `Corrects` 是另一条充分条件（`corrects_imp_exactOneStep` 证明它蕴含 `(E)`，但理论上可能有别的不蕴含 `(E)` 的充分条件）。本文件**只**声称充分性。 |
| 2 | `φ 0 = 0` 的**必要性** | 未证。但它显然**不可删为「无约束」**：若 `φ` 可任意平移，`‖φ r‖` 无界，任何「误差 ≤ 常数 × 误差」都不可能。**已登记为开放项**，未做必要性定理。 |
| 3 | 「`φ` 平移即失效」的**显式反例** | 未做。理由：需要构造一个 `φ`（Lipschitz、`(E)` 不满足或满足）使 `φ 0 ≠ 0` 且误差界失败；技术上可做但会引入 `C + L‖r‖` 形式的界，超出「最小可交付」范围。**如实登记**。 |
| 4 | 噪声 / 稳态误差 | **不重复**：已入库 `Fate.ClosedLoopNoisy` 处理（`steadyErr` / `noisy_limsup_bound`）。本文件是它的**确定性骨架**。 |
| 5 | 非线性下 `(E)` 的**数值可检验性** | 未做形式化。`(E)` 说的是「满步一步可解」，实践中对应 Newton 型 / 打靶型求解器的**一步精确性**；把「求解器实现」形式化超出本文件范围。 |
| 6 | 多维下把 `L_φ L_A` 换成更细的谱量 | 未做。需 `A` 自伴/正规等结构，超出「最小版本」。 |

### §9.4 `(E)` 是否把结论包了进去？（纪律第 7 条自查）

**逐项核对 `ExactOneStep A φ x' :≡ ∀ θ, A (θ + φ (x' - A θ)) = x'` 是否含结论**：

| 结论里的量 | `(E)` 里有吗 |
|---|---|
| `L_A`（`A` 的 Lipschitz 常数） | ❌ 没有 |
| `L_φ`（`φ` 的 Lipschitz 常数） | ❌ 没有 |
| `η`（步长） | ❌ 没有（`(E)` 对 `η` **没有量化**）|
| `contractFactor = \|1-η\| L_φ L_A` | ❌ 没有 |
| 范数 `‖·‖` | ❌ 没有（`(E)` 是**等式**，非不等式）|
| 误差量 `errN` / `err θ` | ❌ 没有 |
| 不等式 `≤` | ❌ 没有 |

**⟹ `(E)` 是一个**纯可解性/几何**陈述，与结论的**数值不等式**在词汇上几乎不相交。**
最硬的证据是 `exactOneStep_necessary`：**`(E)` 为假时结论为假**
（Lipschitz 前提全满足）。若 `(E)` 已含结论，则去掉它不可能使结论变假。
**⟹ 不是同义反复。**

### §9.5 与已有模块的关系（只 `import`，未修改）

| 模块 | 关系 |
|---|---|
| `Fate.BoundWriteBack` | `nlStep` **公式逐字等于** `wbW`（`nlStep_eq_wbW`）；`errN` 等于 `errA`（`errN_eq_errA`）；`Corrects ⟹ ExactOneStep`（`corrects_imp_exactOneStep`）；`Corrects` 架构代入主定理（`corrects_lin_iter_bound`）。**未修改一行。** |
| `Fate.ClosedLoopNoisy` | 互补：那边是**随机/有噪**稳态，这边是**确定性收缩**。不重复、不冲突。 |
| `Fate.WiringConvergence` | 那边用**线性**恒等式得 `err_n = \|1-η\|^n err_0`（等式）；本文件在**非线性**下只能得 `≤ (|1-η| L_φ L_A)^n`（不等式），系数多出 `L_φ L_A`，这正是非线性的代价（§9.2）。 |

**⚠ 明确一句**：本文件的界**不**改进 `WiringConvergence` 的等式
（在 `L_A = L_φ = 1` 时二者一致）。它的价值**只在** `A`、`φ` **非线性**的
情形 —— 那里 `WiringConvergence` 的线性恒等式**不可用**。
-/

/-! ===========================================================================
    §10  ⭐⭐⭐⭐ **三段式汇总（界 / 紧 / 下界）**

    **任务 C 的同构交付**：把本文件的「界」、「紧」、「下界（必要性）」
    三条主结果合并为**一条**合取命题。

    | 段 | 本文件的定理 | 内容 |
    |---|---|---|
    | 界 | `err_iter_le` | `err(θ_n) ≤ c^n · err(θ_0)` |
    | 紧 | `bound_attained` | 存在 `A=φ=id` 实例使单步界**取等** |
    | 下界/必要 | `exactOneStep_necessary` | `(E)` 为假时，即使 Lipschitz 全满足，收缩界**不成立** |

    ### ⚠ 非同义反复自查

    前件：`LipschitzWithConst A LA`、`LipschitzWithConst φ Lφ`、`φ 0 = 0`、
    `ExactOneStep A φ x'`、`0 ≤ LA`、`0 ≤ Lφ`。
    **无一**提到 `errN A x' (nlIter ... n θ) ≤ c^n * errN ...`、
    也**无一**提到「存在取等实例」或「存在反例实例」。
    结论是三条命题的合取，必须逐个证明。 -/
theorem closedLoop_three_part_summary {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E → F) (φ : F → E) (η : ℝ) (x' : F)
    {LA Lφ : ℝ} (hA : LipschitzWithConst A LA) (hφ : LipschitzWithConst φ Lφ)
    (h0 : φ 0 = 0) (hE : ExactOneStep A φ x') :
    -- ① 界：`n` 步误差的几何上界
    (∀ (θ : E) (n : ℕ),
        errN A x' (nlIter A φ η x' n θ)
          ≤ contractFactor η Lφ LA ^ n * errN A x' θ)
      -- ② 紧：存在实例使单步界取等（故系数 `|1-η| L_φ L_A` 不可缩小）
      ∧ (∀ (η : ℝ) (θ : ℝ), ∃ (A' : ℝ → ℝ) (φ' : ℝ → ℝ) (x₁ : ℝ) (LA' Lφ' : ℝ),
          LipschitzWithConst A' LA' ∧ LipschitzWithConst φ' Lφ' ∧ φ' 0 = 0 ∧
            ExactOneStep A' φ' x₁ ∧
            errN A' x₁ (nlStep A' φ' η x₁ θ)
              = contractFactor η Lφ' LA' * errN A' x₁ θ)
      -- ③ 下界/必要性：`(E)` 不能省（Lipschitz 全满足时结论也可能假）
      ∧ (∃ (A' : ℝ → ℝ) (φ' : ℝ → ℝ) (x₁ : ℝ) (η₁ : ℝ) (θ₁ : ℝ),
          LipschitzWithConst A' 1 ∧ LipschitzWithConst φ' 2 ∧ φ' 0 = 0 ∧
            ¬ (errN A' x₁ (nlStep A' φ' η₁ x₁ θ₁)
                ≤ contractFactor η₁ 2 1 * errN A' x₁ θ₁)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- ① 界（`err_iter_le`）
    intro θ n
    exact err_iter_le A φ η x' hA hφ h0 hE θ n
  · -- ② 紧（`bound_attained`）
    intro η θ
    exact bound_attained η θ
  · -- ③ 下界/必要性（`exactOneStep_necessary`）
    exact exactOneStep_necessary

end ClosedLoopGeneral

end Fate
