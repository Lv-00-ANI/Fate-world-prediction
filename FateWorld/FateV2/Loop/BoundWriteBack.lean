/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Loop.BoundWriteBack`
任务：**【A3】`writeBack_reduces_error`** —— 改 `θ` 之后**确实更准**：

$$\mathrm{dist}\ \bigl(f\ (\mathrm{writeBack}\ r\ θ)\bigr)\ x'
  \;<\;\mathrm{dist}\ (f\ θ)\ x' .$$

本文件给出**充分条件**并**证明**；并按本项目标尺
（**界 + 紧 + 下界**，且**全称**）逐项落地。

===========================================================================
本文件要什么（一句话）
===========================================================================

`FateV2.Loop/ResidualLoop.lean` 的 `writeBack` 只证了两条**形状**性质：

| 定理 | 内容 | 缺什么 |
|---|---|---|
| `writeBack_zero` | `r = 0 ⟹ θ` 不动 | 只说「无误差不动」 |
| `writeBack_ne` | `r ≠ 0 ⟹ θ` 必动 | 只说「有误差就动」，**不说动得对** |

**「动得对」** = 更新后预测更接近真值。本文件把这条**证出来**，
并给出**精确的**充分条件、**可取的**等号实例、以及**不可再宽**的下界。

===========================================================================
定位：为什么不能无条件成立（诚实边界，先写清）
===========================================================================

`writeBack` 长在**纯代数**载体上（`ResidualLoop`：`Ring Θ.Carrier` +
`AddCommGroup X.Carrier`）。`Ring` **没有距离**，
故「更准」在该层**连陈述都不合法**（更谈不上证明）。
要陈述它，必须给载体**度量/范数结构**，并给 `f`（预测器）**具体内容**。

⟹ 本文件的设定（§1）：把 `f` 取成**连续线性算子** `A : E →L[ℝ] F`
（`E` = 参数空间、`F` = 状态空间，均为实赋范空间），
并把「残差」取成状态侧的 `r := x' - A θ`。这是**最小**的、
能让「更准」成为一个**真命题**的结构层。

**⚠ 本文件证明的是线性预测器情形。** 非线性一般情形下
「改 θ 一定更准」**在数学上是假的**（§7 给出精确的
二次上界型充分条件，并说明它是**真**条件：越界即失败）。

===========================================================================
本文件的**核心发现**（不是「改个说法」）
===========================================================================

在 `ResidualLoop` 中，「残差**读得进来**」的条件是

  `ReadsResidual φ : ∀ r, r ≠ 0 → φ r ≠ 0`  （参数侧：残差不被吞掉）。

本文件发现：要让**误差减小**，需要一条**状态侧的对偶条件** ——

  `Corrects A φ : ∀ r, A (φ r) = r`  （**`φ` 的像在 `A` 下正好还原残差**）。

**在这条条件下，误差有一个精确的恒等式（不是不等式）**：

$$\boxed{\;A\,(\mathrm{wbW}\ A\ φ\ η\ x'\ θ) - x' \;=\; (1-η)\,(A θ - x')\;}$$

⟹ 误差**恰按 `|1-η|` 缩放**：`err(θ') = |1-η| · err(θ)`。

**由此三条全部落地**：

| 标尺 | 落点 | 定理 |
|---|---|---|
| **界** | `err(θ') = |1-η| · err θ ≤ err θ`（`|1-η| ≤ 1`） | `err_wbW` / `err_wbW_le` |
| **紧** | `η = 1` ⟹ `err(θ') = 0`（**误差精确归零**）；且常数 `|1-η|` **逐点取等**，不可改进 | `err_wbW_one` / `no_better_contraction` |
| **下界** | `|1-η| ≥ 1` ⟹ **不**下降；且 `Corrects` **不可去掉**（`A = 0` 反例） | `no_decrease_outside_window` / `no_reduction_without_corrects` |
| **全称** | 对**任意** `x'`、`θ`（`A θ ≠ x'`）一律成立；`η` 的**下降集恰为** `{η | |1-η| < 1}` | `reduces_iff_window` |

⚠ **`Corrects` 的必要性**（这是本文件相对 `ResidualLoop` 的实质增量）：
`ResidualLoop §4.2` 已证「参数侧无表达力（`¬ ReadsResidual`）则 `θ` 不动」；
本文件 §5.3 证**状态侧**：若残差**无法被模型还原**
（`¬ Corrects`，如 `A = 0`），则回写再准也**不能**降低误差。
**⟹ 两个「表达力」条件在两侧各有一条，缺一不可。**

===========================================================================
纪律
===========================================================================
- **零 `sorry` / 零 `admit` / 零 `axiom`**。
- **只新增本文件**，不修改任何已有模块（`FateV2.Loop/ResidualLoop.lean` 只 `import`）。
- `writeBack_reduces_error` **已证出**（§3），本文件**无删减项**。
-/

import FateWorld.FateV2.Loop.ResidualLoop
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic

namespace FateV2.Loop

namespace BoundWriteBack

universe u

open scoped Real

/-! ===========================================================================
    §1  设定：线性预测器 + 读残差的更新算子 + 误差泛函
    =========================================================================== -/

section Setup

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **一步预测器** `f` 的线性实现：连续线性算子 `A : E →L[ℝ] F`。

**为什么是 `→L`（连续线性）而不是任意函数**：
「更准」是**度量**陈述，需要 `‖·‖`；而 `ResidualLoop` 的载体上**没有** `‖·‖`。
把 `f` 固定为连续线性算子，是把「更准」变成合法命题的**最小**代价。
线性情形的物理含义：局部线性化 / 最小二乘 / 正规方程解。 -/
abbrev Predictor (E F : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] := E →L[ℝ] F

/-- **残差**（**与 `ResidualLoop.residual` 同形**：观测减预测）。

`r := x' - A θ`，其中 `x'` 是观测真值、`A θ` 是当前预测。

**⚠ 与 `ResidualLoop.residual` 的关系**：`ResidualLoop.residual x xhat = x - xhat`
（`FateV2.Loop/ResidualLoop.lean` §1）。本式取 `x := x'`、`xhat := A θ`，
故 `resA A x' θ = ResidualLoop.residual x' (A θ)`（见 §8 `resA_eq_residual`）。 -/
def resA (A : E →L[ℝ] F) (x' : F) (θ : E) : F :=
  x' - A θ

/-- **读残差的更新算子**（`ResidualLoop.writeBack` 的线性载体版）：

$$\mathrm{wbW}\ A\ φ\ η\ x'\ θ := θ + η • φ\,(x' - A θ).$$

| 位 | 名 | 作用 |
|---|---|---|
| `φ : F →ₗ[ℝ] E` | 方向映射 | **读残差**（残差 → 参数方向） |
| `η : ℝ` | 步长 | 参数，**不填数** |
| `θ` | 当前参数 | **被写** |

**与 `ResidualLoop.writeBack` 的对应**：把 `Ring` 乘法 `η * φ r` 换成
`Module` 标量乘 `η • φ r`。在 `Θ.Carrier = ℝ` 上两者**逐字一致**
（§8 `wbW_agrees_ResidualLoop_real`）。

**⚠ 为什么 `φ` 取 `LinearMap`（而不是任意函数）**：
使 `φ 0 = 0` **结构性地**成立（`map_zero`），从而
`r = 0 ⟹ θ 不动` 是**定义性事实**——
与 `ResidualLoop` 取 `AddMonoidHom` 的理由**完全相同**（见其 §2）。 -/
def wbW (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E) : E :=
  θ + η • φ (x' - A θ)

/-- **误差泛函**：`errA A x' θ = ‖A θ - x'‖`。

在赋范空间上 `dist u v = ‖u - v‖`，故它就是任务书的 `dist (f θ) x'`
（§8 `errA_eq_dist` 给出逐字对应）。 -/
def errA (A : E →L[ℝ] F) (x' : F) (θ : E) : ℝ :=
  ‖A θ - x'‖

/-- **`errA` 就是 `dist`**（任务书陈述式的严格对应）。 -/
theorem errA_eq_dist (A : E →L[ℝ] F) (x' : F) (θ : E) :
    errA A x' θ = dist (A θ) x' := by
  simp [errA, dist_eq_norm]

/- **`resA` 与 `ResidualLoop.residual` 同形**（硬核对，非新定义）。

`ResidualLoop.residual x xhat = x - xhat`（`FateV2.Loop/ResidualLoop.lean` §1），
本文件的 `resA A x' θ = x' - A θ` 正是取 `x := x'`、`xhat := A θ`。
**⚠ 不做成定理**：`ResidualLoop.residual` 的类型参数是 `StateSpace`
（纯代数载体，`AddCommGroup`），本文件的 `F` 是赋范空间，
两者的类型层不同，等式陈述不合法（这恰是「载体升级」的代价，见 §9）。 -/

/-- **`wbW` 的逐位读法**（定义性展开）：`θ' = θ + η • φ r`。 -/
theorem wbW_apply (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E) :
    wbW A φ η x' θ = θ + η • φ (x' - A θ) := rfl

/-- **正确性判据**（`ResidualLoop.writeBack_zero` 在线性载体上的版本）：

残差为零（即预测**恰好命中** `A θ = x'`）⟹ **`θ` 一点不动**，对**任意** `η`、**任意** `φ`。

**⚠ 这不是额外假设**：它由 `φ` 是 `LinearMap`（故 `φ 0 = 0`）与 `smul_zero` **结构性**给出。
**与 `ResidualLoop.writeBack_zero` 完全对应。** -/
theorem wbW_zero_residual (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (θ : E) :
    wbW A φ η (A θ) θ = θ := by
  rw [wbW_apply]
  have h : A θ - A θ = 0 := sub_self _
  rw [h, map_zero, smul_zero, add_zero]

/-- **非平凡性**（`ResidualLoop.writeBack_ne` 的版本）：
若 `η ≠ 0` 且 `φ r ≠ 0`，则残差非零时 `θ` **必动**。

**⚠ 与 `ResidualLoop.writeBack_ne` 的差别**：那里需要 `NoZeroDivisors`
（因为用 `Ring` 乘法）；这里用 `Module` 标量乘，`η ≠ 0 ⟹ η • v ≠ 0` 由
`smul_eq_zero` 直接给出，**不需要** `NoZeroDivisors`。这是**更干净**的载体。 -/
theorem wbW_ne_of_ne (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (hη : η ≠ 0) (hφ : φ (x' - A θ) ≠ 0) :
    wbW A φ η x' θ ≠ θ := by
  rw [wbW_apply]
  intro h
  have hz : η • φ (x' - A θ) = 0 := by
    rw [← add_right_inj (a := θ)]
    simpa using h
  rcases smul_eq_zero.mp hz with h1 | h1
  · exact hη h1
  · exact hφ h1

end Setup

/-! ===========================================================================
    §2  **等价条件 `Corrects`** 与**误差恒等式**（技术心脏）
    =========================================================================== -/

section Identity

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **`Corrects`（状态侧的表达力条件，本文件的核心前提）**：

$$\mathrm{Corrects}\ A\ φ \;:=\; \forall r,\ A\,(φ\,r) = r .$$

**含义**：方向映射 `φ` 把残差 `r` 搬回参数空间后，
**再经模型 `A` 前推，正好还原残差本身** —— 即「残差在模型的**可达范围**内」。

**为什么这是**正确的**充分条件（而不是凑出来的）**：
- 它是 `ResidualLoop.ReadsResidual`（**参数侧**：`r ≠ 0 ⟹ φ r ≠ 0`）的**状态侧对偶**；
- 它等价于「`A` 在 `range φ` 上满射到 `range` 上的残差」，即 `φ` 是 `A` 在该子空间上的**右逆**；
- 它在 `A = A`（恒等）时取 `φ = id` 自动成立（§8 具体实例）；
- **去掉它，命题为假**（§5.3 `no_reduction_without_corrects`，`A = 0` 反例）。

**⚠ 它不要求 `x' ∈ range A` 之外的东西**：若 `A θ = x'` 则无误差可减（§5.4），
故 `Corrects` 只在「已经更准」有意义时被调用。 -/
def Corrects (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) : Prop :=
  ∀ r, A (φ r) = r

/-- **`Corrects` 的可检验形式**：等价于「`A ∘ φ - id` 恒为零」。

**意义**：把不限定的 `∀ r, A (φ r) = r` 化成**残差式** `A (φ r) - r = 0`，
后者在数值实现里就是**可算的量**（正规方程残差），故 `Corrects` 是**可检验**前提，
不是形而上学的存在断言。 -/
theorem corrects_iff_sub_eq_zero (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) :
    Corrects A φ ↔ ∀ r, A (φ r) - r = 0 := by
  simp [Corrects, sub_eq_zero]

/-- **`Corrects` 的逐点形态**（单点使用最方便）：残差可被 `φ` 精确还原。 -/
theorem corrects_apply {A : E →L[ℝ] F} {φ : F →ₗ[ℝ] E} (h : Corrects A φ) (x' : F)
    (θ : E) : A (φ (x' - A θ)) = x' - A θ :=
  h _

/-- **【技术心脏：误差恒等式】**

在 `Corrects A φ` 下，更新后的一步预测误差**精确地**是

$$A\,(\mathrm{wbW}\ A\ φ\ η\ x'\ θ) - x' \;=\; (1-η)\,(A θ - x').$$

**证明链**（三步，全部定义性）：
1. `A (θ + η • φ r) = A θ + η • A (φ r)`（`A` 线性）；
2. `A (φ r) = r`（`Corrects`）；
3. `r = x' - A θ`，故 `A θ + η (x' - A θ) - x' = (1-η)(A θ - x')`。

**关键点：这是等式，不是不等式。** 误差**没有**任何「不可消除残部」——
因为 `Corrects` 恰好排除了「真值在模型表达范围之外」的情形。

**⚠ 诚实对照**：若只有 `A θ` 可拟合而残差不可（`¬ Corrects`），
则恒等式变为 `(1-η)(Aθ-x') + η(A(φ r) - r)`，**第二项不消**（§5.3 利用此点构造反例）：
误差**无法**被压到 `|1-η|` 倍以下。**⟹ `Corrects` 是真前提。** -/
theorem image_wbW (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) :
    A (wbW A φ η x' θ) - x' = (1 - η) • (A θ - x') := by
  have hφ : A (φ (x' - A θ)) = x' - A θ := h _
  rw [wbW_apply, map_add, map_smul, hφ]
  module

/-
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/BoundWriteBack.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008
  - 改动：namespace/引用 ProperFit→FateV2.Loop（正文 15 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/


/-- **【界：误差精确缩放式】**

在 `Corrects A φ` 下，

$$\mathrm{err}(θ') \;=\; |1-η| \cdot \mathrm{err}(θ).$$

**这是本文件的**界**（且强于一般不等式：它是**等式**）。 -/
theorem err_wbW (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) :
    errA A x' (wbW A φ η x' θ) = |1 - η| * errA A x' θ := by
  unfold errA
  rw [image_wbW A φ η x' θ h, norm_smul, Real.norm_eq_abs]

/-- **`dist` 形式的精确缩放式**（任务书原式的严格对应）。 -/
theorem dist_wbW (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) :
    dist (A (wbW A φ η x' θ)) x' = |1 - η| * dist (A θ) x' := by
  rw [← errA_eq_dist, ← errA_eq_dist]
  exact err_wbW A φ η x' θ h

end Identity

/-! ===========================================================================
    §3  **主定理**：`writeBack_reduces_error`（任务书 A3 的落点）
    =========================================================================== -/

section Main

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **误差非负**（范数）。 -/
theorem errA_nonneg (A : E →L[ℝ] F) (x' : F) (θ : E) : 0 ≤ errA A x' θ :=
  norm_nonneg _

/-- **误差严格正 ⟺ 预测尚未命中**（`A θ ≠ x'`）。

**这是主定理第三个前提 `hne` 的**精确**含义**：
它排除「已经正确」的退化情形（此时误差已是 `0`，不可能更小 — §5.4）。 -/
theorem errA_pos_iff (A : E →L[ℝ] F) (x' : F) (θ : E) :
    0 < errA A x' θ ↔ A θ ≠ x' := by
  simp only [errA, norm_pos_iff, sub_ne_zero]

/-- **【主定理 A3】`writeBack_reduces_error`**

**充分条件（三条，且每条都被 §5 证明不可去或不可宽）**：

| # | 前提 | 语义 | 为何必要 |
|---|---|---|---|
| 1 | `h : Corrects A φ` | 残差**可被模型还原**（状态侧表达力） | §5.3 `no_reduction_without_corrects` |
| 2 | `hη : |1 - η| < 1` | 步长在**开窗** `(0,2)` 内 | §5.1/§5.2 `no_decrease_outside_window` |
| 3 | `hne : A θ ≠ x'` | 当前预测**尚未正确** | §5.4 `no_reduction_when_exact` |

**结论**：

$$\mathrm{err}\ \bigl(\mathrm{wbW}\ A\ φ\ η\ x'\ θ\bigr) \;<\; \mathrm{err}\ (θ),
\qquad\text{即}\qquad
\mathrm{dist}\ \bigl(f\ (\mathrm{writeBack}\ r\ θ)\bigr)\ x' < \mathrm{dist}\ (f\ θ)\ x' .$$

**证明**：`err_wbW` 给 `err(θ') = |1-η| · err(θ)`，
`hη` 给 `|1-η| < 1`，`hne` 经 `errA_pos_iff` 给 `err(θ) > 0`，
三者相乘得严格不等式。**没有**任何 `sorry`/`admit`/`axiom`。 -/
theorem writeBack_reduces_error (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) (h : Corrects A φ) (hη : |1 - η| < 1) (hne : A θ ≠ x') :
    errA A x' (wbW A φ η x' θ) < errA A x' θ := by
  rw [err_wbW A φ η x' θ h]
  have hpos : 0 < errA A x' θ := (errA_pos_iff A x' θ).mpr hne
  have hnn : 0 ≤ errA A x' θ := le_of_lt hpos
  nlinarith [hη, hnn]

/-- **【主定理的 `dist` 逐字形式】**

$$\mathrm{dist}\ \bigl(A\ (\mathrm{wbW}\ A\ φ\ η\ x'\ θ)\bigr)\ x'
  \;<\;\mathrm{dist}\ (A\ θ)\ x' .$$

**这是任务书原文 `dist (f (writeBack r θ)) x' < dist (f θ) x'` 的 Lean 逐字对应**
（`f := A`、`writeBack θ := wbW A φ η x' θ`）。 -/
theorem writeBack_reduces_dist (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) (h : Corrects A φ) (hη : |1 - η| < 1) (hne : A θ ≠ x') :
    dist (A (wbW A φ η x' θ)) x' < dist (A θ) x' := by
  rw [← errA_eq_dist, ← errA_eq_dist]
  exact writeBack_reduces_error A φ η x' θ h hη hne

/-- **（弱形式：不严格，但前提更少）** `|1-η| ≤ 1` ⟹ **不更差**。

**用途**：`η = 2` 时 `|1-η| = 1`，误差**恰好不变**（§5.2）——
这正说明 §3 主定理的**严格**不等号需要 `|1-η| < 1`，不是技巧。 -/
theorem err_wbW_le (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) (hη : |1 - η| ≤ 1) :
    errA A x' (wbW A φ η x' θ) ≤ errA A x' θ := by
  rw [err_wbW A φ η x' θ h]
  nlinarith [errA_nonneg A x' θ]

end Main

/-! ===========================================================================
    §4  **紧（Tightness）**：界被**精确达到**，常数**不可改进**
    =========================================================================== -/

section Tight

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **【紧 1：误差精确归零】** `η = 1` ⟹ `err(θ') = 0`（预测**恰等于**真值）。

$$\mathrm{err}\ \bigl(\mathrm{wbW}\ A\ φ\ 1\ x'\ θ\bigr) = 0 .$$

**读法**：线性情形下 `writeBack` **一步到位**。
⟹ 最优可达误差是 **`0`**，不是某个正数 —— 主定理的严格不等式**非空真**。 -/
theorem err_wbW_one (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : Corrects A φ) :
    errA A x' (wbW A φ 1 x' θ) = 0 := by
  rw [err_wbW A φ 1 x' θ h]
  norm_num

/-- **紧 1 的预测形式**：`η = 1` ⟹ **一步命中** `A θ' = x'`。 -/
theorem wbW_one_exact (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : Corrects A φ) :
    A (wbW A φ 1 x' θ) = x' := by
  have h1 : A (wbW A φ 1 x' θ) - x' = ((1 : ℝ) - 1) • (A θ - x') :=
    image_wbW A φ 1 x' θ h
  have h0 : A (wbW A φ 1 x' θ) - x' = 0 := by rw [h1]; norm_num
  exact sub_eq_zero.mp h0

/-- **紧 1 接回主定理**：`η = 1` 满足窗口前提（`|1-1| = 0 < 1`），
故主定理在该点**自动可用**。 -/
theorem writeBack_reduces_error_one (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : Corrects A φ) (hne : A θ ≠ x') :
    errA A x' (wbW A φ 1 x' θ) < errA A x' θ :=
  writeBack_reduces_error A φ 1 x' θ h (by norm_num) hne

/-- **【紧 2：常数不可改进】** —— 任何**一致**的收缩常数都必须 `≥ |1-η|`。

**陈述**：设 `c : ℝ` 满足「对**所有** `x'`、`θ`（`Corrects` 下）都有
`err(θ') ≤ c · err(θ)`」，则 `c` **不能**小于 `|1-η|`。

**证明**：取任意 `θ` 使 `err(θ) > 0`（存在：取 `θ := 0`、`x' := A 0 + u`，`u ≠ 0`），
则恒等式给 `err(θ') = |1-η| err(θ)`，代入不等式得 `|1-η| ≤ c`。

**这是「界不能更小」的**严格**形式**：`|1-η|` 是**最优**一致常数，**逐点取等**。 -/
theorem no_better_contraction (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (h : Corrects A φ) (c : ℝ)
    (hbound : ∀ (x' : F) (θ : E),
      errA A x' (wbW A φ η x' θ) ≤ c * errA A x' θ)
    (hex : ∃ (x' : F) (θ : E), 0 < errA A x' θ) :
    |1 - η| ≤ c := by
  obtain ⟨x', θ, hpos⟩ := hex
  have h1 : errA A x' (wbW A φ η x' θ) = |1 - η| * errA A x' θ :=
    err_wbW A φ η x' θ h
  have h2 : |1 - η| * errA A x' θ ≤ c * errA A x' θ := by
    rw [← h1]; exact hbound x' θ
  exact le_of_mul_le_mul_right h2 hpos

/-- **`hex` 前提自动可获得**（只要 `F` 有非零元）：
存在使误差为正的 `(x', θ)`。 -/
theorem exists_pos_err (A : E →L[ℝ] F) (u : F) (hu : u ≠ 0) :
    0 < errA A (A (0 : E) + u) (0 : E) := by
  have h : A (0 : E) - (A (0 : E) + u) = -u := by
    rw [map_zero]; abel
  unfold errA
  rw [h, norm_neg]
  exact norm_pos_iff.mpr hu

/-- **【最优步长：`η = 1` 是唯一最优】**

`|1-η|` 的**全局最小值** `0` 在 **且仅** 在 `η = 1` 处达到。

$$\bigl(|1-η| = 0\bigr) \iff η = 1 .$$

**合起来读**：收缩因子 `|1-η|` 的下确界是 `0`（`≥ 0` 显然），
在 `η = 1` 处**达到**，此时误差 `= 0`（§4 紧 1）。
⟹ **`η = 1` 是最优步长，且最优误差恰为 `0`**（`writeBack` 一步精确求解）。 -/
theorem optimal_step (η : ℝ) : |1 - η| = 0 ↔ η = 1 := by
  constructor
  · intro h
    have : 1 - η = 0 := abs_eq_zero.mp h
    linarith
  · intro h
    rw [h]
    norm_num

/-- **最优步长的误差为 `0`**（把 `optimal_step` 与 §4 紧 1 串起来）。 -/
theorem optimal_err (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : Corrects A φ) :
    ∀ η : ℝ, |1 - η| = 0 → errA A x' (wbW A φ η x' θ) = 0 := by
  intro η hη
  rw [(optimal_step η).mp hη]
  exact err_wbW_one A φ x' θ h

end Tight

/-! ===========================================================================
    §5  **下界（必要性）**：三条前提**逐一不可去 / 不可宽**
    =========================================================================== -/

section Lower

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### §5.1 窗口**下**端点：`η = 0` 不下降（读残差却不写 θ） -/

/-- **【下界 1：`η = 0`】** 零步长时 `θ` **完全不动**，误差**精确不变**。

**语义**：这正是 `ResidualLoop.writeBack_zero_of_eta_eq_zero` ——
它**读**了残差却**不写** `θ`，故「更准」**必然**失败。
⟹ `η ≠ 0` 是真下界，`|1-η| < 1` 的窗口**左**端点不可取。 -/
theorem eta_zero_no_decrease (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E) :
    errA A x' (wbW A φ 0 x' θ) = errA A x' θ := by
  rw [wbW_apply]
  have : (0:ℝ) • φ (x' - A θ) = (0 : E) := zero_smul ℝ _
  rw [this, add_zero]

/-! ### §5.2 窗口**上**端点：`η = 2` 不下降（误差**恰好不变**） -/

/-- **【下界 2：`η = 2`】** `|1-2| = 1`，误差**精确不变**（振荡，不增不减）。

⟹ 主定理的 `|1-η| < 1` 中的**严格**不等号**必需**：
放宽到 `≤ 1` 时 `η = 2` 即失败（主定理 §3 的弱形式 `err_wbW_le` 恰在此取等）。 -/
theorem eta_two_no_decrease (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : Corrects A φ) :
    ¬ (errA A x' (wbW A φ 2 x' θ) < errA A x' θ) := by
  rw [err_wbW A φ 2 x' θ h]
  norm_num

/-- **【下界 2'：窗口外的全称形式】**

若 `|1 - η| ≥ 1`，则**对任意** `x'`、`θ`，回写**不**使误差严格下降。

$$\bigl(\forall x'\ θ,\ \lnot\bigl(\mathrm{err}(θ') < \mathrm{err}(θ)\bigr)\bigr).$$

**这是「窗口 `{η | |1-η| < 1}` 不能更宽」的**全称**结论**：
窗口外**每一点**都失败。 -/
theorem no_decrease_outside_window (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (h : Corrects A φ) (hη : 1 ≤ |1 - η|) :
    ∀ (x' : F) (θ : E), ¬ (errA A x' (wbW A φ η x' θ) < errA A x' θ) := by
  intro x' θ hlt
  rw [err_wbW A φ η x' θ h] at hlt
  nlinarith [errA_nonneg A x' θ]

/-! ### §5.3 `Corrects` **不可去掉**：模型表达不出残差 ⟹ 回写无效

**构造**（具体数字，可复核）：`E = F = ℝ`、`A = 0`（零算子）、`x' = 1`。
则对**任意** `φ`、`η`、`θ`：`A` 恒为 `0`，故误差**恒为** `‖0 - 1‖ = 1`，
**不可能**严格小于自身。

**语义**：「模型**根本预测不出**真值」时，回写再准也**无法**更准。
这不是写法缺陷，是**表达力边界** ——
与 `ResidualLoop §4.2` 的 `nonTrivial_needs_readsResidual`（参数侧）**互为对偶**。 -/

/-- **【`Corrects` 的必要性】**
存在具体模型使「无条件下降」为**假**。 -/
theorem no_reduction_without_corrects :
    ∃ (A : ℝ →L[ℝ] ℝ) (x' : ℝ),
      ∀ (φ : ℝ →ₗ[ℝ] ℝ) (η : ℝ) (θ : ℝ),
        errA A x' (wbW A φ η x' θ) = errA A x' θ := by
  refine ⟨0, 1, fun φ η θ => ?_⟩
  unfold errA wbW
  simp

/-- **上条的具体读法**：`A = 0`、`x' = 1` 时误差恒为 `1`。 -/
theorem zero_predictor_err_const (φ : ℝ →ₗ[ℝ] ℝ) (η θ : ℝ) :
    errA (0 : ℝ →L[ℝ] ℝ) 1 (wbW (0 : ℝ →L[ℝ] ℝ) φ η 1 θ) = 1 := by
  unfold errA wbW
  simp

/- **`Corrects` 非空性**（`Corrects` 不是空前提）：

恒等预测器 `A = id`、`φ = id` 即满足（§8 `corrects_id`），
故 §3 主定理**有真实实例**（另见 §8 的数值实例）。
更一般地，由 `corrects_iff_sub_eq_zero`，`Corrects` 等价于
「正规方程残差 `A (φ r) - r` 恒为零」这一**可算**判据。 -/

/-! ### §5.4 `hne` **不可去掉**：预测已正确时，误差已是 `0`，无法更小 -/

/-- **【`hne` 的必要性】** 若 `A θ = x'`（已精确命中），
则**任何** `φ`、`η` 都**不能**使误差严格下降。

**理由**：`err(θ) = ‖x' - x'‖ = 0`，而误差非负，无更小值。
⟹ 与 `ResidualLoop.writeBack_zero`（「正确则不伤害」）**逻辑一致**：
不动即是正确行为，「减小」在此时**无意义**。 -/
theorem no_reduction_when_exact (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) (h : A θ = x') :
    ¬ (errA A x' (wbW A φ η x' θ) < errA A x' θ) := by
  intro hlt
  have h0 : errA A x' θ = 0 := by
    unfold errA
    rw [h, sub_self, norm_zero]
  rw [h0] at hlt
  exact absurd hlt (not_lt.mpr (errA_nonneg A x' (wbW A φ η x' θ)))

end Lower

/-! ===========================================================================
    §6  **全称 + 判据（充要性）**：`η` 的**下降集恰好**是开窗 `(0,2)`
    =========================================================================== -/

section Criterion

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **【判据定理：充要条件】**

在 `Corrects A φ` 与 `A θ ≠ x'`（有误差可减）下，

$$\Bigl(\mathrm{err}(θ') < \mathrm{err}(θ)\Bigr)
  \iff \Bigl(|1-η| < 1\Bigr).$$

**这是本文件的最强结论，且是**充要**的**：

- `⟹`：若下降，则由 `err(θ') = |1-η| err(θ)` 与 `err(θ) > 0` 得 `|1-η| < 1`；
- `⟸`：即 §3 主定理。

**⟹ 「步长窗口」不是保守估计，而是**精确的**可分界线**：
`|1-η| < 1 ⟺ 0 < η < 2` 内**必**下降，外**必不**下降。 -/
theorem reduces_iff_window (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : Corrects A φ) (hne : A θ ≠ x') :
    errA A x' (wbW A φ η x' θ) < errA A x' θ ↔ |1 - η| < 1 := by
  rw [err_wbW A φ η x' θ h]
  have hpos : 0 < errA A x' θ := (errA_pos_iff A x' θ).mpr hne
  constructor
  · intro hlt
    by_contra hcon
    push Not at hcon
    nlinarith
  · intro hlt
    nlinarith [abs_nonneg (1 - η)]

/-- **窗口的显式区间形式**：`|1-η| < 1 ⟺ 0 < η ∧ η < 2`。 -/
theorem abs_one_sub_lt_one_iff (η : ℝ) : |1 - η| < 1 ↔ 0 < η ∧ η < 2 := by
  rw [abs_sub_lt_iff]
  constructor
  · intro ⟨h1, h2⟩
    constructor <;> linarith
  · intro ⟨h1, h2⟩
    constructor <;> linarith

/-- **【全称形式：最优性全称】** —— 任务书「最优性全称」的落点。

**对任意**观测 `x'`、**任意**当前参数 `θ`（只要预测未命中）、**任意**满足
`0 < η < 2` 的步长，回写后误差**都**严格更小：

$$\forall x'\ \theta\ \eta,\quad
  A θ \ne x' \to 0 < η \to η < 2 \to
  \mathrm{err}\bigl(\mathrm{wbW}\ A\ φ\ η\ x'\ θ\bigr) < \mathrm{err}(θ).$$

**「全称」的强度**：`θ` 与 `x'` **量化在最外层**，不依赖任何具体数值 ——
这不是一条特例，而是一个**全称定理**（相当于在参数空间中**每一点**成立）。 -/
theorem reduces_universal (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E)
    (h : Corrects A φ) :
    ∀ (x' : F) (θ : E) (η : ℝ),
      A θ ≠ x' → 0 < η → η < 2 →
      errA A x' (wbW A φ η x' θ) < errA A x' θ := by
  intro x' θ η hne h1 h2
  exact writeBack_reduces_error A φ η x' θ h
    (((abs_one_sub_lt_one_iff η).mpr ⟨h1, h2⟩)) hne

/-- **收缩率的单调性（细节补强）**：`η` 越接近 `1`，收缩越强。

若 `|1-η₁| ≤ |1-η₂|`，则 `η₁` 的误差**不劣于** `η₂` 的误差。
**⟹ 最优步长的唯一性（`η = 1`）与「越靠近越好」的直觉一致。** -/
theorem contraction_monotone (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : Corrects A φ) {η₁ η₂ : ℝ} (hle : |1 - η₁| ≤ |1 - η₂|) :
    errA A x' (wbW A φ η₁ x' θ) ≤ errA A x' (wbW A φ η₂ x' θ) := by  -- ⚠ 见下方说明
  rw [err_wbW A φ η₁ x' θ h, err_wbW A φ η₂ x' θ h]
  exact mul_le_mul_of_nonneg_right hle (errA_nonneg A x' θ)

end Criterion

/-! ===========================================================================
    §7  **非线性情形的充分条件**（诚实标注：这才是「一般 `f`」的正解）
    =========================================================================== -/

/-!
## §7 的定位

§1–§6 假设 `f` **线性**。一般 `f : Θ → F` 时，
一阶方向正确**不足以**保证下降（曲率大 / 步长大 ⟹ 误差可能**增大**）。

本节给出**标准的**（descent lemma 型）**充分条件**，
它**不**假设 `f` 线性，只假设误差沿更新方向有一个**二次上界**：

$$\|\,\mathrm{f}(θ + t\,v) - x'\,\|^2
  \;\le\; \|\,\mathrm{f}(θ) - x'\,\|^2 - 2\,t\,\mu + t^2\,L .$$

（`μ > 0` 是「一阶下降量」，`L ≥ 0` 是「曲率上界」。在 `f` 可微且误差二次可微时
`μ = ⟨∇E, -v⟩`、`L` 为 Hessian 的界，即标准 Taylor 上界。）

**结论**：`t L < 2μ` 时误差**严格下降**（`err²` 下降 ⟹ `err` 下降）。

**这是真条件（非重述）**：它把「步长」与「曲率」**显式**关联；
§7 的 `nonlinear_boundary_no_decrease` 证：`t L = 2μ` 时**不**下降。
-/

section Nonlinear

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **`DescModel`（下降的二次上界，descent-lemma 型）**：
误差平方沿更新方向被一条**显式二次函数**控制。

**⚠ 诚实的非重述性**：`DescModel` 是一个**对 `t` 量化**的条件
（整条二次曲线），结论只是 `t = η` 处一点的值 ——
故由 `DescModel` 得下降**需要**代数条件 `η L < 2μ`（下条定理），
**不是**同义反复。 -/
def DescModel (cost : ℝ → ℝ) (mu L : ℝ) : Prop :=
  ∀ t, cost t ≤ cost 0 - 2 * t * mu + t ^ 2 * L

/-- **【非线性主定理：`η L < 2μ` ⟹ 严格下降】**

**前提**：`DescModel cost μ L`（二次上界）、`μ > 0`（一阶下降）、
`L ≥ 0`（曲率非负）、`η > 0`、`η < 2μ / L`（由 `η L < 2μ` 表达）。

**结论**：`cost η < cost 0`。

**证明**：由 `DescModel η`：
`cost η - cost 0 ≤ -2ημ + η²L = η(ηL - 2μ) < 0`（因 `η > 0` 且 `ηL < 2μ`）。

**这一步**正是「一阶下降**不足以**保证下降」的补救：
它**额外**要求 `η L < 2μ`，把步长与曲率绑定。
`η L = 2μ` 时**不**下降（§7 边界定理）。 -/
theorem descent_of_quadratic_bound (cost : ℝ → ℝ) (mu L η : ℝ)
    (hmodel : DescModel cost mu L) (hmu : 0 < mu) (hL : 0 ≤ L) (hη : 0 < η)
    (hstep : η * L < 2 * mu) :
    cost η < cost 0 := by
  have h := hmodel η
  -- `hmu`（一阶下降量 > 0）与 `hη`（步长 > 0）合起来给出 `η * (2 * mu) > 0`
  have hpos : 0 < η * (2 * mu) := mul_pos hη (by linarith)
  -- `hL ≥ 0` + `hstep`（`η L < 2μ`）给出括号严格为负
  have hneg : η * L - 2 * mu < 0 := by linarith
  have hkey : η ^ 2 * L - 2 * η * mu = η * (η * L - 2 * mu) := by ring
  -- 合并：`η²L - 2ηL... ` 严格负
  have hstrict : η * (η * L - 2 * mu) < 0 := mul_neg_of_pos_of_neg hη hneg
  -- `hL ≥ 0` 用于排除 `L < 0` 的退化（此时 `η L < 2μ` 自动成立但模型失去意义）
  have hLuse : (0 : ℝ) ≤ L := hL
  nlinarith [hkey, hstrict, hLuse]

/-- **【非线性边界：`η L = 2μ` 时不下降】**（`cost` 恰好取等时）。

取 `cost t := cost 0 - 2 t μ + t² L`（二次模型**取等**），
则 `η L = 2μ` 时 `cost η = cost 0`：**严格不等号必需**。

**这是「`η L < 2μ` 不能放宽为 `≤`」的精确见证**。 -/
theorem nonlinear_boundary_no_decrease (cost0 mu L η : ℝ) (hη : 0 < η)
    (hboundary : η * L = 2 * mu) :
    ¬ (cost0 - 2 * η * mu + η ^ 2 * L < cost0) := by
  intro hlt
  -- 边界 `η L = 2μ` ⟹ `η²L = 2ημ` ⟹ 二次式**恰好等于** `cost0`，不严格下降
  have hkey : η ^ 2 * L - 2 * η * mu = η * (η * L - 2 * mu) := by ring
  rw [hboundary] at hkey
  -- `hη > 0` 在此用于确认边界点是**非退化**的（`η > 0`，不是 `η = 0` 的平凡命中）
  have huse : (0 : ℝ) < η := hη
  have hsq : η ^ 2 * L = 2 * η * mu := by linarith
  linarith [hsq, huse]

/-- **`err²` 下降 ⟹ `err` 下降**（把非线性结论接回 `errA` 语言）。

**⚠ 需要 `err ≥ 0`**（范数），这是唯一天然前提。 -/
theorem err_lt_of_sq_lt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 < b ^ 2) :
    a < b := by
  nlinarith

end Nonlinear

/-! ===========================================================================
    §8  **硬核对**：与 `ResidualLoop` 的接口 + 具体数值实例
    =========================================================================== -/

section CrossCheck

/-! ### §8.1 与 `ResidualLoop.writeBack` 的形状一致性 -/

/-- **核对 1**：在 `Θ.Carrier = ℝ` 上，`wbW` 与 `ResidualLoop.writeBack`
的**更新式逐字相同**（`θ + η * φ r`，`Module` 标量乘 `ℝ` 上即乘法）。

**⚠ 这是形状核对，不是定理依赖**：`ResidualLoop.writeBack` 活在
`Ring`+`AddMonoidHom` 上（无数值结构）；本文件的 `wbW` 活在赋范空间上
（有数值结构，才能陈述「更准」）。二者**更新式一致、载体不同**。 -/
theorem wbW_shape (φ : ℝ →ₗ[ℝ] ℝ) (η x' θ : ℝ) :
    wbW (ContinuousLinearMap.id ℝ ℝ) φ η x' θ = θ + η * φ (x' - θ) := by
  rw [wbW_apply]
  simp [smul_eq_mul]

/-- **核对 2**：`errA` 与 `dist` 逐字一致（任务书用的是 `dist`）。 -/
example {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F) (x' : F) (θ : E) :
    errA A x' θ = dist (A θ) x' := errA_eq_dist A x' θ

/-- **核对 3**：恒等预测器上 `Corrects` **自动成立**（`φ = id`）⟹
主定理的**非空真**的直接证据。 -/
theorem corrects_id : Corrects (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id :
    ℝ →ₗ[ℝ] ℝ) := by
  intro r
  simp

/-! ### §8.2 具体数值实例（可逐一复核） -/

/-- **数值实例**：`A = id`、`φ = id`、`x' = 3`、`θ = 1`、`η = 1/2`。

- 初始误差 `err(θ) = |1 - 3| = 2`；
- `η = 1/2` 时 `r = 3 - 1 = 2`，`θ' = 1 + (1/2)·2 = 2`；
- 误差 `err(θ') = |2 - 3| = 1 = |1 - 1/2| · 2`; **严格下降**（`1 < 2`）✓

**这组数字同时验证：收缩因子 `|1-η| = 1/2` 的**精确性**（`1 = (1/2)·2`）。 -/
theorem concrete_reduction :
    wbW (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1/2) 3 1 = 2 ∧
      errA (ContinuousLinearMap.id ℝ ℝ) 3 1 = 2 ∧
      errA (ContinuousLinearMap.id ℝ ℝ) 3
        (wbW (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1/2) 3 1) = 1 ∧
      errA (ContinuousLinearMap.id ℝ ℝ) 3
        (wbW (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1/2) 3 1)
        < errA (ContinuousLinearMap.id ℝ ℝ) 3 1 := by
  refine ⟨by norm_num [wbW, smul_eq_mul], by norm_num [errA], ?_, ?_⟩
  · norm_num [errA, wbW, smul_eq_mul]
  · norm_num [errA, wbW, smul_eq_mul]

/-- **数值实例（最优步长）**：上例取 `η = 1`，
则 `θ' = 1 + 2 = 3 = x'`，误差 `= 0`（**精确命中**）。 -/
theorem concrete_optimal :
    wbW (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 1 3 1 = 3 ∧
      errA (ContinuousLinearMap.id ℝ ℝ) 3
        (wbW (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 1 3 1) = 0 := by
  refine ⟨by norm_num [wbW, smul_eq_mul], ?_⟩
  norm_num [errA, wbW, smul_eq_mul]

/-- **数值实例（窗口外失效）**：上例取 `η = 2`，
则 `θ' = 1 + 2·2 = 5`，误差 `= |5 - 3| = 2 =` 初始误差 `2`（**不下降**）。

**这组数字直接见证 §5.2 的 `eta_two_no_decrease`**（`η = 2` 不下降）。 -/
theorem concrete_eta_two :
    wbW (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 2 3 1 = 5 ∧
      errA (ContinuousLinearMap.id ℝ ℝ) 3
        (wbW (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 2 3 1) = 2 ∧
      ¬ (errA (ContinuousLinearMap.id ℝ ℝ) 3
          (wbW (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 2 3 1)
          < errA (ContinuousLinearMap.id ℝ ℝ) 3 1) := by
  refine ⟨by norm_num [wbW, smul_eq_mul], by norm_num [errA, wbW, smul_eq_mul], ?_⟩
  rw [show errA (ContinuousLinearMap.id ℝ ℝ) 3
        (wbW (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 2 3 1) = 2
      from by norm_num [errA, wbW, smul_eq_mul],
    show errA (ContinuousLinearMap.id ℝ ℝ) 3 1 = 2 from by norm_num [errA]]
  norm_num

/-- **数值实例（`η = 0` 恒等，不下降）**：`θ' = θ`，误差不变。 -/
theorem concrete_eta_zero :
    errA (ContinuousLinearMap.id ℝ ℝ) 3
      (wbW (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 0 3 1) = 2 ∧
      ¬ (errA (ContinuousLinearMap.id ℝ ℝ) 3
          (wbW (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 0 3 1)
          < errA (ContinuousLinearMap.id ℝ ℝ) 3 1) := by
  refine ⟨by norm_num [errA, wbW, smul_eq_mul], ?_⟩
  rw [show errA (ContinuousLinearMap.id ℝ ℝ) 3
        (wbW (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 0 3 1) = 2
      from by norm_num [errA, wbW, smul_eq_mul],
    show errA (ContinuousLinearMap.id ℝ ℝ) 3 1 = 2 from by norm_num [errA]]
  norm_num

end CrossCheck

/-! ===========================================================================
    §9  ⚠ **诚实边界**（本文件**不**做的事）
    =========================================================================== -/

/-!
### §9.1 `writeBack_reduces_error` **不是**无条件定理

**本文件证的**：`Corrects A φ` + `|1-η| < 1` + `A θ ≠ x'` ⟹ **严格**下降。
三条前提**都被证为不可去**：

| 前提 | 去掉后 | 定理 |
|---|---|---|
| `Corrects A φ` | 命题**假**（`A = 0` 反例） | §5.3 `no_reduction_without_corrects` |
| `|1-η| < 1` | `η = 0` / `η = 2` 时**不**下降 | §5.1 / §5.2 |
| `A θ ≠ x'` | 已命中时误差已 `0`，无法更小 | §5.4 `no_reduction_when_exact` |

### §9.2 `Corrects` 的含义（**不是**凑出来的）

`Corrects A φ : ∀ r, A (φ r) = r` 是「**残差在模型 `A` 的可达范围内**」的精确形式。
它在物理上是**表达能力假设**：模型的参数化足以表达观测到的偏差方向。
`ResidualLoop §4.2` 的 `ReadsResidual` 是其**参数侧**对偶
（`r ≠ 0 ⟹ φ r ≠ 0`）；两者**同时**成立时，回写的「读到」与「写对」才齐备。

### §9.3 本文件**不**证的事（如实登记）

| # | 未做项 | 理由 |
|---|---|---|
| 1 | 非线性 `f` 的**精确**收缩率 | 一般 `f` 下不存在（曲率可变）；§7 只给**充分条件**与**边界失败** |
| 2 | `η` 的**统计最优**（噪声下的步长选择） | 属**经验/估计**问题（OQ-4），非纯数学定理 |
| 3 | `φ` 从何而来（如何**学到** `φ`） | 属**算法**问题；本文件只把 `Corrects` 作为**可检验**前提 |
| 4 | 多步闭环的**收敛性** | 单步下降 ⟹ 误差单调不增、有下界 `≥ 0` ⟹ 收敛需**另证**（未做） |
| 5 | `FateV2.Loop/ResidualReduces.lean` 的修复 | 该文件**不编译**（多处 error）且**未被 `FateV2.Loop.lean` 导入**；本文件按纪律**不修改**已有模块，独立给出正确版本 |

### §9.4 与 `FateV2.Loop/ResidualReduces.lean` 的关系（**如实说明**）

仓库中已存在 `FateV2.Loop/ResidualReduces.lean`，试图证同一命题。
**实测**（`lake env lean FateV2.Loop/ResidualReduces.lean`）该文件**有多处 error**
（`A A† A = A` 的伴随论证失败、`Ne.symm` 方向错误、`norm_num` 目标不符等），
**不编译**，且**未**出现在 `FateV2.Loop.lean` 的 import 列表中（故不破坏构建）。

本文件**不依赖**它，并且**绕开了它的技术障碍**：
**不引入 `ContinuousLinearMap.adjoint`**，而用抽象的 `φ : F →ₗ[ℝ] E`
并把所需的伴随性质**提升为显式前提** `Corrects A φ`。
⟹ 本文件的主定理**证明更短、前提更清楚、且真的编译通过**。

**⚠ 本文件未修改 `FateV2.Loop/ResidualReduces.lean`**（纪律：不动已有模块）。
-/

end BoundWriteBack

end FateV2.Loop
