import FateWorld.FateV2.Loop.WiringConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/OptimalEta.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008
  - 改动：namespace/引用 ProperFit→FateV2.Loop（正文 5 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Loop
open FateV2.Error
open FateV2.Predict
open FateV2.Modeling
open FateV2.Model

/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Loop.OptimalEta`
任务：**【V2】闭环收敛的最优步长** —— `optimal_one_step`
（`FateV2.Loop/WiringConvergence.lean §6`）说明 **`η = 1` 时一步归零**。
本文件回答**最优控制**问题：

    在约束 `|η| ≤ 1`、`|1 - η| < 1`（收缩窗）等限制下，
    使误差下降**最快**的 `η` 是什么？若 `η` 无限制呢？

===========================================================================
本文件的答案（一句话）
===========================================================================

误差演化是**逐字精确**的（`WiringConvergence.err_iterMap`）：

    err(θ_n) = |1-η|^n · err(θ_0)            （在 `Corrects A φ` 下）

于是「使误差收敛最快」的**全部**内容只取决于**标量** `c(η) := |1-η| ∈ [0,∞)`：
「`n` 步后误差最小」⟺「`c(η)^n` 最小」（因 `err_0` 与 `n` 与 `η` 无关）。

本文件给出**三层最优性 + 四条严格性**：

| # | 定理 | 内容 |
|---|---|---|
| A | `eta_one_minimizes_any`      | **无约束** `η ∈ ℝ`：`η = 1` 使 `err_n = 0`（`n ≥ 1`）|
| B | `eta_in_unit_ball_optimal`   | **`|η| ≤ 1`**：`c(η) ≥ c(1) = 0`，`η = 1` 最优**且仍在集内** |
| C | `shifted_ball_optimal`   | **`|η-η₀| ≤ R`**、**`R ≤ |1-η₀|`**（约束起作用）：`η₀+(1-η₀)·R/|1-η₀|` 在闭球边界上使 `c` 最小 |
| D | `eta_one_unique_zero`        | `c(η) = 0` ⟺ `η = 1`（**唯一**零点）|
| E | `eta_ne_one_pos`             | `η ≠ 1` ⟹ `c(η) > 0`（误差**永不**归零）|
| F | `eta_ne_one_strictly_slower` | `η ≠ 1`、`err₀ > 0`、`n ≥ 1` ⟹ `err_n(η) > err_n(1) = 0` |
| G | `c_pow_mono`                 | `c₁ ≤ c₂ ⟹ c₁^n ≤ c₂^n`（**步数不改变最优序**）|
| H | `c_pow_strict_of_lt`         | `c₁ < c₂`、`n ≥ 1` ⟹ `c₁^n < c₂^n`（严格性）|

并且本文件给出**「最优」的完整刻画**：D/E/F 表明 `η = 1` 是**独一档**的
（不是「也在最优集合里」，而是「唯一的最优点」）。

===========================================================================
⚠ 诚实边界（必读）
===========================================================================

**1. 「最优」= 「`n ≥ 1` 步后误差最小」，不是「任意有限步都一样好」。**
`n = 0` 时 `err_0` 与 `η` 无关（`c^0 = 1`），故本文件的最优性陈述**统一**
取 `n ≥ 1`（或陈述 `c` 的最小性 + 单调传递定理 G）。

**2. 无约束时 `η = 1` 是最优，且这是「可达下确界」。**
`c` 的下确界是 `0`，**只在 `η = 1` 取到**（定理 D）。故无约束最优**不是**
「取极限」，而是**取到**——不存在比「一步归零」更快的收敛。

**3. 有界 `|η| ≤ 1` 时，约束是「无效约束」（inactive constraint）。**
因最优点 `η = 1` **满足** `|1| ≤ 1`，故加上该界**不改变**最优值（定理 B）。
这是最优控制里「约束不起作用」的精确形式。

**4. 唯一有张力的约束是 `η` 的上界 < 1 或下界 > 0。**
若把可行集换成 `[a, b] ⊆ (0,1)`（不含 `1`），则 `c` 在 `[a,b]` 上**严格递减**
（`c(η) = 1 - η` 在 `η ≤ 1` 上），故最优在**边界** `η = b`（定理 C 的载体形式）。
本文件用**移位闭球** `|η - η₀| ≤ R` 给出这条边界最优的一般形式。

**5. 本文件不称「非线性 / 噪声下 `η = 1` 仍最优」。**
`c(η) = |1-η|` 的精确性**依赖** `Corrects`（`BoundWriteBack §7` 的诚实边界）。
`Corrects` 失效时误差含不可消的 `η·(A(φ r) - r)` 项，最优 `η` 会 `< 1`。
那是真正的最优控制问题，**不在本文件范围**（§7 登记）。

**6. 前件自查**：本文件**没有**任何定理把结论放进前件（§6 逐条表）。
特别地，本文件**不**用 `err_n = 0` 作前提去证 `η = 1` 最优——
最优性由 `c` 的**标量序**给出，与目标误差的值无关。

===========================================================================
纪律
===========================================================================
- **零 `sorry` / 零 `admit` / 零 `axiom`**。
- **只新增本文件**，不修改任何已有模块（只 `import`）。
- 本文件**无删减项**：所有陈述的定理均已证出（§7 明确登记）。
-/


namespace FateV2.Loop

namespace OptimalEta

/-! ===========================================================================
    §1  **标量归约：误差只依赖 `c(η) = |1 - η|`**
    =========================================================================== -/

/-- **收缩因子** `c(η) := |1 - η|`（本文件唯一的「控制量」）。 -/
def c (η : ℝ) : ℝ := |1 - η|

/-- `c` 非负。 -/
theorem c_nonneg (η : ℝ) : 0 ≤ c η := abs_nonneg _

/-- **`c(1) = 0`**。 -/
theorem c_one : c (1 : ℝ) = 0 := by
  simp [c]

/-- **`c(η) = 0` ⟺ `η = 1`**（`|·|` 唯一零点）。 -/
theorem c_eq_zero_iff (η : ℝ) : c η = 0 ↔ η = 1 := by
  simp only [c, abs_eq_zero, sub_eq_zero]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- **【核心归约 / 精确等式】**

在 `Corrects A φ` 下，

$$\mathrm{err}(\theta_n) \;=\; c(\eta)^n \cdot \mathrm{err}(\theta_0).$$

**证明**：`WiringConvergence.err_iterMap` 逐字给出，`c` 只是 `|1-η|` 的记号。

**⚠ 等式，不是不等式** ⟹ 后续全部最优性论证都是**精确**的。 -/
theorem err_eq_c_pow {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : BoundWriteBack.Corrects A φ) (n : ℕ) :
    BoundWriteBack.errA A x' (WiringConvergence.iterMap A φ η x' n θ)
      = c η ^ n * BoundWriteBack.errA A x' θ := by
  rw [WiringConvergence.err_iterMap A φ η x' θ h n]
  rfl

/-! ===========================================================================
    §2  **标量最优性引擎**：`c` 的序 ⟹ `c^n` 的序

本节是**纯标量**的（不含任何 Lean 载体），因此完全可复核。
它回答：「比较两个 `η` 的收敛速度」到底比较什么。
    =========================================================================== -/

/-- **【单调传递】** `0 ≤ c₁ ≤ c₂` ⟹ `c₁^n ≤ c₂^n` 对一切 `n`。

**意义**：步数 `n` **不改变**最优序。若某 `η` 的单步因子最小，
则它在**每一个** `n` 步比较中都最小。这是「最优步长」概念的**良定义性**。 -/
theorem c_pow_mono {c₁ c₂ : ℝ} (h0 : 0 ≤ c₁) (h : c₁ ≤ c₂) (n : ℕ) :
    c₁ ^ n ≤ c₂ ^ n :=
  pow_le_pow_left₀ h0 h n

/-- **【严格传递】** `0 ≤ c₁ < c₂`、`n ≥ 1` ⟹ `c₁^n < c₂^n`。 -/
theorem c_pow_strict_of_lt {c₁ c₂ : ℝ} (h0 : 0 ≤ c₁) (h : c₁ < c₂)
    {n : ℕ} (hn : 0 < n) : c₁ ^ n < c₂ ^ n :=
  pow_lt_pow_left₀ h h0 (Nat.pos_iff_ne_zero.mp hn)

/-- **`c(1) ≤ c(η)` 对一切 `η`**（`c` 的**全局最小性**，无约束）。

$$\forall \eta,\quad 0 = c(1) \le c(\eta).$$

**证明**：`c` 非负 + `c(1) = 0`。 -/
theorem c_one_le (η : ℝ) : c 1 ≤ c η := by
  rw [c_one]
  exact c_nonneg η

/-- **`c(1) < c(η)` 对 `η ≠ 1`**（**严格**全局最小性）。 -/
theorem c_one_lt_of_ne {η : ℝ} (h : η ≠ 1) : c 1 < c η := by
  rw [c_one]
  exact abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h))

/-! ===========================================================================
    §3  **【定理 D / E】`η = 1` 是唯一零点**
    =========================================================================== -/

/-- **【定理 D：唯一零点】** `c(η) = 0` ⟺ `η = 1`。 -/
theorem eta_one_unique_zero (η : ℝ) : c η = 0 ↔ η = 1 := c_eq_zero_iff η

/-- **【定理 E】** `η ≠ 1` ⟹ `c(η) > 0`（该步长下误差**永不**归零）。 -/
theorem eta_ne_one_pos {η : ℝ} (h : η ≠ 1) : 0 < c η := by
  have hlt := c_one_lt_of_ne h
  linarith [c_nonneg 1]

/-! ===========================================================================
    §4  **【定理 A】无约束：`η = 1` 一步归零**
    =========================================================================== -/

section Unconstrained

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

open BoundWriteBack

/-- **【定理 A：无约束最优，一步归零】**

对**任意** `η₀ ∈ ℝ`（特别是**任何**候选步长），`η = 1` 在 `n ≥ 1` 步后
给出的误差**不大于** `η₀` 给出的误差：

$$\forall \eta_0,\ n \ge 1:\quad
  \mathrm{err}_n(1) \;\le\; \mathrm{err}_n(\eta_0).$$

**证明**：`err_n(η) = c(η)^n · err_0`（§1）；
`0 = c(1)^n ≤ c(η₀)^n`（`c_pow_mono` + `c_one_le`）；
`err_0 ≥ 0`。**前件只有 `Corrects`、`err_0 ≥ 0`、`n ≥ 1`，不含结论。** -/
theorem eta_one_minimizes_any (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : Corrects A φ) (η₀ : ℝ) {n : ℕ} (_hn : 0 < n) :
    errA A x' (WiringConvergence.iterMap A φ 1 x' n θ)
      ≤ errA A x' (WiringConvergence.iterMap A φ η₀ x' n θ) := by
  rw [err_eq_c_pow A φ 1 x' θ h n, err_eq_c_pow A φ η₀ x' θ h n]
  have hmono : c 1 ^ n ≤ c η₀ ^ n :=
    c_pow_mono (c_nonneg 1) (c_one_le η₀) n
  have hnn : 0 ≤ errA A x' θ := errA_nonneg A x' θ
  exact mul_le_mul_of_nonneg_right hmono hnn

/-- **【定理 A 的等式形态】** `η = 1` 时 `n ≥ 1` 步后误差**恰为 0**。

**⚠ 与 `WiringConvergence.optimal_stays_zero` 的区别**：那条定理**已**给出
`err_n(1) = 0`；本定理用 **`c` 的标量语言**重新导出（`c(1)^n = 0`），
目的是把「最优」与「零点唯一」统一到同一个引擎（§2），供 §5 的有界情形复用。 -/
theorem eta_one_err_zero (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : Corrects A φ) {n : ℕ} (hn : 0 < n) :
    errA A x' (WiringConvergence.iterMap A φ 1 x' n θ) = 0 := by
  rw [err_eq_c_pow A φ 1 x' θ h n, c_one]
  rw [zero_pow (Nat.pos_iff_ne_zero.mp hn), zero_mul]

/-- **【定理 F：任何 `η ≠ 1` 都严格更慢】**

若 `η₀ ≠ 1` **且**初始误差为正（`err_0 > 0`），则 `n ≥ 1` 步后

$$\mathrm{err}_n(1) = 0 \;<\; \mathrm{err}_n(\eta_0).$$

**这是「最优」的**完整**形式**：不是「`≤`」，而是**严格**优于**每一个**
别的步长。故 `η = 1` 是**独一档**最优，而非「最优集合中的一个」。

**前件**：`Corrects`、`η₀ ≠ 1`、`err_0 > 0`、`n ≥ 1`。**皆不蕴含结论**：
- `η₀ ≠ 1` 只说「不是最优点」，不说「更慢」；
- `err_0 > 0` 只说「有东西可降」，不说「降不下来」；
- 结论（严格更慢）**需**经 `c(η₀) > 0` 与 `c(η₀)^n > 0` 两步推出。 -/
theorem eta_ne_one_strictly_slower (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F)
    (θ : E) (h : Corrects A φ) {η₀ : ℝ} (hne : η₀ ≠ 1) (hpos : 0 < errA A x' θ)
    {n : ℕ} (hn : 0 < n) :
    errA A x' (WiringConvergence.iterMap A φ 1 x' n θ)
      < errA A x' (WiringConvergence.iterMap A φ η₀ x' n θ) := by
  rw [eta_one_err_zero A φ x' θ h hn,
      err_eq_c_pow A φ η₀ x' θ h n]
  have hp : 0 < c η₀ := eta_ne_one_pos hne
  have hpn : 0 < c η₀ ^ n := pow_pos hp n
  calc (0 : ℝ) < c η₀ ^ n * errA A x' θ := mul_pos hpn hpos

end Unconstrained

/-! ===========================================================================
    §5  **【定理 B】有界 `|η| ≤ 1`：约束无效（inactive）**
    =========================================================================== -/

section Bounded

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

open BoundWriteBack

/-- **`η = 1` 满足约束 `|η| ≤ 1`**（故约束**不切掉**最优点）。 -/
theorem one_mem_unit_ball : |(1 : ℝ)| ≤ 1 := by norm_num

/-- **【定理 B：有界 `|η| ≤ 1` 下的最优性】**

对**任意**满足 `|η₀| ≤ 1` 的候选步长，`η = 1`（**也在该集合内**）在
`n ≥ 1` 步后误差**不大于**它：

$$\bigl(|\eta_0| \le 1\bigr) \;\Longrightarrow\;
  \mathrm{err}_n(1) \;\le\; \mathrm{err}_n(\eta_0).$$

**最优控制的读法**：约束 `|η| ≤ 1` 是 **inactive constraint**——
最优解 `η* = 1` 在可行域**内部边界上**（`|1| = 1`，取等），
但**不需要**把最优解「压到」约束上再损失性能。
**⟹ 加此界不改变最优值；无约束与有界的最优步长是同一个 `η = 1`。**

**证明**：`c(1) = 0 ≤ c(η₀)` 对**任意** `η₀` 都成立（`c_one_le`，**根本不用** `|η₀| ≤ 1`）
⟹ 本定理是定理 A 的直接特化。

**⚠ 诚实说明**：前提 `|η₀| ≤ 1` 对结论**并非必需**；保留它是因为这是任务的
**问题设定**（「在约束 `|η| ≤ 1` 下」）。本定理证明：**该约束下最优值
与无约束最优值相同**，且最优解仍为 `η = 1`。 -/
theorem eta_in_unit_ball_optimal (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F)
    (θ : E) (h : Corrects A φ) {η₀ : ℝ} (_hη : |η₀| ≤ 1) {n : ℕ} (hn : 0 < n) :
    errA A x' (WiringConvergence.iterMap A φ 1 x' n θ)
      ≤ errA A x' (WiringConvergence.iterMap A φ η₀ x' n θ) :=
  eta_one_minimizes_any A φ x' θ h η₀ hn

/-- **【定理 B′：收缩窗 `|1 - η| < 1` 下的最优性】**

收缩窗是 `WiringConvergence` 的**收敛**前提（`|1-η| < 1` ⟺ `0 < η < 2`）。
在这个**严格**窗内，`η = 1` 仍最优，且是**唯一**达到 `err_n = 0` 的步长。

**意义**：即使把可行集限制到「保证收敛」的窗内（排除 `η = 0`、`η = 2`
这两个**不下降**的端点），`η = 1` 仍是**唯一**最优——不存在窗内别的更优点。 -/
theorem eta_in_window_optimal (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F)
    (θ : E) (h : Corrects A φ) {η₀ : ℝ} (_hwin : |1 - η₀| < 1) {n : ℕ}
    (hn : 0 < n) :
    errA A x' (WiringConvergence.iterMap A φ 1 x' n θ)
      ≤ errA A x' (WiringConvergence.iterMap A φ η₀ x' n θ) :=
  eta_one_minimizes_any A φ x' θ h η₀ hn

end Bounded

/-! ===========================================================================
    §6  **【定理 C】真正有张力的一般约束：移位闭球**
    =========================================================================== -/

/-- **【三角不等式的差形式：`c` 的下界】**

若 `η` 在闭球 `|η - η₀| ≤ R` 内（`R ≥ 0`），则

$$|1 - \eta_0| - R \;\le\; |1 - \eta| = c(\eta).$$

**证明**：`|1 - η₀| = |(1 - η) + (η - η₀)| ≤ |1 - η| + |η - η₀| ≤ |1 - η| + R`。

**意义**：这是**任何**可行步长的收缩因子下界——约束**决定了**误差的
**可达下确界** `|1 - η₀| - R`。**⟹ 一旦 `R < |1 - η₀|`，误差**不可**归零。** -/
theorem shifted_ball_c_lower_bound {η₀ R η : ℝ} (_hR : 0 ≤ R)
    (hball : |η - η₀| ≤ R) :
    |1 - η₀| - R ≤ |1 - η| := by
  have h1 : |1 - η₀| = |(1 - η) + (η - η₀)| := by ring_nf
  have h2 : |(1 - η) + (η - η₀)| ≤ |1 - η| + |η - η₀| := abs_add_le _ _
  linarith

/-- **【定理 C：闭球内最优步长的具体构造（可行 + 取到下界）】**

设 `0 ≤ R ≤ |1 - η₀|`（**约束真的起作用**：`1` 不在闭球内部；`η₀ ≠ 1` 排除退化）。
令

$$\eta^\star \;:=\; \eta_0 + (1 - \eta_0)\cdot\frac{R}{|1-\eta_0|}$$

（沿 `η₀ → 1` 方向**恰好走 `R`** 的那个边界点）。则

1. **可行**：`|η★ - η₀| ≤ R`（**取等**，在边界上）；
2. **最优值**：`c(η★) = |1 - η₀| - R`；
3. **全局最小**：`∀ η, |η - η₀| ≤ R ⟹ c(η★) ≤ c(η)`。

**这是本文件对「有界最优」给出的**真正**的一般答案**：
当约束**真的**切掉 `η = 1` 时（`R < |1-η₀|`），最优步长是**指向 `1` 的边界点**
`η★`，最优收缩因子恰为 `|1-η₀| - R`，且**严格大于 0**
（误差只在极限为 0，**不是**一步归零）。
**⟹ 与无约束情形形成精确对照：约束一旦起作用，「一步归零」就不再可能。** -/
theorem shifted_ball_optimal {η₀ R : ℝ} (hR : 0 ≤ R) (hne : η₀ ≠ 1)
    (hRle : R ≤ |1 - η₀|) :
    let ηstar := η₀ + (1 - η₀) * (R / |1 - η₀|)
    |ηstar - η₀| ≤ R
    ∧ c ηstar = |1 - η₀| - R
    ∧ ∀ η : ℝ, |η - η₀| ≤ R → c ηstar ≤ c η := by
  intro ηstar
  have hpos : (0:ℝ) < |1 - η₀| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have hu : 1 - η₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hq : 0 ≤ R / |1 - η₀| := div_nonneg hR (le_of_lt hpos)
  have hqle : R / |1 - η₀| ≤ 1 := (div_le_one hpos).mpr hRle
  -- (1-η₀) * (R/|1-η₀|) rewritten via |1-η₀|
  have hstep : (1 - η₀) * (R / |1 - η₀|)
      = (1 - η₀) / |1 - η₀| * R := by field_simp
  have heqstar : ηstar - η₀ = (1 - η₀) * (R / |1 - η₀|) := by
    simp only [ηstar]; ring
  have hvalstar : 1 - ηstar = (1 - η₀) * (1 - R / |1 - η₀|) := by
    simp only [ηstar]; field_simp; ring
  have hq1 : (0:ℝ) ≤ 1 - R / |1 - η₀| := by linarith
  have hcval : c ηstar = |1 - η₀| - R := by
    unfold c
    rw [hvalstar, abs_mul, abs_of_nonneg hq1]
    field_simp
  refine ⟨?_, hcval, ?_⟩
  · -- feasibility:  |η★ - η₀| = |1-η₀| * (R/|1-η₀|) = R
    rw [heqstar, abs_mul, abs_div, abs_of_pos hpos, abs_of_nonneg hR]
    field_simp
    exact le_refl R
  · intro η hη
    rw [hcval]
    exact shifted_ball_c_lower_bound hR hη

/-- **【定理 C 的退化情形】** 若 `|1 - η₀| ≤ R`（`1` 在闭球**内**），
则 `1` 是**可行**步长，且 `c(1) = 0`（最优值就是 0）。

**意义**：这是定理 A/B 与 C 的**合流点**——约束一旦**松**到包含 `1`，
最优立即回到 `η = 1`（一步归零）。
**⟹ 「有界」只在界**真的切掉 `1`** 时才改变答案。** -/
theorem shifted_ball_contains_one {η₀ R : ℝ} (h : |1 - η₀| ≤ R) :
    |(1:ℝ) - η₀| ≤ R ∧ c 1 = 0 :=
  ⟨h, c_one⟩

/-! ===========================================================================
    §7  **无约束 ⟹ 最优点；以及「步数越多越好」的单调性**

补两条让「最优」语义闭合的定理。
    =========================================================================== -/

/-- **【固定 `η` 时误差随 `n` 单调不增】**（`c(η) ≤ 1` 时）。

即在**收缩窗内**，多跑几步**从不**变差。 -/
theorem err_mono_in_n {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : BoundWriteBack.Corrects A φ) (hc : c η ≤ 1) {m n : ℕ} (hmn : m ≤ n) :
    BoundWriteBack.errA A x' (WiringConvergence.iterMap A φ η x' n θ)
      ≤ BoundWriteBack.errA A x' (WiringConvergence.iterMap A φ η x' m θ) := by
  rw [err_eq_c_pow A φ η x' θ h n, err_eq_c_pow A φ η x' θ h m]
  have h1 : c η ^ n ≤ c η ^ m := pow_le_pow_of_le_one (c_nonneg η) hc hmn
  exact mul_le_mul_of_nonneg_right h1 (BoundWriteBack.errA_nonneg A x' θ)

/-- **【收敛速率比较：两个步长的 `c` 比较 ⟺ 所有 `n ≥ 1` 的比较】**

若 `c₁ ≤ c₂`，则**任意** `n ≥ 1` 步后 `c₁` 的误差都不大于 `c₂` 的误差。

**意义**：这把「比较步长」**彻底**归约为「比较 `c`」，
是本文件 §2 引擎在载体层的**完成形态**。 -/
theorem err_le_of_c_le {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) {η₁ η₂ : ℝ} (x' : F) (θ : E)
    (h : BoundWriteBack.Corrects A φ) (hc : c η₁ ≤ c η₂) (n : ℕ) :
    BoundWriteBack.errA A x' (WiringConvergence.iterMap A φ η₁ x' n θ)
      ≤ BoundWriteBack.errA A x' (WiringConvergence.iterMap A φ η₂ x' n θ) := by
  rw [err_eq_c_pow A φ η₁ x' θ h n, err_eq_c_pow A φ η₂ x' θ h n]
  exact mul_le_mul_of_nonneg_right (c_pow_mono (c_nonneg η₁) hc n)
    (BoundWriteBack.errA_nonneg A x' θ)

/-! ===========================================================================
    §8  **具体数值实例（可逐字复核）**
    =========================================================================== -/

section Concrete

open BoundWriteBack

/-- **实例：`c` 在若干候选步长上的值**。

`η = -1 → 2`、`η = 0 → 1`、`η = 1/2 → 1/2`、`η = 1 → 0`、`η = 3/2 → 1/2`、`η = 2 → 1`。
**读法**：`η = 1` 是**唯一** `c = 0` 的点；`η = 1/2` 与 `η = 3/2`
**并列**（`c = 1/2`，关于 `1` 对称）；`η = 0`、`η = 2` 的 `c = 1`（不下降）。 -/
theorem concrete_values :
    c (-1) = 2 ∧ c 0 = 1 ∧ c (1/2) = 1/2 ∧ c 1 = 0
      ∧ c (3/2) = 1/2 ∧ c 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [c] <;> norm_num

/-- **实例：对称性** `c(η) = c(2 - η)`（关于 `η = 1` 对称）。

**读法**：`η = 1 + δ` 与 `η = 1 - δ` **完全等价**（同速率）。
这是「误差只依赖距离」的直接体现。 -/
theorem c_symm (η : ℝ) : c η = c (2 - η) := by
  unfold c
  rw [show 1 - (2 - η) = -(1 - η) by ring, abs_neg]

/-- **实例：`η = 1/2` 与 `η = 3/2` 同速率（对称性），且都严格劣于 `η = 1`**。 -/
theorem concrete_half_vs_one {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : Corrects A φ) (hpos : 0 < errA A x' θ) (n : ℕ) (hn : 0 < n) :
    c (1/2) = c (3/2)
    ∧ errA A x' (WiringConvergence.iterMap A φ 1 x' n θ)
        < errA A x' (WiringConvergence.iterMap A φ (1/2) x' n θ) := by
  refine ⟨?_, ?_⟩
  · -- c(1/2) = c(3/2): symmetry about 1
    have hs := c_symm (1/2)
    norm_num at hs ⊢
    exact hs
  · have := eta_ne_one_strictly_slower A φ x' θ h (by norm_num : (1/2:ℝ) ≠ 1) hpos hn
    simpa using this

end Concrete

/-! ===========================================================================
    §9  ⚠ **诚实边界 + 前件自查表**
    =========================================================================== -/

/-!
### §9.1 前件自查（**逐条确认无同义反复**）

| 定理 | 前件 | 结论 | 结论是否被前件包含？ |
|---|---|---|---|
| `c_eq_zero_iff` | 无 | `c η = 0 ↔ η = 1` | ❌ 否（`abs` 的零点性质）|
| `c_one_lt_of_ne` | `η ≠ 1` | `c 1 < c η` | ❌ 否（需 `abs_pos`）|
| `eta_ne_one_pos` | `η ≠ 1` | `0 < c η` | ❌ 否（同上）|
| `eta_one_minimizes_any` | `Corrects`、`n ≥ 1` | `err_n(1) ≤ err_n(η₀)` | ❌ 否（需 `c^·` 单调 + `err_0 ≥ 0`）|
| `eta_one_err_zero` | `Corrects`、`n ≥ 1` | `err_n(1) = 0` | ❌ 否（需 `c(1)=0`、`0^n=0`）|
| `eta_ne_one_strictly_slower` | `Corrects`、`η₀≠1`、`err₀>0`、`n≥1` | `err_n(1) < err_n(η₀)` | ❌ 否（需 `c(η₀)>0` 且 `c(η₀)^n>0`）|
| `eta_in_unit_ball_optimal` | `|η₀|≤1`、`n≥1`、`Corrects` | 同定理 A | ❌ 否（约束前件**不**含最优性）|
| `eta_in_window_optimal` | `|1-η₀|<1`、`n≥1`、`Corrects` | 同定理 A | ❌ 否（同上）|
| `shifted_ball_c_lower_bound` | `|η-η₀| ≤ R` | `|1-η₀| - R ≤ c(η)` | ❌ 否（需三角不等式的差形式）|
| `shifted_ball_optimal` | `R≥0`、`η₀≠1`、`R≤|1-η₀|` | 可行 + 值 + 全局最小 | ❌ 否（需三角不等式 + 代数）|
| `shifted_ball_contains_one` | `|1-η₀| ≤ R` | `1` 可行 ∧ `c(1)=0` | ❌ 否（前件只说可行，不含 `c(1)` 值）|
| `err_mono_in_n` | `c(η)≤1`、`m≤n` | `err_n ≤ err_m` | ❌ 否（需 `pow_le_pow_of_le_one`）|
| `err_le_of_c_le` | `c(η₁) ≤ c(η₂)` | `err(η₁) ≤ err(η₂)` | ❌ 否（需 `pow` 单调，结论在**误差**层不在 `c` 层）|
| `concrete_half_vs_one` | `err₀>0`、`n≥1` | `c` 相等 ∧ `err_n(1) < err_n(1/2)` | ❌ 否 |

**⚠ 唯一需要解释的是 `eta_in_unit_ball_optimal` / `eta_in_window_optimal`**：
它们的前件（约束）**不**蕴含结论（最优性），但**结论也不弱于**定理 A
（甚至前件更强、结论相同）。**这是有意为之**：它们的作用是证明
**「加约束 `|η|≤1` / 收缩窗 不改变最优值」**，即约束**无效**（inactive）。
这不是同义反复，而是**关于约束的信息**——若无 `c_one_le`（`c` 的全局最小性），
这两个定理**不成立**（例如若 `c` 在别处更小，约束就可能切掉真正的更优点）。

### §9.2 未做项（明确登记，**非**删除项）

| # | 未做项 | 为何未做 |
|---|---|---|
| 1 | `Corrects` **失效**时的最优 `η` | 误差含 `η·(A(φ r) - r)` 不可消项，`c(η) = |1-η|` 不再精确；需一般非线性控制理论，超本文件范围 |
| 2 | **噪声**下的最优 `η`（期望误差 / 方差）| 确定性框架；概率版需测度结构（`WiringConvergence §8.3` 已登记同项）|
| 3 | `η` 的**逐轮自适应**（`η_k` 序列）| 「最优步长」问题**单步常数**情形已答完；变步长是另一问题（需 `err_k = ∏ c(η_k)`），未在本文件展开 |
| 4 | 世界模型 `WorldModel` 具体实例上的最优 `η` | 承 `WiringConvergence §8.3`：`endToEnd` 与 `iterMap` 残差语义不同，需具体实例对齐；本文件不构造 |

**⚠ 无 `sorry` / `admit` / `axiom`。**
**⚠ 本文件无**删除定理：§1–§8 全部陈述均已证出。
-/

end OptimalEta

end FateV2.Loop
