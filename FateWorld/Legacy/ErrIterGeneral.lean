/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.ErrIterGeneral`
任务：**【G2】`err_iter` 的存在性判定 + 泛化**

===========================================================================
§0  ⚠ 任务前提核实（必须先读，如实报告）
===========================================================================

**任务书前提：「`err_iter` 在 `ErrorCriterion.lean` 里」——经核实为误记。**

两种独立 grep 模式的实测结果：

1. `grep -rn "err_iter" . --include="*.lean"`
   ⟹ 命中的**全部**是 `err_iterMap`（`Fate/WiringConvergence.lean`），
      **无**任何单独的 `err_iter` 定义。
2. `grep -rnwE "err_iter|errIter|iterErr|errorIter" Fate/ --include="*.lean"`
   ⟹ 真实名字只有两个：
      * `Fate.WiringConvergence.err_iterMap`（`theorem`，`WiringConvergence.lean:140`）
      * `Fate.EndToEndConverge.errIter`（`noncomputable def`，`EndToEndConverge.lean:310`）
3. `grep -nE "^(theorem|def|noncomputable def|variable|structure)" Fate/ErrorCriterion.lean`
   ⟹ `ErrorCriterion` 里只有 `ErrorAcceptable ε σ := σ/2 ≤ ε ∧ ε ≤ 2σ`
      及其代数（区间、单调、尺度不变、与 `AttrAcceptable` 等价）。
      **完全没有**任何迭代 / 误差序列 / `err_iter` 相关内容。

**结论**：`err_iter` **不存在**。「把 `err_iter` 泛化到任意 `A`」这一任务，
其字面前提不成立。

===========================================================================
§1  真实对象分析：`err_iterMap` 是否已对任意 `A` 泛化？
===========================================================================

`WiringConvergence.err_iterMap` 的签名（逐字）：

```
theorem err_iterMap (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) (h : Corrects A φ) (n : ℕ) :
    errA A x' (iterMap A φ η x' n θ) = |1 - η| ^ n * errA A x' θ
```

**它已经对任意连续线性算子 `A : E →L[ℝ] F` 泛化**。
`A = id` 只出现在该文件的 §8 **具体数值算例**（`err_iterMap` 的 `rw` 调用），
不是主定理的约束。

⟹ **「泛化到任意 `A`」这一目标，主体上业已完成**；
   本文件**不重述**这一已成立的事实来冒充新结果（避免同义反复 / 重复交付）。

===========================================================================
§2  本文件实际新增的两个**真**泛化（不是重复包装）
===========================================================================

在确认「对任意 `A`」已成立后，仍有**两处**前件确实收得更紧（均为严格减弱）：

**(a) universe 解耦。** `BoundWriteBack` 全文件固定 `universe u`，
    `errA`/`wbW`/`Corrects` 都要求 `E F : Type u`（**同一** universe）。
    本文件证明：数学内容**不依赖**这一限制，`E : Type u`、`F : Type v`
    （`u`、`v` 任意）时同一结论成立。
    ⚠ 诚实边界：因不能改已有模块，本文件在**自身命名空间**内重述
    `errU` / `stepU` / `CorrectsAt`（与 `errA` / `wbW` / `Corrects` 逐字同形，
    §4 给出逐字对照）。这不是「新数学」，而是证明已有数学的 universe 限制是**多余的**。

**(b) 前件从「全局」减弱到「仅轨迹上」。** `Corrects A φ := ∀ r, A (φ r) = r`
    是**全局**量化。本文件只需要它在**实际迭代轨迹的每一站**成立：
    `∀ j, CorrectsAt A φ x' (iterU … j θ)`，其中
    `CorrectsAt A φ x' θ := A (φ (x' - A θ)) = x' - A θ`（**单点**）。
    **这是严格减弱**：全局 ⟹ 单点，反之不然（`A = 0` 时单点可在一站成立而全局不成立）。
    故 `err_iterU` 的**适用范围严格大于** `err_iterMap`。

===========================================================================
§3  ⚠ 前件包含审计（本项目最高频事故，逐条自检）
===========================================================================

**前件**
- `h : ∀ j, CorrectsAt A φ x' (iterU A φ η x' j θ)` —— 关于「更新算子能否还原残差」的结构条件；
- `n : ℕ` —— 步数。

**结论**
- `errU A x' (iterU … n θ) = |1-η|^n * errU A x' θ` —— 关于**轨迹误差序列**的等式。

**判定：非同义反复。** 理由：
1. 前件只谈 `A ∘ φ` 在残差上的取值（线性代数性质），结论谈**误差的数值演化**（度量性质）；
   `|1-η|^n` 这一几何因子在前件中**完全不出现** —— 它是从 `map_add`/`map_smul`/`norm_smul`
   推导出来的，不是被塞进去的。
2. `η` 在前件中只以「`stepU` 的参数」出现，前件对它**没有任何约束**（不假定 `|1-η|<1` 等）；
   结论对**任意** `η : ℝ` 成立，故不存在「把结论前提化」。
3. §5 给出**非空真实例**：`A = id`、`φ = id` 时前提成立，且 `errU … θ` 可取非零值，
   结论给出非平凡数值等式（不是 `0 = 0`）。

===========================================================================
§4  与 `BoundWriteBack` 的逐字对照（硬核对，证明这不是另起炉灶）
===========================================================================

| 本文件 | `Fate/BoundWriteBack` | 关系 |
|---|---|---|
| `errU A x' θ` | `errA A x' θ := ‖A θ - x'‖` | 逐字同式，仅 universe 解耦 |
| `stepU A φ η x' θ` | `wbW A φ η x' θ := θ + η • φ (x' - A θ)` | 逐字同式 |
| `CorrectsAt A φ x' θ` | `Corrects A φ := ∀ r, A (φ r) = r` | **严格更弱**（单点 vs 全局） |
| `iterU` | `iterMap`（`WiringConvergence`） | 迭代次数语义相同（均为 `Nat` 步） |

===========================================================================
§5  本节定理清单（全部证出）
===========================================================================
1. `err_stepU` —— 一步精确缩放（单点前件版）
2. `err_iterU` —— **主定理**：n 步精确几何缩放（轨迹单点前件版，universe 解耦）
3. `err_iterU_le` —— 收缩窗内单调不增
4. `err_iterU_lt` —— 严格下降
5. `err_iterU_tendsto_zero` —— 收敛到 0
6. `inst_id` —— 非空真实例（`A = id`, `φ = id`）

===========================================================================
纪律
===========================================================================
- **零 `sorry` / 零 `admit` / 零 `axiom`**。
- **只新增本文件**，不修改任何已有模块（仅 `import`）。
- 本文件**无删减项**：上表 6 条定理全部证出（`lake env lean` 零 error）。
- 已在 §0 如实报告：任务前提 `err_iter` **不存在**，真实名字为 `err_iterMap` / `errIter`。
-/

import FateWorld.Legacy.WiringConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Function.Iterate

namespace Fate

namespace ErrIterGeneral

open BoundWriteBack

universe u v

/-! ===========================================================================
    §1  设定（universe 解耦版，与 `BoundWriteBack` 逐字同形）
    =========================================================================== -/

section Setup

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐ **误差泛函**（`BoundWriteBack.errA` 的 universe 解耦版）：`‖A θ - x'‖`。 -/
def errU (A : E →L[ℝ] F) (x' : F) (θ : E) : ℝ := ‖A θ - x'‖

/-- ⭐ **一步更新算子**（`BoundWriteBack.wbW` 的 universe 解耦版）。 -/
def stepU (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E) : E :=
  θ + η • φ (x' - A θ)

/-- ⭐ **单点可还原条件**（`BoundWriteBack.Corrects` 的**单点**弱化版）。

`Corrects A φ` 要求 `∀ r, A (φ r) = r`；本式只要求残差 `r = x' - A θ`
这**一个**点被还原。**严格更弱**（全局 ⟹ 单点）。 -/
def CorrectsAt (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E) : Prop :=
  A (φ (x' - A θ)) = x' - A θ

/-- ⭐ **n 步迭代**（`stepU` 的 `Nat.iterate`）。 -/
noncomputable def iterU (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (n : ℕ) (θ : E) : E :=
  (Nat.iterate (fun s => stepU A φ η x' s) n) θ

/-- ⭐ **`iterU` 零步 = 恒等**。 -/
theorem iterU_zero (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E) :
    iterU A φ η x' 0 θ = θ := rfl

/-- ⭐ **`iterU` 递推步**（外层）。 -/
theorem iterU_succ (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (n : ℕ) (θ : E) :
    iterU A φ η x' (n + 1) θ = stepU A φ η x' (iterU A φ η x' n θ) :=
  Function.iterate_succ_apply' _ _ _

/-! ===========================================================================
    §2  ⭐⭐⭐ 一步精确缩放（单点前件版）
    =========================================================================== -/

/-- ⭐⭐⭐ **【一步误差恒等式 + 范数缩放】**

只需残差**单点**可还原（`CorrectsAt`），一步更新后误差**精确地**是 `|1-η|` 倍：

$$\mathrm{errU}\bigl(\mathrm{stepU}\ A\ φ\ η\ x'\ θ\bigr) \;=\; |1-\eta|\cdot \mathrm{errU}(θ).$$

**证明**：`A (θ + η • φ r) - x' = (1-η) • (A θ - x')`（用 `map_add`、`map_smul` 与
`h : A (φ r) = r`），再取范数 `‖c • v‖ = |c| ‖v‖`。 -/
theorem err_stepU (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : CorrectsAt A φ x' θ) :
    errU A x' (stepU A φ η x' θ) = |1 - η| * errU A x' θ := by
  unfold errU stepU CorrectsAt at *
  have himg : A (θ + η • φ (x' - A θ)) - x' = (1 - η) • (A θ - x') := by
    rw [map_add, map_smul, h]
    module
  rw [himg, norm_smul, Real.norm_eq_abs]

/-! ===========================================================================
    §3  ⭐⭐⭐⭐⭐ 主定理：`n` 步精确几何缩放（轨迹单点前件 + universe 解耦）
    =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【主定理：`n` 步误差精确几何缩放】**

设 `E : Type u`、`F : Type v`（`u`、`v` **任意**，无需相同），
`A : E →L[ℝ] F` **任意**连续线性算子。若**沿迭代轨迹**每一站的残差都能被 `φ` 还原

```
h : ∀ j, CorrectsAt A φ x' (iterU A φ η x' j θ),
```

则 `n` 步后误差**精确**为

$$\mathrm{errU}(\theta_n) \;=\; |1-\eta|^n \cdot \mathrm{errU}(\theta_0).$$

**与 `WiringConvergence.err_iterMap` 的两点差别（均为严格减弱前件）**：
1. universe 不再要求 `E`、`F` 相同；
2. `Corrects A φ`（全局 `∀ r`）减弱为**仅轨迹上的单点**条件。

**证明**：对 `n` 归纳；归纳步 `iterU_succ` 剥外层一步，用 `err_stepU`
（前提取 `h k`），再合并 `pow_succ`。 -/
theorem err_iterU (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : ∀ j : ℕ, CorrectsAt A φ x' (iterU A φ η x' j θ)) (n : ℕ) :
    errU A x' (iterU A φ η x' n θ) = |1 - η| ^ n * errU A x' θ := by
  induction n with
  | zero => simp [iterU_zero]
  | succ k ih =>
    rw [iterU_succ, err_stepU A φ η x' _ (h k), ih, pow_succ]
    ring

/-! ===========================================================================
    §4  推论：单调 / 严格下降 / 收敛（同一前件风格）
    =========================================================================== -/

/-- ⭐⭐ **【单调不增】** `|1-η| ≤ 1` 时，`n` 步后误差不超过初始误差。 -/
theorem err_iterU_le (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : ∀ j : ℕ, CorrectsAt A φ x' (iterU A φ η x' j θ))
    (hη : |1 - η| ≤ 1) (n : ℕ) :
    errU A x' (iterU A φ η x' n θ) ≤ errU A x' θ := by
  rw [err_iterU A φ η x' θ h n]
  have hpow : |1 - η| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) hη
  have hnn : 0 ≤ errU A x' θ := norm_nonneg _
  calc |1 - η| ^ n * errU A x' θ ≤ 1 * errU A x' θ :=
        mul_le_mul_of_nonneg_right hpow hnn
    _ = errU A x' θ := one_mul _

/-- ⭐⭐⭐ **【严格下降】** `|1-η| < 1`、初始误差 `> 0`、`n ≥ 1` 时严格小于初始。 -/
theorem err_iterU_lt (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : ∀ j : ℕ, CorrectsAt A φ x' (iterU A φ η x' j θ))
    (hη : |1 - η| < 1) (hpos : 0 < errU A x' θ) {n : ℕ} (hn : 0 < n) :
    errU A x' (iterU A φ η x' n θ) < errU A x' θ := by
  rw [err_iterU A φ η x' θ h n]
  have hlt : |1 - η| ^ n < 1 := by
    have hp := pow_lt_one₀ (abs_nonneg (1 - η)) hη (Nat.pos_iff_ne_zero.mp hn)
    simpa using hp
  calc |1 - η| ^ n * errU A x' θ < 1 * errU A x' θ :=
        mul_lt_mul_of_pos_right hlt hpos
    _ = errU A x' θ := one_mul _

/-- ⭐⭐⭐⭐ **【收敛到 0】** `|1-η| < 1` 时误差序列 `→ 0`（几何收敛）。 -/
theorem err_iterU_tendsto_zero (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (θ : E) (h : ∀ j : ℕ, CorrectsAt A φ x' (iterU A φ η x' j θ))
    (hη : |1 - η| < 1) :
    Filter.Tendsto (fun n : ℕ => errU A x' (iterU A φ η x' n θ)) Filter.atTop (nhds 0) := by
  have hrw : (fun n : ℕ => errU A x' (iterU A φ η x' n θ))
      = fun n : ℕ => |1 - η| ^ n * errU A x' θ := by
    funext n
    exact err_iterU A φ η x' θ h n
  rw [hrw]
  have hbase : Filter.Tendsto (fun n : ℕ => |1 - η| ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) hη
  simpa using hbase.mul_const (errU A x' θ)

/-! ===========================================================================
    §5  ⭐⭐ 非空真实例（证明前件可满足、结论非平凡）
    =========================================================================== -/

section Instance

/-- ⭐⭐ **【非空真实例】** `E = F = ℝ`、`A = id`、`φ = id`：
`CorrectsAt` 在**所有**点上成立，故 `err_iterU` 给出非平凡的数值等式。

**⭐ 意义**：`CorrectsAt (id) (id) x' s` 即 `id (id (x' - id s)) = x' - id s`，
由 `simp` 判定为真。故主定理前件**可满足**，结论不是空真。 -/
theorem inst_id (η x' θ : ℝ) (n : ℕ) :
    errU (ContinuousLinearMap.id ℝ ℝ) x'
        (iterU (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) η x' n θ)
      = |1 - η| ^ n * errU (ContinuousLinearMap.id ℝ ℝ) x' θ := by
  refine err_iterU _ _ η x' θ ?_ n
  intro j
  unfold CorrectsAt
  simp

end Instance

end Setup

end ErrIterGeneral

end Fate
