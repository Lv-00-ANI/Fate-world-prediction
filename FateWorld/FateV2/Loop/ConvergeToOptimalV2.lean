import FateWorld.FateV2.Loop.BoundWriteBack
import FateWorld.FateV2.Loop.T1Verify

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ConvergeToOptimalV2.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008
  - 改动：namespace/引用 ProperFit→FateV2.Loop（正文 8 处，含 2 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Loop
open FateV2.Predict
open FateV2.Model
open FateV2.Modeling

/-! ===========================================================================
  §0  版本 2：收敛到唯一最优参数（作者第 39 轮裁决 D）

  ## 背景

  T-1 验证（`FateV2.Loop/T1Verify.lean`）确认：
  * **版本 1**：`Corrects A φ` ⟹ 误差按 `|1-η|^n` 收敛（**不需要 φ 单射**）。
  * **版本 2**：`Corrects A φ` + `φ` 单射 ⟹ 收敛到**唯一**最优参数。

  `FateV2.Loop/T1MultiDim.lean` 进一步给出：参数唯一的充要条件是**观测张成参数空间**。

  **作者裁决：D 两个版本并存**，不删除任何路线。

  ## 本文件的内容

  1. `optimal_unique`：`A` 单射 ⟹ 最优参数至多一个。
  2. `optimal_exists`：`x' ∈ range A` ⟹ 最优参数存在。
  3. `optimal_existsUnique`：`A` 双射 ⟹ 最优参数**恰有一个**。
  4. `fixed_iff_optimal`：`Corrects` + `φ` 单射 ⟹ `wbW` 不动点 ⟺ 最优。

  ## 诚实边界

  * 不声称「`φ` 单射是唯一途径」——`A` 单射/双射也可给唯一性。
  * 不改动版本 1 的任何定理。
  * 存在性需要 `x' ∈ range A`（或 `A` 满射）。
  =========================================================================== -/

namespace FateV2.Loop

namespace ConvergeToOptimalV2

open FateV2.Loop.BoundWriteBack

universe u

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### §1 什么是最优参数 -/

/-- **「θ 是最优参数」= `A θ = x'`**（预测恰好命中观测）。 -/
def IsOptimal (A : E →ₗ[ℝ] F) (x' : F) (θ : E) : Prop :=
  A θ = x'

/-- **最优参数至多一个**：`A` 单射即可。 -/
theorem optimal_unique (A : E →ₗ[ℝ] F) (hA : Function.Injective A)
    (x' : F) {θ₁ θ₂ : E} (h₁ : IsOptimal A x' θ₁) (h₂ : IsOptimal A x' θ₂) :
    θ₁ = θ₂ :=
  hA (h₁.trans h₂.symm)

/-- **最优参数存在**：只要 `x'` 在 `A` 的值域里。 -/
theorem optimal_exists (A : E →ₗ[ℝ] F) (x' : F) (hx : x' ∈ LinearMap.range A) :
    ∃ θ, IsOptimal A x' θ := by
  obtain ⟨θ, hθ⟩ := hx
  exact ⟨θ, hθ⟩

/-- **【主定理 1】`A` 双射 ⟹ 最优参数恰有一个。** -/
theorem optimal_existsUnique (A : E →ₗ[ℝ] F)
    (hAinj : Function.Injective A) (hAsurj : Function.Surjective A) (x' : F) :
    ∃! θ, IsOptimal A x' θ := by
  obtain ⟨θ, hθ⟩ := hAsurj x'
  exact ⟨θ, hθ, fun θ' h' => optimal_unique A hAinj x' h' hθ⟩

/-! ### §2 不动点 ⟺ 最优（在 `Corrects` + `φ` 单射下） -/

/-- **单步更新的展开**：`wbW θ - θ = η • φ (x' - A θ)`。 -/
theorem wbW_sub (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E) :
    (BoundWriteBack.wbW A φ η x' θ : E) - θ = η • φ (x' - A θ) := by
  unfold BoundWriteBack.wbW
  abel

/-- **【主定理 2】`Corrects` + `φ` 单射 ⟹ `wbW` 的不动点 ⟺ 最优参数。**

这是版本 2 的核心：把「全局收敛」归约为「不动点唯一」，
再用 §1 的唯一性得「收敛到唯一最优」。 -/
theorem fixed_iff_optimal (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (hη : η ≠ 0)
    (h : Corrects A φ) (hφ : Function.Injective φ) (x' : F) (θ : E) :
    (BoundWriteBack.wbW A φ η x' θ : E) = θ ↔ IsOptimal (A : E →ₗ[ℝ] F) x' θ := by
  have hstep : (BoundWriteBack.wbW A φ η x' θ : E) = θ ↔ φ (x' - A θ) = 0 := by
    rw [← sub_eq_zero (a := (BoundWriteBack.wbW A φ η x' θ : E)) (b := θ), wbW_sub]
    constructor
    · intro heq
      rcases smul_eq_zero.mp heq with h0 | h0
      · exact absurd h0 hη
      · exact h0
    · intro h0
      rw [h0, smul_zero]
  rw [hstep]
  exact FateV2.Loop.T1Verify.fixed_iff_of_injective (A : E →ₗ[ℝ] F) φ hφ x' θ

/-- **【主定理 3】版本 2 的收敛到唯一最优的完整陈述。**

若 `A` 双射、`φ` 单射、`Corrects` 成立，则：
* 最优参数 `θ*` 存在且唯一；
* `wbW` 的不动点恰是 `θ*`。 -/
theorem existsUnique_optimal_and_fixed (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (hη : η ≠ 0) (h : Corrects A φ) (hφ : Function.Injective φ)
    (hAinj : Function.Injective A) (hAsurj : Function.Surjective A) (x' : F) :
    ∃! θ, IsOptimal (A : E →ₗ[ℝ] F) x' θ ∧ (BoundWriteBack.wbW A φ η x' θ : E) = θ := by
  obtain ⟨θ₀, hθ₀, huniq⟩ := optimal_existsUnique (A : E →ₗ[ℝ] F) hAinj hAsurj x'
  refine ⟨θ₀, ⟨hθ₀, ?_⟩, ?_⟩
  · exact (fixed_iff_optimal A φ η hη h hφ x' θ₀).mpr hθ₀
  · intro θ' h'
    exact huniq θ' h'.1

end ConvergeToOptimalV2

end FateV2.Loop
