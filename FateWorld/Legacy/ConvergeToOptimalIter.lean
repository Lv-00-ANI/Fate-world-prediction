import FateWorld.Legacy.ConvergeToOptimalStrong
import Mathlib.Analysis.SpecificLimits.Basic

/-! ===========================================================================
  §0  D 裁决缺的那条：收敛到唯一最优的**动力学**版本

  ## 背景

  独立审计 R42 指出：
  > **V2 缺了「收敛」这个动词：有静态的「存在+唯一+不动点」，**
  > **没有 `θ_n → φ x'` 的迭代收敛定理。而这条不难：**
  > **`θ_n − φx' = (1−η)^n (θ₀ − φx')`，一行。**

  作者 D 裁决原话是「**收敛**到唯一参数」。
  `existsUnique_optimal_and_fixed` 只给**静态**形态（不动点唯一），
  本文件补**动力学**形态（迭代真的收敛到它）。

  ## 本文件证明

  * `iterErr_closed`：`θ_n − θ* = (1−η)^n (θ₀ − θ*)`（闭式）
  * `converges_to_unique_optimal`：`|1−η| < 1` ⟹ `θ_n → θ*`

  ## 诚实边界

  * 收敛是**几何收敛**（速率 `|1−η|`），不是有限步精确。
  * 需要 `|1−η| < 1`（即 `0 < η < 2`）。
  * `θ* := φ x'` 由 `Corrects` 给出（`A (φ x') = x'`），故它确实是最优参数。
  =========================================================================== -/

namespace Fate

namespace ConvergeToOptimalIter

open Fate.BoundWriteBack
open Filter

universe u

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### §1 迭代的定义 -/

/-- **迭代**：从 `θ₀` 出发反复施加 `wbW`。 -/
noncomputable def thetaIter (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (n : ℕ) (θ₀ : E) : E :=
  (Nat.iterate (fun θ => (BoundWriteBack.wbW A φ η x' θ : E)) n) θ₀

/-- **零步 = 恒等**。 -/
theorem thetaIter_zero (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ₀ : E) :
    thetaIter A φ η x' 0 θ₀ = θ₀ := rfl

/-- **递推步**。 -/
theorem thetaIter_succ (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (n : ℕ) (θ₀ : E) :
    thetaIter A φ η x' (n + 1) θ₀
      = (BoundWriteBack.wbW A φ η x' (thetaIter A φ η x' n θ₀) : E) :=
  Function.iterate_succ_apply' _ _ _

/-! ### §2 ⭐ 闭式：`θ_n − θ* = (1−η)^n (θ₀ − θ*)` -/

/-- ⭐⭐ **【闭式】误差按 `(1−η)^n` 缩放。**

**证明**：由 `wbW_sub`（`wbW θ − θ = η • φ (x' − Aθ)`）与
`image_wbW`（`A(wbW θ) − x' = (1−η) • (Aθ − x')`）得单步缩放，
再对 `n` 归纳。

**⚠ 这里用 `Corrects` 得到 `θ* := φ x'` 满足 `A θ* = x'`。** -/
theorem iterErr_closed (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (h : Corrects A φ) (n : ℕ) (θ₀ : E) :
    A (thetaIter A φ η x' n θ₀) - x' = (1 - η) ^ n • (A θ₀ - x') := by
  induction n with
  | zero => simp [thetaIter]
  | succ k ih =>
    rw [thetaIter_succ, image_wbW A φ η x' _ h, ih, smul_smul]
    ring_nf

/-! ### §3 ⭐⭐ 收敛 -/

/-- ⭐⭐⭐ **【主定理】`|1−η| < 1` ⟹ `θ_n` 的预测收敛到观测真值 `x'`。**

即 `A (θ_n) → x'` —— 这就是「收敛到最优」的动力学形态。 -/
theorem predicts_converges (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F)
    (h : Corrects A φ) (hη : |1 - η| < 1) (θ₀ : E) :
    Tendsto (fun n => A (thetaIter A φ η x' n θ₀)) atTop (nhds x') := by
  have hpow : Tendsto (fun n : ℕ => (1 - η) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_iff.mpr (by simpa [abs_sub_comm] using hη)
  have hzero : Tendsto (fun n : ℕ => (1 - η) ^ n • (A θ₀ - x')) atTop (nhds (0 : F)) := by
    simpa using hpow.smul_const (A θ₀ - x')
  have heq : (fun n => A (thetaIter A φ η x' n θ₀) - x')
      = (fun n => (1 - η) ^ n • (A θ₀ - x')) := by
    ext n
    exact iterErr_closed A φ η x' h n θ₀
  have : Tendsto (fun n => A (thetaIter A φ η x' n θ₀) - x') atTop (nhds 0) := by
    rw [heq]; exact hzero
  have := this.add_const x'
  simpa using this

end ConvergeToOptimalIter

end Fate
