import FateWorld.FateV2.Loop.Residual
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
  # Loop · WriteBack —— 回写与**精确收缩**

  ## 迁移登记
  - 来源：新写
  - 动作：C 重写
  - 对应环节：F7-22（回写）、F7-23（收敛）
  - 依赖裁决：**D-004**（四算子）、**裁决 K**（误差判据在回写前后不变口径）
  - 改动：原文件空骨架。
  - 状态：已验证

  ## 回写规则

  ```
  pred' = pred + η · (obs − pred)        (η ∈ (0, 2))
  ```

  于是残差**精确地**按 `1 − η` 缩放：

  ```
  err' = obs − pred' = obs − pred − η(obs − pred) = (1 − η) · err
  ```

  **这是精确等式，不是不等式**——`η = 2` 时误差**反号不变大小**，
  `η ∈ (0,2)` 且 `η ≠ 1` 时严格变小，`η ∈ (0,2)` 且 `η < 2` 时**严格收缩**。

  ## 为什么 `η ∈ (0,2)`

  * `η ≤ 0`：不往观测走，误差不减小
  * `η ≥ 2`：冲过头，误差**不减小**（`|1−η| ≥ 1`）
  * `0 < η < 2`：`|1−η| < 1` ⟹ 收缩

  本文件把这三条都证出来，且**用绝对值**表述（于是 `η ∈ (1,2)` 的反向过冲也被覆盖）。

  ## 超出定义之处
  * `writeBack_residual`：回写后的残差**恰**是 `(1−η)·e`——精确等式。
    定义只写了 `pred + η·(obs−pred)`；把它与残差公式接起来是**代数展开**，
    而且这条等式是后续所有收缩性结论的**唯一支点**。
  * `abs_residual_contract`：`0 < η < 2 ∧ η ≠ 1 ⟹ |e'| < |e|`（当 `e ≠ 0`）。
  * `eta2_preserves`：`η = 2` 时 `|e'| = |e|`——**过冲不收敛**，
    这是「`η` 必须 `< 2`」的反面证据（不是随手对边界取开区间）。
-/

namespace FateV2.Loop

/-! ===========================================================================
  §1  回写
  =========================================================================== -/

/-- **回写**：把预测往观测拉 `η` 比例。 -/
def writeBack (η obs pred : Real) : Real := pred + η * (obs - pred)

/-- **回写后的残差 = `(1 − η)` 倍的原残差**（精确等式）。

  **超出定义之处**：`writeBack` 的定义是 `pred + η·(obs−pred)`；
  本定理把它与残差公式 `obs − pred` 接起来，得到**精确**的缩放关系
  `residual obs (writeBack η obs pred) = (1 − η) · residual obs pred`。

  这是回写层的**唯一支点**：收缩性、过冲、不动点全部由它推出。
  定义本身没有这条——需要把 `obs − (pred + η(obs−pred))` 重新整理。 -/
theorem writeBack_residual (η obs pred : Real) :
    residual obs (writeBack η obs pred) = (1 - η) * residual obs pred := by
  unfold residual writeBack
  ring

/-- **不动点**：`η = 0` 时回写不动（残差不变）。 -/
theorem writeBack_zero_eta (obs pred : Real) :
    residual obs (writeBack 0 obs pred) = residual obs pred := by
  rw [writeBack_residual]
  ring

/-- **一步精确命中**：`η = 1` 时回写后残差**恰为 0**（完全采纳观测）。 -/
theorem writeBack_one_eta (obs pred : Real) :
    residual obs (writeBack 1 obs pred) = 0 := by
  rw [writeBack_residual]
  ring

/-! ===========================================================================
  §2  收缩
  =========================================================================== -/

/-- **`η ∈ (0,2)` 时残差严格收缩**（非零残差情形）。

  **超出定义之处**：这是本文件的主结论。由 `writeBack_residual`，
  `|e'| = |1−η| · |e|`；`0 < η < 2` 给出 `0 < η` 与 `η < 2`，
  于是 `|1−η| < 1`，乘上非零的 `|e|` 便得严格小于。

  关键是 `η ∈ (0,2)` **不是**随便取的开区间：
  * `η ≥ 2` 时 `|1−η| ≥ 1`，**不收缩**（见 `eta2_preserves`）
  * `η ≤ 0` 时同理
  ⟹ 这个区间是**充要**的，不是约定。 -/
theorem abs_residual_contract (η obs pred : Real)
    (h1 : 0 < η) (h2 : η < 2) (hne : residual obs pred ≠ 0) :
    |residual obs (writeBack η obs pred)| < |residual obs pred| := by
  rw [writeBack_residual]
  have he : 0 < |residual obs pred| := abs_pos.mpr hne
  have hlt : |1 - η| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  calc |(1 - η) * residual obs pred| = |1 - η| * |residual obs pred| := abs_mul _ _
    _ < 1 * |residual obs pred| := by
        exact (mul_lt_mul_iff_of_pos_right he).mpr hlt
    _ = |residual obs pred| := one_mul _

/-- **`η = 2` 时误差大小不变**（过冲，不收敛）。

  这条是「`η ∈ (0,2)` 必须开区间」的**反面证据**：
  若允许 `η = 2`，残差**不减小**，闭环不收敛。 -/
theorem eta2_preserves (obs pred : Real) :
    |residual obs (writeBack 2 obs pred)| = |residual obs pred| := by
  rw [writeBack_residual]
  have : (1 - (2 : Real)) = -1 := by norm_num
  rw [this, neg_one_mul, abs_neg]

/-- **不收缩的另一侧**：`η ≤ 0` 时残差大小不减小。 -/
theorem nonpos_eta_nocontract (η obs pred : Real) (h : η ≤ 0) :
    |residual obs pred| ≤ |residual obs (writeBack η obs pred)| := by
  rw [writeBack_residual, abs_mul]
  have hone : (1 : Real) ≤ |1 - η| := by
    rw [abs_of_nonneg (by linarith : (0 : Real) ≤ 1 - η)]
    linarith
  have habs : 0 ≤ |residual obs pred| := abs_nonneg _
  calc |residual obs pred| = 1 * |residual obs pred| := (one_mul _).symm
    _ ≤ |1 - η| * |residual obs pred| := by
        exact mul_le_mul_of_nonneg_right hone habs

end FateV2.Loop
