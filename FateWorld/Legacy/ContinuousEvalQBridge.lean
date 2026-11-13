import FateWorld.Legacy.ContinuousEvalQ
import FateWorld.Legacy.ThetaConvergence

/-! ===========================================================================
  `Fate/ContinuousEvalQBridge` —— **`ℚ` 版 `thetaNQ` 与 `ℝ` 版 `thetaN` 的桥**
  ===========================================================================

  ## 为什么需要本文件

  审计 R316 指出 `ContinuousEvalQ` 的一个硬伤：

  > **「`ContinuousEvalQ` 只 import Mathlib，`Fate` import 数 = 0，与 `WorldModel`/`thetaN`
  > 无任何形式化联系，是另写的同名算法。『同一个算法』是**断言不是定理**（缺 `thetaNQ_cast` 桥）。」**

  本文件补上那条桥。

  ## 桥的证明

  两侧都化到闭式：
  * `ContinuousEvalQ.thetaNQ_dev`：`thetaNQ η θhat θ₀ n - θhat = (1-η)^n * (θ₀ - θhat)`（`ℚ`）
  * `ThetaConvergence.thetaN_closed`：`thetaN η θstar x θ₀ n - θstar = (1-η)^n * (θ₀ - θstar)`（`ℝ`）

  把 `ℚ` 侧等式逐项 `congrArg` 到 `ℝ`（`push_cast` 保持 `+ - * ^`），
  再与 `ℝ` 侧闭式比较即可。
-/

namespace Fate
namespace ContinuousEvalQBridge

open ContinuousEvalQ

/-- ⭐⭐ **【核心桥：`ℚ` 版 `thetaNQ` 转到 `ℝ` 就是 `ℝ` 版 `thetaN`】**

`xhat = 1`，故 `thetaN` 的 `x ≠ 0` 前提自动成立。 -/
theorem thetaNQ_cast (η θstar θ₀ : ℚ) (n : ℕ) :
    ((thetaNQ η θstar θ₀ n : ℚ) : ℝ)
      = ThetaConvergence.thetaN (↑η) (↑θstar) 1 (↑θ₀) n := by
  -- ℚ 侧的闭式
  have hq : thetaNQ η θstar θ₀ n - θstar = (1 - η) ^ n * (θ₀ - θstar) :=
    thetaNQ_dev η θstar θ₀ n
  -- ℝ 侧的闭式
  have hr : ThetaConvergence.thetaN (↑η) (↑θstar) 1 (↑θ₀) n - (↑θstar : ℝ)
      = (1 - (↑η : ℝ)) ^ n * ((↑θ₀ : ℝ) - ↑θstar) :=
    ThetaConvergence.thetaN_closed (↑η) (↑θstar) 1 (↑θ₀) one_ne_zero n
  -- 把 ℚ 侧等式转到 ℝ
  have hq' : ((thetaNQ η θstar θ₀ n : ℚ) : ℝ) - (↑θstar : ℝ)
      = (1 - (↑η : ℝ)) ^ n * ((↑θ₀ : ℝ) - ↑θstar) := by
    have hcast := congrArg (fun z : ℚ => (z : ℝ)) hq
    push_cast at hcast
    exact hcast
  -- 两侧相减为零
  have hgoal : ((thetaNQ η θstar θ₀ n : ℚ) : ℝ)
      - ThetaConvergence.thetaN (↑η) (↑θstar) 1 (↑θ₀) n = 0 := by
    linarith [hq', hr]
  linarith [hgoal]

end ContinuousEvalQBridge
end Fate
