import FateWorld.FateV2.Error.Loss
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
  # Loop · Residual —— 残差 `e = obs − pred`

  ## 迁移登记
  - 来源：新写
  - 动作：C 重写
  - 对应环节：F7-20（闭环残差）、F7-21（残差→回写）
  - 依赖裁决：**D-004**（四算子与来源传播）——本文件只管**数值残差**这一半，
          规则层的 support 传播在 `Core/Ops.lean`
  - 改动：原文件空骨架。
  - 状态：已验证

  ## 残差是什么

  ```
  e_t = obs_t − pred_t
  ```

  这里 `obs` 是观测值、`pred` 是预测值，都是**标量**（本批 demo 在实数上跑）。
  闭环回写（`Loop/WriteBack`）吃这个残差。

  ## 为什么残差要单独一层

  D-009 §三 说损失来自「抽象」与「预测」两处。
  残差是**这两处损失在单个时刻的合并表现**——但**不是**它们之和：
  抽象错误会一直偏（系统性），预测错误会跳（随机性）。
  本文件只给残差本身，不预设分解（分解在 `Error/` 层做）。

  ## 超出定义之处
  * `Residual.abs_zero_iff`：残差为零 ⟺ 观测等于预测。
    定义只是减法；「零残差 = 预测准」需要把 `sub_eq_zero` 这一代数事实搬过来。
-/

namespace FateV2.Loop

/-! ===========================================================================
  §1  残差
  =========================================================================== -/

/-- **残差**：观测减预测。 -/
def residual (obs pred : Real) : Real := obs - pred

/-- **残差为零 ⟺ 预测准**。

  **超出定义之处**：`residual` 的定义只是一个减法；
  「残差 = 0 说明预测对齐了观测」需要代数事实 `a - b = 0 ↔ a = b`。
  这是回写「不动点 = 预测已经对了」的判据。 -/
theorem residual_eq_zero_iff (obs pred : Real) : residual obs pred = 0 ↔ obs = pred := by
  unfold residual
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- **残差对称性**：交换观测与预测，残差变号。

  **超出定义之处**：定义是 `obs − pred`，本身不对称；
  本定理说明「反着减」只是变号——这使「残差大小」`|e|` 与顺序无关，
  于是回写可以只看残差绝对值判收敛。 -/
theorem residual_swap (obs pred : Real) : residual pred obs = - residual obs pred := by
  unfold residual
  ring

/-- **残差的三角型**：两个时刻的残差之差 = 两个时刻的观测差 − 预测差。

  这条把「残差的变化」拆成「观测的变化」与「预测的变化」两部分，
  是闭环里「观测在动 vs 模型在追」的分界线。 -/
theorem residual_diff (o₁ p₁ o₂ p₂ : Real) :
    residual o₁ p₁ - residual o₂ p₂ = (o₁ - o₂) - (p₁ - p₂) := by
  unfold residual
  ring

end FateV2.Loop
