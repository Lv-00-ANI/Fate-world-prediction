import FateWorld.Legacy.FinCondIndep
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! ===========================================================================
  `Fate/CondMulSeparable` —— **条件独立 ⟹ 可分离**（**第 244 轮**）

  ## ⭐⭐⭐ 本文件补的是**反方向**

  **第 242 轮的 `PearlCondIndepBridge` 只证明了**一个方向**：
  **可分离 ⟹ 条件乘性（`CondMul`）。**

  **⭐⭐ 但 `ChainMarkov` / `ForkFac` 的定义**就是**可分离** ——
  **⟹ 那个方向是**半内容**。**

  **✅ 本文件证**反方向**（**真正有内容**）：
  **条件乘性 + 正分布 ⟹ 可分离。**

  **⭐⭐ 合起来是 Pearl 1.2.4 的**双向刻画**：
  > **`X ⊥ Y | Z`  ⟺  `p(x,y,z)` 可分解为 `f(x,z) · g(y,z)`。**

  ## ⭐ 为什么需要「正分布」
  **反方向**必须**要正性**：若无正性，零概率区域会使 `margZ z = 0`，除法无定义。
  **⚠ 这是 Pearl 的**标准假设**（positivity），不是为凑结论加的。**
================================================================================ -/

namespace Fate.CondMulSeparable

open Fate.FinCondIndep

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-! ## §1 ⭐⭐⭐ **核心定理：条件乘性 + 正性 ⟹ 可分离** -/

/-- ⭐⭐⭐⭐ **条件乘性 + 正分布 ⟹ 可分离**（**Pearl 1.2.4 的**反方向**）。

**⭐⭐ 构造**：`f x z := margXZ x z / margZ z`、`g y z := margYZ y z`。

**⚠ 验证需要三步**：
1. `margZ z ≠ 0`（由正性给出）
2. `CondMul` 的等式
3. 两边除以 `margZ z`（**真代数**） -/
theorem condMul_implies_separable (p : FinJoint α β γ)
    [Nonempty α] [Nonempty β]
    (h : CondMul p) (hpos : ∀ x y z, 0 < p ((x, y), z)) :
    ∃ (f : α → γ → ℝ) (g : β → γ → ℝ),
      ∀ x y z, p ((x, y), z) = f x z * g y z := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty α›
  obtain ⟨y₀⟩ := ‹Nonempty β›
  -- ⭐ margZ z > 0：取 (x₀, y₀) 这一个正项
  have hz : ∀ z : γ, 0 < margZ p z := by
    intro z
    unfold margZ
    exact Finset.sum_pos (fun x _ => Finset.sum_pos (fun y _ => hpos x y z)
      ⟨y₀, Finset.mem_univ y₀⟩) ⟨x₀, Finset.mem_univ x₀⟩
  refine ⟨fun x z => margXZ p x z / margZ p z, fun y z => margYZ p y z, ?_⟩
  intro x y z
  have hne : margZ p z ≠ 0 := ne_of_gt (hz z)
  have hcm := h x y z
  -- 目标：p x y z = (margXZ x z / margZ z) * margYZ y z
  -- ⚠ field_simp 在本环境不可用 ⟹ 用 div_mul_eq_mul_div + eq_div_iff 手写
  rw [div_mul_eq_mul_div, eq_div_iff hne]
  linarith [hcm]

end Fate.CondMulSeparable