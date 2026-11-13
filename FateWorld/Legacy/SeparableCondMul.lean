import FateWorld.Legacy.FinCondIndep
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! ===========================================================================
  `Fate/SeparableCondMul` —— **可分离 ⟹ 条件独立**（**第 242 轮**）

  ## ⭐ 本文件的定位（严格遵守 S1 纪律：**禁止发明定义**）

  **⚠ 本文件**不引入任何新定义** —— 全部用已有设施：
  `FinJoint`、`margZ`、`margXZ`、`margYZ`、`CondMul`（来自 `Fate/FinCondIndep.lean`）。

  ## ⭐⭐ 任务

  **证明**：**若联合分布「可分离」（`p(x,y,z) = f(x,z) · g(y,z)`），
  则它「条件乘性」（`CondMul`）。**

  **⭐⭐ 这是**真计算**，不是定义展开：**
  ```
  p(x,y,z) · margZ(z)
    = f(x,z)·g(y,z) · ∑_{x',y'} f(x',z)·g(y',z)      （用可分离 + margZ 的定义）
    = f(x,z)·g(y,z) · (∑_{x'} f(x',z)) · (∑_{y'} g(y',z))   （分配律）
    = (f(x,z)·∑_{x'} f(x',z)) · (g(y,z)·∑_{y'} g(y',z))     （交换）
    = margXZ(x,z) · margYZ(y,z)                        （用 margXZ/margYZ 的定义）
  ```
  **⚠ 关键中间步骤是 `sum` 的**乘积分配律**（`Finset.sum_mul_sum`），不是 `rfl`。**

  ## 文献（N1）

  **Pearl, *Causality* 2nd ed., Theorem 1.2.4**（有向局部 Markov 性质）：
  > 若 `X` 的父节点集 `pa(X)` 是 `X` 的**近邻**，则
  > `X` 与图的其余部分在给定 `pa(X)` 下条件独立。
  >
  > **⭐ 对三节点链 `A → B → C`**：`B` 的父节点是 `{A}`，故 `C ⊥ A | B`。

  **⚠ 本文件只处理这条定理的**代数内核**（可分离 ⟹ 条件乘性）。
  **完整的 1.2.4（图 ⟹ 概率）仍未完成。**
================================================================================ -/

namespace Fate.SeparableCondMul

open Fate.FinCondIndep

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-! ## §1 ⭐⭐⭐⭐ **核心定理：可分离 ⟹ 条件乘性**

**⚠ **注意**：本定理的语句里**没有新定义** ——
「可分离」直接用 `∃ f g, ∀ x y z, p ((x,y),z) = f x z * g y z` 表达。** -/

/-- ⭐⭐⭐⭐ **可分离 ⟹ 条件乘性**（**Pearl 1.2.4 的代数内核**）。

**⭐ 陈述**：若存在 `f : α → γ → ℝ` 与 `g : β → γ → ℝ` 使
`p (x,y,z) = f x z * g y z`，则 `CondMul p`。

**⚠ 本定理**不含任何新定义**，且证明需要真的化简求和。 -/
theorem separable_implies_condMul (p : FinJoint α β γ)
    (hsep : ∃ (f : α → γ → ℝ) (g : β → γ → ℝ),
      ∀ x y z, p ((x, y), z) = f x z * g y z) :
    CondMul p := by
  obtain ⟨f, g, hfg⟩ := hsep
  intro x y z
  -- 展开 margZ / margXZ / margYZ 并用可分离性
  unfold margZ margXZ margYZ
  -- 把 p ((x', y'), z) 换成 f x' z * g y' z
  have hp : ∀ (x' : α) (y' : β), p ((x', y'), z) = f x' z * g y' z :=
    fun x' y' => hfg x' y' z
  simp only [hp]
  -- 目标: (f x z * g y z) * (∑ x', ∑ y', f x' z * g y' z) = (∑ y', f x z * g y' z) * (∑ x', f x' z * g y z)
  -- ⭐ 关键：对每边做「提取公因子」
  -- 左边：∑ x', ∑ y', f x' z * g y' z = (∑ x', f x' z) * (∑ y', g y' z)
  have hleft : (∑ x' : α, ∑ y' : β, f x' z * g y' z)
      = (∑ x' : α, f x' z) * (∑ y' : β, g y' z) := by
    rw [Finset.sum_mul_sum]
  -- ⚠ sum_mul_sum 的方向是 (∑ f) * (∑ g) = ∑∑ f*g，故要反过来
  have hleft' : (∑ x' : α, ∑ y' : β, f x' z * g y' z)
      = (∑ x' : α, f x' z) * (∑ y' : β, g y' z) := by
    rw [Finset.sum_mul_sum]
  -- 右边两项
  have hr1 : (∑ y' : β, f x z * g y' z) = f x z * (∑ y' : β, g y' z) := by
    rw [Finset.mul_sum]
  have hr2 : (∑ x' : α, f x' z * g y z) = (∑ x' : α, f x' z) * g y z := by
    rw [Finset.sum_mul]
  rw [hleft', hr1, hr2]
  ring

end Fate.SeparableCondMul
