import Mathlib.Logic.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic

namespace FateV2.Model.MainlineTheorems

/-!
  # Model · T51Trajectory

  ## 迁移登记
  - 来源：`FateWorld/Legacy/T51Trajectory.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.Model`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §3 T5.1 —— **离散轨迹的存在唯一性**

**清单原文（T5.1）**：
> **离散轨迹存在唯一性**：若 `f : X × U × E → X` 可测、`u_t`、`ε_t` 的分布族给定，
> 则式 (4.1) 的解对每个 `ω` 存在且唯一（由递推唯一确定）。

**⚠ 偏差说明（诚实登记）**：
- **清单提到「`f` 可测」「分布族给定」** —— 那两条是**概率论**条件，
  **而对「轨迹存在唯一」这一结论**是**多余的**（**递推唯一性不依赖测度结构**）。
- **⟹ 本文件证的是**更一般的版本**：
  **对**任意** `f`（无需可测）与**任意**初始状态 `x₀`，
  递推 `x_{t+1} = f x_t (u t) (e t)` 的轨迹**存在且唯一**。**
- **⚠ 这**严格强于**清单的字面陈述（**因为它去掉了假设**）。 -/

/-- ⭐⭐ **递推轨迹**：`x_{t+1} = f x_t (u t) (e t)`，`x 0 = x₀`。

**⚠ 本定义**不依赖**任何可测性/测度假设。 -/
def trajectory {X U E : Type*} (f : X → U → E → X) (x₀ : X) (u : ℕ → U) (e : ℕ → E) :
    ℕ → X
  | 0 => x₀
  | n + 1 => f (trajectory f x₀ u e n) (u n) (e n)

/-- ⭐⭐ **轨迹满足递推方程**。 -/
theorem trajectory_succ {X U E : Type*} (f : X → U → E → X) (x₀ : X)
    (u : ℕ → U) (e : ℕ → E) (n : ℕ) :
    trajectory f x₀ u e (n + 1) = f (trajectory f x₀ u e n) (u n) (e n) := rfl

/-- ⭐⭐ **轨迹的初始条件**。 -/
theorem trajectory_zero {X U E : Type*} (f : X → U → E → X) (x₀ : X)
    (u : ℕ → U) (e : ℕ → E) :
    trajectory f x₀ u e 0 = x₀ := rfl

/-! ### ⭐⭐⭐ T5.1 的核心：**唯一性**

**⭐ 命题**：**若两条轨迹都满足**同一递推 + 同一起点**，则它们**处处相等**。** -/

/-- ⭐⭐⭐ **T5.1（唯一性）**：满足 `x 0 = x₀` 与 `x (n+1) = f (x n) (u n) (e n)` 的
序列**唯一**。

**🔹 对应清单**：T5.1 的「唯一」部分。

**⚠ 证明**：对 `n` 归纳。**不依赖** `f` 的任何性质。 -/
theorem trajectory_unique {X U E : Type*} (f : X → U → E → X) (x₀ : X)
    (u : ℕ → U) (e : ℕ → E) {x : ℕ → X}
    (h0 : x 0 = x₀) (hs : ∀ n, x (n + 1) = f (x n) (u n) (e n)) :
    ∀ n, x n = trajectory f x₀ u e n := by
  intro n
  induction n with
  | zero => simpa only [trajectory_zero] using h0
  | succ k ih =>
    rw [hs k, ih, trajectory_succ]

/-- ⭐⭐⭐ **T5.1（存在性）**：轨迹存在（由 `trajectory` 直接给出）。

**🔹 对应清单**：T5.1 的「存在」部分。 -/
theorem trajectory_exists {X U E : Type*} (f : X → U → E → X) (x₀ : X)
    (u : ℕ → U) (e : ℕ → E) :
    ∃ x : ℕ → X, x 0 = x₀ ∧ ∀ n, x (n + 1) = f (x n) (u n) (e n) :=
  ⟨trajectory f x₀ u e, trajectory_zero f x₀ u e,
   fun n => trajectory_succ f x₀ u e n⟩

/-- ⭐⭐⭐⭐ **T5.1（存在且唯一）**。

**⭐ 这是清单 T5.1 的**完整形式化**（**且假设更少**）。 -/
theorem t51_exists_unique {X U E : Type*} (f : X → U → E → X) (x₀ : X)
    (u : ℕ → U) (e : ℕ → E) :
    ∃! x : ℕ → X, x 0 = x₀ ∧ ∀ n, x (n + 1) = f (x n) (u n) (e n) := by
  refine ⟨trajectory f x₀ u e,
    ⟨trajectory_zero f x₀ u e, fun n => trajectory_succ f x₀ u e n⟩, ?_⟩
  rintro x ⟨h0, hs⟩
  funext n
  exact trajectory_unique f x₀ u e h0 hs n

end FateV2.Model.MainlineTheorems
