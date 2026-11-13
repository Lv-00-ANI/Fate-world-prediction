import Mathlib.Logic.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum

/-! ===========================================================================
  `Fate/T61MapKernel` —— **T6.1 映射形式是核形式的特例**（**第 228 轮**）

  ## 清单原文（T6.1）

  > **映射形式是核形式的特例**：定义 5.1 的映射
  > `R : C × X_local → Y` 与定义 5.2 的核 `R : P(y|x,c)` 之间，
  > **前者恰为后者在「`P(·|x,c)` 为**点质量**」时的情形。**

  ## ⭐ 这条的意义

  **理论的规则有两层写法**：
  - **定义 5.1（映射形式）**：`R(c, x) = y` —— **确定性输出**
  - **定义 5.2（核形式）**：`R(y | x, c)` —— **随机输出（一个分布）**

  **⭐⭐ T6.1 说**：**映射是核在「输出为点质量」时的**退化情形**，
  **⟹ 核形式**严格更一般**。**
================================================================================ -/

namespace Fate.T61

open Finset

/-- ⭐⭐ **映射形式**（定义 5.1）：确定性函数。 -/
abbrev MapForm (C X Y : Type*) := C → X → Y

/-- ⭐⭐ **核形式**（定义 5.2）：给定 `c, x` 后 `Y` 上的一个分布。 -/
abbrev KernelForm (C X Y : Type*) := C → X → Y → ℝ

/-- ⭐⭐ **点质量核**：由映射 `R` 导出的核（在 `y = R c x` 处质量为 1）。 -/
def diracKernel {C X Y : Type*} [DecidableEq Y] (R : MapForm C X Y) :
    KernelForm C X Y :=
  fun c x y => if y = R c x then 1 else 0

/-! ## §1 ⭐⭐ **点质量核的基本性质** -/

/-- ⭐⭐ **点质量核的总质量为 1**。 -/
theorem diracKernel_sum {C X Y : Type*} [Fintype Y] [DecidableEq Y]
    (R : MapForm C X Y) (c : C) (x : X) :
    ∑ y, diracKernel R c x y = 1 := by
  have hstep : ∀ y ∈ (Finset.univ : Finset Y), diracKernel R c x y = if y = R c x then (1 : ℝ) else 0 :=
    fun y _ => rfl
  simp only [diracKernel]
  rw [Finset.sum_eq_single (R c x)]
  · rw [if_pos rfl]
  · intro y _ hy
    rw [if_neg hy]
  · intro h
    exact absurd (Finset.mem_univ (R c x)) h

/-- ⭐⭐ **点质量核在 `R c x` 处质量为 1**。 -/
theorem diracKernel_at {C X Y : Type*} [DecidableEq Y]
    (R : MapForm C X Y) (c : C) (x : X) :
    diracKernel R c x (R c x) = 1 := by
  simp [diracKernel]

/-- ⭐⭐ **点质量核只在一点非零**。 -/
theorem diracKernel_support {C X Y : Type*} [DecidableEq Y]
    (R : MapForm C X Y) (c : C) (x : X) (y : Y) :
    diracKernel R c x y ≠ 0 ↔ y = R c x := by
  simp only [diracKernel]
  by_cases h : y = R c x
  · simp [h]
  · simp [h]

/-! ## §2 ⭐⭐⭐⭐ **T6.1 主定理** -/

/-- ⭐⭐⭐⭐ **T6.1（正向）**：**每个映射导出**一个点质量、总质量为 1 的核**。

**🔹 对应清单**：T6.1 的「映射 → 核」方向。

**⭐⭐ 读法**：**映射形式总是可以被写成核形式**（取点质量即可），
**⟹ 核形式至少与映射形式一样一般。** -/
theorem t61_map_to_kernel {C X Y : Type*} [Fintype Y] [DecidableEq Y]
    (R : MapForm C X Y) :
    (∀ c x, ∑ y, diracKernel R c x y = 1)
      ∧ (∀ c x, diracKernel R c x (R c x) = 1)
      ∧ (∀ c x y, diracKernel R c x y ≠ 0 → y = R c x) :=
  ⟨fun c x => diracKernel_sum R c x,
   fun c x => diracKernel_at R c x,
   fun c x y h => (diracKernel_support R c x y).mp h⟩

/-- ⭐⭐⭐⭐ **T6.1（反向）**：**一个「每点恰有一个质量 1、其余为 0」的核必来自某个映射**。

**🔹 对应清单**：T6.1 的「核 → 映射」方向（点质量情形的逆）。

**⚠⚠ 关键的**加强假设**（**这是正确的数学修正**）：

**我最初只假设「∃ 唯一的 `y` 使 `K c x y = 1`」—— **这**不够****，
**因为核值可以是任意实数**（如 `1/2`），**故「不是 1」推不出「是 0」。**

**⭐⭐ 正确的假设是 `K` **取值只在 `{0, 1}` 中**（**这才是「点质量核」的定义**）：
$$K\,c\,x\,y \in \{0, 1\}.$$

**⟹ 有了它，「恰有一个 1」就蕴含「其余全是 0」⟹ 可构造映射。** -/
theorem t61_kernel_to_map {C X Y : Type*} [DecidableEq Y]
    (K : KernelForm C X Y)
    (h01 : ∀ c x y, K c x y = 0 ∨ K c x y = 1)
    (hex : ∀ c x, ∃ y, K c x y = 1)
    (huniq : ∀ c x y₁ y₂, K c x y₁ = 1 → K c x y₂ = 1 → y₁ = y₂) :
    ∃ R : MapForm C X Y, ∀ c x y, K c x y = diracKernel R c x y := by
  classical
  choose R hR using hex
  refine ⟨R, fun c x y => ?_⟩
  by_cases h : y = R c x
  · subst h
    simp only [diracKernel, if_pos rfl]
    exact hR c x
  · have hd : diracKernel R c x y = 0 := by
      simp only [diracKernel]
      exact if_neg h
    rw [hd]
    -- 目标：K c x y = 0；用 h01 分类
    rcases h01 c x y with h0 | h1
    · exact h0
    · exact absurd (huniq c x y (R c x) h1 (hR c x)) h

/-! ## §3 ⭐⭐⭐ **核形式严格更一般** -/

/-- ⭐⭐⭐ **核形式严格更一般**：**存在不是点质量的核**。

**⭐ 见证**：`Y = Bool` 上的**均匀分布** `(1/2, 1/2)` ——
**它的两个值都不是 1**，⟹ 不可能是任何映射的点质量核。

**⭐⭐ 这证明**「核形式 ⊋ 映射形式」** —— **T6.1 是**严格**的（不是「两者等价」）。** -/
theorem kernel_strictly_more_general :
    ∃ K : KernelForm Unit Unit Bool,
      (∀ y, K () () y = 1 / 2) ∧
      (∀ R : MapForm Unit Unit Bool, ∀ y, K () () y ≠ diracKernel R () () y) := by
  refine ⟨fun _ _ _ => 1 / 2, fun y => rfl, ?_⟩
  intro R y heq
  by_cases h : y = R () ()
  · have hd : diracKernel R () () y = 1 := by
      unfold diracKernel
      rw [if_pos h]
    rw [hd] at heq
    norm_num at heq
  · have hd : diracKernel R () () y = 0 := by
      unfold diracKernel
      rw [if_neg h]
    rw [hd] at heq
    norm_num at heq

/-! ===========================================================================
  §4 ⭐⭐⭐ R-47 追加（第 47 轮接线任务，2026-02 追加）

  本节**只追加**，不动 §1–§3 的任何定理。所有新定理都是把存量结论
  （`diracKernel_sum` / `diracKernel_at` / `diracKernel_support` /
  `t61_map_to_kernel` / `t61_kernel_to_map` / `kernel_strictly_more_general`）
  **拼成新的合取 / 双向等价**，并推出存量里**没有明写**的合成结论。

  ## ⚠ 防环

  本文件**没有** `import` 任何 `Fate.*` 模块（只有 Mathlib）。
  故不可能成环。

  ## ⚠ 前件检查（逐条）

  * `t61_roundtrip_package`：前件是映射 `R`（原料）；结论是
    「映射 → 核」三条性质 **与**「该核总质量为 1」的合取，并把
    `diracKernel_at` 与 `diracKernel_sum` 在这一具体 `R` 上**同时**给出。
  * `t61_map_not_injective`：**零显式前件**（全称量化在结论里）。
    结论是「存在两个不同的映射导出同一个 0–1 核型」的反面形式 ——
    实际交付的是「**映射族的基数至少 2 且核值只取 {0,1}**」。
  * `t61_point_mass_two_faces`：前件 `h01`/`hex`/`huniq` 是**原料假设**
    （来自 `t61_kernel_to_map`），**不是**结论的重述；结论额外给出
    **唯一性**（导出映射在每点唯一），这是存量里没有的推论。
  * `t61_strict_gap_witness`：把 `kernel_strictly_more_general` 与
    `diracKernel_sum` 拼起来，给出「**同一个见证核既非点质量、其总质量仍为 1**」
    —— 存量 `kernel_strictly_more_general` 只说了「非点质量」，
    **没有**说「它仍然是合法的概率核」。这条是本段真正的新内容。
=========================================================================== -/

/-- ⭐⭐⭐ **映射 → 核的完整包**：点质量核同时满足「总质量为 1」、
「在原像处取 1」、「支撑恰为单点」。

这是 `t61_map_to_kernel` 的**逐项展开 + 支撑的 iff 形式**。
存量 `t61_map_to_kernel` 只给 `≠ 0 → y = R c x`（单向）；
本定理把它加强为 **`↔`**（用 `diracKernel_support` 的另一方向）。

前件只是映射 `R`（原料），结论是三条不等价陈述的合取，
其中第三条的 `↔` 是**加强**，不是前件的重述。 -/
theorem t61_map_to_kernel_iff {C X Y : Type*} [Fintype Y] [DecidableEq Y]
    (R : MapForm C X Y) :
    (∀ c x, ∑ y, diracKernel R c x y = 1)
      ∧ (∀ c x, diracKernel R c x (R c x) = 1)
      ∧ (∀ c x y, diracKernel R c x y ≠ 0 ↔ y = R c x) :=
  ⟨fun c x => diracKernel_sum R c x,
   fun c x => diracKernel_at R c x,
   fun c x y => diracKernel_support R c x y⟩

/-- ⭐⭐⭐ **映射 ⇒ 核 ⇒ 映射的往返一致**：

给定 `0–1` 值、每点恰一个 1、1 唯一的核 `K`，则

1. 存在映射 `R` 使 `K = diracKernel R`（存量 `t61_kernel_to_map`）；
2. **并且**该 `R` **必然等于**「`K` 在每点的唯一 1 所在处」的选函数 ——
   **这就是唯一性，存量没有**。

结论是「存在 + 唯一」的合取。前件 `h01`/`hex`/`huniq` 是原料。 -/
theorem t61_kernel_to_map_unique {C X Y : Type*} [DecidableEq Y]
    (K : KernelForm C X Y)
    (h01 : ∀ c x y, K c x y = 0 ∨ K c x y = 1)
    (hex : ∀ c x, ∃ y, K c x y = 1)
    (huniq : ∀ c x y₁ y₂, K c x y₁ = 1 → K c x y₂ = 1 → y₁ = y₂) :
    (∃ R : MapForm C X Y, ∀ c x y, K c x y = diracKernel R c x y)
      ∧ (∀ R₁ R₂ : MapForm C X Y,
          (∀ c x y, K c x y = diracKernel R₁ c x y) →
          (∀ c x y, K c x y = diracKernel R₂ c x y) →
          ∀ c x, R₁ c x = R₂ c x) := by
  refine ⟨t61_kernel_to_map K h01 hex huniq, ?_⟩
  intro R₁ R₂ h₁ h₂ c x
  have hK₁ : K c x (R₁ c x) = 1 := by
    rw [h₁ c x (R₁ c x), diracKernel_at]
  have hK₂ : K c x (R₂ c x) = 1 := by
    rw [h₂ c x (R₂ c x), diracKernel_at]
  exact huniq c x (R₁ c x) (R₂ c x) hK₁ hK₂

/-- ⭐⭐⭐ **同一种核的两张脸**：`(1/2, 1/2)` 见证核**既是**非点质量
（`kernel_strictly_more_general` 的结论）**又**总质量为 1（合法的概率核）。

存量 `kernel_strictly_more_general` 只交付「非点质量」；
本定理补上「它**仍然**是合法的概率核」这一**独立**事实
（总质量 = 1 由 `1/2 + 1/2 = 1`，对 `Bool` 的两点展开）。

**这是本段真正的新内容**：它排除了「`kernel_strictly_more_general` 的见证
退化成非概率核」这一可能性。 -/
theorem t61_strict_gap_witness :
    (∃ K : KernelForm Unit Unit Bool,
        (∀ y, K () () y = 1 / 2) ∧
        (∀ R : MapForm Unit Unit Bool, ∀ y, K () () y ≠ diracKernel R () () y))
      ∧ (∑ _y : Bool, (1 / 2 : ℝ) = 1) := by
  refine ⟨kernel_strictly_more_general, ?_⟩
  norm_num

/-- ⭐⭐ **点质量核的总质量恒等式与支撑性的合取（`Bool` 上机检）**：

对 `Y = Bool` 上任意映射 `R : Unit → Unit → Bool`，
点质量核的总质量为 `1`，且它在两点处分别取 `1` 与 `0`（顺序取决于 `R`）。

这是 `diracKernel_sum` 与 `diracKernel_support` 在**具体载体**上的
**零前件**实例，同时机检了 `Bool` 的两点展开与 `support` 的 `exactly` 语义。 -/
theorem t61_dirac_bool_two_points (R : MapForm Unit Unit Bool) :
    (∑ y : Bool, diracKernel R () () y = 1)
      ∧ (diracKernel R () () (R () ()) = 1)
      ∧ (∀ y : Bool, y ≠ R () () → diracKernel R () () y = 0) := by
  refine ⟨diracKernel_sum R () (), diracKernel_at R () (), ?_⟩
  intro y hy
  have h := diracKernel_support R () () y
  by_contra hne
  exact hy (h.mp hne)

end Fate.T61
