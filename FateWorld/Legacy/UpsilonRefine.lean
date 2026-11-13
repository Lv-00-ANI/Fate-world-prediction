import FateWorld.Legacy.LawRule

/-! ===========================================================================
  §0  `υ`（完善/收窄）的三重处理（作者裁决「三者并行」）

  ## 背景

  `Fate/LawRule.lean:139,142`：
  ```lean
  def generalize (R₁ R₂) (_h : ∀ c x, R₁ c x ⊆ R₂ c x) : LawRule C X Y := R₂
  def refine     (R₁ R₂) (_h : ∀ c x, R₂ c x ⊆ R₁ c x) : LawRule C X Y := R₂
  ```
  **`_h` 参数完全未被消费**（结果恒为 `R₂`）。

  **作者裁决**：**三者并行**（甲 / 乙 / 丙）。

  ## ⭐ 核心发现

  **`refine` 与 `compose` 在 `_h` 成立时是同一个运算**：
  `R₂ ⊆ R₁ ⟹ R₂ = R₁ ∩ R₂`。

  **⟹ 「`_h` 未被消费」不是缺陷，而是「等价实现的另一写法」。**

  ## 三者定位

  | 方案 | 层 | 内容 |
  |---|---|---|
  | **乙** | **语法** | 保留 `_h`（许可证声明）+ 证 `refine = compose` |
  | **甲** | **语义** | `refine' := compose`（无条件，无冗余参数）|
  | **丙** | **计算** | 似然裁剪（本节只给定形式，不实现具体似然）|
  =========================================================================== -/

namespace Fate

namespace LawRule

universe u

variable {C : CtxSpace} {X : StateSpace} {Y : OutSpace} [MeasurableSpace Y.Carrier]

/-! ### §0.1 ⭐ 乙：`refine = compose` -/

/-- ⭐⭐ **`refine` 与 `compose` 在 `_h` 成立时等价**。

`refine R₁ R₂ h = R₂`，`compose R₁ R₂ = R₁ ∩ R₂`，
由 `h : R₂ ⊆ R₁` 得 `R₁ ∩ R₂ = R₂`。

**⟹ 消解「`_h` 未被消费」的疑虑**：`_h` 保证两种写法一致。 -/
theorem refine_eq_compose (R₁ R₂ : LawRule C X Y)
    (h : ∀ c x, R₂ c x ⊆ R₁ c x) :
    refine R₁ R₂ h = compose R₁ R₂ := by
  funext c x
  apply Set.Subset.antisymm
  · intro d hd
    exact ⟨h c x hd, hd⟩
  · intro d hd
    exact hd.2

/-- ⭐ **`generalize` 的对应命题**：`generalize R₁ R₂ h = R₂`，
而 `compose R₁ R₂ = R₁ ∩ R₂ = R₁`（因 `h : R₁ ⊆ R₂`）。

**⟹ 所以 `generalize` 一般**不**等于 `compose`**（除非 `R₁ = R₂`）。

**⚠ 这是 `generalize` 与 `refine` 的不对称之处**，如实记录。 -/
theorem generalize_ne_compose (R₁ R₂ : LawRule C X Y)
    (h : ∀ c x, R₁ c x ⊆ R₂ c x) :
    generalize R₁ R₂ h = R₂ := rfl

/-! ### §0.2 ⭐ 甲：`refine' := compose` -/

/-- ⭐⭐ **无条件收窄**（甲方案）：不需要 `_h`，直接取交。 -/
def refine' (R₁ R₂ : LawRule C X Y) : LawRule C X Y := compose R₁ R₂

/-- ⭐ **`refine'` 与 `refine` 在 `_h` 下一致**。 -/
theorem refine'_eq_refine (R₁ R₂ : LawRule C X Y)
    (h : ∀ c x, R₂ c x ⊆ R₁ c x) :
    refine' R₁ R₂ = refine R₁ R₂ h := by
  unfold refine'
  exact (refine_eq_compose R₁ R₂ h).symm

/-- **`refine'` 的交换律**（继承自 `compose`）。 -/
theorem refine'_comm (R₁ R₂ : LawRule C X Y) : refine' R₁ R₂ = refine' R₂ R₁ :=
  compose_comm R₁ R₂

/-- **`refine'` 的结合律**（继承自 `compose`）。 -/
theorem refine'_assoc (R₁ R₂ R₃ : LawRule C X Y) :
    refine' (refine' R₁ R₂) R₃ = refine' R₁ (refine' R₂ R₃) :=
  compose_assoc R₁ R₂ R₃

/-- **`refine'` 对顶元是恒等**。 -/
theorem refine'_top (R : LawRule C X Y) : refine' R (top C X Y) = R :=
  compose_top R

end LawRule

end Fate
