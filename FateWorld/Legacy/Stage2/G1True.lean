import FateWorld.Legacy.FinMarkov
import FateWorld.Legacy.FinCondIndep
import FateWorld.Legacy.FinJoint
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

/-!
# `Fate/Stage2/G1True` —— `G1`：三因子 ⟹ `CondMul`

## 内容

把 `FinMarkov.Factorizes`（三因子）与 `FinCondIndep.CondMul`（双边缘）接起来。

**⚠ 这是项目唯一的真缺口**：`factorizes_condIndepFin` 用 `margA`，
而 `CondMul` 用 `margXZ·margYZ`，**求和次序不同**。

## 变量角色对应

`Factorizes` 的变量是 `(a, b, c)`：`a` = 共同父（分离集），`b`、`c` = 两个结果。
`CondMul p` 的变量是 `p ((x, y), z)`：`x`、`y` = 两个结果，`z` = 条件变量（分离集）。

    Factorizes 的 a  ↔  CondMul 的 z
    Factorizes 的 b  ↔  CondMul 的 x
    Factorizes 的 c  ↔  CondMul 的 y

**⚠ `A × B × C` 在 Lean 中右结合为 `A × (B × C)`**，
故 `P (a, b, c)` 的构造子是 `(a, (b, c))`。

**⚠ universe 对齐**：`FinMarkov.Factorizes` 定义在 `universe u` 上，
故本文的 `A B C` 也声明在同一个 `universe u` 上
（否则 `Type*` 的独立层级无法统一到 `u`）。
-/

universe u

namespace Fate.Stage2.G1True

open Finset
open Fate.FinCondIndep

variable {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]

-- ⭐⭐ 重排：把 `(a, (b, c))` 顺序重排成 `((x, y), z) = ((b, c), a)`。
-- 角色对应：`a` → `z`（条件）、`b` → `x`、`c` → `y`。
def reorder (P : A × B × C → ℝ) : FinJoint B C A :=
  fun xyz => P (xyz.2, (xyz.1.1, xyz.1.2))

-- ⭐ 三因子形式下的重排展开：`p ((x,y),z) = α z * β (z,x) * γ (z,y)`。
omit [Fintype A] [Fintype B] [Fintype C] in
theorem reorder_apply {P : A × B × C → ℝ} {α : A → ℝ} {β : A × B → ℝ}
    {γ : A × C → ℝ} (hP : ∀ a b c, P (a, b, c) = α a * β (a, b) * γ (a, c))
    (x : B) (y : C) (z : A) :
    reorder P ((x, y), z) = α z * β (z, x) * γ (z, y) := by
  show P (z, (x, y)) = α z * β (z, x) * γ (z, y)
  exact hP z x y

-- ⭐ 内层求和：`∑ y, α z * β (z,x) * γ (z,y) = (α z * β (z,x)) * ∑ y, γ (z,y)`。
omit [Fintype A] [Fintype B] in
theorem sumY_reorder {α : A → ℝ} {β : A × B → ℝ} {γ : A × C → ℝ}
    (x : B) (z : A) :
    (∑ y : C, α z * β (z, x) * γ (z, y)) = (α z * β (z, x)) * (∑ y : C, γ (z, y)) := by
  rw [← Finset.mul_sum]

-- ⭐ `(X,Z)` 边缘：`margXZ p x z = α z * β (z,x) * (∑ y, γ (z,y))`。
omit [Fintype A] [Fintype B] in
theorem margXZ_reorder {P : A × B × C → ℝ} {α : A → ℝ} {β : A × B → ℝ}
    {γ : A × C → ℝ} (hP : ∀ a b c, P (a, b, c) = α a * β (a, b) * γ (a, c))
    (x : B) (z : A) :
    margXZ (reorder P) x z = α z * β (z, x) * (∑ y : C, γ (z, y)) := by
  show (∑ y : C, reorder P ((x, y), z)) = α z * β (z, x) * (∑ y : C, γ (z, y))
  rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => reorder_apply hP x y z)]
  exact sumY_reorder x z

-- ⭐ `(Y,Z)` 边缘：`margYZ p y z = γ (z,y) * (α z * ∑ x, β (z,x))`。
omit [Fintype A] [Fintype C] in
theorem margYZ_reorder {P : A × B × C → ℝ} {α : A → ℝ} {β : A × B → ℝ}
    {γ : A × C → ℝ} (hP : ∀ a b c, P (a, b, c) = α a * β (a, b) * γ (a, c))
    (y : C) (z : A) :
    margYZ (reorder P) y z = γ (z, y) * (α z * (∑ x : B, β (z, x))) := by
  show (∑ x : B, reorder P ((x, y), z)) = γ (z, y) * (α z * (∑ x : B, β (z, x)))
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => reorder_apply hP x y z)]
  -- 把 `γ (z,y)` 提到求和之前
  have h1 : ∀ x : B, α z * β (z, x) * γ (z, y) = γ (z, y) * (α z * β (z, x)) := by
    intro x; ring
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => h1 x)]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]

-- ⭐ `Z` 边缘：`margZ p z = (α z * ∑ x, β (z,x)) * (∑ y, γ (z,y))`。
-- 用 `∑ x ∑ y, f x * g y = (∑ x, f x) * (∑ y, g y)`（`Finset.sum_mul_sum`）。
omit [Fintype A] in
theorem margZ_reorder {P : A × B × C → ℝ} {α : A → ℝ} {β : A × B → ℝ}
    {γ : A × C → ℝ} (hP : ∀ a b c, P (a, b, c) = α a * β (a, b) * γ (a, c))
    (z : A) :
    margZ (reorder P) z = (α z * (∑ x : B, β (z, x))) * (∑ y : C, γ (z, y)) := by
  show (∑ x : B, ∑ y : C, reorder P ((x, y), z))
      = (α z * (∑ x : B, β (z, x))) * (∑ y : C, γ (z, y))
  -- 内层：`∑ y, reorder … = (α z * β (z,x)) * ∑ y, γ (z,y)`
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
    (show (∑ y : C, reorder P ((x, y), z)) = (α z * β (z, x)) * (∑ y : C, γ (z, y)) from by
      rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => reorder_apply hP x y z)]
      exact sumY_reorder x z))]
  -- 外层：`∑ x, (α z * β (z,x)) * S = (∑ x, α z * β (z,x)) * S`
  rw [← Finset.sum_mul]
  -- 再提 `α z`：`∑ x, α z * β (z,x) = α z * ∑ x, β (z,x)`
  rw [← Finset.mul_sum]

-- ⭐⭐⭐⭐⭐ `G1` 主定理：三因子分解 ⟹ `CondMul`。
--
-- **⚠ 这是全库第一条把 `FinMarkov.Factorizes` 与 `FinCondIndep.CondMul`
-- 接起来的定理。**
--
-- 设 `P (a,b,c) = α a * β (a,b) * γ (a,c)`，`p = reorder P`。则
--
--   `margZ p z     = (α z * ∑x β(z,x)) * (∑y γ(z,y))`
--   `margXZ p x z  = α z * β(z,x) * (∑y γ(z,y))`
--   `margYZ p y z  = γ(z,y) * (α z * ∑x β(z,x))`
--
-- 于是 `LHS = p((x,y),z) * margZ p z` 与 `RHS = margXZ p x z * margYZ p y z`
-- 是同一组因子 `α z, β(z,x), γ(z,y), (∑x β), (∑y γ)` 的乘积，
-- 两边只在乘法结合/交换次序上不同，故 `ring` 收尾。
omit [Fintype A] in
theorem factorizes_condMul {P : A × B × C → ℝ} (h : Fate.FinMarkov.Factorizes P) :
    CondMul (reorder P) := by
  obtain ⟨α, β, γ, hP⟩ := h
  intro x y z
  show reorder P ((x, y), z) * margZ (reorder P) z
      = margXZ (reorder P) x z * margYZ (reorder P) y z
  rw [reorder_apply hP, margZ_reorder hP, margXZ_reorder hP, margYZ_reorder hP]
  -- 此时两边已是同一组因子的乘积（只差乘法的次序/括号）
  ring_nf

-- 公理审计
#print axioms factorizes_condMul

end Fate.Stage2.G1True
