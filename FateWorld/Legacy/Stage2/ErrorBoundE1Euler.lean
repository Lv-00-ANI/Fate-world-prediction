/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.Stage2.ErrorBoundE1Euler`
阶段：**阶段 2 —— 误差界 E1 的 Euler 全局误差推论**

---------------------------------------------------------------------------
本文件的地位
---------------------------------------------------------------------------
`Fate.Stage2.ErrorBoundE1` 已把 **离散 Gronwall 不等式**真证出来：

> `a (n+1) ≤ r * a n + b`，`r ≥ 1`、`b ≥ 0`  ⟹
> `a n ≤ r^n * a 0 + b * ∑_{j<n} r^j`。

本文件从它**推出 Euler 方法的全局误差界**，即标准数值分析中的
「局部误差 O(h²) ⟹ 全局误差 O(h)」这一步。

---------------------------------------------------------------------------
形式（抽象版，无需 ODE 精确解的载体）
---------------------------------------------------------------------------
设 `x : ℕ → ℝ` 是数值解、`y : ℕ → ℝ` 是「精确解」（任意序列），
`f : ℝ → ℝ` 是向量场，`h` 步长，`L` Lipschitz 常数，`M` 单步误差常数。

**前件**：
1. `h > 0`、`L > 0`、`M ≥ 0`；
2. `f` 是 `L`-Lipschitz；
3. `x 0 = y 0`（初值精确）；
4. Euler 递推 `x (k+1) = x k + h * f (x k)`；
5. **单步局部误差** `|y (k+1) - (y k + h * f (y k))| ≤ h² M / 2`。

**结论**：

    |x n - y n| ≤ (h M / (2 L)) * ((1 + L h)^n - 1)          -- 层 1
                ≤ (h M / (2 L)) * (exp (L * n * h) - 1)      -- 层 2

⚠ **这是「抽象版」**：`y` 可以是任意序列（不必真的来自 ODE），
只要它满足单步误差界 `hloc`，结论就成立。这避开了
「ODE 精确解存在性」（Picard–Lindelöf）这一载体问题。

---------------------------------------------------------------------------
证明结构
---------------------------------------------------------------------------
§1 `step_rec`：单步误差递推 `a (k+1) ≤ (1 + L h) * a k + h² M / 2`。
   三角不等式拆成「Euler 映射的 Lipschitz 部分」+「局部截断误差」。
§2 `geom_growth_eq`：`(h² M / 2) * ∑_{j<n} (1+Lh)^j = (hM/(2L)) * ((1+Lh)^n - 1)`。
   用 `geom_sum_eq`，再 `field_simp` 清分母。
§3 `euler_global_error_abstract`：**层 1**，用 `discrete_gronwall` 收口。
§4 `euler_global_error_exp`：**层 2**，用 `(1+x)^n ≤ exp(n x)` 换成指数形。

依阶段 0 验收标准：**零 `sorry`、零 `admit`、零 `axiom`。**
-/

import Mathlib
import FateWorld.Legacy.Stage2.ErrorBoundE1

namespace Fate.Stage2.ErrorBoundE1Euler

open Finset

/-! ===========================================================================
  §1  单步误差递推
  =========================================================================== -/

/-- ⭐⭐ **单步误差递推**：

    |x (k+1) - y (k+1)| ≤ (1 + L*h) * |x k - y k| + h^2 * M / 2 。

**证明**：三角不等式拆成两支。

* 第一支 `|x(k+1) - (y k + h f(y k))|`：
  代入 `x(k+1) = x k + h f(x k)`，得
  `|(x k - y k) + h (f(x k) - f(y k))|`
  `≤ |x k - y k| + h |f(x k) - f(y k)| ≤ (1 + L h) |x k - y k|`（Lipschitz）。
* 第二支 `|(y k + h f(y k)) - y(k+1)| = |y(k+1) - (y k + h f(y k))| ≤ h² M / 2`
  （`abs_sub_comm` + 局部误差假设）。

⚠ 本引理**不需要** `L > 0` 与 `M ≥ 0`：只需 `h > 0` 把 `|h|` 消成 `h`。 -/
theorem step_rec
    (x y : ℕ → ℝ) (f : ℝ → ℝ) (h L M : ℝ)
    (hh : 0 < h)
    (hLip : ∀ a b, |f a - f b| ≤ L * |a - b|)
    (hx : ∀ k, x (k+1) = x k + h * f (x k))
    (hloc : ∀ k, |y (k+1) - (y k + h * f (y k))| ≤ h^2 * M / 2)
    (k : ℕ) :
    |x (k+1) - y (k+1)| ≤ (1 + L*h) * |x k - y k| + h^2 * M / 2 := by
  have habs_h : |h| = h := abs_of_pos hh
  -- 第二支：局部截断误差
  have hsecond : |(y k + h * f (y k)) - y (k+1)| ≤ h^2 * M / 2 := by
    rw [abs_sub_comm]
    exact hloc k
  -- 第一支：Euler 映射的 Lipschitz 界
  have hfirst : |x (k+1) - (y k + h * f (y k))| ≤ (1 + L*h) * |x k - y k| := by
    rw [hx k]
    have hid : x k + h * f (x k) - (y k + h * f (y k))
        = (x k - y k) + h * (f (x k) - f (y k)) := by ring
    have hab : |(x k - y k) + h * (f (x k) - f (y k))|
        ≤ |x k - y k| + |h * (f (x k) - f (y k))| := abs_add_le _ _
    have h2 : |h * (f (x k) - f (y k))| = h * |f (x k) - f (y k)| := by
      rw [abs_mul, habs_h]
    rw [h2] at hab
    have h3 : h * |f (x k) - f (y k)| ≤ h * (L * |x k - y k|) :=
      mul_le_mul_of_nonneg_left (hLip _ _) (le_of_lt hh)
    have h4 : h * (L * |x k - y k|) = L * h * |x k - y k| := by ring
    rw [h4] at h3
    have h5 : (1 + L * h) * |x k - y k|
        = |x k - y k| + L * h * |x k - y k| := by ring
    rw [h5]
    rw [hid]
    linarith
  -- 三角不等式
  have htri : |x (k+1) - y (k+1)|
      ≤ |x (k+1) - (y k + h * f (y k))| + |(y k + h * f (y k)) - y (k+1)| :=
    abs_sub_le _ _ _
  linarith

/-! ===========================================================================
  §2  几何级数的闭式
  =========================================================================== -/

/-- ⭐⭐ **代数核心**（把 Gronwall 的几何级数压成闭式）：

    (h² M / 2) * ∑_{j<n} (1 + L h)^j = (h M / (2 L)) * ((1 + L h)^n - 1) 。

**证明**：`geom_sum_eq` 给出 `∑_{j<n} x^j = (x^n - 1)/(x - 1)`，
其中 `x = 1 + L h ≠ 1`（因 `L h ≠ 0`）、`x - 1 = L h`；
代入后两边同乘常数，`field_simp` 清分母即得。

⚠ `geom_sum_eq` 是顶层名（**不是** `Finset.geom_sum_eq`），且需要 `x ≠ 1`。 -/
theorem geom_growth_eq (h L M : ℝ) (hh : 0 < h) (hL : 0 < L) (n : ℕ) :
    h^2 * M / 2 * ∑ j ∈ range n, (1 + L*h) ^ j
      = (h * M / (2 * L)) * ((1 + L*h)^n - 1) := by
  have hLh : L * h ≠ 0 := ne_of_gt (mul_pos hL hh)
  have hone : (1 + L*h) - 1 = L * h := by ring
  have hx1 : (1 + L*h : ℝ) ≠ 1 := by
    intro hc
    have : L * h = 0 := by linarith
    exact hLh this
  rw [geom_sum_eq hx1]
  rw [hone]
  field_simp

/-! ===========================================================================
  §3  层 1：Euler 全局误差界（抽象形式）
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **层 1：Euler 全局误差界（抽象形式）**：

设 `x : ℕ → ℝ` 是 Euler 数值解（`x (k+1) = x k + h * f (x k)`），
`y : ℕ → ℝ` 是「精确解」在网格点上的取值，且每步局部误差不超过 `h² M / 2`。
若 `f` 是 `L`-Lipschitz、初值精确，则

    |x n - y n| ≤ (h M / (2 L)) * ((1 + L h)^n - 1) 。

**证明**：令 `a k := |x k - y k|`，由 `step_rec` 得
`a (k+1) ≤ (1 + L h) * a k + h² M / 2`，且 `a 0 = |y 0 - y 0| = 0`；
以 `r := 1 + L h ≥ 1`、`b := h² M / 2 ≥ 0` 喂给 `discrete_gronwall`，
最后用 `geom_growth_eq` 把几何级数压成闭式。 -/
theorem euler_global_error_abstract
    (x y : ℕ → ℝ) (f : ℝ → ℝ) (h L M : ℝ)
    (hh : 0 < h) (hL : 0 < L) (hM : 0 ≤ M)
    (hLip : ∀ a b, |f a - f b| ≤ L * |a - b|)
    (hx0 : x 0 = y 0)
    (hx : ∀ k, x (k+1) = x k + h * f (x k))
    (hloc : ∀ k, |y (k+1) - (y k + h * f (y k))| ≤ h^2 * M / 2)
    (n : ℕ) :
    |x n - y n| ≤ (h * M / (2 * L)) * ((1 + L*h)^n - 1) := by
  have hr : (1 : ℝ) ≤ 1 + L*h := by nlinarith
  have hb : (0 : ℝ) ≤ h^2 * M / 2 := by positivity
  have hrec : ∀ k, |x (k+1) - y (k+1)|
      ≤ (1 + L*h) * |x k - y k| + h^2 * M / 2 :=
    step_rec x y f h L M hh hLip hx hloc
  have hg := Fate.Stage2.ErrorBoundE1.discrete_gronwall
    (fun k => |x k - y k|) (1 + L*h) (h^2 * M / 2) hr hb hrec n
  -- `a 0 = |x 0 - y 0| = |y 0 - y 0| = 0`
  rw [hx0] at hg
  have hz : y 0 - y 0 = (0 : ℝ) := sub_self _
  rw [hz, abs_zero, mul_zero, zero_add] at hg
  rw [geom_growth_eq h L M hh hL n] at hg
  exact hg

/-! ===========================================================================
  §4  层 2：换成指数形
  =========================================================================== -/

/-- ⭐⭐ **`(1 + L h)^n ≤ exp (L * n * h)`**（`L, h ≥ 0`）。

由 `ErrorBoundE1.one_add_pow_le_exp_nat`（`(1+x)^n ≤ exp(n x)`，`x ≥ -1`）
取 `x := L h` 即得。 -/
theorem one_add_pow_le_exp_Lnh (L h : ℝ) (hL : 0 ≤ L) (hh : 0 ≤ h) (n : ℕ) :
    (1 + L*h)^n ≤ Real.exp (L * ((n:ℝ) * h)) := by
  have hx : (-1 : ℝ) ≤ L * h := by
    have h0 : (0 : ℝ) ≤ L * h := mul_nonneg hL hh
    linarith
  have h1 := Fate.Stage2.ErrorBoundE1.one_add_pow_le_exp_nat (L * h) hx n
  calc (1 + L*h)^n ≤ Real.exp (((n : ℝ)) * (L * h)) := h1
    _ = Real.exp (L * ((n : ℝ) * h)) := by ring_nf

/-- ⭐⭐ **几何级数的指数上界**：

    ∑_{j<n} (1 + L h)^j ≤ (exp (L * n * h) - 1) / (L h) 。

**证明**：`geom_sum_mul` 给出 `S * (L h) = (1 + L h)^n - 1`（不除法），
故 `S = ((1+Lh)^n - 1)/(L h)`；再用 `one_add_pow_le_exp_Lnh` 放大分子。 -/
theorem geom_sum_le_exp (L h : ℝ) (hL : 0 < L) (hh : 0 < h) (n : ℕ) :
    ∑ j ∈ range n, (1 + L*h)^j ≤ (Real.exp (L * ((n:ℝ) * h)) - 1) / (L * h) := by
  have hLhpos : (0 : ℝ) < L * h := mul_pos hL hh
  have hS1 : (∑ j ∈ range n, (1 + L * h) ^ j) * (L * h) = (1 + L * h) ^ n - 1 := by
    have hgeo : (∑ j ∈ range n, (1 + L * h) ^ j) * ((1 + L * h) - 1)
        = (1 + L * h) ^ n - 1 := geom_sum_mul (1 + L * h) n
    have hsub : ((1 + L * h) - 1) = L * h := by ring
    rw [hsub] at hgeo
    exact hgeo
  have hS2 : (∑ j ∈ range n, (1 + L * h) ^ j)
      = ((1 + L * h) ^ n - 1) / (L * h) := by
    rw [eq_div_iff (ne_of_gt hLhpos)]
    exact hS1
  rw [hS2]
  have hbnd : (1 + L * h) ^ n ≤ Real.exp (L * ((n:ℝ) * h)) :=
    one_add_pow_le_exp_Lnh L h (le_of_lt hL) (le_of_lt hh) n
  have hnum : (1 + L * h) ^ n - 1 ≤ Real.exp (L * ((n:ℝ) * h)) - 1 := by linarith
  exact div_le_div_of_nonneg_right hnum (le_of_lt hLhpos)

/-- ⭐⭐⭐⭐ **层 2：Euler 全局误差界（指数形式）**：

    |x n - y n| ≤ (h M / (2 L)) * (exp (L * n * h) - 1) 。

这是标准教科书形式 `(hM/2L)(e^{L T} - 1)`（`T = n h`）。

**证明**：先取层 1 的 `(hM/(2L)) ((1+Lh)^n - 1)`；
由 `one_add_pow_le_exp_Lnh` 得 `(1+Lh)^n - 1 ≤ exp(L n h) - 1`，
再乘上非负常数 `h M / (2 L)` 即得。 -/
theorem euler_global_error_exp
    (x y : ℕ → ℝ) (f : ℝ → ℝ) (h L M : ℝ)
    (hh : 0 < h) (hL : 0 < L) (hM : 0 ≤ M)
    (hLip : ∀ a b, |f a - f b| ≤ L * |a - b|)
    (hx0 : x 0 = y 0)
    (hx : ∀ k, x (k+1) = x k + h * f (x k))
    (hloc : ∀ k, |y (k+1) - (y k + h * f (y k))| ≤ h^2 * M / 2)
    (n : ℕ) :
    |x n - y n| ≤ (h * M / (2 * L)) * (Real.exp (L * ((n:ℝ) * h)) - 1) := by
  have hg := euler_global_error_abstract x y f h L M hh hL hM hLip hx0 hx hloc n
  -- 常数 `h M / (2 L) ≥ 0`
  have hc : (0 : ℝ) ≤ h * M / (2 * L) := by positivity
  have hbnd : (1 + L*h)^n - 1 ≤ Real.exp (L * ((n:ℝ) * h)) - 1 := by
    have := one_add_pow_le_exp_Lnh L h (le_of_lt hL) (le_of_lt hh) n
    linarith
  calc |x n - y n|
      ≤ (h * M / (2 * L)) * ((1 + L*h)^n - 1) := hg
    _ ≤ (h * M / (2 * L)) * (Real.exp (L * ((n:ℝ) * h)) - 1) :=
        mul_le_mul_of_nonneg_left hbnd hc

end Fate.Stage2.ErrorBoundE1Euler

/-! ===========================================================================
  §5  公理审计
  =========================================================================== -/

-- ⚠ 验收：以下应只列出 `propext`、`Classical.choice`、`Quot.sound`（**不含 `sorryAx`**）
#print axioms Fate.Stage2.ErrorBoundE1Euler.step_rec
#print axioms Fate.Stage2.ErrorBoundE1Euler.geom_growth_eq
#print axioms Fate.Stage2.ErrorBoundE1Euler.euler_global_error_abstract
#print axioms Fate.Stage2.ErrorBoundE1Euler.one_add_pow_le_exp_Lnh
#print axioms Fate.Stage2.ErrorBoundE1Euler.geom_sum_le_exp
#print axioms Fate.Stage2.ErrorBoundE1Euler.euler_global_error_exp
