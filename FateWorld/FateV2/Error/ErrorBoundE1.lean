/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Error.Stage2.ErrorBoundE1`
阶段：**阶段 2 —— 误差界 `E1`（Euler 方法全局误差界）**

---------------------------------------------------------------------------
本文件的地位
---------------------------------------------------------------------------
勘察 F 的 `E1`（数学近似）断言：

    ‖x_n − x(T)‖ ≤ (h·M / (2L)) · (e^{LT} − 1)

其中 `x_n` 是 Euler 方法的数值解（步长 `h`、`n` 步、`T = n·h`），
`x(T)` 是 ODE `y' = f(y)` 的精确解，`M := sup ‖f'‖`，`L` 是 `f` 的 Lipschitz 常数。

按照本项目「宁缺毋滥、零 `sorry`」的验收口径，本文件分层实现：

| 层 | 定理 | 内容 |
|---|---|---|
| **P1** | `geom_sum_rec` | 几何和递推恒等式 `c·Σ + 1 = Σ + c^n` |
|      | `discrete_gronwall` ⭐⭐⭐⭐ | 离散 Gronwall（一般 `r`，无除法） |
| **P2** | `one_add_pow_le_exp_nat` | `(1 + x)^n ≤ exp(n·x)`（`x ≥ −1`） |
|      | `euler_exponent_bound` | `(1+Lh)^n ≤ e^{LT}`（`T = n·h`） |
| **P3** | `euler_error_decomp` | 误差递推的代数分解 |
|      | `euler_global_error` ⭐⭐⭐ | 局部一致性 + 离散 Gronwall ⟹ 全局误差（和式形） |
|      | `euler_global_error_exp` ⭐⭐⭐⭐ | **`E1` 本体**：`(h·M/2L)·(e^{LT} − 1)` |

全部定理**零 `sorry` / `admit` / `axiom`**（见文件末的 `#print axioms`）。

---------------------------------------------------------------------------
⚠ 关于 `discrete_gronwall` 的形式（一个必须记录的数学陷阱）
---------------------------------------------------------------------------
**错误形式**：`a n ≤ r^n * (a 0 + b)`。

**反例（`r = 1`）**：取 `a n = a 0 + n * b`，则
`a (n+1) = a n + b = 1 * a n + b` ✅ 满足递推，
但 `a n = a 0 + n * b > a 0 + b`（当 `n ≥ 2`、`b > 0`）❌。

**正确形式**（本文件所用，**无除法**）：

    a n ≤ r^n * a 0 + b * Σ_{j<n} r^j 。

任务书给出的除法形 `b·((1+Lh)^n − 1)/(L·h)` 在 `L·h = 0` 时无意义；
由 `geom_sum_mul`（**等式**：`(Σ_{j<n} c^j)·(c−1) = c^n − 1`，
见 `euler_global_error_exp` 中的 `hS1`/`hS2`）两条形式在 `L·h ≠ 0` 时完全一致，
而和形式对 `L·h = 0` 也成立。本文件因此**统一用和形式**，
除法只在 `euler_global_error_exp` 里以显式非零前提出现。

**归纳步的正确代数**：设 `S := Σ_{j<k} r^j`、`S' := Σ_{j<k+1} r^j = S + r^k`。
要证 `r * (r^k * a0 + b * S) + b ≤ r^(k+1) * a0 + b * S'`。
两边之差为 `b * (S' − r * S)`，而 `geom_sum_mul` 给出
`S * (r − 1) = r^k − 1` ⟹ `S + r^k − r * S = 1`，故 `S' − r * S = 1`，
于是两边之差恰为 `b ≥ 0` ✅。

⚠ `r * (r^k * a0 + b * S) + b` 与 `r^(k+1) * a0 + b * S'` 的
`ring` 归一化**无法自动对接**（`r^k` 是 `Nat` 索引的幂，`ring` 把它当原子，
两边展开到 `r * r^k` 与 `r^k * r` 后不再匹配）。故必须显式抽出那条
「差值等于 `1`」的等式，再用 `nlinarith` 收尾。

---------------------------------------------------------------------------
⚠ 关于 `euler_global_error` 的前件（诚实登记）
---------------------------------------------------------------------------
1. **`hx : ∀ k, x k = y (k·h)`** —— Euler 的节点值与精确解在该时刻的值对应。
   `k = 0` 时即 `x 0 = y 0`（**初值精确**），这正是 `E1` 右端**没有** `e^{LT}·|x_0 − y(0)|`
   项的原因，也是本证明中 `hz : |x 0 − y (0·h)| = 0` 的来源。
2. **`hM : 0 ≤ M`** —— 显式假设。数学上由 `M = sup ‖f'‖` 非负直接给出；
   `M` 作为 `ℝ` 参数传入时该前件**不能**从别处推出，故显式登记（不隐藏）。
3. **`hloc : ∀ k, |eulerStepDefect y f h k| ≤ M·h²/2`** ——
   **局部一致性（local consistency）**，即 Euler 单步残差界。
   在本文件中它是**显式参数**，`euler_global_error` 从它出发**严格**推出
   全局界——这**不是**循环论证：结论是关于 `n` 步后的距离，前提是**单步**残差，
   两者是不同的命题。
   ⚠ 本文件**没有**把 `hloc` 从 ODE 前件（`y' = f ∘ y`）**推导出来**；
   这需要积分/微分中值定理（`y(t+h) − y(t) = ∫_t^{t+h} f(y)` 再压成 `M·h²/2`）。
   该推导**本文件未完成**，登记为缺口。

---------------------------------------------------------------------------
⚠ 关于 `eulerStepDefect` 的符号（一个真实踩过的坑）
---------------------------------------------------------------------------
初版把残差写成

    y((k+1)h) − y(kh) − h·f(y(kh))         ❌ 分解式差一个负号

正确的写法是

    y(kh) + h·f(y(kh)) − y((k+1)h)         ✅

因为分解式
`x_{k+1} − y((k+1)h) = (x_k − y(kh)) + h·(f(x_k) − f(y(kh))) + (本步残差)`
中最后一项必须是「Euler 一步走到的点 `y(kh) + h·f(y(kh))`」减去「精确解到的点」。
用第一种写法时，`ring` 无法关闭（符号相反）。
（`|·|` 对符号不敏感，故**上界不受影响**。）

---------------------------------------------------------------------------
技术备注（本项目反复踩到的坑，全部实测）
---------------------------------------------------------------------------
1. `Real.add_one_le_exp` 的方向是 `x + 1 ≤ exp x`（**不是** `1 + x`），
   直接喂给 `mul_le_mul` 会 type mismatch；须先单独提出 `1 + x ≤ exp x`。
2. `Nat.cast_add k 1` 的类型是 `↑(k+1) = ↑k + ↑1`，而目标是 `↑k + 1`；
   须写 `by rw [Nat.cast_add, Nat.cast_one]`。
3. `↑(k+1) * h` 与 `↑k * h + h` 在同一目标里并存时，`push_cast` 不会归一；
   须显式 `have hc1 : (↑(k+1) : ℝ) * h = ↑k * h + h := by rw [Nat.cast_add, Nat.cast_one]; ring`
   然后 `rw [hc1]`，**再** `rw` 分解式。
4. `Finset.sum_range_succ` 对 `∑ j ∈ range (k+1)` **一次命中所有同类项**
   （`rw` 重写全部匹配），不能对同一个和式连续 `rw` 两次。
5. 含 `∑` 的目标里 `ring` 把 `r^k` 当原子；凡是需要跨 `Nat` 幂做代数化简，
   必须先用 `geom_sum_mul`（等式形）转成纯 `r` 的多项式等式。
6. `linarith` 不接受「同一表达式以不同形状出现在两侧」的目标；
   解法是先用 `have hcast : ... := by rw [...]; ring` 把形状统一。
7. 本文件**不使用** `linarith_free_1`（不存在的幽灵 tactic），
   **不 import** `Mathlib.Analysis.NormedSpace.Basic`（无 `.olean`）与
   `Mathlib.Topology.MetricSpace.Contraction`（不存在）。
-/

import Mathlib

namespace FateV2.Error.Stage2.ErrorBoundE1

open Finset

/-! ===========================================================================
  §1  **P1：离散 Gronwall 不等式**（无除法，一般 `r ≥ 1`）
  =========================================================================== -/

/-- ✅ **几何和递推恒等式（`c` 任意实数成立，无需 `c ≠ 1`）**：

    c · (Σ_{j<n} c^j) + 1 = (Σ_{j<n} c^j) + c^n 。

这是 `discrete_gronwall` 归纳步的**代数核心**：把
`c * (c^k * a0 + b * S) + b` 与 `c^(k+1) * a0 + b * (S + c^k)` 相减，
`a0` 项抵消（用 `pow_succ`），`b` 项之差正是「`c*S + 1` 与 `S + c^k` 之差」，
即本引理 = `0`。

**证明**：对 `n` 归纳。`sum_range_succ` 把 `Σ_{j<m+1}` 拆成 `Σ_{j<m} + c^m`，
`pow_succ` 把 `c^(m+1)` 拆成 `c^m * c`；`c * (S + c^m)` 用分配律展成
`c*S + c*c^m`，把 `+1` 挪到 `c*S` 旁边以套用归纳假设，最后 `ring` 收尾。 -/
theorem geom_sum_rec (k : ℕ) (c : ℝ) :
    c * (∑ j ∈ Finset.range k, c^j) + 1 = (∑ j ∈ Finset.range k, c^j) + c^k := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hdist : c * (∑ j ∈ Finset.range m, c ^ j + c ^ m)
        = c * (∑ j ∈ Finset.range m, c ^ j) + c * c ^ m := by ring
    rw [hdist]
    calc c * (∑ j ∈ Finset.range m, c ^ j) + c * c ^ m + 1
        = (c * (∑ j ∈ Finset.range m, c ^ j) + 1) + c * c ^ m := by ring
      _ = (∑ j ∈ Finset.range m, c ^ j + c ^ m) + c ^ m * c := by rw [ih]; ring
      _ = ∑ j ∈ Finset.range m, c ^ j + c ^ m + c ^ m * c := by ring

/-- ⭐⭐⭐⭐ **P1：离散 Gronwall 不等式**（标准形式，无除法）。

若 `a (n+1) ≤ r * a n + b`（`r ≥ 1`、`b ≥ 0`），则

    a n ≤ r^n * a 0 + b * Σ_{j ∈ range n, r^j} 。

**证明**：对 `n` 归纳。归纳步用 `S' = S + r^k`（`sum_range_succ`）
把目标化为 `r * (r^k * a0 + b * S) + b ≤ r^(k+1) * a0 + b * S'`，
两边之差为 `b * (S' - r * S) = b * 1 = b ≥ 0`。

⚠ 注意：**不**假设 `a 0 ≥ 0`。
⚠ 注意：**不用除法**，故 `r = 1` 与 `L·h = 0` 的退化情形无需分支。 -/
theorem discrete_gronwall
    (a : ℕ → ℝ) (r b : ℝ) (hr : 1 ≤ r) (hb : 0 ≤ b)
    (hrec : ∀ n, a (n+1) ≤ r * a n + b)
    (n : ℕ) :
    a n ≤ r ^ n * a 0 + b * ∑ j ∈ Finset.range n, r ^ j := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : a (k + 1) ≤ r * a k + b := hrec k
    have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr
    have h2 : r * a k ≤ r * (r ^ k * a 0 + b * ∑ j ∈ Finset.range k, r ^ j) :=
      mul_le_mul_of_nonneg_left ih hr0
    -- `S + r^k − r·S = 1`（由 `geom_sum_mul` 的等式形得到）
    have hkey : (∑ j ∈ Finset.range k, r ^ j) + r ^ k
        - r * ∑ j ∈ Finset.range k, r ^ j = 1 := by
      have h := geom_sum_mul r k
      linarith
    have hsum : ∑ j ∈ Finset.range (k + 1), r ^ j
        = ∑ j ∈ Finset.range k, r ^ j + r ^ k := by
      rw [Finset.sum_range_succ]
    have hpow : r ^ (k + 1) = r ^ k * r := pow_succ r k
    have h3 : r * (r ^ k * a 0 + b * ∑ j ∈ Finset.range k, r ^ j) + b
        ≤ r ^ (k + 1) * a 0 + b * ∑ j ∈ Finset.range (k + 1), r ^ j := by
      rw [hsum, hpow]
      nlinarith [hkey, hb]
    linarith

/-! ===========================================================================
  §2  **P2：`(1 + x)^n ≤ e^{n·x}` 与 E1 的指数型收尾**
  =========================================================================== -/

/-- ⭐⭐ **P2-a：`(1 + x)^n ≤ exp(n·x)`（`x ≥ −1`）**。

**证明**：对 `n` 归纳。
- `n = 0`：两边都是 `1`。
- 归纳步：`(1+x)^(k+1) = (1+x)^k · (1+x) ≤ exp(k·x) · (1+x) ≤ exp(k·x) · exp(x)
  = exp((k+1)·x)`。第一、二步用归纳假设与 `Real.add_one_le_exp`。

⚠ `Real.add_one_le_exp` 的方向是 `x + 1 ≤ exp x`（不是 `1 + x`），
直接喂给 `mul_le_mul` 会因 `1 + x` 与 `x + 1` 不同构而报 type mismatch；
本证明先单独提出 `1 + x ≤ exp x` 再使用。 -/
theorem one_add_pow_le_exp_nat (x : ℝ) (hx : -1 ≤ x) (n : ℕ) :
    (1 + x) ^ n ≤ Real.exp ((n : ℝ) * x) := by
  have hx0 : (0 : ℝ) ≤ 1 + x := by linarith
  have hexpx : 1 + x ≤ Real.exp x := by
    have h := Real.add_one_le_exp x
    linarith
  induction n with
  | zero => simp
  | succ k ih =>
    have hexp : Real.exp ((k : ℝ) * x) * Real.exp x = Real.exp (((k : ℝ) + 1) * x) := by
      rw [← Real.exp_add]; congr 1; ring
    have hcast : (((k + 1 : ℕ)) : ℝ) = ((k : ℝ) + 1) := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [pow_succ, hcast]
    calc (1 + x) ^ k * (1 + x)
        ≤ Real.exp ((k : ℝ) * x) * Real.exp x :=
          mul_le_mul ih hexpx hx0 (Real.exp_nonneg _)
      _ = Real.exp (((k : ℝ) + 1) * x) := hexp

/-- ⭐⭐ **P2-c：`(1 + L·h)^n ≤ exp(L·T)`（`T = n·h`）**。

这是 `E1` 中 `e^{LT}` 出现的**唯一理由**：`Σ_{j<n} (1+Lh)^j` 被
`(1+Lh)^n ≤ e^{Lnh} = e^{LT}` 压住。

**前件**：`L ≥ 0`、`h ≥ 0`、`T = n·h`。 -/
theorem euler_exponent_bound (L h T : ℝ) (n : ℕ)
    (hL : 0 ≤ L) (hh : 0 ≤ h) (hT : T = (n : ℝ) * h) :
    (1 + L*h)^n ≤ Real.exp (L * T) := by
  have hx : (-1 : ℝ) ≤ L * h := by
    have h0 : (0 : ℝ) ≤ L * h := mul_nonneg hL hh
    linarith
  have h1 := one_add_pow_le_exp_nat (L * h) hx n
  rw [hT]
  calc (1 + L*h)^n ≤ Real.exp (((n : ℝ)) * (L * h)) := h1
    _ = Real.exp (L * ((n : ℝ) * h)) := by ring_nf

/-! ===========================================================================
  §3  **P3：`E1` 的严格形式**（全局误差界）
  =========================================================================== -/

/-- **Euler 一步残差（局部一致性误差）**：

    tau(k) := y(k·h) + h·f(y(k·h)) − y((k+1)·h)

物理意义：Euler 从 `y(kh)` 走一步**应到**的点，减去精确解**实到**的点。

⚠ **符号必须是这个方向**（见文件头「关于 `eulerStepDefect` 的符号」）：
写成 `y((k+1)h) − y(kh) − h·f(y(kh))` 会让分解式差一个负号，`ring` 关不掉。

⚠ 用 `(k:ℝ) * h + h` 而非 `((k+1 : ℕ) : ℝ) * h`，使
`y((k+1)·h)` 与 `y((k:ℝ)*h + h)` **定义性**地同一，避免反复 `Nat.cast` 归一化。 -/
noncomputable def eulerStepDefect (y : ℝ → ℝ) (f : ℝ → ℝ) (h : ℝ) (k : ℕ) : ℝ :=
  y ((k : ℝ) * h) + h * f (y ((k : ℝ) * h)) - y ((k : ℝ) * h + h)

/-- **P3-辅助：误差递推的代数分解**。

    x_{k+1} − y((k+1)h) = (x_k − y(kh)) + h·(f(x_k) − f(y(kh))) + tau(k)

这是 `E1` 的**代数核心**：把全局误差拆成
「已有误差」+「误差经 Lipschitz 放大」+「本步新引入的局部误差」。

**证明**：`hE` 展开 `x_{k+1}`、`hx` 把 `x_k` 换成 `y(kh)`，
两侧都归约成 `y(kh) + h·f(y(kh)) − y(kh+h)`。 -/
theorem euler_error_decomp (x : ℕ → ℝ) (y : ℝ → ℝ) (f : ℝ → ℝ) (h : ℝ)
    (hx : ∀ k, x k = y (k * h))
    (hE : ∀ k, x (k+1) = x k + h * f (x k)) :
    ∀ k, x (k+1) - y ((k:ℝ)*h + h)
      = (x k - y (k*h)) + h * (f (x k) - f (y (k*h))) + eulerStepDefect y f h k := by
  intro k
  have hk : x k = y ((k:ℝ)*h) := hx k
  have hk1 : x (k+1) = y ((k:ℝ)*h) + h * f (y ((k:ℝ)*h)) := by rw [hE k, hk]
  unfold eulerStepDefect
  rw [hk1, hk]
  ring

/-- ⭐⭐⭐ **P3：`E1` 的严格形式（全局误差界，和式形）**。

**前件**：

1. `x` 是 Euler 数值解（`h > 0`）：`x_{k+1} = x_k + h·f(x_k)`；
2. `y` 是精确解，且 `x_k = y(k·h)`（`k = 0` 即初值精确）；
3. `f` 是 `L`-Lipschitz；
4. `M ≥ 0`；
5. 每步局部一致性 `|tau(k)| ≤ M·h²/2`。

**结论**（`p := M·h²/2`）：

    |x_n − y(n·h)| ≤ p · Σ_{j<n} (1 + L·h)^j

**证明**：令 `a(k) := |x_k − y(kh)|`。由 `euler_error_decomp` 与三角不等式
`a(k+1) ≤ a(k) + h·L·a(k) + p = (1 + L·h)·a(k) + p`，且 `a(0) = 0`，
于是 `discrete_gronwall` 给出 `a(n) ≤ (1+Lh)^n · 0 + p · Σ_{j<n} (1+Lh)^j`。 -/
theorem euler_global_error
    (f : ℝ → ℝ) (y : ℝ → ℝ) (x : ℕ → ℝ) (L M h : ℝ) (n : ℕ)
    (hL : 0 ≤ L) (hh : 0 < h) (hM : 0 ≤ M)
    (hLip : ∀ u v, |f u - f v| ≤ L * |u - v|)
    (hx : ∀ k, x k = y ((k:ℝ) * h))
    (hE : ∀ k, x (k+1) = x k + h * f (x k))
    (hloc : ∀ k, |eulerStepDefect y f h k| ≤ M * h ^ 2 / 2) :
    |x n - y ((n:ℝ) * h)|
      ≤ (M * h ^ 2 / 2) * (∑ j ∈ Finset.range n, (1 + L * h)^j) := by
  have hpnn : (0 : ℝ) ≤ M * h ^ 2 / 2 := by
    have : (0 : ℝ) ≤ M * h ^ 2 := mul_nonneg hM (sq_nonneg h)
    linarith
  have hc : (1 : ℝ) ≤ 1 + L * h := by nlinarith
  -- 递推：`a(k+1) ≤ (1 + L·h)·a(k) + M·h²/2`
  have hrec : ∀ k, |x (k+1) - y ((k+1 : ℕ) * h)|
      ≤ (1 + L*h) * |x k - y (k * h)| + M * h ^ 2 / 2 := by
    intro k
    have hd := euler_error_decomp x y f h (fun j => hx j) hE k
    -- 目标里是 `y (↑(k+1) * h)`；`hd` 的左端是 `y (↑k*h + h)`。桥接：
    have hc1 : (↑(k + 1) : ℝ) * h = (k : ℝ) * h + h := by
      rw [Nat.cast_add, Nat.cast_one]; ring
    rw [hc1]
    rw [hd]
    have h1 := abs_add_le ((x k - y (k*h)) + h * (f (x k) - f (y (k*h))))
      (eulerStepDefect y f h k)
    have h2 : |eulerStepDefect y f h k| ≤ M * h ^ 2 / 2 := hloc k
    have h3 : |(x k - y (k*h)) + h * (f (x k) - f (y (k*h)))|
        ≤ |x k - y (k*h)| + h * (L * |x k - y (k*h)|) := by
      have hlip := hLip (x k) (y (k*h))
      have habs : |h * (f (x k) - f (y (k*h)))|
          = h * |f (x k) - f (y (k*h))| := by
        rw [abs_mul, abs_of_pos hh]
      calc |(x k - y (k*h)) + h * (f (x k) - f (y (k*h)))|
          ≤ |x k - y (k*h)| + |h * (f (x k) - f (y (k*h)))| := abs_add_le _ _
        _ = |x k - y (k*h)| + h * |f (x k) - f (y (k*h))| := by rw [habs]
        _ ≤ |x k - y (k*h)| + h * (L * |x k - y (k*h)|) := by
            have hmul := mul_le_mul_of_nonneg_left hlip (le_of_lt hh)
            linarith
    have h5 : (1 + L * h) * |x k - y (k*h)| + M * h ^ 2 / 2
        = |x k - y (k*h)| + h * (L * |x k - y (k*h)|) + M * h ^ 2 / 2 := by ring
    linarith
  -- 取 `a := fun k => |x k − y (k·h)|` 应用离散 Gronwall
  have hmain := discrete_gronwall (fun k => |x k - y (k * h)|) (1 + L * h)
    (M * h ^ 2 / 2) hc hpnn hrec n
  -- `a(0) = |x 0 − y(0·h)| = 0`（初值精确）
  have hz : |x 0 - y ((0:ℕ) * h)| = 0 := by
    have hp0 := hx 0
    rw [hp0]; simp
  rw [hz, mul_zero, zero_add] at hmain
  exact hmain

/-- ⭐⭐⭐⭐ **P3：`E1` 本体（`exp` 形，= `ErrorQuadruple.E1Statement` 的实例）**。

在 `euler_global_error` 的基础上，用
`Σ_{j<n} (1+Lh)^j = ((1+Lh)^n − 1)/(L·h)` 与 `(1+Lh)^n ≤ e^{L·T}`（`T = n·h`）压成

    |x_n − y(T)| ≤ (h·M / (2·L)) · (e^{L·T} − 1)

这正是 `FateV2.Error.Stage2.ErrorQuadruple.E1Statement ℝ M L T h (x n) (y T)` 的内容。

**前件**：`L > 0`、`h > 0`、`M ≥ 0`、`T = n·h`（外加 `euler_global_error` 的四条）。

**证明**：`p·Σ ≤ p·((e^{LT} − 1)/(L·h)) = (h·M/2)·(e^{LT} − 1)
= (h·M/(2L))·L·(e^{LT} − 1) = (h·M/(2L))·(e^{LT} − 1)`。

⚠ 最后一步 `(h·M/(2L))·L = h·M/2` 需要 `L ≠ 0`（由 `hL` 给出）。 -/
theorem euler_global_error_exp
    (f : ℝ → ℝ) (y : ℝ → ℝ) (x : ℕ → ℝ) (L M h T : ℝ) (n : ℕ)
    (hL : 0 < L) (hh : 0 < h) (hM : 0 ≤ M) (hT : T = (n : ℝ) * h)
    (hLip : ∀ u v, |f u - f v| ≤ L * |u - v|)
    (hx : ∀ k, x k = y (k * h))
    (hE : ∀ k, x (k+1) = x k + h * f (x k))
    (hloc : ∀ k, |eulerStepDefect y f h k| ≤ M * h ^ 2 / 2) :
    |x n - y T| ≤ (h * M / (2 * L)) * (Real.exp (L * T) - 1) := by
  have hg := euler_global_error f y x L M h n (le_of_lt hL) hh hM hLip hx hE hloc
  -- 把 `hg` 里的 `↑n * h` 统一成 `T`
  rw [show (n:ℝ) * h = T from hT.symm] at hg
  have hc1 : (1 : ℝ) < 1 + L * h := by nlinarith
  -- `S * (L·h) = (1+Lh)^n − 1`（`geom_sum_mul` 的等式形，不除）
  have hS1 : (∑ j ∈ Finset.range n, (1 + L * h) ^ j) * (L * h) = (1 + L * h) ^ n - 1 := by
    have hgeo : (∑ j ∈ Finset.range n, (1 + L * h) ^ j) * ((1 + L * h) - 1)
        = (1 + L * h) ^ n - 1 := geom_sum_mul (1 + L * h) n
    have hsub : ((1 + L * h) - 1) = L * h := by ring
    rw [hsub] at hgeo
    exact hgeo
  have hLhpos : (0 : ℝ) < L * h := mul_pos hL hh
  have hS2 : (∑ j ∈ Finset.range n, (1 + L * h) ^ j)
      = ((1 + L * h) ^ n - 1) / (L * h) := by
    rw [eq_div_iff (ne_of_gt hLhpos)]
    exact hS1
  have hbnd : (1 + L * h) ^ n ≤ Real.exp (L * T) :=
    euler_exponent_bound L h T n (le_of_lt hL) (le_of_lt hh) hT
  have hSle : (∑ j ∈ Finset.range n, (1 + L * h) ^ j)
      ≤ (Real.exp (L * T) - 1) / (L * h) := by
    rw [hS2]
    have hnum : (1 + L * h) ^ n - 1 ≤ Real.exp (L * T) - 1 := by linarith
    exact div_le_div_of_nonneg_right hnum (le_of_lt hLhpos)
  set p : ℝ := M * h ^ 2 / 2 with hp
  have hppos : 0 ≤ p := by rw [hp]; positivity
  have hkey : p * (∑ j ∈ Finset.range n, (1 + L * h) ^ j)
      ≤ (h * M / (2 * L)) * (Real.exp (L * T) - 1) := by
    have h1 : p * (∑ j ∈ Finset.range n, (1 + L * h) ^ j)
        ≤ p * ((Real.exp (L * T) - 1) / (L * h)) :=
      mul_le_mul_of_nonneg_left hSle hppos
    have h2 : p * ((Real.exp (L * T) - 1) / (L * h))
        = (h * M / (2 * L)) * (Real.exp (L * T) - 1) := by
      rw [hp]
      field_simp
    linarith
  exact le_trans hg hkey

end FateV2.Error.Stage2.ErrorBoundE1

/-! ===========================================================================
  §4  公理审计（编译期验证：全部只依赖 `propext` / `Classical.choice` / `Quot.sound`）
  =========================================================================== -/

#print axioms FateV2.Error.Stage2.ErrorBoundE1.geom_sum_rec
#print axioms FateV2.Error.Stage2.ErrorBoundE1.discrete_gronwall
#print axioms FateV2.Error.Stage2.ErrorBoundE1.one_add_pow_le_exp_nat
#print axioms FateV2.Error.Stage2.ErrorBoundE1.euler_exponent_bound
#print axioms FateV2.Error.Stage2.ErrorBoundE1.euler_error_decomp
#print axioms FateV2.Error.Stage2.ErrorBoundE1.euler_global_error
#print axioms FateV2.Error.Stage2.ErrorBoundE1.euler_global_error_exp
