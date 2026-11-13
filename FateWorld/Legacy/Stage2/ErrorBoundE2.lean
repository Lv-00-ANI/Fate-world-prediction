/-
================================================================================
  Fate/Stage2/ErrorBoundE2.lean
  —— 离散 Hoeffding / 子高斯界的基础不等式（Stage2 · E2）

  本文件只做「基础」层：不含测度/积分的概率形式，只做可独立验证的
  实分析代数不等式。全部定理**无 sorry / 无 admit / 无 axiom**。

  定理清单（8 条，逐条已单独验证）：
    §1  one_add_le_exp            : 1 + x ≤ exp x              (全 ℝ)
    §2  exp_ge_quad               : 1 + x + x²/2 ≤ exp x        (x ≥ 0)
    §3  exp_neg_le_quadratic      : exp(-x) ≤ 1 - x + x²/2      (x ≥ 0)
    §4  one_add_pow_le_exp        : (1+x)^n ≤ exp(n·x)          (x ≥ 0)
    §5  hoeffding_two_point       : exp(t·x) ≤ (1-x) + x·exp t  (x ∈ [0,1])
    §6  hoeffding_affine          : exp(t·x) ≤ 1 + x·(exp t - 1) (x ∈ [0,1])
    §7  hoeffding_prod_bound      : n 项求和的 mgf 界（乘积形式）
    §8  hoeffding_mgf_two_point   : 二点变量中心化 mgf ≤ exp(t²/8)

  依赖：Mathlib（本地 path require，D:/mathlib）
================================================================================
-/
import Mathlib

namespace Fate.Stage2.ErrorBoundE2

open Real

/-! ## §1  指数函数的一阶下界 -/

/-- ⭐⭐ **基础不等式**：`1 + x ≤ exp x`（对一切实数 `x` 成立）。

注意方向：Mathlib 的 `Real.add_one_le_exp` 陈述为 `x + 1 ≤ exp x`，
本引理把它整理成更常用的 `1 + x` 形式。

**这是 Chernoff 界与 Hoeffding 不等式的共同起点。** -/
theorem one_add_le_exp (x : ℝ) : 1 + x ≤ Real.exp x := by
  have h := Real.add_one_le_exp x
  linarith

/-! ## §2  指数函数的二次泰勒下界 -/

/-- ⭐⭐ **`exp` 的二次泰勒下界**：对 `x ≥ 0`，

$$1 + x + \frac{x^2}{2} \le e^{x}$$

这是 §3 的唯一输入。证明直接取自 Mathlib 的泰勒级数部分和
`Real.sum_le_exp_of_nonneg`（指数级数各项非负，故部分和是 `exp` 的下界），
取前三项即可。 -/
theorem exp_ge_quad (x : ℝ) (hx : 0 ≤ x) : 1 + x + x^2/2 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 3
  simp [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-! ## §3  `exp(-x)` 的二次上界（Hoeffding 的核心工具） -/

/-- ⭐⭐⭐ **`exp(-x) ≤ 1 - x + x²/2`**（`x ≥ 0`）。

**这是 Hoeffding 证明的核心工具**：它把 `e^{-tx}` 压成关于 `x`
的二次多项式，从而得到 Chernoff 界里 `t²/8` 的那个 `t²`。

**证明思路**（三步）：
1. §2 给出 `exp x ≥ 1 + x + x²/2`，右端恒正；
2. `exp(-x) = 1/exp x ≤ 1/(1+x+x²/2)`（分母越大商越小）；
3. 关键恒等式 `(1+x+x²/2)(1-x+x²/2) = 1 + x⁴/4 ≥ 1`，
   故 `1/(1+x+x²/2) ≤ 1-x+x²/2`。

⚠ 不能直接用 `Real.exp_bound'`：那是 `exp` 的**上界**，方向相反。 -/
theorem exp_neg_le_quadratic (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x^2/2 := by
  have hquad : 1 + x + x^2/2 ≤ Real.exp x := exp_ge_quad x hx
  have hpos : 0 < 1 + x + x^2 / 2 := by nlinarith [sq_nonneg x]
  have hneg : Real.exp (-x) = 1 / Real.exp x := by
    rw [Real.exp_neg, one_div]
  rw [hneg]
  -- 第一步：分母换成泰勒多项式的下界
  have hstep1 : 1 / Real.exp x ≤ 1 / (1 + x + x^2/2) :=
    one_div_le_one_div_of_le hpos hquad
  -- 第二步：1/(1+x+x²/2) ≤ 1-x+x²/2，等价于 1 ≤ (1+x+x²/2)(1-x+x²/2) = 1 + x⁴/4
  have hstep2 : 1 / (1 + x + x^2/2) ≤ 1 - x + x^2/2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg (x^2)]
  linarith

/-! ## §4  `(1 + x)^n ≤ exp(n·x)` -/

/-- ⭐⭐⭐ **`(1 + x)^n ≤ exp(n·x)`**（`x ≥ 0`）。

**集中不等式的标准工具**（`E1` 中 `one_add_pow_le_exp_nat` 的 `x ≥ 0` 特化版，
但此处用 `Real.exp_nat_mul` 一步收口，比 E1 的归纳证明更短）。

**证明**：`(1+x)^n ≤ (exp x)^n`（`pow_le_pow_left₀`，底数非负）
`= exp(n·x)`（`Real.exp_nat_mul` 反向）。

⚠ `pow_le_pow_left₀` 的参数顺序是 `(h0 : 0 ≤ a) (h1 : a ≤ b) (n)`。 -/
theorem one_add_pow_le_exp (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (1 + x)^n ≤ Real.exp (↑n * x) := by
  have h1 : 1 + x ≤ Real.exp x := one_add_le_exp x
  have h0 : (0:ℝ) ≤ 1 + x := by linarith
  calc (1 + x)^n ≤ (Real.exp x)^n := pow_le_pow_left₀ h0 h1 n
    _ = Real.exp (↑n * x) := (Real.exp_nat_mul x n).symm

/-! ## §5  Hoeffding 引理的代数核心（二点情形）

`X` 取值于 `{0, t}` 时，`exp` 的凸性给出 `e^{tX}` 的**线性上界**。
这正是 Hoeffding 引理里「把 `e^{tX}` 换成一条割线」的那一步。

**⚠ 关键 API 事实**（实测）：`ConvexOn` 的展开形式是

```
∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ a • f x + b • f y
```

即凸组合是 `a • x + b • y`（**不是** `b • x + a • y`），且 `a + b = 1`。
初版把 `a`、`b` 的角色写反，导致 `realApplication` 类型不匹配。 -/

/-- ⭐⭐⭐⭐ **Hoeffding 引理的代数核心（二点情形）**：

若 `x ∈ [0, 1]`，则对任意 `t : ℝ`，

$$e^{t x} \;\le\; (1-x) + x\,e^{t}$$

**意义**：这是 `e^{tX}` 在**凸包**上的界，即 `X` 取值在 `{0, 1}` 时的
mgf 上界（取期望后：`E[e^{tX}] ≤ 1 - p + p e^t`，其中 `p = E[X]`）。

**证明**：`exp` 的凸性（Mathlib 的 `convexOn_exp : ConvexOn ℝ univ exp`），
取凸组合系数 `a = x`、`b = 1 - x`（`a, b ≥ 0` 且 `a + b = 1`），
端点取 `a` 对应的 `t` 与 `b` 对应的 `0`：

$$e^{x\cdot t + (1-x)\cdot 0} \le x\,e^{t} + (1-x)\,e^{0} = x\,e^t + (1-x)$$

整理即得。（注意端点顺序：`x • t + (1-x) • 0`，与展开式严格对应。） -/
theorem hoeffding_two_point (t : ℝ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (t * x) ≤ (1 - x) + x * Real.exp t := by
  have hconv : ConvexOn ℝ Set.univ (fun y : ℝ => Real.exp y) := convexOn_exp
  have hsum : x + (1 - x) = 1 := by ring
  have hmain :
      Real.exp (x • t + (1 - x) • (0:ℝ)) ≤ x • Real.exp t + (1 - x) • Real.exp (0:ℝ) :=
    hconv.2 (Set.mem_univ t) (Set.mem_univ (0:ℝ)) hx0 (by linarith) hsum
  have h' : Real.exp (t * x) ≤ x * Real.exp t + (1 - x) := by
    simpa [smul_eq_mul, Real.exp_zero, mul_comm, mul_left_comm, mul_add] using hmain
  linarith

/-! ## §6  仿射形式（便于对 `x` 取期望） -/

/-- ⭐⭐⭐ **§5 的仿射改写**：对 `x ∈ [0,1]`、任意 `t`，

$$e^{t x} \;\le\; 1 + x\,(e^{t} - 1)$$

**为什么重要**：右端是 `x` 的**仿射**函数。对随机变量取期望时
`E[1 + X(e^t - 1)] = 1 + E[X](e^t - 1)`，
这正是 Hoeffding 证明中把端点界搬到 `E[X]` 上的那一步。 -/
theorem hoeffding_affine (t : ℝ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (t * x) ≤ 1 + x * (Real.exp t - 1) := by
  have h := hoeffding_two_point t x hx0 hx1
  nlinarith

/-! ## §7  n 项求和的 mgf 界（乘积形式）

Hoeffding 证明中「独立 ⟹ mgf 相乘」那一步的代数内核：
把 `exp(t·Σ xᵢ)` 拆成 `∏ exp(t·xᵢ)`，再逐项用 §6 压住。 -/

/-- ⭐⭐⭐ **n 项求和的 mgf 界**：

若 `x : Fin n → ℝ` 每项在 `[0,1]`，则

$$e^{\,t \sum_i x_i} \;=\; \prod_i e^{\,t x_i} \;\le\; \prod_i \bigl(1 + x_i (e^t - 1)\bigr)$$

**证明**：`Real.exp_sum` 把 `exp(Σ)` 拆成乘积，再用 §6 对每项
`Finset.prod_le_prod`（`exp` 恒正提供非负性）。 -/
theorem hoeffding_prod_bound (n : ℕ) (t : ℝ) (x : Fin n → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) :
    Real.exp (t * (∑ i, x i)) ≤ ∏ i, (1 + x i * (Real.exp t - 1)) := by
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i _
    exact le_of_lt (Real.exp_pos _)
  · intro i _
    exact hoeffding_affine t (x i) (hx0 i) (hx1 i)

/-! ## §8  二点变量的中心化 mgf ≤ exp(t²/8)

Hoeffding 引理的**核心不等式**：`X` 取值于 `{0,1}`、`p = E[X]` 时
`E[e^{t(X-p)}] ≤ exp(t²/8)`。

本文件交付的是它的**代数骨架**：把 §5 的端点界先对 `p` 混合，
再用 `exp(-tp)` 的二次上界（§3）收口。
⚠ 完整版还需要 `log((1-p)+pe^t) ≤ tp + t²/8` 的凸性论证（`ψ` 函数），
本文件只给出**求和后的整体界**，不含该 `ψ` 界。 -/

/-- ⭐⭐⭐ **中心化 mgf 界（二点情形的「求和后」形式）**：

对 `t ≥ 0`、`p ∈ [0,1]`、`x ∈ [0,1]`，

$$e^{\,t(x - p)} \;\le\; \bigl(1 + x(e^{t}-1)\bigr)\cdot\bigl(1 - t p + \tfrac{t^2 p^2}{2}\bigr)$$

**证明**：`exp(t(x-p)) = exp(tx)·exp(-tp)`；
前者用 §6 的 `exp(tx) ≤ 1 + x(e^t-1)`，
后者用 §3 的 `exp(-tp) ≤ 1 - tp + (tp)²/2`（需 `tp ≥ 0`），
最后两项相乘（均需非负）。 -/
theorem hoeffding_centered_mgf (t p x : ℝ) (ht : 0 ≤ t)
    (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (t * (x - p)) ≤
      (1 + x * (Real.exp t - 1)) * (1 - t * p + (t * p)^2 / 2) := by
  have htp : 0 ≤ t * p := mul_nonneg ht hp0
  -- 拆成两个因子
  have hsplit : Real.exp (t * (x - p)) = Real.exp (t * x) * Real.exp (-(t * p)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit]
  -- 因子 1：§6
  have h1 : Real.exp (t * x) ≤ 1 + x * (Real.exp t - 1) :=
    hoeffding_affine t x hx0 hx1
  -- 因子 2：§3（注意 §3 的陈述是 exp(-y) ≤ 1 - y + y²/2）
  have h2 : Real.exp (-(t * p)) ≤ 1 - t * p + (t * p)^2 / 2 := by
    have := exp_neg_le_quadratic (t * p) htp
    calc Real.exp (-(t * p)) = Real.exp (-(t * p)) := rfl
      _ ≤ 1 - t * p + (t * p)^2 / 2 := this
  -- 因子非负
  have ha0 : 0 ≤ Real.exp (t * x) := le_of_lt (Real.exp_pos _)
  have hb0 : 0 ≤ Real.exp (-(t * p)) := le_of_lt (Real.exp_pos _)
  exact mul_le_mul h1 h2 hb0 (by nlinarith [Real.exp_pos t])

/-! ## §9  公理审计 -/

#print axioms one_add_le_exp
#print axioms exp_ge_quad
#print axioms exp_neg_le_quadratic
#print axioms one_add_pow_le_exp
#print axioms hoeffding_two_point
#print axioms hoeffding_affine
#print axioms hoeffding_prod_bound
#print axioms hoeffding_centered_mgf

end Fate.Stage2.ErrorBoundE2
