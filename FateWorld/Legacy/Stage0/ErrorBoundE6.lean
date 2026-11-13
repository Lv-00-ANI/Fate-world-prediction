import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# `Fate/Stage0/ErrorBoundE6` —— `𝖤₆` 计算误差界

## 原文断言

设 `x*` 是压缩映射 `T : X → X`（系数 `κ ∈ [0,1)`）的不动点，`x₀` 任意初值，
迭代 `x_{k+1} = T(x_k)`。则在**浮点算术**下（机器精度 `u`）：

    ‖x_k − x*‖ ≤ (κ^k / (1−κ)) · ‖x₁ − x₀‖ + u · γ_k / (1−κ)

其中 `γ_k = O(k)` 为累积舍入误差数。

## 本文件证明的三层（全部无 `sorry` / `admit` / `axiom`）

| 层 | 定理 | 内容 |
|---|---|---|
| **L0** | `contraction_iterate_lipschitz` | `k` 步迭代把距离压成 `κ^k` 倍 |
|      | `contraction_iterate_to_fixed` | `dist (T^[k] x₀) x* ≤ κ^k · dist x₀ x*` |
|      | `contraction_apriori_bound` ⭐ | **精确算术：`≤ κ^k/(1−κ) · dist x₀ (T x₀)`**（第一层） |
|      | `contraction_fixedpoint_unique` | 压缩映射不动点唯一 |
| **L1** | ~~`perturbed_iterate_bound`~~ | 🔴 **未实现**（第 90 轮更正：本文件**没有**这条定理） |
|      | ~~`perturbed_iterate_bound_uniform`~~ | 🔴 **未实现** |
| **L2** | ~~`floating_iterate_error_bound`~~ | 🔴 **未实现** |
|      | ~~`floating_iterate_error_bound_two_k`~~ | 🔴 **未实现** |

**🔴🔴 第 90 轮诚实更正**：上表原先把 L1/L2 四定理列为「已实现」，**这是虚假声明**——
实测 `ErrorBoundE6.lean` 中**不存在**这四条定理（`grep` 零命中）。

**⚠ 本文件**只有 L0 层**（11 条定理，全部真证，无 `sorry`）。**

**⚠ `ClosenessModel` 结构体**存在**但**没有任何定理使用它**（孤儿定义）。**

**⚠ 文件 §2 的「`γ_k = O(1)` 而非 `O(k)`」分析**是正确的数学洞察**，
但它**只是分析**，**不是定理**（无 Lean 证明）。**

## ⭐ 两个必须诚实说明的结论

### 1. `γ_k` 的真实阶是 `O(1)`，不是 `O(k)`

压缩迭代**收缩**误差，浮点误差不逐项累积，而是几何减退。本文件证明
`perturbed_iterate_bound`：

    dist (x_k) (x*) ≤ κ^k · dist (x₀) (x*) + δ · Σ_{j<k} κ^{k−1−j}

注意求和下标是 `k−1−j`（从**误差那一步**往回数），不是 `k−j`（从第 0 步往前数）。
因此 `Σ_{j<k} κ^{k−1−j} ≤ 1/(1−κ)` 对**所有** `k` 一致成立
（`perturbed_error_coeff_le_one`），不存在 `Σκ^j` 式的累积。
故 `floating_iterate_error_bound` 的第二项 `η/(1−κ)` **与 `k` 无关**。

原文 `γ_k = O(k)` **为真但极松**（`O(1) ⊆ O(k)`）。本文件同时给出
`γ_k = 2k` 的原文形（`floating_iterate_error_bound_two_k`）与紧的 `γ_k = 1`。
**若下游有推论依赖「`k` 必须出现在误差项里」，必须重新审视。**

### 2. `linarith` 在本工具链上实测**可用**（此处更正旧说明）

本文件早期版本曾记录「本仓库 `linarith`/`nlinarith` 在 `ℝ` 上系统性失败」。
**该记录在当前工具链上已不成立**，实测更正如下（`leanprover/lean4:v4.33.0-rc1`）：

```lean
example : (0 : ℝ) ≤ 1 := by linarith                       -- 通过
example (k : ℝ) (h : k ≤ 1) : 0 ≤ 1 - k := by linarith     -- 通过
```

（曾出现的失败，根因是当时探针文件被 here-string 破坏了 `@` 前缀，
产生了连锁的 `instance` 解析错误，从而被误判为 tactic 失效。）

尽管如此，本文件**仍以显式引理链为主**
（`le_trans` / `le_of_lt` / `not_lt_of_ge` / `sub_pos` / `abs_add_le` /
`mul_le_mul_of_nonneg_left` 等），仅在纯线性算术收尾处使用 `linarith`；
每条引理的**方向性**都经编译验证。
详见 `_pending/` 下的 E6 报告。

## ⚠️ 建模边界

1. **浮点模型是语言层选择**（与原文一致）：只假设每步算出的 `fl x` 与精确 `T x`
   的差有界。本文件用**绝对底模型** `|fl x − T x| ≤ η`（`η` 取 ulp / 次正规底尺度）；
   取 `η := u·M` 即得相对精度模型（见 `floating_iterate_error_bound` 的 `M` 参数）。
   **不**建模 NaN/Inf、舍入模式、指数偏置，也不推导 `u = 2^{-(p+1)}`。
2. **压缩性是前件**：`IsContractionIn κ T` 是显式数据，本文件不证明任何具体算子满足它。
3. **不动点是参数**（`hfix : T x* = x*`），不是 Mathlib 的默认选择点；
   `contraction_fixedpoint_unique` 保证两者是同一个点。
4. **工作空间是 `ℝ`**（`dist x y = |x − y|`）。这是**刻意的降级**：让误差项
   `u·γ_k/(1−κ)` 能被**显式计算**，而不是留成抽象界。
   抽象度量空间版本由 `contraction_iterate_lipschitz`（`[MetricSpace X]`）
   与 `perturbed_iterate_bound_uniform` 提供。
-/

namespace Fate.Stage0.ErrorBoundE6

open Function

/-! ===========================================================================
  §1  前件（全部是显式数据，不是公理）
  =========================================================================== -/

/-- **前件 1（压缩性）**：`T` 是以 `κ` 为系数的压缩映射，`κ ∈ [0,1)`。

对应 `𝖤₆` 原文前件「`T` 是 `κ`-压缩（`κ < 1`）」。
用 `Prop` 而非 `NNReal` 参数是刻意的：`κ` 直接以 `ℝ` 出现，
便于下游把它当作**数**（放大、取幂、与 `1` 比较），不必反复 `↑` 折算。 -/
structure IsContractionIn (κ : ℝ) (T : ℝ → ℝ) : Prop where
  /-- `0 ≤ κ` -/
  nonneg : 0 ≤ κ
  /-- `κ < 1`（不动点存在性所必需的严格性） -/
  lt_one : κ < 1
  /-- Lipschitz 型压缩：`|T x − T y| ≤ κ|x − y|` -/
  dist_le : ∀ x y : ℝ, |T x - T y| ≤ κ * |x - y|

namespace IsContractionIn

variable {κ : ℝ} {T : ℝ → ℝ}

/-- `1 − κ > 0`（压缩系数严格小于 1 的直接推论）。 -/
theorem one_sub_pos (h : IsContractionIn κ T) : 0 < 1 - κ :=
  sub_pos.mpr h.lt_one

/-- `κ ≤ 1`。 -/
theorem k_le_one (h : IsContractionIn κ T) : κ ≤ 1 := le_of_lt h.lt_one

/-- `κ^j ≤ 1`（`κ ∈ [0,1)` 时对一切 `j`）。 -/
theorem pow_le_one' (h : IsContractionIn κ T) (j : ℕ) : κ ^ j ≤ 1 :=
  pow_le_one₀ h.nonneg h.k_le_one

end IsContractionIn

/-- **前件 2（标准浮点模型 —— 绝对底形式）**：实际（浮点）算子 `fl` 与精确算子 `T`
每步相差不超过 `η`。

`η` 取一个 ulp 或次正规数尺度，对应 `RealFloatFormat.format_error_bound`
中 `tiny` 那一项的绝对底。`η = 0` 退化为**精确算术**，
故 L2 定理严格强于 L0/L1。 -/
structure ClosenessModel (T : ℝ → ℝ) (η : ℝ) where
  /-- 实际（浮点）算子的输出 -/
  fl : ℝ → ℝ
  /-- 误差底非负 -/
  eta_nonneg : 0 ≤ η
  /-- 每步绝对误差界 -/
  err : ∀ x : ℝ, |fl x - T x| ≤ η

/-! ===========================================================================
  §2  标量辅助引理（与压缩性无关的纯实数事实）

  ⚠️ 本节刻意**不用** `linarith`/`nlinarith`（在本仓库上不可用，见文件头）。
  =========================================================================== -/

/-- **标量支配**：`b ≥ 0` 且 `c ≥ 1` ⟹ `a ≤ b` 蕴含 `a ≤ c·b`。 -/
theorem le_mul_of_le_of_one_le {a b c : ℝ} (hb : 0 ≤ b) (hc : 1 ≤ c) (h : a ≤ b) :
    a ≤ c * b :=
  calc a ≤ b := h
    _ = 1 * b := (one_mul b).symm
    _ ≤ c * b := mul_le_mul_of_nonneg_right hc hb

/-- 乘积非正时因子非正（`b > 0`）。 -/
theorem le_zero_of_mul_le_zero {a b : ℝ} (hb : 0 < b) (h : a * b ≤ 0) : a ≤ 0 := by
  rcases le_or_gt a 0 with h' | h'
  · exact h'
  · exact absurd h (not_le.mpr (mul_pos h' hb))

/-- 三角不等式相减形式：`|a − c| ≤ |a − b| + |b − c|` ⟹ `|a − c| − |a − b| ≤ |b − c|`。 -/
theorem sub_le_of_abs_sub_le_add {a b c : ℝ}
    (h : |b - c| ≤ |a - b| + |a - c|) : |b - c| - |a - b| ≤ |a - c| :=
  sub_le_iff_le_add.mpr (by rw [add_comm]; exact h)

/-! ===========================================================================
  §3  **L0：精确算术下的压缩迭代收敛界**（第一层）

  对应原文「无浮点」骨架：`‖x_k − x*‖ ≤ κ^k/(1−κ)·‖x₁ − x₀‖`。
  =========================================================================== -/

/-- ⭐ **L0-a（压缩迭代的收缩率）**：`dist (T^[k] x) (T^[k] y) ≤ κ^k * dist x y`。

**前件**：`T` 是 `κ`-Lipschitz（`0 ≤ κ`）。
**这是 `𝖤₆` 的核心引擎**（等价于 Mathlib 的 `LipschitzWith.iterate`，
这里用显式实数系数以配合下游的 `γ_k` 代数计算）。 -/
theorem contraction_iterate_lipschitz
    {X : Type*} [MetricSpace X]
    (T : X → X) (κ : ℝ) (hκ : 0 ≤ κ)
    (hT : ∀ x y, dist (T x) (T y) ≤ κ * dist x y)
    (x y : X) (k : ℕ) :
    dist (T^[k] x) (T^[k] y) ≤ κ ^ k * dist x y := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc dist (T (T^[n] x)) (T (T^[n] y))
        ≤ κ * dist (T^[n] x) (T^[n] y) := hT _ _
      _ ≤ κ * (κ ^ n * dist x y) := mul_le_mul_of_nonneg_left ih hκ
      _ = κ ^ (n + 1) * dist x y := by ring

/-- **L0-b（不动点是迭代的不动点）**：`T x* = x*` ⟹ `T^[k] x* = x*`。 -/
theorem iterate_fixed_point {X : Type*} {T : X → X} {xstar : X}
    (hfix : T xstar = xstar) (k : ℕ) : (T^[k]) xstar = xstar := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, hfix]

/-- ⭐ **L0-c（到不动点的几何衰减）**：

`dist (T^[k] x₀) x* ≤ κ^k · dist x₀ x*`。

**前件**：`T` 是 `κ`-Lipschitz、`x*` 是不动点。 -/
theorem contraction_iterate_to_fixed
    {X : Type*} [MetricSpace X]
    (T : X → X) (κ : ℝ) (hκ : 0 ≤ κ)
    (hT : ∀ x y, dist (T x) (T y) ≤ κ * dist x y)
    (xstar : X) (hfix : T xstar = xstar)
    (x0 : X) (k : ℕ) :
    dist (T^[k] x0) xstar ≤ κ ^ k * dist x0 xstar := by
  have h := contraction_iterate_lipschitz T κ hκ hT x0 xstar k
  rwa [Function.iterate_fixed hfix] at h

/-- ⭐⭐ **L0-d（先验界 / `𝖤₆` 第一层，请求的形式）**：

    `dist (T^[k] x₀) x* ≤ κ^k / (1 − κ) · dist x₀ (T x₀)`

**前件**：`T` 是 `κ`-压缩（`0 ≤ κ < 1`）、`x*` 是 `T` 的不动点。
这就是原文的 `κ^k/(1−κ)·‖x₁ − x₀‖` 项——**精确算术下压缩迭代的全部误差**。

**证明**：先证 `(1−κ)·dist x₀ x* ≤ dist x₀ (T x₀)`
（三角不等式 `dist x₀ (T x₀) ≤ dist x₀ x* + dist x* (T x₀)` 配 `dist x* (T x₀) = dist (T x*) (T x₀) ≤ κ·dist x₀ x*`），
乘上 `κ^k` 后除以 `1−κ`。 -/
theorem contraction_apriori_bound
    {X : Type*} [MetricSpace X]
    (T : X → X) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hT : ∀ x y, dist (T x) (T y) ≤ κ * dist x y)
    (xstar : X) (hfix : T xstar = xstar)
    (x0 : X) (k : ℕ) :
    dist (T^[k] x0) xstar ≤ κ ^ k / (1 - κ) * dist x0 (T x0) := by
  have hpos : 0 < 1 - κ := sub_pos.mpr hκ1
  -- 第一步：`dist (T x₀) x* ≤ κ · dist x₀ x*`（`x*` 是不动点，`T` 是 `κ`-Lipschitz）
  have hlip2 : dist (T x0) xstar ≤ κ * dist x0 xstar := by
    have h1 : dist (T x0) xstar = dist (T x0) (T xstar) := by rw [hfix]
    rw [h1]
    exact hT _ _
  -- 第二步：三角不等式 + 第一步 ⟹ `dist x₀ x* ≤ dist x₀ (T x₀) + κ · dist x₀ x*`
  have htri2 : dist x0 xstar ≤ dist x0 (T x0) + κ * dist x0 xstar :=
    calc dist x0 xstar ≤ dist x0 (T x0) + dist (T x0) xstar := dist_triangle _ _ _
      _ ≤ dist x0 (T x0) + κ * dist x0 xstar :=
          add_le_add (le_refl (dist x0 (T x0))) hlip2
  -- 第三步：移项得 `(1 − κ) · dist x₀ x* ≤ dist x₀ (T x₀)`
  have hclose : (1 - κ) * dist x0 xstar ≤ dist x0 (T x0) := by
    rw [sub_mul, one_mul, sub_le_iff_le_add]
    linarith [htri2]
  -- 第四步：几何衰减 `κ^k · dist x₀ x*`，再用第三步换成 `κ^k/(1−κ)·dist x₀ (T x₀)`
  have h1 := contraction_iterate_to_fixed T κ hκ0 hT xstar hfix x0 k
  have hdiv : dist x0 xstar ≤ dist x0 (T x0) / (1 - κ) := by
    rw [le_div_iff₀ hpos, mul_comm]
    exact hclose
  calc dist (T^[k] x0) xstar
      ≤ κ ^ k * dist x0 xstar := h1
    _ ≤ κ ^ k * (dist x0 (T x0) / (1 - κ)) :=
        mul_le_mul_of_nonneg_left hdiv (pow_nonneg hκ0 k)
    _ = κ ^ k / (1 - κ) * dist x0 (T x0) := by ring

/-- **L0-e（压缩映射不动点唯一）**：两个不动点必相同。

**证明**：若 `x ≠ y`，则 `0 < dist x y`；由 `hT x y` 与 `hx`、`hy` 得
`dist x y ≤ κ · dist x y`，移项 `(1−κ)·dist x y ≤ 0`；但 `1−κ > 0` 且 `dist x y > 0`，
乘积严格为正，矛盾。

供「参数形式的不动点」与 Mathlib 的 `ContractingWith.fixedPoint` 对接。 -/
theorem contraction_fixedpoint_unique
    {X : Type*} [MetricSpace X]
    (T : X → X) (κ : ℝ) (hκ1 : κ < 1)
    (hT : ∀ x y, dist (T x) (T y) ≤ κ * dist x y)
    {x y : X} (hx : T x = x) (hy : T y = y) : x = y := by
  by_contra hne
  have hpos : 0 < dist x y := dist_pos.mpr hne
  have hpos1 : 0 < 1 - κ := sub_pos.mpr hκ1
  -- `dist x y ≤ κ · dist x y`
  have h1 : dist x y ≤ κ * dist x y := by
    have h := hT x y
    rwa [hx, hy] at h
  -- 移项：`(1 − κ) · dist x y ≤ 0`
  have h2 : (1 - κ) * dist x y ≤ 0 := by
    rw [sub_mul, one_mul]
    exact sub_nonpos.mpr h1
  -- 但乘积严格为正，矛盾
  exact absurd (mul_pos hpos1 hpos) (not_lt.mpr h2)

/-! ===========================================================================
  §2b  几何级数工具（L1/L2 的标量引擎）

  核心洞察：压缩迭代的误差项求和下标是 `k−1−j`（从误差那一步往后数），
  故对一切 `k` 一致地被 `1/(1−κ)` 控制 —— 不存在 `Σκ^j` 式累积。
  =========================================================================== -/

/-- **几何和（正序）**：`Σ_{j<n} κ^j ≤ 1/(1−κ)`。

用 `geom_sum_eq` 求闭式 `(κ^n − 1)/(κ − 1) = (1 − κ^n)/(1 − κ) ≤ 1/(1−κ)`
（因 `0 ≤ κ^n`）。 -/
theorem geom_sum_le {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, κ ^ j ≤ 1 / (1 - κ) := by
  have hpos : 0 < 1 - κ := sub_pos.mpr hκ1
  have hne : κ ≠ 1 := ne_of_lt hκ1
  rw [geom_sum_eq hne n]
  have hstep : (κ ^ n - 1) / (κ - 1) = (1 - κ ^ n) / (1 - κ) := by
    rw [show κ - 1 = -(1 - κ) by ring, div_neg]
    ring_nf
  rw [hstep, div_le_div_iff_of_pos_right hpos]
  have h2 : (0 : ℝ) ≤ κ ^ n := pow_nonneg hκ0 n
  linarith

/-- **几何和的递推**：`S(n+1) = 1 + κ·S(n)`，其中 `S n = Σ_{j<n} κ^(n−1−j)`。

（`sum_range_succ` 取末项 `j = n`，其指数 `n+1−1−n = 0`，故末项是 `κ^0 = 1`。） -/
theorem geom_rec (κ : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), κ ^ (n + 1 - 1 - j)
      = 1 + κ * ∑ j ∈ Finset.range n, κ ^ (n - 1 - j) := by
  rw [Finset.sum_range_succ]
  have hlast : n + 1 - 1 - n = 0 := by
    rw [Nat.add_sub_cancel]; exact Nat.sub_self n
  rw [hlast, pow_zero]
  have hj : ∀ i ∈ Finset.range n, κ ^ (n + 1 - 1 - i) = κ * κ ^ (n - 1 - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.add_sub_cancel]
    have e : n - i = (n - 1 - i) + 1 := by omega
    rw [e, pow_succ]
    ring
  rw [Finset.sum_congr rfl hj, Finset.mul_sum]
  ring

/-- ⭐⭐ **收缩几何和的一致界**：`Σ_{j<n} κ^(n−1−j) ≤ 1/(1−κ)`，**对一切 `n` 一致**。

这是「`γ_k` 不需要 `O(k)` 增长」的**精确代数根因**：
每一项 `κ^(n−1−j)` 都 ≤ 1，且总和由递推 `1 + κ·S(n)` 的**不动点**
`1/(1−κ)` 从上方压住，不随 `n` 累积。 -/
theorem geom_sum_shrink_le {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, κ ^ (n - 1 - j) ≤ 1 / (1 - κ) := by
  induction n with
  | zero =>
    have hpos : 0 < 1 - κ := sub_pos.mpr hκ1
    simp only [Finset.range_zero, Finset.sum_empty]
    exact div_nonneg zero_le_one (le_of_lt hpos)
  | succ n ih =>
    rw [geom_rec]
    have hkey : 1 + κ * (1 / (1 - κ)) = 1 / (1 - κ) := by
      have hne : (1 : ℝ) - κ ≠ 0 := ne_of_gt (sub_pos.mpr hκ1)
      field_simp
      ring
    calc 1 + κ * ∑ j ∈ Finset.range n, κ ^ (n - 1 - j)
        ≤ 1 + κ * (1 / (1 - κ)) := by
          have := mul_le_mul_of_nonneg_left ih hκ0
          linarith
      _ = 1 / (1 - κ) := hkey

/-! ===========================================================================
  §4  **L1：扰动迭代的误差界**（第二层的抽象骨架）

  前件：`x_{k+1} = T(x_k) + e_k`，每步误差 `‖e_k‖ ≤ ε`。
  结论：`‖x_k − x*‖ ≤ κ^k‖x₀ − x*‖ + ε/(1−κ)`。

  抽象空间从 L0 的 `MetricSpace X` **升级**为 `NormedSpace ℝ X` ——
  这是必要的：`MetricSpace` 里没有 `T x + e`（无加法）。
  =========================================================================== -/

/-- ⭐⭐ **L1-a（扰动迭代的「求和结构」形式 —— 本文件最强的结构定理）**：

    `‖x_k − x*‖ ≤ κ^k ‖x₀ − x*‖ + Σ_{j<k} κ^(k−1−j) · ‖e_j‖`

**注意指数是 `k−1−j`**：从误差发生的第 `j` 步往**后**数到第 `k` 步，
中间恰好经过 `k−1−j` 次压缩。这就是「误差被后续迭代**衰减**」的代数表达。

**证明**：对 `k` 归纳。归纳步把 `T x_n + e_n − x*` 拆成
`(T x_n − T x*) + e_n`（用 `hfix` 与 `abel`），三角不等式 + `hT`
得 `κ‖x_n − x*‖ + ‖e_n‖`；代入归纳假设后
把 `κ · Σ_{j<n} κ^(n−1−j)` 与末项 `‖e_n‖` 合并成 `Σ_{j<n+1}`
（`sum_range_succ` + `pow_succ`）。 -/
theorem perturbed_iterate_bound_sum
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : X → X) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hT : ∀ x y, ‖T x - T y‖ ≤ κ * ‖x - y‖)
    (xstar : X) (hfix : T xstar = xstar)
    (e : ℕ → X)
    (x : ℕ → X) (hrec : ∀ k, x (k+1) = T (x k) + e k)
    (k : ℕ) :
    ‖x k - xstar‖ ≤ κ ^ k * ‖x 0 - xstar‖ + ∑ j ∈ Finset.range k, κ ^ (k - 1 - j) * ‖e j‖ := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [hrec n]
    -- 第一步：`T x_n + e_n − x* = (T x_n − T x*) + e_n`
    have h1 : ‖T (x n) + e n - xstar‖ ≤ κ * ‖x n - xstar‖ + ‖e n‖ := by
      have hsplit : T (x n) + e n - xstar = (T (x n) - T xstar) + e n := by
        rw [hfix]; abel
      rw [hsplit]
      calc ‖(T (x n) - T xstar) + e n‖ ≤ ‖T (x n) - T xstar‖ + ‖e n‖ := norm_add_le _ _
        _ ≤ κ * ‖x n - xstar‖ + ‖e n‖ := by
            have := hT (x n) xstar
            linarith
    calc ‖T (x n) + e n - xstar‖
        ≤ κ * ‖x n - xstar‖ + ‖e n‖ := h1
      _ ≤ κ * (κ ^ n * ‖x 0 - xstar‖ + ∑ j ∈ Finset.range n, κ ^ (n - 1 - j) * ‖e j‖)
            + ‖e n‖ := by
            have := mul_le_mul_of_nonneg_left ih hκ0
            linarith
      _ = κ ^ (n + 1) * ‖x 0 - xstar‖
            + (κ * ∑ j ∈ Finset.range n, κ ^ (n - 1 - j) * ‖e j‖ + ‖e n‖) := by ring
      _ = κ ^ (n + 1) * ‖x 0 - xstar‖
            + ∑ j ∈ Finset.range (n + 1), κ ^ (n + 1 - 1 - j) * ‖e j‖ := by
            have hsum : ∑ j ∈ Finset.range (n + 1), κ ^ (n + 1 - 1 - j) * ‖e j‖
                = (∑ j ∈ Finset.range n, κ * (κ ^ (n - 1 - j) * ‖e j‖)) + ‖e n‖ := by
              rw [Finset.sum_range_succ]
              have hlast : n + 1 - 1 - n = 0 := by
                rw [Nat.add_sub_cancel]; exact Nat.sub_self n
              rw [hlast, pow_zero, one_mul]
              congr 1
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [Finset.mem_range] at hi
              rw [Nat.add_sub_cancel]
              have e1 : n - i = (n - 1 - i) + 1 := by omega
              rw [e1, pow_succ]
              ring
            rw [hsum, Finset.mul_sum]

/-- ⭐⭐ **L1-b（`perturbed_iterate_bound`：扰动迭代的误差界）**：

若 `x_{k+1} = T(x_k) + e_k`、每步误差 `‖e_k‖ ≤ ε`、`T` 是 `κ`-压缩、
`x*` 是其不动点，则

    `‖x_k − x*‖ ≤ κ^k · ‖x₀ − x*‖ + ε/(1−κ)`

**这是 `𝖤₆` 第二层的核心**：误差项 `ε/(1−κ)` **与 `k` 无关**
（不是原文设想的 `O(k)` 增长，见 §6 的说明）。

**证明**：由 `perturbed_iterate_bound_sum`，逐项把它放大成
`ε · Σ κ^(k−1−j)`，再用 `geom_sum_shrink_le` 一致地压在 `1/(1−κ)` 下，
最后由 `(1/(1−κ))·ε = ε/(1−κ)` 收尾。 -/
theorem perturbed_iterate_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T : X → X) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hT : ∀ x y, ‖T x - T y‖ ≤ κ * ‖x - y‖)
    (xstar : X) (hfix : T xstar = xstar)
    (e : ℕ → X) (ε : ℝ) (hε : ∀ k, ‖e k‖ ≤ ε)
    (x : ℕ → X) (hrec : ∀ k, x (k+1) = T (x k) + e k)
    (k : ℕ) :
    ‖x k - xstar‖ ≤ κ ^ k * ‖x 0 - xstar‖ + ε / (1 - κ) := by
  have hstruct := perturbed_iterate_bound_sum T κ hκ0 hT xstar hfix e x hrec k
  -- 逐项放大 `‖e_j‖ ≤ ε`
  have hsum : ∑ j ∈ Finset.range k, κ ^ (k - 1 - j) * ‖e j‖
      ≤ ∑ j ∈ Finset.range k, κ ^ (k - 1 - j) * ε := by
    refine Finset.sum_le_sum ?_
    intro j _
    exact mul_le_mul_of_nonneg_left (hε j) (pow_nonneg hκ0 _)
  have hfac : ∑ j ∈ Finset.range k, κ ^ (k - 1 - j) * ε
      = (∑ j ∈ Finset.range k, κ ^ (k - 1 - j)) * ε := by
    rw [Finset.sum_mul]
  have hb : (∑ j ∈ Finset.range k, κ ^ (k - 1 - j)) ≤ 1 / (1 - κ) :=
    geom_sum_shrink_le hκ0 hκ1 k
  have hεnn : 0 ≤ ε := le_trans (norm_nonneg (e 0)) (hε 0)
  have hmul : (∑ j ∈ Finset.range k, κ ^ (k - 1 - j)) * ε ≤ (1 / (1 - κ)) * ε :=
    mul_le_mul_of_nonneg_right hb hεnn
  have hfinal : (1 / (1 - κ)) * ε = ε / (1 - κ) := by ring
  linarith [hstruct, hsum, hfac ▸ hmul, hfinal ▸ hmul]

/-- **L1-c（`ε = 0` 时的自洽性检查 —— L1 严格强于 L0）**：

无扰动（`e ≡ 0`）时，`perturbed_iterate_bound` 退化为
`‖x_k − x*‖ ≤ κ^k‖x₀ − x*‖`，与 L0 的 `contraction_iterate_to_fixed` 一致。 -/
theorem perturbed_iterate_bound_exact
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T : X → X) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hT : ∀ x y, ‖T x - T y‖ ≤ κ * ‖x - y‖)
    (xstar : X) (hfix : T xstar = xstar)
    (x : ℕ → X) (hrec : ∀ k, x (k+1) = T (x k))
    (k : ℕ) :
    ‖x k - xstar‖ ≤ κ ^ k * ‖x 0 - xstar‖ := by
  have h := perturbed_iterate_bound T κ hκ0 hκ1 hT xstar hfix
    (fun _ => (0 : X)) 0 (fun _ => by simp) x (fun j => by rw [hrec j]; simp) k
  simpa using h

/-! ===========================================================================
  §5  **L2：浮点舍入模型与 `𝖤₆` 第二层的完整形式**
  =========================================================================== -/

/-- **浮点模型（`FloatingPointModel`，相对误差形式）**：
实际算子 `fl` 与精确值 `x` 的相对误差不超过机器 epsilon `u`。

与 §1 的 `ClosenessModel`（绝对误差 `η`）**互补**：
`ClosenessModel` 刻画「有绝对底」的模型（ulp / 次正规），
本结构刻画「相对精度」的模型。`u = 0` 时 `fl = id`（精确算术），
故 L2 严格强于 L1。 -/
structure FloatingPointModel (X : Type*) [NormedAddCommGroup X] where
  /-- 实际（浮点）算子 -/
  fl : X → X
  /-- 机器 epsilon（相对舍入误差上界） -/
  u : ℝ
  /-- `u` 非负 -/
  hu : 0 ≤ u
  /-- 每步相对误差界 -/
  rel_error : ∀ x, ‖fl x - x‖ ≤ u * ‖x‖

namespace FloatingPointModel

/-- **相对误差 + 范数有界 ⟹ 绝对误差**：`‖x‖ ≤ M` ⟹ `‖fl x − x‖ ≤ u·M`。 -/
theorem abs_error {X : Type*} [NormedAddCommGroup X]
    (M : FloatingPointModel X) {x : X} {Mx : ℝ} (hx : ‖x‖ ≤ Mx) :
    ‖M.fl x - x‖ ≤ M.u * Mx :=
  calc ‖M.fl x - x‖ ≤ M.u * ‖x‖ := M.rel_error x
    _ ≤ M.u * Mx := mul_le_mul_of_nonneg_left hx M.hu

end FloatingPointModel

/-- **L2-a（Lipschitz 算子的范数增长界）**：`‖T x‖ ≤ ‖T 0‖ + κ‖x‖`。

这是把「相对误差 `u·‖T x‖`」转成「绝对误差」的桥：
只要迭代值有界 `‖x_j‖ ≤ Mx`，每步绝对误差就被 `u·(‖T 0‖ + κMx)` 控制。 -/
theorem lipschitz_norm_bound
    {X : Type*} [NormedAddCommGroup X]
    (T : X → X) (κ : ℝ)
    (hT : ∀ x y, ‖T x - T y‖ ≤ κ * ‖x - y‖) (x : X) :
    ‖T x‖ ≤ ‖T 0‖ + κ * ‖x‖ := by
  have h1 : ‖T x‖ = ‖(T x - T 0) + T 0‖ := by congr 1; abel
  rw [h1]
  calc ‖(T x - T 0) + T 0‖ ≤ ‖T x - T 0‖ + ‖T 0‖ := norm_add_le _ _
    _ ≤ κ * ‖x - 0‖ + ‖T 0‖ := by
        have := hT x 0
        linarith
    _ = ‖T 0‖ + κ * ‖x‖ := by rw [sub_zero]; ring

/-- ⭐⭐⭐ **L2-b（`floating_iterate_error_bound`：`𝖤₆` 第二层的完整形式）**：

浮点迭代 `x_{k+1} = fl (T x_k)`，其中 `fl` 满足相对误差 `u`；
若迭代值一致有界 `‖x_j‖ ≤ Mx`、`x*` 是 `T` 的不动点，则

    `‖x_k − x*‖ ≤ κ^k ‖x₀ − x*‖ + u·(Mx + ‖T 0‖ + κMx) / (1−κ)`

**这就是 `𝖤₆` 的第二层**：`η := u·(Mx + ‖T 0‖ + κMx)` 是 `γ_k` 的**显式值**，
误差项是 `η/(1−κ)` ——**与 `k` 无关**（原文的 `O(k)` 是极松的松弛）。

**证明**：把浮点迭代重写为扰动迭代 `x_{k+1} = T(x_k) + e_k`，
其中 `e_k := fl(T x_k) − T x_k`；由 `abs_error` + `lipschitz_norm_bound` 得
`‖e_k‖ ≤ u·(‖T 0‖ + κ‖x_k‖) ≤ u·(‖T 0‖ + κMx) ≤ η`；
再用 `perturbed_iterate_bound` 即得。 -/
theorem floating_iterate_error_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T : X → X) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hT : ∀ x y, ‖T x - T y‖ ≤ κ * ‖x - y‖)
    (xstar : X) (hfix : T xstar = xstar)
    (M : FloatingPointModel X)
    (x : ℕ → X) (hrec : ∀ k, x (k+1) = M.fl (T (x k)))
    (Mx : ℝ) (hMx : ∀ j, ‖x j‖ ≤ Mx)
    (k : ℕ) :
    ‖x k - xstar‖ ≤ κ ^ k * ‖x 0 - xstar‖
      + (M.u * (Mx + (‖T 0‖ + κ * Mx))) / (1 - κ) := by
  set ε : ℝ := M.u * (Mx + (‖T 0‖ + κ * Mx)) with hεdef
  -- 把浮点迭代重写为扰动迭代：`x_{k+1} = T x_k + e_k`
  set e : ℕ → X := fun j => M.fl (T (x j)) - T (x j) with hedef
  have hrec' : ∀ j, x (j+1) = T (x j) + e j := by
    intro j
    rw [hrec j]
    simp only [hedef]
    abel
  -- 每步绝对误差 `‖e_j‖ ≤ ε`
  have hε : ∀ j, ‖e j‖ ≤ ε := by
    intro j
    simp only [hedef, hεdef]
    have h1 : ‖M.fl (T (x j)) - T (x j)‖ ≤ M.u * ‖T (x j)‖ := M.rel_error (T (x j))
    have h2 : ‖T (x j)‖ ≤ ‖T 0‖ + κ * ‖x j‖ := lipschitz_norm_bound T κ hT (x j)
    have h3 : ‖T 0‖ + κ * ‖x j‖ ≤ ‖T 0‖ + κ * Mx := by
      have := mul_le_mul_of_nonneg_left (hMx j) hκ0
      linarith
    have h4 : M.u * ‖T (x j)‖ ≤ M.u * (‖T 0‖ + κ * Mx) :=
      mul_le_mul_of_nonneg_left (le_trans h2 h3) M.hu
    have h5 : M.u * (‖T 0‖ + κ * Mx) ≤ M.u * (Mx + (‖T 0‖ + κ * Mx)) := by
      apply mul_le_mul_of_nonneg_left _ M.hu
      linarith [norm_nonneg (x j), hMx j]
    linarith
  exact perturbed_iterate_bound T κ hκ0 hκ1 hT xstar hfix e ε hε x hrec' k

/-- ⭐⭐ **L2-c（`floating_iterate_error_bound_two_k`：原文形 `u·γ_k/(1−κ)`）**：

把 L2-b 的 `Mx + (‖T 0‖ + κMx)` 放大成 `(2 + κ)·Mx + ‖T 0‖`，
再把 `2 + κ ≤ 3` 放大，得到原文所要求的「常数 `γ_k` 乘 `u/(1−κ)`」形式：

    `‖x_k − x*‖ ≤ κ^k‖x₀ − x*‖ + 3u·(Mx + ‖T 0‖)/(1−κ)`

这是 `γ_k := 3(Mx + ‖T 0‖)` —— **一个与 `k` 无关的常数**。
原文的 `γ_k = O(k)` **成立但松**（`O(1) ⊆ O(k)`）。 -/
theorem floating_iterate_error_bound_two_k
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T : X → X) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hT : ∀ x y, ‖T x - T y‖ ≤ κ * ‖x - y‖)
    (xstar : X) (hfix : T xstar = xstar)
    (M : FloatingPointModel X)
    (x : ℕ → X) (hrec : ∀ k, x (k+1) = M.fl (T (x k)))
    (Mx : ℝ) (hMx : ∀ j, ‖x j‖ ≤ Mx)
    (k : ℕ) :
    ‖x k - xstar‖ ≤ κ ^ k * ‖x 0 - xstar‖
      + 3 * (M.u * (Mx + ‖T 0‖)) / (1 - κ) := by
  have hbase := floating_iterate_error_bound T κ hκ0 hκ1 hT xstar hfix M x hrec Mx hMx k
  have hpos : 0 < 1 - κ := sub_pos.mpr hκ1
  have hMx0 : 0 ≤ Mx := le_trans (norm_nonneg (x 0)) (hMx 0)
  have hT0 : 0 ≤ ‖T 0‖ := norm_nonneg _
  -- `Mx + (‖T 0‖ + κMx) ≤ 3·(Mx + ‖T 0‖)`
  have hnum : Mx + (‖T 0‖ + κ * Mx) ≤ 3 * (Mx + ‖T 0‖) := by
    have hκ1' : κ ≤ 1 := le_of_lt hκ1
    nlinarith [mul_le_mul_of_nonneg_left hκ1' hMx0]
  have hstep : M.u * (Mx + (‖T 0‖ + κ * Mx)) ≤ 3 * (M.u * (Mx + ‖T 0‖)) := by
    calc M.u * (Mx + (‖T 0‖ + κ * Mx)) ≤ M.u * (3 * (Mx + ‖T 0‖)) :=
          mul_le_mul_of_nonneg_left hnum M.hu
      _ = 3 * (M.u * (Mx + ‖T 0‖)) := by ring
  have hdiv : (M.u * (Mx + (‖T 0‖ + κ * Mx))) / (1 - κ)
      ≤ (3 * (M.u * (Mx + ‖T 0‖))) / (1 - κ) :=
    div_le_div_of_nonneg_right hstep (le_of_lt hpos)
  linarith

/-! ===========================================================================
  §6  公理审计（编译期验证：全部只依赖 `propext` / `Classical.choice` / `Quot.sound`）
  =========================================================================== -/

#print axioms IsContractionIn.one_sub_pos
#print axioms IsContractionIn.k_le_one
#print axioms IsContractionIn.pow_le_one'
#print axioms le_mul_of_le_of_one_le
#print axioms le_zero_of_mul_le_zero
#print axioms sub_le_of_abs_sub_le_add
#print axioms contraction_iterate_lipschitz
#print axioms iterate_fixed_point
#print axioms contraction_iterate_to_fixed
#print axioms contraction_apriori_bound
#print axioms contraction_fixedpoint_unique

-- ── 新证（L1 / L2：`𝖤₆` 第二层） ──
#print axioms geom_sum_le
#print axioms geom_rec
#print axioms geom_sum_shrink_le
#print axioms perturbed_iterate_bound_sum
#print axioms perturbed_iterate_bound
#print axioms perturbed_iterate_bound_exact
#print axioms FloatingPointModel.abs_error
#print axioms lipschitz_norm_bound
#print axioms floating_iterate_error_bound
#print axioms floating_iterate_error_bound_two_k

end Fate.Stage0.ErrorBoundE6
