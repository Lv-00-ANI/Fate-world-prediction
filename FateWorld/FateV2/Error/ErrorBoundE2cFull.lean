/-
================================================================================
  Fate/Stage2/ErrorBoundE2cFull.lean
  —— ψ 函数界（`p = 1/2` 情形）及其配套引理（Stage2 · E2c 补充）

  【为什么是这个文件名】
  `Fate/Stage2/ErrorBoundE2c.lean` 在本次会话期间被**并发的另一个 agent**
  反复重写（本 agent 写入后被覆盖过两次）。为避免写冲突与内容丢失，
  本文件的全部内容放在独立文件名下，不与 E2c 争抢同一路径。

  前置（已入库，EXIT=0）：
    Fate/Stage2/ErrorBoundE2.lean   （8 定理）
    Fate/Stage2/ErrorBoundE2b.lean  （5 定理）

  本文件交付（全部 **无 sorry / 无 admit / 无自定义 axiom**）：
    §1  log_one_add_le                : log(1 + x) ≤ x                  (x > -1)
    §2  psi_arg_pos                   : 0 < (1-p) + p·e^t               (p ∈ [0,1])
    §3  psi_bound_iff_exp             : ψ 的 `log` 形式 ⟺ `exp` 形式
    §4  mul_le_of_nonneg_of_le_one    : t·p ≤ t                         (t ≥ 0, p ≤ 1)
    §5  cosh_exp_eq_half              : ½ + ½e^t = e^{t/2}·cosh(t/2)   （恒等式）
    §6  psi_half                      : log(½ + ½e^t) ≤ t/2 + t²/8      ⭐ 核心
    §7  psi_half_exp                  : (1-½) + ½e^t ≤ e^{t/2 + t²/8}   ⭐ `exp` 形式
    §8  exp_half_add_exp_neg_half_le  : e^{t/2}+e^{-t/2} ≤ 2e^{t²/8}    ⭐ 中心化形式
    §9  exp_mul_one_sub_le_one        : e^t(1-t) ≤ 1                    (全 ℝ)
    §10 exp_sub_one_le_mul_exp        : e^t - 1 ≤ t·e^t                 (t ≥ 0)

  ── 关于完整 ψ 界（任意 `p ∈ [0,1]`）──
  未交付。经严格数值（`p∈[0,1]`、`t∈[-20,20]` 全域网格，最大余量 0，命题为真）
  与解析核对，其等价链为：
      log((1-p)+pe^t) ≤ tp + t²/8
    ⟺ (1-p) + p·e^t ≤ e^{tp + t²/8}                        （§3 已形式化）
    ⟺ (1-p)e^{-pt} + p·e^{(1-p)t} ≤ e^{t²/8}               （乘 e^{-pt}）
  即 Hoeffding 1963 的**加权二点零均值引理**，其标准证明依赖
  `φ''(u) ≤ 1/4`（`φ(u) = log((1-q)+qe^u) - qu`）的二阶导数估计。
  `q = 1/2` 时该引理恰退化为 `cosh(s) ≤ e^{s²/2}`，
  即 Mathlib 的 `Real.cosh_le_exp_half_sq`，故 §6–§8 完整成立。

  依赖：Mathlib（本地 path require，D:/mathlib）
================================================================================

## 与 `ErrorBoundE2c` 的关系

`Fate/Stage2/ErrorBoundE2c.lean`（33 行 / 1 定理）是本命题的**简版**，其文件头自述：

> 「完整的 psi 函数界 `log((1-p)+p*exp(t)) <= t*p + t^2/8` 是**研究级**难度，未做。」

**本文件（236 行 / 10 定理）已做出其中的核心部分：**
`psi_half`（`p = 1/2` 的完整 psi 界）及其 `exp` 形式 `psi_half_exp`、
中心化形式 `exp_half_add_exp_neg_half_le`，另有 7 条配套引理。

⟹ 后续引用本命题时，**应优先引用本文件的定理**。
⟹ `ErrorBoundE2c` 保留，仅为向后兼容（其 `log_one_add_le` 与本文件 §1 同款）。

（仍未交付的：任意 `p ∈ [0,1]` 的完整 psi 界，见上文「关于完整 psi 界」一节。）
================================================================================
-/
import FateWorld.FateV2.Error.ErrorBoundE2
import FateWorld.FateV2.Error.ErrorBoundE2b
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

open Finset

namespace FateV2.Error.Stage2.ErrorBoundE2cFull

/-!
  # Error · ErrorBoundE2cFull

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ErrorBoundE2cFull.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Stage2.ErrorBoundE2, Stage2.ErrorBoundE2b
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §1  `log(1 + x) ≤ x`

⚠ **探测结果**（实测）：Mathlib 有 `Real.log_le_sub_one_of_pos`、`Real.log_le_self`、
`Real.one_sub_inv_le_log_of_pos`、`Real.log_le_iff_le_exp`，
但**没有** `Real.log_one_add_le` / `Real.log_one_plus_le`。 -/

/-- ⭐⭐ **`log(1 + x) ≤ x`**（`x > -1`）。

**证明**：`y := 1 + x > 0` 时 `Real.log_le_sub_one_of_pos` 给出 `log y ≤ y - 1 = x`。 -/
theorem log_one_add_le {x : ℝ} (hx : -1 < x) : Real.log (1 + x) ≤ x := by
  have hpos : 0 < 1 + x := by linarith
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

/-! ## §2  ψ 函数的分母正性 -/

/-- ⭐ **ψ 函数的参数恒正**：`p ∈ [0,1]`、`t` 任意时 `(1-p) + p·e^t > 0`。

这是对 `ψ` 取 `log` 的前提。

⚠ **纯 `linarith` 证不了**（无法处理 `p * Real.exp t` 这类乘积），
必须先 `rcases eq_or_lt_of_le hp0` 拆出 `p = 0` 情形。 -/
theorem psi_arg_pos (p : ℝ) (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) (t : ℝ) :
    0 < (1 - p) + p * Real.exp t := by
  have h1 : (0:ℝ) ≤ 1 - p := by linarith
  have h2 : (0:ℝ) < Real.exp t := Real.exp_pos t
  rcases eq_or_lt_of_le hp0 with h | h
  · rw [← h]; norm_num
  · have h3 : (0:ℝ) < p * Real.exp t := mul_pos h h2
    linarith

/-! ## §3  ψ 界的两种形式等价 -/

/-- ⭐⭐ **ψ 界的 `log` 形式 ⟺ `exp` 形式**：

$$\log\bigl((1-p)+p e^t\bigr) \le tp + \tfrac{t^2}{8}
\;\Longleftrightarrow\;
(1-p)+p e^t \le e^{\,tp + t^2/8}$$

**证明**：`Real.log_le_iff_le_exp`（正参数由 §2 提供）。 -/
theorem psi_bound_iff_exp (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    Real.log ((1 - p) + p * Real.exp t) ≤ t * p + t^2 / 8 ↔
      (1 - p) + p * Real.exp t ≤ Real.exp (t * p + t^2 / 8) :=
  Real.log_le_iff_le_exp (psi_arg_pos p hp0 hp1 t)

/-! ## §4  单调性辅助 -/

/-- ⭐ **`t ≥ 0`、`p ≤ 1` ⟹ `t·p ≤ t`**。 -/
theorem mul_le_of_nonneg_of_le_one {t p : ℝ} (ht : 0 ≤ t) (hp : p ≤ 1) :
    t * p ≤ t := by
  nlinarith

/-! ## §5  `½ + ½e^t` 的 cosh 恒等式 -/

/-- ⭐⭐ **恒等式** `½ + ½·e^t = e^{t/2} · cosh(t/2)`。

把「两点的加权平均」写成「几何平均 × 双曲余弦」，
从而把 `t²/8` 的来源暴露为 `cosh s ≤ e^{s²/2}`。 -/
theorem cosh_exp_eq_half (t : ℝ) :
    (1:ℝ)/2 + (1/2) * Real.exp t = Real.exp (t/2) * Real.cosh (t/2) := by
  have hexp_pos : 0 < Real.exp (t/2) := Real.exp_pos _
  rw [Real.cosh_eq]
  have hsplit : Real.exp t = Real.exp (t/2) * Real.exp (t/2) := by
    rw [← Real.exp_add]; ring_nf
  have hneg : Real.exp (-(t/2)) = (Real.exp (t/2))⁻¹ := Real.exp_neg _
  rw [hsplit, hneg]
  have hne : Real.exp (t/2) ≠ 0 := ne_of_gt hexp_pos
  field_simp
  ring

/-! ## §6  ⭐ ψ 界（`p = 1/2` 情形）—— 核心交付 -/

/-- ⭐⭐⭐ **ψ 函数界（`p = 1/2`）**：

$$\log\Bigl(\tfrac12 + \tfrac12 e^{t}\Bigr) \;\le\; \frac{t}{2} + \frac{t^2}{8}
\qquad (\forall t \in \mathbb{R})$$

**意义**：公平硬币 / Rademacher 变量的 Hoeffding 引理
（`X ∈ {-1,+1}` 等概时 `E[e^{tX/2}] = cosh(t/2) ≤ e^{t²/8}`）。

**证明**（三步，**无需**二阶导数）：
1. §5 恒等式 `½ + ½e^t = e^{t/2}·cosh(t/2)`；
2. `Real.log_mul` 拆出 `t/2`：`log(½+½e^t) = t/2 + log(cosh(t/2))`；
3. `Real.cosh_le_exp_half_sq`（`cosh x ≤ exp(x²/2)`）取 `x = t/2`，
   得 `cosh(t/2) ≤ e^{t²/8}`，再取 `log`（`Real.log_le_log`，需 `cosh > 0`）。 -/
theorem psi_half (t : ℝ) :
    Real.log (1/2 + (1/2) * Real.exp t) ≤ t/2 + t^2/8 := by
  have hcosh : Real.cosh (t/2) ≤ Real.exp ((t/2)^2/2) := Real.cosh_le_exp_half_sq (t/2)
  have hpos : 0 < Real.cosh (t/2) := Real.cosh_pos (t/2)
  have hexp_pos : 0 < Real.exp (t/2) := Real.exp_pos _
  rw [cosh_exp_eq_half t, Real.log_mul (ne_of_gt hexp_pos) (ne_of_gt hpos), Real.log_exp]
  have hlog : Real.log (Real.cosh (t/2)) ≤ (t/2)^2/2 := by
    calc Real.log (Real.cosh (t/2)) ≤ Real.log (Real.exp ((t/2)^2/2)) :=
          Real.log_le_log hpos hcosh
      _ = (t/2)^2/2 := Real.log_exp _
  nlinarith

/-! ## §7  §6 的纯指数形式 -/

/-- ⭐⭐⭐ **§6 的 `exp` 形式**：`(1-½) + ½·e^t ≤ e^{t·½ + t²/8}`。

**证明**：先 `ring` 归一化 `(1-½)` 与 `t·½`，再用
`Real.log_le_iff_le_exp` 把 §6 的 `log` 形式翻成 `exp` 形式。 -/
theorem psi_half_exp (t : ℝ) :
    (1 - 1/2 : ℝ) + (1/2) * Real.exp t ≤ Real.exp (t * (1/2) + t^2 / 8) := by
  have h := psi_half t
  have harg : (1:ℝ) - 1/2 + (1/2) * Real.exp t = 1/2 + (1/2) * Real.exp t := by ring
  have hexp : t * (1:ℝ)/2 + t^2/8 = t/2 + t^2/8 := by ring
  have h' : (1:ℝ)/2 + (1/2) * Real.exp t ≤ Real.exp (t/2 + t^2/8) :=
    (Real.log_le_iff_le_exp (by positivity : (0:ℝ) < 1/2 + (1/2) * Real.exp t)).mp h
  rw [harg]
  convert h' using 2
  ring

/-! ## §8  中心化形式 -/

/-- ⭐⭐⭐ **中心化形式**：`e^{t/2} + e^{-t/2} ≤ 2·e^{t²/8}`。

Rademacher mgf 的标准陈述：`E[e^{tX}] = (e^t+e^{-t})/2 = cosh t ≤ e^{t²/2}`。

**证明**：`Real.cosh_eq` 把左端写成 `2·cosh(t/2)`，
再用 `Real.cosh_le_exp_half_sq`（`s = t/2`，`s²/2 = t²/8`）。 -/
theorem exp_half_add_exp_neg_half_le (t : ℝ) :
    Real.exp (t/2) + Real.exp (-(t/2)) ≤ 2 * Real.exp (t^2/8) := by
  have hcosh : Real.cosh (t/2) ≤ Real.exp ((t/2)^2/2) := Real.cosh_le_exp_half_sq (t/2)
  have h2 : Real.exp (t/2) + Real.exp (-(t/2)) = 2 * Real.cosh (t/2) := by
    rw [Real.cosh_eq]; ring
  rw [h2]
  have hsq : (t/2)^2/2 = t^2/8 := by ring
  rw [hsq] at hcosh
  linarith

/-! ## §9  `e^t(1 - t) ≤ 1`（全 ℝ） -/

/-- ⭐ **`e^t(1 - t) ≤ 1`**（对**一切** `t : ℝ`）。

- `t ≥ 1`：`1 - t ≤ 0` 而 `e^t > 0`，故左端 `≤ 0 ≤ 1`；
- `t ≤ 1`：由 `Real.add_one_le_exp (-t)` 得 `-t + 1 ≤ e^{-t} = (e^t)⁻¹`，
  即 `1 - t ≤ (e^t)⁻¹`，两边乘 `e^t > 0` 得 `(1-t)e^t ≤ 1`。

⚠ 细节：`Real.add_one_le_exp (-t)` 给出的是 `-t + 1 ≤ e^{-t}`（**`-t+1` 形式**），
不能直接当 `1 - t` 用，必须先 `linarith` 转换一次。 -/
theorem exp_mul_one_sub_le_one (t : ℝ) : Real.exp t * (1 - t) ≤ 1 := by
  have he : (0:ℝ) < Real.exp t := Real.exp_pos t
  rcases le_total t 1 with h1 | h1
  · have h := Real.add_one_le_exp (-t)
    have hne : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
    rw [hne] at h
    have h' : 1 - t ≤ (Real.exp t)⁻¹ := by linarith
    have h3 : (1 - t) * Real.exp t ≤ (Real.exp t)⁻¹ * Real.exp t :=
      mul_le_mul_of_nonneg_right h' (le_of_lt he)
    have h4 : (Real.exp t)⁻¹ * Real.exp t = 1 := inv_mul_cancel₀ (ne_of_gt he)
    rw [h4] at h3
    linarith
  · have h2 : (1 - t) * Real.exp t ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt he)
    linarith

/-! ## §10  `e^t - 1 ≤ t·e^t`（`t ≥ 0`） -/

/-- ⭐ **`e^t - 1 ≤ t·e^t`**（`t ≥ 0`）。

⚠ 直觉上这条像是 `add_one_le_exp` 的直接推论，但**纯 `linarith` 证不了**
（要联系 `t` 与 `t·e^t`，中间隔着乘积）。
真正的来源是 §9 的 `e^t(1-t) ≤ 1`（对一切 `t` 成立，更强）：
`e^t(1-t) ≤ 1 ⟺ e^t - t·e^t ≤ 1 ⟺ e^t - 1 ≤ t·e^t`。 -/
theorem exp_sub_one_le_mul_exp {t : ℝ} (_ht : 0 ≤ t) :
    Real.exp t - 1 ≤ t * Real.exp t := by
  have h := exp_mul_one_sub_le_one t
  nlinarith

/-! ## §11  公理审计（逐条） -/

#print axioms log_one_add_le
#print axioms psi_arg_pos
#print axioms psi_bound_iff_exp
#print axioms mul_le_of_nonneg_of_le_one
#print axioms cosh_exp_eq_half
#print axioms psi_half
#print axioms psi_half_exp
#print axioms exp_half_add_exp_neg_half_le
#print axioms exp_mul_one_sub_le_one
#print axioms exp_sub_one_le_mul_exp

end FateV2.Error.Stage2.ErrorBoundE2cFull
