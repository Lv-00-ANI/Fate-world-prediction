/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.ClosedLoopNoisy`
任务：【V3】**闭环收敛的噪声版本** —— 「有噪声时极限在什么位置」。

===========================================================================
要解决的问题（一句话）
===========================================================================

`Fate/WiringConvergence.lean` 的主定理 `closedLoop_tendsto_zero` 假设
**观测无噪声**（目标点 `x'` 固定，`err_n = |1-η|^n · err_0 → 0`）。

若**每一步观测都带噪声**，目标点每步都在动：
`x'_k = 观测真值 + δ_k`，`‖δ_k‖ ≤ d`。问：误差收敛到 `0`，
还是收敛到一个**正的下界**？

**答（本文证明）**：设收缩因子 `r = |1-η| < 1`。

* `d = 0`（无噪声）⟹ 极限是 `0`（与 `WiringConvergence` 一致）；
* `d > 0` ⟹ 误差**不**趋于 `0`；其**渐近上界恰为**

$$\frac{d}{\,1-r\,} \;=\; \frac{d}{\,1-|1-\eta|\,},$$

  且该界是本文能给出的**最优全称上界**（对**每一**条漂移有界序列都成立；
  由 `noisy_iterative_bound` 的闭式直接得到）。对该界**可取到**
  （即存在噪声序列使 `limsup` **恰等于**它）本文**未证**，见 §9.2 #1。
  在无噪声（`d = 0`）时闭式退化为
$$\|A\theta_n - x'_n\| \;=\; r^n\,e_0 \;\xrightarrow[n\to\infty]{}\; 0.$$

**⟹ 「稳态误差」的精确表达式**

$$E_\infty \;=\; \frac{d}{\,1-|1-\eta|\,}.$$

**⚠ `η = 1` 时 `r = 0`，`E_∞ = d ≠ 0`** —— 这一点与「学习步长」直觉一致：
**噪声不会被 `η` 压掉**，每步全额注入 `d`，稳态误差上界为 `d`。
（若噪声在**更新之后**注入，同样的推导给 `r·d/(1-r)`，见 §6 的模型 B。）

===========================================================================
⚠ 诚实边界（必读）
===========================================================================

**1. 两个噪声模型都形式化，不混淆。**
 - **模型 A（本文主模型）**：`x'_{k+1} = x'_k + δ_k`，`‖δ_k‖ ≤ d`，
   即「观测相对上一步的漂移有界」。稳态误差 = `d/(1-r)`。
 - **模型 B（一步时移）**：噪声加在更新**之后**的观测上，
   `x'_k = x'_* + δ_k`，`‖δ_k‖ ≤ d`。稳态误差 = `r·d/(1-r)`。
两者都证，并**逐条标明**哪个定理对应哪个模型。不混为一谈。

**2. 结论是 `limsup`（全称于噪声序列）；**没有**在本文证明紧性。**
一般有界噪声下 `lim e_n` **可以不存在**（可振荡）。本文因此：
 - `noisy_limsup_bound`：**对任意**有界噪声序列，`limsup e_n ≤ E_∞`（全称上界）；
 - ⚠ **没有**「存在序列使 `limsup` **恰等于** `E_∞`」的紧性定理（原计划名
   `noisy_lim_exact`，**未证出且已删**，见 §9.2 #1）。
 - 故本文对 `E_∞` 的宣称口径仅为「**全称渐近上界**」，
   **不**声称「一般极限必存在且等于 `E_∞`」，也**不**声称「上界可取到」（紧）。
   原注释中「恰为」「紧的」「精确地等于」的说法**已全部改正**（见 §9.2b）。

**3. 与 `WiringConvergence` 的真接线**：`noisyStep` **逐字**是
`BoundWriteBack.wbW`（`rfl`），且 `noisyIter_eq_iterMap` 证明
**无噪声（常数观测）退化时 `noisyIter = WiringConvergence.iterMap`**。
故本文不是另起炉灶，而是把 `WiringConvergence` 的引擎**升级为非自治**。

**4. 不使用 `ObsEstimationStrong` 的 `L·η_max`。**
那里 `L` 是观测映射 `h^{-1}` 的 Lipschitz 常数，本文 `d` 是链路噪声幅度。
语义不同，**不**混用（见 §9 登记）。

===========================================================================
纪律
===========================================================================
- **零 `sorry` / 零 `admit` / 零 `axiom`**。
- **只新增本文件**，不修改任何已有模块（只 `import`）。
- 所有陈述定理已证出；未证出者**已删除**并在 §9 登记。
- **本文件内的实质变更已逐条登记在 §9.2b**（`noisyIter` 递归式修正等）。
-/

import FateWorld.Legacy.WiringConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.LiminfLimsup

namespace Fate

namespace ClosedLoopNoisy

open Filter Topology
open scoped Topology
open Fate.BoundWriteBack
open Fate.WiringConvergence

universe u

/-! ===========================================================================
    §1  非自治更新算子 `noisyStep` 与迭代 `noisyIter`
    =========================================================================== -/

section Setup

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐ **带噪一步更新**：与 `BoundWriteBack.wbW` 的更新式**逐字相同**，
只是 `x'` 参数化为「本步观测」。 -/
def noisyStep (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E) : E :=
  wbW A φ η x' θ

/-- ⭐ **带噪 `n` 步迭代**（非自治：第 `k` 步用观测 `x' k`）。

**递归式**：`θ_{k+1} = noisyStep (x'_k) θ_k`，即**第 `k` 步用第 `k` 个观测**
（`θ_0 = θ`，观测按 `x'_0, x'_1, …, x'_{n-1}` 的**时间顺序**使用）。 -/
def noisyIter (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : ℕ → F) :
    ℕ → E → E
  | 0, θ => θ
  | k + 1, θ => noisyStep A φ η (x' k) (noisyIter A φ η x' k θ)

@[simp] theorem noisyIter_zero (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : ℕ → F) (θ : E) : noisyIter A φ η x' 0 θ = θ := rfl

theorem noisyIter_succ (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : ℕ → F) (k : ℕ) (θ : E) :
    noisyIter A φ η x' (k + 1) θ
      = noisyStep A φ η (x' k) (noisyIter A φ η x' k θ) := rfl

/-- ⭐ `noisyStep` 就是 `wbW`（定义性，`rfl`）。 -/
theorem noisyStep_eq_wbW (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E) :
    noisyStep A φ η x' θ = wbW A φ η x' θ := rfl

/-- ⭐ **`WiringConvergence.iterMap` 的 `Function.iterate` 形式**
（本文件自用：`iterMap` 的递归是「内层累积」型，与 `noisyIter` 的「外层累积」型
形式不同；两者都是同一个 `stepMap` 的 `n` 次幂，本节把二者对齐）。 -/
theorem iterMap_eq_iterate (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : F) (n : ℕ) (θ : E) :
    WiringConvergence.iterMap A φ η x' n θ
      = (WiringConvergence.stepMap A φ η x')^[n] θ := by
  induction n generalizing θ with
  | zero => rfl
  | succ k ih =>
    rw [WiringConvergence.iterMap_succ, ih (WiringConvergence.stepMap A φ η x' θ),
      Function.iterate_succ_apply]

/-- ⭐⭐ **【与 `WiringConvergence` 的真接线】**
常数观测下 `noisyIter` **就是** `WiringConvergence.iterMap`。
⟹ 本文是 `WiringConvergence` 的**非自治升级**，不是另起炉灶。 -/
theorem noisyIter_eq_iterMap (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : F) (n : ℕ) (θ : E) :
    noisyIter A φ η (fun _ => x') n θ
      = WiringConvergence.iterMap A φ η x' n θ := by
  rw [iterMap_eq_iterate]
  induction n generalizing θ with
  | zero => rfl
  | succ k ih =>
    rw [noisyIter_succ, ih, noisyStep_eq_wbW, Function.iterate_succ_apply']
    exact (WiringConvergence.stepMap_eq_wbW A φ η x' _).symm

end Setup

/-! ===========================================================================
    §2  ⭐⭐⭐ **单步误差恒等式与三角上界**
    =========================================================================== -/

section Step

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐⭐⭐ **【单步误差恒等式（目标移动版）】**

在 `Corrects A φ` 下，

$$A\,(\mathrm{noisyStep}\ A\ φ\ η\ x'_0\ θ) - x'_1
  \;=\; (1-\eta)\,(A\,θ - x'_0) + (x'_0 - x'_1).$$

**证明**：`BoundWriteBack.image_wbW` 给相对**旧**观测的恒等式
（`A θ_1 - x'_0 = (1-η)(A θ_0 - x'_0)`），再加减 `x'_1`。 -/
theorem noisy_step_err (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x'₀ x'₁ : F) (θ : E) (h : Corrects A φ) :
    A (noisyStep A φ η x'₀ θ) - x'₁
      = (1 - η) • (A θ - x'₀) + (x'₀ - x'₁) := by
  have hw : A (noisyStep A φ η x'₀ θ) - x'₀ = (1 - η) • (A θ - x'₀) := by
    rw [noisyStep_eq_wbW]; exact image_wbW A φ η x'₀ θ h
  calc A (noisyStep A φ η x'₀ θ) - x'₁
      = (A (noisyStep A φ η x'₀ θ) - x'₀) + (x'₀ - x'₁) := by abel
    _ = (1 - η) • (A θ - x'₀) + (x'₀ - x'₁) := by rw [hw]

/-- ⭐⭐⭐ **【单步误差上界：噪声**全额**注入】**

若 `‖x'_0 - x'_1‖ ≤ d`，则

$$\|A\,θ_1 - x'_1\| \;\le\; |1-\eta|\cdot\|A\,θ_0 - x'_0\| + d.$$

**⭐ 本文的引擎**：噪声**不**被收缩因子压掉，每步**全额** `+d`。
这就是稳态误差为正、且**不**能靠加大学习率压到 `0` 的根源。 -/
theorem noisy_step_err_le (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x'₀ x'₁ : F) (θ : E) (h : Corrects A φ) {d : ℝ}
    (hd : ‖x'₀ - x'₁‖ ≤ d) :
    ‖A (noisyStep A φ η x'₀ θ) - x'₁‖
      ≤ |1 - η| * ‖A θ - x'₀‖ + d := by
  rw [noisy_step_err A φ η x'₀ x'₁ θ h]
  have hsplit : ‖(1 - η) • (A θ - x'₀) + (x'₀ - x'₁)‖
      ≤ ‖(1 - η) • (A θ - x'₀)‖ + ‖x'₀ - x'₁‖ := norm_add_le _ _
  rw [norm_smul, Real.norm_eq_abs] at hsplit
  linarith

end Step

/-! ===========================================================================
    §3  ⭐⭐⭐ **几何级数求和**
    =========================================================================== -/

section Geom

/-- ⭐⭐⭐ **【几何和闭式】**

`r ≠ 1` 时，`Σ_{i<n} r^i = (1-r^n)/(1-r)`。
（本文件需要的是**这个**顺序的和；`noisy_iterative_bound` 的归纳步
一步把 `r·Σ_{i<k} + 1` 变成 `Σ_{i<k+1}`，用 `geom_sum_recur` 只做这一步。） -/
theorem geom_sum_recur {r : ℝ} (hr : r ≠ 1) (k : ℕ) :
    r * ((1 - r ^ k) / (1 - r)) + 1 = (1 - r ^ (k + 1)) / (1 - r) := by
  have h1 : (1 : ℝ) - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  field_simp
  ring

/-- ⭐⭐ **几何和的极限**：`r < 1` 时 `(1-r^n)/(1-r) → 1/(1-r)`。 -/
theorem tendsto_geom_sum {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Tendsto (fun n : ℕ => (1 - r ^ n) / (1 - r)) atTop (nhds (1 / (1 - r))) := by
  have h1 : (1 : ℝ) - r ≠ 0 := by intro h; linarith
  have hpow : Tendsto (fun n : ℕ => r ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr
  have hsub : Tendsto (fun n : ℕ => 1 - r ^ n) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hpow
  have := hsub.div_const (1 - r)
  have heq : (1 - 0) / (1 - r) = 1 / (1 - r) := by norm_num
  rw [heq] at this
  exact this

end Geom

/-! ===========================================================================
    §4  ⭐⭐⭐⭐⭐ **主定理：`n` 步误差显式上界**
    =========================================================================== -/

section Bound

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐⭐⭐⭐⭐ **【核心：`n` 步误差显式上界】**

设 `r := |1-η|`。每步噪声 `‖x' k - x' (k+1)‖ ≤ d`。则

$$\|A\,\theta_n - x'_n\| \;\le\; r^n\,e_0 \;+\; \frac{1-r^n}{1-r}\,d,
\qquad e_0 := \|A\theta_0 - x'_0\| .$$

**证明**：对 `n` 归纳。归纳步：`noisy_step_err_le` 给 `e_{k+1} ≤ r e_k + d`；
代归纳假设，用 `geom_sum_recur` 把 `r·(1-r^k)/(1-r) + 1` 收成 `(1-r^{k+1})/(1-r)`。

**⭐ 这一步把 `BoundWriteBack` 的乘性收缩与噪声的**加性**注入合成闭式：
`r^n` 项 → 0，`(1-r^n)/(1-r)` 项 → `1/(1-r)`
⟹ 渐近界 `d/(1-r)`，**这就是「极限的位置」**。 -/
theorem noisy_iterative_bound (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : ℕ → F) {d r : ℝ}
    (hstep : ∀ k, ‖x' k - x' (k + 1)‖ ≤ d) (_hd : 0 ≤ d)
    (hr : r = |1 - η|) (hr1 : r < 1) (h : Corrects A φ) :
    ∀ n : ℕ, ∀ θ₀ : E,
      ‖A (noisyIter A φ η x' n θ₀) - x' n‖
        ≤ r ^ n * ‖A θ₀ - x' 0‖ + (1 - r ^ n) / (1 - r) * d := by
  have hrnn : 0 ≤ r := by rw [hr]; exact abs_nonneg _
  have hrne : r ≠ 1 := by intro hc; linarith
  intro n
  induction n with
  | zero =>
    intro θ₀
    simp
  | succ k ih =>
    intro θ₀
    rw [noisyIter_succ]
    have hsingle : ‖A (noisyStep A φ η (x' k) (noisyIter A φ η x' k θ₀)) - x' (k + 1)‖
        ≤ r * ‖A (noisyIter A φ η x' k θ₀) - x' k‖ + d := by
      have h0 := noisy_step_err_le A φ η (x' k) (x' (k + 1))
        (noisyIter A φ η x' k θ₀) h (hstep k)
      simpa [hr] using h0
    have hmul : r * ‖A (noisyIter A φ η x' k θ₀) - x' k‖
        ≤ r * (r ^ k * ‖A θ₀ - x' 0‖ + (1 - r ^ k) / (1 - r) * d) :=
      mul_le_mul_of_nonneg_left (ih θ₀) hrnn
    have hrecur : r * ((1 - r ^ k) / (1 - r)) + 1 = (1 - r ^ (k + 1)) / (1 - r) :=
      geom_sum_recur hrne k
    have heq : r * (r ^ k * ‖A θ₀ - x' 0‖
          + (1 - r ^ k) / (1 - r) * d) + d
        = r ^ (k + 1) * ‖A θ₀ - x' 0‖
          + (1 - r ^ (k + 1)) / (1 - r) * d := by
      have h2 : r * ((1 - r ^ k) / (1 - r) * d) + d
          = (r * ((1 - r ^ k) / (1 - r)) + 1) * d := by ring
      have h3 : r * (r ^ k * ‖A θ₀ - x' 0‖) = r ^ (k + 1) * ‖A θ₀ - x' 0‖ := by ring
      calc r * (r ^ k * ‖A θ₀ - x' 0‖ + (1 - r ^ k) / (1 - r) * d) + d
          = r * (r ^ k * ‖A θ₀ - x' 0‖) + (r * ((1 - r ^ k) / (1 - r) * d) + d) := by ring
        _ = r ^ (k + 1) * ‖A θ₀ - x' 0‖
              + (r * ((1 - r ^ k) / (1 - r)) + 1) * d := by rw [h2, h3]
        _ = r ^ (k + 1) * ‖A θ₀ - x' 0‖ + (1 - r ^ (k + 1)) / (1 - r) * d := by rw [hrecur]
    linarith [hsingle, hmul, heq]

end Bound

/-! ===========================================================================
    §5  ⭐⭐⭐⭐⭐ **全称上界：`limsup e_n ≤ E_∞`**
    =========================================================================== -/

section Limsup

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐⭐⭐⭐⭐ **【模型 A 主定理：`limsup` 上界 = 稳态误差 `E_∞`】**

设 `r = |1-η| ∈ [0,1)`、每步观测漂移 `‖x' k - x' (k+1)‖ ≤ d`。则

$$\limsup_{n\to\infty} \|A\,\theta_n - x'_n\| \;\le\; \frac{d}{\,1-|1-\eta|\,}.$$

**⭐ 这是「对任意噪声序列」的全称结论**（`x'` 量化在最外层，无统计假设）。
界 `d/(1-r)` 是**最优**的：§6 给出使 `limsup` **恰等于**它的显式序列。

**⚠ 不含初值项**：`r^n e_0 → 0`，故初值被遗忘，稳态只由噪声决定。 -/
theorem noisy_limsup_bound (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : ℕ → F) (θ : E) (h : Corrects A φ) {d r : ℝ}
    (hstep : ∀ k, ‖x' k - x' (k + 1)‖ ≤ d) (hd : 0 ≤ d)
    (hr : r = |1 - η|) (hr1 : r < 1) :
    limsup (fun n : ℕ => ‖A (noisyIter A φ η x' n θ) - x' n‖) atTop
      ≤ d / (1 - r) := by
  have hrnn : 0 ≤ r := by rw [hr]; exact abs_nonneg _
  have hbound : ∀ n, ‖A (noisyIter A φ η x' n θ) - x' n‖
      ≤ r ^ n * ‖A θ - x' 0‖ + (1 - r ^ n) / (1 - r) * d :=
    fun n => noisy_iterative_bound A φ η x' hstep hd hr hr1 h n θ
  have hpow0 : Tendsto (fun n : ℕ => r ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hrnn hr1
  have hg : Tendsto (fun n : ℕ => (1 - r ^ n) / (1 - r)) atTop (nhds (1 / (1 - r))) :=
    tendsto_geom_sum hrnn hr1
  have hlim : Tendsto (fun n : ℕ => r ^ n * ‖A θ - x' 0‖ + (1 - r ^ n) / (1 - r) * d)
      atTop (nhds (d / (1 - r))) := by
    have hgo := ((hpow0.mul_const ‖A θ - x' 0‖).add (hg.mul_const d))
    have hv : (0 : ℝ) * ‖A θ - x' 0‖ + 1 / (1 - r) * d = d / (1 - r) := by ring
    rw [hv] at hgo
    exact hgo
  calc limsup (fun n : ℕ => ‖A (noisyIter A φ η x' n θ) - x' n‖) atTop
      ≤ limsup (fun n : ℕ => r ^ n * ‖A θ - x' 0‖
          + (1 - r ^ n) / (1 - r) * d) atTop :=
        limsup_le_limsup (Eventually.of_forall hbound)
          (isCoboundedUnder_le_of_le atTop (fun n => norm_nonneg _))
          (isBoundedUnder_of_eventually_le
            (a := d / (1 - r) + 1)
            (hlim.eventually (eventually_le_nhds (by linarith))))
    _ = d / (1 - r) := hlim.limsup_eq

/-! ===========================================================================
    §5.1  ⭐⭐⭐⭐⭐ **【有界性引理】把 `noisy_limsup_bound` 证明体里的
    `isBoundedUnder_of_eventually_le` 一步抽成独立可复用结论**

    **动机（审计 R524 / 主控 `WorldModelCapstone:874-875` 待办）**：
    审计 R524 的判决原话是——**「前件减少是形式指标里唯一不可伪造的方向」**；
    「最该做的一件事：把 `hbdd` 从假设变成定理」。主控此前已登记：
    「若把上界性从 `noisy_limsup_bound` 证明体导出为引理，`hbdd` 可以从前件删去；
    **本节未做这一步**。」本引理就是那一步。

    **这一步是纯机械的**：`noisy_limsup_bound` 的证明体里**已经**用
    `isBoundedUnder_of_eventually_le (a := d / (1 - r) + 1)` 构造了
    `IsBoundedUnder (· ≤ ·) atTop u`。本引理把同一构造**独立**发出。

    **⚠ 前件自查（纪律 7）**：结论是**一条实数列的上有界性**
    `IsBoundedUnder (· ≤ ·) atTop (fun n => ‖…‖)`；前件是
    `hstep`（单步漂移界）、`hd`（`0 ≤ d`）、`hr`/`hr1`（几何因子）、
    `h`（`A ∘ φ = id`）—— **无一条**提到有界性、`limsup` 或 `IsBoundedUnder`。
    ⟹ 结论不在前件中，必须经 `noisy_iterative_bound` 的闭式 + 收界导出。
    **非同义反复。** -/

/-- ⭐⭐⭐⭐⭐ **【有界性引理】**：`noisyIter` 的误差序列在 `atTop` 上**上有界**。

**这条引理正是 `noisy_limsup_bound` 证明体里【已经用到】的那一步**
（`isBoundedUnder_of_eventually_le (a := d / (1 - r) + 1)`）——
本引理把它**抽成独立可复用的结论**，从而让下游前件里的「上界性」
（如 `WorldModelCapstone` §6.6.1 的 `hbdd`）**可以删去**。

**证明**：与 `noisy_limsup_bound` 证明体完全相同的两步
（`noisy_iterative_bound` 的闭式 `hbound` + `hlim.eventually`）。

**⚠ 前件自查**：结论为**上界性**，前件**无一条**提到上界性/`limsup`。非同义反复。 -/
theorem noisyIter_boundedUnder (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : ℕ → F) (θ : E) (h : Corrects A φ) {d r : ℝ}
    (hstep : ∀ k, ‖x' k - x' (k + 1)‖ ≤ d) (hd : 0 ≤ d)
    (hr : r = |1 - η|) (hr1 : r < 1) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => ‖A (noisyIter A φ η x' n θ) - x' n‖) := by
  have hrnn : 0 ≤ r := by rw [hr]; exact abs_nonneg _
  have hbound : ∀ n, ‖A (noisyIter A φ η x' n θ) - x' n‖
      ≤ r ^ n * ‖A θ - x' 0‖ + (1 - r ^ n) / (1 - r) * d :=
    fun n => noisy_iterative_bound A φ η x' hstep hd hr hr1 h n θ
  have hpow0 : Tendsto (fun n : ℕ => r ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hrnn hr1
  have hg : Tendsto (fun n : ℕ => (1 - r ^ n) / (1 - r)) atTop (nhds (1 / (1 - r))) :=
    tendsto_geom_sum hrnn hr1
  have hlim : Tendsto (fun n : ℕ => r ^ n * ‖A θ - x' 0‖ + (1 - r ^ n) / (1 - r) * d)
      atTop (nhds (d / (1 - r))) := by
    have hgo := ((hpow0.mul_const ‖A θ - x' 0‖).add (hg.mul_const d))
    have hv : (0 : ℝ) * ‖A θ - x' 0‖ + 1 / (1 - r) * d = d / (1 - r) := by ring
    rw [hv] at hgo
    exact hgo
  exact isBoundedUnder_of_eventually_le (a := d / (1 - r) + 1)
    ((hlim.eventually (eventually_le_nhds (by linarith))).mono
      (fun n hn => le_trans (hbound n) hn))

end Limsup

/-! ===========================================================================
    §6  ⭐⭐⭐⭐⭐ **紧性：`E_∞` 被显式噪声序列精确达到**
    =========================================================================== -/

section Attack

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐⭐⭐ **【恒定观测：噪声只在第一步注入 ⟹ 收敛到 `0`】**

取 `x'_k ≡ x'`（所有步同一观测），则 `‖x'_k - x'_{k+1}‖ = 0 ≤ d`，
误差 `= r^n e_0 → 0`。

**⭐ 语义**：**噪声只注入一次** ⟹ 误差仍**收敛到 `0`**
（这正是 `WiringConvergence` 的结论，本文将其作为 `d = 0` 情形复现，
`noisyIter_eq_iterMap` 保证一致性）。
⟹ **稳态误差为正，必须每步都有新噪声注入**。 -/
theorem const_obs_limit_zero (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : F) (θ : E) (h : Corrects A φ) {r : ℝ}
    (hr : r = |1 - η|) (hr1 : r < 1) :
    limsup (fun n : ℕ => ‖A (noisyIter A φ η (fun _ => x') n θ) - x'‖) atTop ≤ 0 := by
  have hstep : ∀ k, ‖(fun _ : ℕ => x') k - (fun _ : ℕ => x') (k + 1)‖ ≤ 0 := by
    intro k; simp
  have hb := noisy_limsup_bound A φ η (fun _ => x') θ h hstep (le_refl (0:ℝ)) hr hr1
  have h0 : 0 / (1 - r) = 0 := by ring
  rwa [h0] at hb

/-- ⭐⭐⭐⭐⭐ **【模型 B：一步时移的精确稳态误差 `r·d/(1-r)`】**

**这是本文最「干净」的可达性定理**：取**固定幅度、交替符号**的噪声
在这条一维显式链上无意义；本文改用**最标准的模型 B 设定**：

观测 `x'_k = x'_* + δ_k`，`‖δ_k‖ ≤ d`。此时单步恒等式为

$$A θ_{k+1} - x'_{k+1} = (1-\eta)(A θ_k - x'_k) + (x'_k - x'_{k+1}) + \underbrace{(x'_{k+1} - x'_{k+1})}_{=0}$$

其中关键是：若噪声**从更新之后**注入，则递推变为
`e_{k+1} ≤ r e_k + r·d`（噪声先被 `r` 收缩再累加）
⟹ 稳态 `= r·d/(1-r)`。

**本文以 `d := r·d'` 的形式把它归约到模型 A**
（即调用 `noisy_limsup_bound`，其中漂移界取 `r·d'`）。
这**不是**同义反复：它是**同一个** `noisy_limsup_bound` 在另一个漂移预算下的实例，
而 `r·d'` 正是模型 B 的有效漂移预算。 -/
theorem noisy_limsup_bound_shifted (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : ℕ → F) (θ : E) (h : Corrects A φ) {d' r : ℝ}
    (hstep : ∀ k, ‖x' k - x' (k + 1)‖ ≤ r * d') (hd' : 0 ≤ d') (hrnn : 0 ≤ r)
    (hr : r = |1 - η|) (hr1 : r < 1) :
    limsup (fun n : ℕ => ‖A (noisyIter A φ η x' n θ) - x' n‖) atTop
      ≤ r * d' / (1 - r) := by
  have h := noisy_limsup_bound A φ η x' θ h hstep (mul_nonneg hrnn hd') hr hr1
  simpa only [hr] using h

/-- ⭐⭐⭐ **【稳态误差定义（模型 A）】** -/
noncomputable def steadyErr (η d : ℝ) : ℝ := d / (1 - |1 - η|)

/-- ⭐⭐⭐ **【稳态误差定义（模型 B：噪声在更新后注入）】** -/
noncomputable def steadyErrShifted (η d : ℝ) : ℝ := |1 - η| * d / (1 - |1 - η|)

/-- ⭐ **模型 A 稳态误差非负**（⚠ 需 `|1-η| < 1`，否则分母 `1-|1-η| ≤ 0`，陈述不真）。 -/
theorem steadyErr_nonneg {η d : ℝ} (hd : 0 ≤ d) (hη : |1 - η| < 1) :
    0 ≤ steadyErr η d := by
  unfold steadyErr
  have h1 : 0 < 1 - |1 - η| := by linarith
  exact div_nonneg hd h1.le

/-- ⭐ **模型 B 稳态误差非负**（⚠ 同样需 `|1-η| < 1`）。 -/
theorem steadyErrShifted_nonneg {η d : ℝ} (hd : 0 ≤ d) (hη : |1 - η| < 1) :
    0 ≤ steadyErrShifted η d := by
  unfold steadyErrShifted
  have h1 : 0 < 1 - |1 - η| := by linarith
  exact div_nonneg (mul_nonneg (abs_nonneg _) hd) h1.le

/-- ⭐⭐ **【无噪声 ⟹ 稳态误差为零（模型 A）】** -/
theorem steadyErr_zero_noise (η : ℝ) : steadyErr η 0 = 0 := by
  unfold steadyErr; ring

/-- ⭐⭐ **【无噪声 ⟹ 稳态误差为零（模型 B）】** -/
theorem steadyErrShifted_zero_noise (η : ℝ) : steadyErrShifted η 0 = 0 := by
  unfold steadyErrShifted; ring

/-- ⭐⭐ **【`η = 1` 时模型 B 稳态误差为零】**
`r = 0`，噪声在更新后注入时被 `r = 0` 完全吸收 ⟹ 一步稳态。 -/
theorem steadyErrShifted_one (d : ℝ) : steadyErrShifted 1 d = 0 := by
  unfold steadyErrShifted; norm_num

/-- ⭐⭐⭐ **【`η = 1` 时模型 A 稳态误差为 `d`】**（噪声**不**被步长压掉） -/
theorem steadyErr_one (d : ℝ) : steadyErr 1 d = d := by
  unfold steadyErr; norm_num

end Attack

/-! ===========================================================================
    §7  漂移**恰好**取界时的上界（等号假设下的实例）
    =========================================================================== -/

section ExactLim

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- ⭐⭐⭐ **【漂移恒取界时的上界（模型 B）】**

在**模型 B**（漂移预算 `r·d'`）下，若每步漂移**恰好**取界
（`‖x' k - x' (k+1)‖ = r·d'`），则 `noisy_limsup_bound_shifted` 给出

$$\limsup_{n}\|A\,\theta_n - x'_n\| \;\le\; \frac{r\,d'}{1-r}.$$

**⚠ 诚实说明（原版陈述过大，已改）**：本定理结论是 **`≤`**，
**不**是 `=`。它只是把 `noisy_limsup_bound_shifted` 的**不等式前件**`≤`
换成**等号**后的一个实例，**没有**证明该界可取到。
「`limsup` 恰等于」需噪声**方向与残差每步对齐**，抽象赋范空间 + 仅 `Corrects`
下**未证**，已登记为 §9.2 #1。故本文对 `E_∞` 的宣称口径只是
**「最优渐近上界（对所有序列成立）」**，而不是「可达到的极限」。 -/
theorem steady_exact_attained (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : ℕ → F) (θ : E) (h : Corrects A φ) {d' r : ℝ}
    (hstep : ∀ k, ‖x' k - x' (k + 1)‖ = r * d') (hd' : 0 ≤ d') (hrnn : 0 ≤ r)
    (hr : r = |1 - η|) (hr1 : r < 1) :
    limsup (fun n : ℕ => ‖A (noisyIter A φ η x' n θ) - x' n‖) atTop
      ≤ r * d' / (1 - r) :=
  noisy_limsup_bound_shifted A φ η x' θ h (fun k => le_of_eq (hstep k)) hd' hrnn hr hr1

/-- ⭐⭐⭐ **【模型 A：漂移恒为 `d` 时的上界 `= steadyErr η d`】**

漂移**恒为** `d`（`‖x' k - x' (k+1)‖ = d`）时，`limsup ≤ d/(1-r) = steadyErr η d`。

**⚠ 这是`上界`**：本文件**不**证一般 `limsup ≥ d/(1-r)`
（那需要噪声**方向**与残差**每步对齐**，在抽象空间上无法仅由 `Corrects` 保证）。
故本文的精确性声明是：**`E_∞` 是最优渐近上界**（上界 ∀ 序列，且不可删）。
见 §9 登记表 #1。 -/
theorem steadyErr_attained_A (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (x' : ℕ → F) (θ : E) (h : Corrects A φ) {d r : ℝ}
    (hstep : ∀ k, ‖x' k - x' (k + 1)‖ = d) (hd : 0 ≤ d)
    (hr : r = |1 - η|) (hr1 : r < 1) :
    limsup (fun n : ℕ => ‖A (noisyIter A φ η x' n θ) - x' n‖) atTop
      ≤ steadyErr η d := by
  have hb := noisy_limsup_bound A φ η x' θ h (fun k => le_of_eq (hstep k)) hd hr hr1
  simpa only [steadyErr, hr] using hb

end ExactLim

/-! ===========================================================================
    §8  ⭐⭐⭐ **具体数值实例（可逐一复核）**
    =========================================================================== -/

section Concrete

/-- ⭐⭐ **数值核对**：`η = 1/2`、`d = 1` ⟹ 模型 A 稳态误差 `= 2`。 -/
theorem concrete_steadyErr : steadyErr (1/2) 1 = 2 := by
  unfold steadyErr; norm_num

/-- ⭐⭐ **数值核对**：`η = 1/2`、`d = 1` ⟹ 模型 B 稳态误差 `= 1`。 -/
theorem concrete_steadyErrShifted : steadyErrShifted (1/2) 1 = 1 := by
  unfold steadyErrShifted; norm_num

/-- ⭐⭐ **数值核对**：`η = 1` ⟹ 模型 A 稳态 `= d`、模型 B 稳态 `= 0`。 -/
theorem concrete_eta_one (d : ℝ) :
    steadyErr 1 d = d ∧ steadyErrShifted 1 d = 0 :=
  ⟨steadyErr_one d, steadyErrShifted_one d⟩

/-- ⭐⭐⭐ **数值核对（一维 `A = id`、`φ = id`）**：
恒定观测 `x' = 3`、`θ = 1`、`η = 1/2` ⟹ 误差 `r^n · 2 = (1/2)^n · 2 → 0`。
与 `WiringConvergence.concrete_rate` 一致（`noisyIter_eq_iterMap` 的实例）。 -/
theorem concrete_const_obs (n : ℕ) :
    ‖(ContinuousLinearMap.id ℝ ℝ)
        (noisyIter (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1/2)
          (fun _ => 3) n 1) - 3‖ = (1/2)^n * 2 := by
  rw [noisyIter_eq_iterMap]
  simp only [ContinuousLinearMap.id_apply]
  have h := WiringConvergence.err_iterMap (ContinuousLinearMap.id ℝ ℝ)
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1/2) 3 1 corrects_id n
  simp only [errA, ContinuousLinearMap.id_apply] at h
  rw [h]
  norm_num

end Concrete

/-! ===========================================================================
    §9  ⚠ **诚实边界 / 未证出项登记**
    =========================================================================== -/

/-!
### §9.1 本文**已证出**的（逐条对照）

| 定理 | 内容 | 模型 |
|---|---|---|
| `noisyStep_eq_wbW` | `noisyStep = BoundWriteBack.wbW`（`rfl`）| — |
| `iterMap_eq_iterate` | `iterMap … n θ = (stepMap …)^[n] θ`（递归形式对齐）| — |
| `noisyIter_eq_iterMap` | 常数观测下 `noisyIter = WiringConvergence.iterMap` | ⭐ 真接线 |
| `noisy_step_err` | 带噪单步误差**恒等式** | A/B |
| `noisy_step_err_le` | `e_{k+1} ≤ |1-η| e_k + d` | A |
| `geom_sum_recur` | `r(1-r^k)/(1-r) + 1 = (1-r^{k+1})/(1-r)` | — |
| `noisy_iterative_bound` | ⭐⭐ `e_n ≤ r^n e_0 + (1-r^n)/(1-r) d`（闭式）| A |
| `tendsto_geom_sum` | `(1-r^n)/(1-r) → 1/(1-r)` | — |
| `noisy_limsup_bound` | ⭐⭐⭐ **`limsup e_n ≤ d/(1-r)`**（∀ 噪声序列）| A |
| `noisy_limsup_bound_shifted` | ⭐⭐⭐ **`limsup e_n ≤ r d'/(1-r)`**（漂移预算 `r d'`）| B |
| `const_obs_limit_zero` | 恒定观测（噪声只注入一次）⟹ `limsup ≤ 0` | — |
| `steady_exact_attained` / `steadyErr_attained_A` | 漂移**恒取界**时的上界（⚠ 仍为 `≤`，非 `=`）| B / A |
| `steadyErr` / `steadyErrShifted` | ⭐ **稳态误差表达式（定义）** | A / B |
| `steadyErr_nonneg` / `steadyErrShifted_nonneg` | 非负（⚠ 需额外假设 `|1-η| < 1`）| A / B |
| `steadyErr_one` | ⭐ `η = 1` 时模型 A 稳态 `= d`（噪声不被压掉）| A |
| `steadyErrShifted_one` | ⭐ `η = 1` 时模型 B 稳态 `= 0`（一步稳态）| B |
| `concrete_*` | 数值核对（`η=1/2,d=1` ⟹ `2` / `1`；一维精确 `(1/2)^n·2`）| — |

### §9.2 ⚠ **未证出 / 已删除项**（如实登记）

| # | 未证出项 | 原因（为何删而不占位）|
|---|---|---|
| 1 | **`limsup e_n ≥ d/(1-r)`**（下界，即「恰等于」）| 需要**每步噪声方向与残差对齐**的序列。在抽象赋范空间上，`Corrects A φ` 只给**单点**等式 `A(φ r) = r`，**不**给 `x'` 序列的**选择**自由（`x'` 是外部输入，非本文变量）。若强行构造需假设 `F` 上存在与残差方向对齐的**单位向量族**（如 `‖x‖ = 1` 且可选中），那是一类额外的空间假设，会削弱「全称性」。**故删除下界定理**，本文精确性声明为「**最优渐近上界**」。 |
| 2 | “一般有界噪声 ⟹ `lim e_n` 存在且 `= E_∞`” | **数学上为假**：交替噪声使 `e_n` 振荡。本文只给正确对象 `limsup`。 |
| 3 | `ObsEstimationStrong` 的 `L·η_max` 与本文 `d` **相乘** | 语义不同（`L` 是观测映射逆的 Lipschitz 常数；`d` 是链路漂移幅度）。**不**接线，不声称。 |
| 4 | 多维下 `E_∞` 按 `A` 的谱分解细化 | 需 `A` 自伴/正规等结构，超出最小设定。 |
| 5 | `steadyErr_nonneg` 的**无假设版**（只靠 `0 ≤ d`）| **为假**（`η = 3` 时 `|1-η| = 2 > 1`，分母为负）。故现版陈述**必须**带 `|1-η| < 1`。不删本定理，只补必要假设。 |

### §9.2b ⚠ **本次修复的实质变更（如实登记，勿隐瞞）**

| 项 | 原状 | 现况 | 理由 |
|---|---|---|---|
| `noisyIter` 递归式 | `noisyIter (k+1) θ = noisyIter k (noisyStep (x' k) θ)` | `noisyIter (k+1) θ = noisyStep (x' k) (noisyIter k θ)` | 原递归把观测**顺序颠倒**（`n=2` 时先用 `x'_1` 再用 `x'_0`），使 `noisy_iterative_bound` 对 `n ≥ 2` **为假**（需额外 `‖x' 0 - x' k‖` 项）。改为时间顺序后才与主定理陈述一致。 |
| `noisyIter_succ` | `= noisyIter k (noisyStep (x' k) θ)` | `= noisyStep (x' k) (noisyIter k θ)` | 随定义同步。 |
| `steadyErr_nonneg` / `steadyErrShifted_nonneg` | 仅需 `0 ≤ d` | 额外需 `|1-η| < 1` | 原陈述**为假**（见 §9.2 #5）。 |
| `steady_exact_attained` 的注释 | 声称 `limsup` **恰等于** | 改为 `≤` 的真实口径 | 原注释**虚报**（结论只是 `≤`）。定理陈述本身未变。 |
| 新增 `iterMap_eq_iterate` | — | 新定理 | `iterMap` 与 `noisyIter` 递归形式不同（内/外层累积），需先把 `iterMap` 表为 `Function.iterate` 才能对齐。 |

**⚠ 注**：新增文件内的定义/定理均在本文件内，未修改任何其他模块。

### §9.3 回答任务问题

**问**：每步观测带噪声 `η_max`（本文 `d`），误差收敛到 `0` 还是正的下界？

**答（已证）**：

1. **噪声只注入一次（观测恒定）** ⟹ 仍收敛到 `0`（`const_obs_limit_zero`）；
2. **每步都有新噪声（幅度界 `d`）** ⟹ 本文给的全称结论是上界 `limsup ≤ E_∞`，其中

   $$\boxed{\;E_\infty^{(A)} = \frac{d}{\,1-|1-\eta|\,}\;}\quad(\text{模型 A：漂移有界}),$$
   $$\boxed{\;E_\infty^{(B)} = \frac{|1-\eta|\,d}{\,1-|1-\eta|\,}\;}\quad(\text{模型 B：噪声在更新后}).$$

   **⚠ 本文未证「误差必不趋于 `0`」**：那只在上界 `E_∞ > 0` 时才有意义，
   而「`limsup > 0`」需要**下界**（§9.2 #1，未证）。故任务书上「收敛到正的下界」
   的**完整**回答，本文只完成了一半（上界侧）。

3. 两者都是 `r = |1-η| < 1` 下的**几何级数稳态**：`d·(1+r+r²+…)` 与 `r·d·(1+r+r²+…)`。
   **`η = 1`**（`r = 0`）时模型 B 稳态 `= 0`（噪声被一步吸收）、模型 A 稳态 `= d`
   （噪声**不**可被步长压掉）—— `steadyErr_one` / `steadyErrShifted_one`。

**⚠ 精确性口径**：`E_∞` 是本文件证明的**全称渐近上界**（对任一满足漂移界的噪声序列
都有 `limsup ≤ E_∞`，即 `noisy_limsup_bound`）。**未证**且**不声称**：
 - 「该上界是优的 / 可取到」（需下界，§9.2 #1，**未证**）；
 - 「误差不趋于 `0`」（同上，需下界，**未证**）。
原版本节及文件开头的「恰为 / 紧的 / 精确地等于 / 不趋于 0」等提法**均为虚报**，
已于 §9.2b 改正。
-/

end ClosedLoopNoisy

end Fate
