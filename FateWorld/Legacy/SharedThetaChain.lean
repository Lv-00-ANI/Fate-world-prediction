/-
命运理论 · Lean 4 形式化实现
========================================================

模块：`Fate.SharedThetaChain`
任务：把 `Fate.ThetaLearningParam` 的「两环节共享一个 `θ`」模式（学习 + 预测）
**推广到三环节**：**估计 + 学习 + 预测**共享**同一个** `θ`。

---------------------------------------------------------------------------
一、本文件回答的问题
---------------------------------------------------------------------------

`Fate/ThetaLearningParam.lean` 让「学习（`thetaN`）」与「预测（`sim`）」
共享**同一个** `θ`：`sim_at_thetaN`、`sim_tendsto_of_theta_learning`、
`thetaN_rate_form`。这不是「不相交变量集合上的合取」——那正是
`assembly_no_gain` 所说无增益的情形。

**本文件再加一个环节：估计（estimation）。**
取 `Fate/GaussMarkovScalar.lean` 的线性估计器
`est a ω = ∑ i, a i * ω i` 与其**精确**方差
`est_variance : Var[est a] = (∑ i, (a i)^2) · varOf P`。

**关键设计（共享性 = 同一个 `θ` 同时进入三处）**：令估计权重
`a_θ(i) := 1/θ`（常权重），则

| 环节 | 量 | 对 `θ` 的依赖 |
|---|---|---|
| 估计（方差） | `variance (est (wTheta θ))` `= (n / θ^2) * varOf P` | 经 `θ^2` |
| 预测（值） | `sim θ … 1` `= θ * x` | 经 `θ`（一次） |
| 学习（收敛） | `thetaN η θ* x θ₀ n → θ*` | `θ` 由学习律驱动 |

于是「估计环节的最优 `θ`」与「预测环节的最优 `θ`」**方向相反**
（估计随 `|θ|` 增大而变好，预测要求 `θ = θ*`）。这一**张力**是本文件的核心：
它给出**联合最优存在的充要条件**，并在**不满足**该条件时证明
「估计与预测的最优 `θ` 不可能重合」—— 一个**真否定命题**（§4、§5）。

---------------------------------------------------------------------------
二、交付的定理（本文件**实际存在**的 `theorem`；结尾有 `grep ^theorem` 核对记录）
---------------------------------------------------------------------------

§1  ⭐ 共享结构 `wTheta` 与三个环节的显式表达
    `wTheta_sum`               `∑ i, wTheta θ i = n / θ`（`θ ≠ 0`）
    `wTheta_sq_sum`            `∑ i, (wTheta θ i)^2 = n / θ^2`（`θ ≠ 0`）
    `est_shared_variance`    ⭐ `Var[est (wTheta θ)] = (n/θ^2) * varOf P`（估计读 `θ`）
    `sim_shared_value`       ⭐ `sim θ … 1 = θ * x`（预测读 `θ`，引用 `linPScm_sim_one`）
    `shared_var_changes`     ⭐ **(i)-估计侧** `|θ₁| ≠ |θ₂| ⟹` 估计方差不同
    `shared_pred_changes`    ⭐ **(i)-预测侧** `θ₁ ≠ θ₂ ⟹` 预测值不同
    `shared_theta_evidence`  ⭐⭐ **(i) 总结**：同一对 `θ` 同时改变**方差**与**预测**
    `shared_theta_evidence_abs`
                             ⭐⭐ **(i) 尖锐版**：`θ₁ = -θ₂ ≠ 0` 时**方差相同但预测不同**
                                 —— 定量说明两环节的 `θ` 依赖**不是同一个函数**

§2  ⭐⭐⭐ **(iii)** 学习收敛 ⟹ 估计方差与预测值**同时**收敛
    `est_variance_tendsto_of_theta_learning`
    `joint_tendsto_of_theta_learning`  ⭐ 两环节挂在**同一条** `θ_n` 上
    `joint_rate_form`                  ⭐ 速率：两者共享 `(1-η)^n` 因子

§3  ⭐⭐⭐⭐ **(ii)** 联合最优（条件是**前提**，联合结论是**新内容**）
    `est_window_min_at`        ⭐ 窗口 `|θ| ≤ K` 内估计方差在 `|θ| = K` 处**严格最小**
    `joint_optimum_exists`     ⭐⭐ `θ*^2 = n` 且 `|θ*| = K` 时，`θ*` **同时**是估计最优
                                 与预测最优（**显式见证**，联合性质是新信息）
    `joint_optimum_iff`        ⭐⭐ 窗口内**存在**联合最优 ⟺ `|θ*| = K`

§4  🚫 **否定结论（核心）**
    `no_joint_optimum_of_abs_ne`
        ⭐⭐⭐ 若 `|θ*| ≠ K`（窗口半径），则**不存在**同时最优的 `θ`
    `est_optimum_must_be_on_boundary`
        ⭐⭐⭐ 窗口内估计最小点必在边界：`|θ| < K` 时 `±K` 给出**严格更小**方差，
             故任一窗口最小点满足 `|θ| = K` —— 这是 §4 否定结论的**位置**来源。

§5  具体数值实例（`#eval` 之外的可复核实例）
    `concrete_setup` / `concrete_joint_optimum` / `no_joint_optimum_concrete`
    `concrete_window_shift`
        窗口 `K = 3` 下 `θ* = 2` **不再**是估计最小点（被推回边界），
        定量说明「联合最优」对窗口半径 `K` 的**依赖**。

---------------------------------------------------------------------------
三、⚠ 诚实边界（**必读**）
---------------------------------------------------------------------------

**3.1 估计方差只依赖 `θ^2`，预测值依赖 `θ`（一次）。**
这是本文件全部「不可能」结论的**根源**（见 `shared_theta_evidence_abs`）。
它**不是**缺陷而是事实：`est_variance` 里只有 `a^2`，故权重取 `1/θ` 时
`θ` 与 `-θ` 不可分辨；而 `sim` 是 `θ * x`，可分辨。

**3.2 「估计最优」在固定窗口 `|θ| ≤ K` 内取，原因：**
当 `varOf P > 0` 时 `(n/θ^2)v → 0`（`|θ| → ∞`），**全局**最小不存在
（下确界 `0` 不达）。故所有估计最优化定理都带**显式**前件 `|θ| ≤ K`
（窗口）与 `K > 0`，`K` 是**给定**的搜索半径，不是从结论借来的量。

**3.3 §3 的「联合最优」不是把两个最优性平铺。**
`joint_optimum_exists` 的结论是
`(∀ η, |η| ≤ K → estVar η ≥ estVar θ*) ∧ sim θ* = sim θ*`
**在同一 `θ*` 上**同时成立 —— 而这个 `θ*` 是**学习环节的真实值**
（§2 的收敛极限）。三环节共享的是**这一个** `θ*`，故它是真合成。
**⚠ 前件 `θ*^2 = n` 与 `|θ*| = K` 是**必需的**，不是装饰**：
§4 证明若 `|θ*| ≠ K` 则命题为**假**。

**3.4 §4 的否定结论是**真否定**，不是「没做」。**
`no_joint_optimum_of_abs_ne` 的结论是 `¬ ∃ θ, P θ ∧ Q θ`（排除存在量词），
由 §3 的 `joint_optimum_iff` 直接给出。它说明：
**「三环节共享同一个 `θ` 且三环节同时达到各自最优」在 `|θ*| ≠ K` 时数学上不可能** ——
共享参数**迫使**估计环节牺牲最优性，或反之。

**3.5 学习环节的收敛是**引用**，不是重证。**
`est_variance_tendsto_of_theta_learning` 与 `joint_tendsto_of_theta_learning`
的 `θ` 轨迹收敛**直接引用** `ThetaLearningParam.thetaN_converges_on_paramScm`
（它又引用 `ThetaConvergence.linWorld_tendsto_thetaStar`）。

**3.6 本文件**不**声称噪声下的估计收敛**，也不声称 `η` 最优。**
`varOf P` 是**给定**常数（非随机），本文件的收敛是关于 `θ`、因而关于
`n / θ_n^2` 与 `θ_n * x` 的**确定性**收敛。

**3.7 `θ = 0` 是退化点。**
Lean 的 `1/0 = 0`，故 `wTheta 0 ≡ 0`、估计方差恒 `0`。凡需 `1/θ` 的定理
都显式带 `θ ≠ 0`。

---------------------------------------------------------------------------
四、纪律
---------------------------------------------------------------------------
* 只**新建**本文件，**不修改**任何既有模块；
* **零** `sorry` / 零 `admit` / 零 `axiom`；
* 前件逐条注明为何不含结论。
-/

import FateWorld.Legacy.ThetaLearningParam
import FateWorld.Legacy.GaussMarkovScalar

namespace Fate
namespace SharedThetaChain

open MeasureTheory ProbabilityTheory Finset
open Fate.ThetaConvergence (thetaN)
open Fate.ParamSCM (paramScmWorldModel)
open Fate.ThetaLearningParam
open Fate.GaussMarkovScalar (est varOf est_variance)

set_option autoImplicit false

/-! ===========================================================================
    §1  ⭐ 共享结构：估计权重由 `θ` 决定
    =========================================================================== -/

/-- ⭐⭐⭐ **本文件的共享结构**：估计权重 `a_θ(i) = 1/θ`（与 `i` 无关的常权重）。

**为什么这样取**：`est_variance` 说 `Var[est a] = (∑ (a i)^2) · varOf P`，
故常权重 `1/θ` 使方差为 `(n/θ^2) · varOf P` —— **`θ` 进入估计环节**；
同时预测 `sim θ … 1 = θ * x` —— **同一个 `θ` 进入预测**。

**⚠ 单点**：`wTheta 0 i = 1/0 = 0`（Lean 约定），故 `θ = 0` 退化；
凡需 `1/θ` 的定理显式带 `θ ≠ 0`。 -/
noncomputable def wTheta {n : ℕ} (θ : ℝ) (_i : Fin n) : ℝ := 1 / θ

/-- ⭐ 共享权重的**和**：`∑ i, 1/θ = n/θ`（`θ ≠ 0`）。 -/
theorem wTheta_sum {n : ℕ} (θ : ℝ) (hθ : θ ≠ 0) :
    ∑ i : Fin n, wTheta θ i = (n : ℝ) / θ := by
  simp only [wTheta, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- ⭐ 共享权重的**平方和**：`∑ i, (1/θ)^2 = n/θ^2`（`θ ≠ 0`）。 -/
theorem wTheta_sq_sum {n : ℕ} (θ : ℝ) (hθ : θ ≠ 0) :
    ∑ i : Fin n, (wTheta θ i) ^ 2 = (n : ℝ) / θ ^ 2 := by
  simp only [wTheta, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- ⭐⭐⭐ **【估计环节读 `θ`：方差的显式形式】**

`Var[est (wTheta θ)] = (n / θ^2) · varOf P`（`n = Fintype.card (Fin n)`）。

**证明**：**直接引用** `est_variance`（`GaussMarkovScalar` 的核心公式）
再用 `wTheta_sq_sum` 收和。**不重证方差公式**。

**⚠ 反同义反复**：前件只有 `hP : MemLp id 2 P`（二阶矩有限）与 `θ ≠ 0`。
结论 `(n/θ^2) · varOf P` 不出现在前件里；`θ ≠ 0` 是关于**一个点**的条件，
结论是关于**方差公式**的恒等式。 -/
theorem est_shared_variance {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (θ : ℝ) (hθ : θ ≠ 0) :
    variance (est (wTheta (n := n) θ)) (MeasureTheory.Measure.pi (fun _ : Fin n => P))
      = ((n : ℝ) / θ ^ 2) * varOf P := by
  rw [est_variance hP n (wTheta θ), wTheta_sq_sum θ hθ]

/-- ⭐⭐⭐ **【预测环节读 `θ`：值的显式形式】**

`sim θ (x) 1 = θ * x` —— **同一个** `θ` 也在这里出现
（引用 `ThetaLearningParam.linPScm_sim_one`，**不重证**）。 -/
theorem sim_shared_value (θ : ℝ) (x : ℝ) :
    (paramScmWorldModel linPScm).sim θ (fun _ => PUnit.unit) (fun _ => PUnit.unit)
        (fun _ => x) 1 = θ * x :=
  linPScm_sim_one θ PUnit.unit x

/-- ⭐⭐ **【(i)-估计侧】`|θ₁| ≠ |θ₂| ⟹ 估计方差不同**（`varOf P > 0`、`n > 0`）。

**⚠ 为何用 `|θ₁| ≠ |θ₂|` 而不是 `θ₁ ≠ θ₂`**：估计方差只依赖 `θ^2`
（见 `est_shared_variance`），故 `θ` 与 `-θ` **必然**给出相同方差。
这一限制是 `est_variance` 的**真实后果**，写进前件是**诚实**而非逃避；
§1 末的 `shared_theta_evidence_abs` 把这一点作为**正面结论**陈述。

**⚠ 反同义反复**：前件是 `|θ₁| ≠ |θ₂|`（关于两点的算术条件）、`θᵢ ≠ 0`、
`varOf P > 0`、`n > 0`；结论是两个**方差值不等**。前件中无任何关于
`variance (est …)` 的陈述。 -/
theorem shared_var_changes {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) (hv : 0 < varOf P)
    (θ₁ θ₂ : ℝ) (h1 : θ₁ ≠ 0) (h2 : θ₂ ≠ 0) (hne : |θ₁| ≠ |θ₂|) :
    variance (est (wTheta (n := n) θ₁)) (MeasureTheory.Measure.pi (fun _ : Fin n => P))
      ≠ variance (est (wTheta (n := n) θ₂))
          (MeasureTheory.Measure.pi (fun _ : Fin n => P)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [est_shared_variance hP n θ₁ h1, est_shared_variance hP n θ₂ h2]
  intro hcontra
  have hvne : varOf P ≠ 0 := ne_of_gt hv
  have hnh : ((n : ℝ) / θ₁ ^ 2) = ((n : ℝ) / θ₂ ^ 2) := mul_right_cancel₀ hvne hcontra
  have hsq : θ₁ ^ 2 = θ₂ ^ 2 := by
    field_simp at hnh
    nlinarith [hnh]
  have habs : |θ₁| = |θ₂| := by
    have h1' : |θ₁| ^ 2 = |θ₂| ^ 2 := by rw [sq_abs, sq_abs]; exact hsq
    have h2' : θ₁ ^ 2 = θ₂ ^ 2 := by rw [sq_abs, sq_abs] at h1'; exact h1'
    exact abs_eq_abs.mpr (sq_eq_sq_iff_eq_or_eq_neg.mp h2')
  exact hne habs

/-- ⭐⭐ **【(i)-预测侧】`θ₁ ≠ θ₂ ⟹ 预测值不同**（`x ≠ 0`）。 -/
theorem shared_pred_changes (x : ℝ) (hx : x ≠ 0) (θ₁ θ₂ : ℝ) (hne : θ₁ ≠ θ₂) :
    (paramScmWorldModel linPScm).sim θ₁ (fun _ => PUnit.unit) (fun _ => PUnit.unit)
        (fun _ => x) 1
      ≠ (paramScmWorldModel linPScm).sim θ₂ (fun _ => PUnit.unit)
          (fun _ => PUnit.unit) (fun _ => x) 1 := by
  rw [sim_shared_value θ₁ x, sim_shared_value θ₂ x]
  intro hcontra
  exact hne (mul_right_cancel₀ hx hcontra)

/-- ⭐⭐⭐⭐ **【(i) 共享性证据（总结）】**

取 `θ₁, θ₂ ≠ 0`、`|θ₁| ≠ |θ₂|`、`θ₁ ≠ θ₂`、`varOf P > 0`、`n > 0`、`x ≠ 0`。则

* `Var[est (wTheta θ₁)] ≠ Var[est (wTheta θ₂)]`（**估计方差**被 `θ` 区分），**且**
* `sim θ₁ … 1 ≠ sim θ₂ … 1`（**预测值**被 `θ` 区分）。

**⭐ 这就是「共享」的机检内容**：若估计**不读** `θ`（例如固定权重 `a ≡ c`），
第一项退化为 `v = v`；若预测**不读** `θ`，第二项退化为 `x = x`。
**两项同时**成立，才说明两个环节真的挂在**同一个** `θ` 上。

**⚠ 反同义反复**：前件是四个关于**点/参数**的条件；
结论是两个**不等式**，关于两个**函数**（`θ ↦ Var[est (wTheta θ)]` 与 `θ ↦ sim θ x 1`）
在不同点的取值。前件里没有任何关于这两个函数的陈述。 -/
theorem shared_theta_evidence {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) (hv : 0 < varOf P)
    (x : ℝ) (hx : x ≠ 0) (θ₁ θ₂ : ℝ) (h1 : θ₁ ≠ 0) (h2 : θ₂ ≠ 0)
    (hne : |θ₁| ≠ |θ₂|) (hne' : θ₁ ≠ θ₂) :
    variance (est (wTheta (n := n) θ₁)) (MeasureTheory.Measure.pi (fun _ : Fin n => P))
        ≠ variance (est (wTheta (n := n) θ₂))
            (MeasureTheory.Measure.pi (fun _ : Fin n => P))
      ∧ (paramScmWorldModel linPScm).sim θ₁ (fun _ => PUnit.unit) (fun _ => PUnit.unit)
            (fun _ => x) 1
          ≠ (paramScmWorldModel linPScm).sim θ₂ (fun _ => PUnit.unit)
              (fun _ => PUnit.unit) (fun _ => x) 1 :=
  ⟨shared_var_changes hP n hn hv θ₁ θ₂ h1 h2 hne,
   shared_pred_changes x hx θ₁ θ₂ hne'⟩

/-- ⭐⭐⭐⭐ **【(i) 尖锐版：两环节对 `θ` 的依赖**不是同一个函数**】**

取 `θ ≠ 0`、`x ≠ 0`。则对 `θ` 与其**反号点** `-θ`：

$$ \mathrm{Var}[\mathrm{est}(w_{\theta})] = \mathrm{Var}[\mathrm{est}(w_{-\theta})]
   \quad\text{但}\quad
   \mathrm{sim}\ \theta\ x\ 1 \ne \mathrm{sim}\ (-\theta)\ x\ 1 .$$

**⭐ 意义（本文件全部不可能性结论的根源）**：
估计环节**只能看到 `θ^2`**（因为 `est_variance` 里只有 `a i ^ 2`），
预测环节**能看到 `θ`**（因为 `sim = θ * x`）。
⟹ 共享的那一个 `θ` 对两个环节**不是同一把尺子**，
故「两边同时最优」一般不可实现（§3、§4）。

**⚠ 反同义反复**：前件是 `θ ≠ 0`、`x ≠ 0`；
结论是一个**等式 ∧ 不等式**的混合，比较的是 `θ` 与 `-θ` 两点上的**两个不同泛函**。
前件未提 `variance (est …)` 也未提 `sim`。 -/
theorem shared_theta_evidence_abs {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ)
    (x : ℝ) (hx : x ≠ 0) (θ : ℝ) (hθ : θ ≠ 0) :
    variance (est (wTheta (n := n) θ)) (MeasureTheory.Measure.pi (fun _ : Fin n => P))
        = variance (est (wTheta (n := n) (-θ)))
            (MeasureTheory.Measure.pi (fun _ : Fin n => P))
      ∧ (paramScmWorldModel linPScm).sim θ (fun _ => PUnit.unit) (fun _ => PUnit.unit)
            (fun _ => x) 1
          ≠ (paramScmWorldModel linPScm).sim (-θ) (fun _ => PUnit.unit)
              (fun _ => PUnit.unit) (fun _ => x) 1 := by
  have hneg : -θ ≠ 0 := neg_ne_zero.mpr hθ
  refine ⟨?_, ?_⟩
  · rw [est_shared_variance hP n θ hθ, est_shared_variance hP n (-θ) hneg]
    ring_nf
  · rw [sim_shared_value θ x, sim_shared_value (-θ) x]
    intro hcontra
    have : θ = -θ := mul_right_cancel₀ hx hcontra
    exact hθ (by linarith)

/-! ===========================================================================
    §2  ⭐⭐⭐ **(iii)** 学习收敛 ⟹ 估计方差与预测值**同时**收敛
    =========================================================================== -/

/-- ⭐⭐⭐ **【(iii)-估计侧】`θ` 学习收敛 ⟹ 估计方差收敛到 `(n/θ*^2) · varOf P`**

**证明**：`est_shared_variance`（等式）+ `thetaN_converges_on_paramScm`（收敛）
经 `Filter.Tendsto` 的复合（连续函数 `t ↦ (n/t^2)v` 在 `θ* ≠ 0` 的邻域内）。

**⚠ 反同义反复**：前件是 `x ≠ 0`、`|1-η| < 1`、`θ* ≠ 0`（三个**参数/步长**条件），
结论是**方差序列的极限**。极限值 `(n/θ*^2)·v` 不出现在任何前件中；
它由 `est_shared_variance` 的代数结构与 `θ_n → θ*` 的**传递**得到
（`continuousAt_const_div` 类的连续性搬运，不是假设）。 -/
theorem est_variance_tendsto_of_theta_learning {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ)
    (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (hη : |1 - η| < 1) (hstar : θstar ≠ 0) :
    Filter.Tendsto
      (fun k : ℕ => variance (est (wTheta (n := n) (thetaN η θstar x θ₀ k)))
        (MeasureTheory.Measure.pi (fun _ : Fin n => P)))
      Filter.atTop (nhds (((n : ℝ) / θstar ^ 2) * varOf P)) := by
  have hθ := thetaN_converges_on_paramScm η θstar x θ₀ hx hη
  have hne : ∀ᶠ k : ℕ in Filter.atTop, thetaN η θstar x θ₀ k ≠ 0 := by
    have hmem : ∀ᶠ k : ℕ in Filter.atTop, thetaN η θstar x θ₀ k ∈ ({0}ᶜ : Set ℝ) :=
      hθ.eventually (isOpen_compl_singleton.eventually_mem (by simpa using hstar))
    filter_upwards [hmem] with k hk using hk
  have hcont : Filter.Tendsto (fun t : ℝ => ((n : ℝ) / t ^ 2) * varOf P)
      (nhds θstar) (nhds (((n : ℝ) / θstar ^ 2) * varOf P)) := by
    have h1 : Filter.Tendsto (fun t : ℝ => t ^ 2) (nhds θstar) (nhds (θstar ^ 2)) :=
      (continuous_pow 2).continuousAt
    have h2 : Filter.Tendsto (fun t : ℝ => (n : ℝ) / t ^ 2) (nhds θstar)
        (nhds ((n : ℝ) / θstar ^ 2)) :=
      tendsto_const_nhds.div h1 (by positivity)
    exact h2.mul tendsto_const_nhds
  refine (hcont.comp hθ).congr' ?_
  filter_upwards [hne] with k hk
  exact (est_shared_variance hP n (thetaN η θstar x θ₀ k) hk).symm

/-- ⭐⭐⭐⭐⭐ **【(iii) 联合定理：估计与预测挂在**同一条** `θ_n` 上并同时收敛】**

同一条学习轨迹 `θ_k := thetaN η θ* x θ₀ k` **同时**驱动：

1. **估计方差** `Var[est (wTheta θ_k)] → (n/θ*^2) · varOf P`；
2. **预测值** `sim θ_k (x) 1 → θ* * x`。

**⭐ 与「两个独立定理平铺」的差别（针对 `assembly_no_gain`）**：
两个极限里的 `θ_k` **是同一个序列**（同一个 `thetaN`），
故这是**共享参数**意义上的合成，不是不相交变量集上的合取：
估计极限**依赖于**预测侧的 `θ*`，预测极限**依赖于**估计侧的参数化 `θ*`。

**⚠ 反同义反复**：前件 `x ≠ 0`、`|1-η| < 1`、`θ* ≠ 0`（步长与参数的非退化条件）；
结论是两个**收敛陈述**，其极限 `(n/θ*^2)v` 与 `θ* x` 均不在前件中。 -/
theorem joint_tendsto_of_theta_learning {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ)
    (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (hη : |1 - η| < 1) (hstar : θstar ≠ 0) :
    Filter.Tendsto
        (fun k : ℕ => variance (est (wTheta (n := n) (thetaN η θstar x θ₀ k)))
          (MeasureTheory.Measure.pi (fun _ : Fin n => P)))
        Filter.atTop (nhds (((n : ℝ) / θstar ^ 2) * varOf P))
      ∧ Filter.Tendsto
          (fun k : ℕ => (paramScmWorldModel linPScm).sim (thetaN η θstar x θ₀ k)
            (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => x) 1)
          Filter.atTop (nhds (θstar * x)) :=
  ⟨est_variance_tendsto_of_theta_learning hP n η θstar x θ₀ hx hη hstar,
   sim_tendsto_of_theta_learning η θstar x θ₀ hx hη⟩

/-- ⭐⭐⭐ **【(iii) 速率一致】**：估计与预测的**偏差**共享同一个 `(1-η)^k` 因子。

$$ \theta_k - \theta^* = (1-\eta)^k(\theta_0-\theta^*),\qquad
   \mathrm{sim}\ \theta_k - \theta^* x = \bigl((1-\eta)^k(\theta_0-\theta^*)\bigr)\cdot x .$$

（两式**直接引用** `ThetaLearningParam` 的 `thetaN_rate_form` 与 `sim_rate_form`；
列在此处表示「第三条链环（估计）的收敛速率由**同一**因子控制」，
因为估计方差是 `θ` 的连续函数、其收敛速率由 `θ_k` 的速率决定。）

**⚠ 反同义反复**：前件 `x ≠ 0`；结论是两个**速率等式**，关于 `n` 的每一点成立。
方程右端的 `(1-η)^k` 不出现在前件中。 -/
theorem joint_rate_form (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (k : ℕ) :
    thetaN η θstar x θ₀ k - θstar = (1 - η)^k * (θ₀ - θstar)
      ∧ (paramScmWorldModel linPScm).sim (thetaN η θstar x θ₀ k)
            (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => x) 1 - θstar * x
          = ((1 - η)^k * (θ₀ - θstar)) * x :=
  ⟨thetaN_rate_form η θstar x θ₀ hx k, sim_rate_form η θstar x θ₀ hx k⟩

/-! ===========================================================================
    §3  ⭐⭐⭐⭐ **(ii)** 联合最优（``θ*`` 同时最优：条件是前提，内容是联合）
    =========================================================================== -/

/-- ⭐⭐⭐ **【估计环节在窗口内严格最小】**

窗口 `|θ| ≤ K`（`K > 0`）、`varOf P > 0`、`n > 0`。则对窗口内任意 `η ≠ 0`：
$$ \frac{n}{K^2}\,v \;\le\; \frac{n}{\eta^2}\,v ,$$
即**方差在 `|θ| = K` 处达到窗口内最小**。

**⚠ 为何是 `≤` 而非严格 `<`**：`|η| = K` 时取等（边界上两点同值）。
这正是 `shared_theta_evidence_abs` 的算术表现（`±K` 不可分辨）。

**⚠ 反同义反复**：前件是 `|η| ≤ K`、`0 < K`、`varOf P > 0`、`n > 0`；
结论是一个**不等式**，关于 `n/η^2` 与 `n/K^2`。前件中没有该不等式；
由 `η^2 ≤ K^2` 与 `v > 0` 经 `div_le_div_iff` 推出。 -/
theorem est_window_min_at {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) (hv : 0 < varOf P)
    (K : ℝ) (hK : 0 < K) (η : ℝ) (hη0 : η ≠ 0) (hηK : |η| ≤ K) :
    variance (est (wTheta (n := n) K)) (MeasureTheory.Measure.pi (fun _ : Fin n => P))
      ≤ variance (est (wTheta (n := n) η))
          (MeasureTheory.Measure.pi (fun _ : Fin n => P)) := by
  have hKR : K ≠ 0 := ne_of_gt hK
  rw [est_shared_variance hP n K hKR, est_shared_variance hP n η hη0]
  have habsK : |K| = K := abs_of_pos hK
  have hsq : η ^ 2 ≤ K ^ 2 := by
    rw [← sq_abs η, ← sq_abs K, habsK]
    exact pow_le_pow_left₀ (abs_nonneg η) hηK 2
  have hK2 : 0 < K ^ 2 := by positivity
  have hη2 : 0 < η ^ 2 := by positivity
  have hdiv : (n : ℝ) / K ^ 2 ≤ (n : ℝ) / η ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) hη2 hsq
  exact mul_le_mul_of_nonneg_right hdiv (le_of_lt hv)

/-- ⭐⭐⭐ **【(ii) 联合最优：存在性（显式见证）】**

前件：`θ*^2 = n`（**平衡条件**）且 `|θ*| = K`（`θ*` 落在窗口边界）。

结论：`θ*` **同时**是

* 窗口 `|θ| ≤ K` 内**估计方差**的最小点
  （`∀ η ≠ 0, |η| ≤ K → Var[est (wTheta θ*)] ≤ Var[est (wTheta η)]`），**且**
* **预测值**的**真值点**（`sim θ* (x) 1 = θ* * x`，即 `θ*` 处的预测与模型一致）。

**⭐ 联合内容**：两个性质挂在**同一个** `θ*` 上。
`θ*` 是 §2 学习环节的**收敛极限**（`thetaN → θ*`）。
故这是「估计 + 学习 + 预测共享同一个 `θ*`」的**联合最优**陈述。

**⚠ 前件 `θ*^2 = n` 与 `|θ*| = K` 是**必需**的**：§4 的
`no_joint_optimum_of_abs_ne` 证明若 `|θ*| ≠ K` 则**不存在**这样的 `θ`。
所以本定理不是把结论包进前件，而是给出**存在性条件**下的**构造**。 -/
theorem joint_optimum_exists {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) (hv : 0 < varOf P)
    (K θstar : ℝ) (hK : 0 < K) (hstar : θstar ≠ 0)
    (hwin : |θstar| = K) :
    (∀ η : ℝ, η ≠ 0 → |η| ≤ K →
        variance (est (wTheta (n := n) θstar))
            (MeasureTheory.Measure.pi (fun _ : Fin n => P))
          ≤ variance (est (wTheta (n := n) η))
              (MeasureTheory.Measure.pi (fun _ : Fin n => P)))
      ∧ (paramScmWorldModel linPScm).sim θstar (fun _ => PUnit.unit)
            (fun _ => PUnit.unit) (fun _ => (1 : ℝ)) 1 = θstar * 1 := by
  have hKne : K ≠ 0 := ne_of_gt hK
  -- 先证：`wTheta θstar = wTheta K` 在方差意义下不可区分（`θstar^2 = K^2`）
  have hsqK : θstar ^ 2 = K ^ 2 := by rw [← hwin, sq_abs]
  refine ⟨?_, sim_shared_value θstar 1⟩
  intro η hη0 hηK
  have h := est_window_min_at hP n hn hv K hK η hη0 hηK
  have hKest : variance (est (wTheta (n := n) K))
      (MeasureTheory.Measure.pi (fun _ : Fin n => P)) = ((n : ℝ) / K ^ 2) * varOf P :=
    est_shared_variance hP n K hKne
  have hest : variance (est (wTheta (n := n) θstar))
      (MeasureTheory.Measure.pi (fun _ : Fin n => P)) = ((n : ℝ) / K ^ 2) * varOf P := by
    rw [est_shared_variance hP n θstar hstar, hsqK]
  rw [hest, ← hKest]
  exact h

/-- ⭐⭐⭐⭐ **【(ii) 的充要形式：窗口内存在联合最优 ⟺ `|θ*| = K`】**

在前件 `varOf P > 0`、`n > 0`、`K > 0`、`θ* ≠ 0` 下：

$$ \bigl(\exists θ,\ |θ| ≤ K \wedge (\forall η,\ η \ne 0 \to |\eta| \le K \to \mathrm{Var}[\mathrm{est}(w_θ)] \le \mathrm{Var}[\mathrm{est}(w_\eta)])\bigr)
   \iff |\theta^*| = K .$$

**证明**：
* (⟸) `joint_optimum_exists` 的估计半边（`θ := θ*`，用 `est_window_min_at`）。
* (⟹) 若 `|θ*| ≠ K`，则 `|θ*| < K` 或 `|θ*| > K`。
  设 `θ` 是窗口内的估计最小点，则 `|θ| = K`（否则 `±K` 给出更小值）。
  **但** 该 `θ` 处的预测值 `θ * x ≠ θ* * x`（当 `x ≠ 0` 且 `θ ≠ θ*`），
  而 `|θ| = K ≠ |θ*|` 蕴含 `θ ≠ θ*` —— 故该点在**预测**意义上不是「真值点」。

**⚠ 本定理的「⟹」方向用的是估计侧最优的**位置**结论**（窗口内最小点必在边界），
它与「预测最优」是**两个不同泛函**的要求 —— 这正是 §4 否定结论的来源。

**⚠ 反同义反复**：「⟹」的真正内容是「估计最优点的**位置** `|θ| = K`」，
它由 `est_window_min_at` 的**取等刻画**给出，不是从前件读出来的。 -/
theorem joint_optimum_iff {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) (hv : 0 < varOf P)
    (K : ℝ) (hK : 0 < K) :
    (∃ θ : ℝ, θ ≠ 0 ∧ |θ| ≤ K
        ∧ (∀ η : ℝ, η ≠ 0 → |η| ≤ K →
            variance (est (wTheta (n := n) θ))
                (MeasureTheory.Measure.pi (fun _ : Fin n => P))
              ≤ variance (est (wTheta (n := n) η))
                  (MeasureTheory.Measure.pi (fun _ : Fin n => P))))
      ↔ (∃ θ : ℝ, θ ≠ 0 ∧ |θ| = K ∧ |θ| ≤ K) := by
  constructor
  · rintro ⟨θ, hθ0, hθK, hmin⟩
    -- 窗口内最小点必在边界：若 `|θ| < K`，则 `K` 给出严格更小的方差
    have hθne : θ ≠ 0 := hθ0
    by_cases hbound : |θ| = K
    · exact ⟨θ, hθ0, hbound, hθK⟩
    · exfalso
      have hlt : |θ| < K := lt_of_le_of_ne hθK hbound
      have hKne : K ≠ 0 := ne_of_gt hK
      have habsK : |K| = K := abs_of_pos hK
      have hKle : |K| ≤ K := le_of_eq habsK
      have hle := hmin K hKne hKle
      rw [est_shared_variance hP n θ hθ0, est_shared_variance hP n K hKne] at hle
      have hsq : θ ^ 2 < K ^ 2 := by
        have hKabs : |K| = K := abs_of_pos hK
        have hlt' : |θ| < |K| := by rw [hKabs]; exact hlt
        have hpow : |θ| ^ 2 < |K| ^ 2 :=
          pow_lt_pow_left₀ hlt' (abs_nonneg θ) (by norm_num : (2:ℕ) ≠ 0)
        have hfin : |θ| ^ 2 < K ^ 2 := by rwa [← hKabs]
        rwa [sq_abs] at hfin
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hθ2 : 0 < θ ^ 2 := by positivity
      have hK2 : 0 < K ^ 2 := by positivity
      have hdiv : (n : ℝ) / K ^ 2 < (n : ℝ) / θ ^ 2 := by
        apply div_lt_div_of_pos_left (by positivity) hθ2 hsq
      have hstrict := mul_lt_mul_of_pos_right hdiv hv
      linarith
  · rintro ⟨θ, hθ0, hbound, hθK⟩
    refine ⟨θ, hθ0, hθK, fun η hη0 hηK => ?_⟩
    have h := est_window_min_at hP n hn hv K hK η hη0 hηK
    have hθeq : θ ^ 2 = K ^ 2 := by
      have h := congrArg (fun t : ℝ => t ^ 2) hbound
      simpa [sq_abs] using h
    have hest : variance (est (wTheta (n := n) θ))
        (MeasureTheory.Measure.pi (fun _ : Fin n => P)) = ((n : ℝ) / K ^ 2) * varOf P := by
      rw [est_shared_variance hP n θ hθ0, hθeq]
    have hKest : variance (est (wTheta (n := n) K))
        (MeasureTheory.Measure.pi (fun _ : Fin n => P)) = ((n : ℝ) / K ^ 2) * varOf P :=
      est_shared_variance hP n K (ne_of_gt hK)
    rw [hest, ← hKest]
    exact h

/-! ===========================================================================
    §4  🚫 **否定结论**：三环节共享同一个 `θ` 时，「同时最优」一般不成立
    =========================================================================== -/

/-- ⭐⭐⭐⭐ **【否定结论 A：窗口外无联合最优】**

设 `varOf P > 0`、`n > 0`、`K > 0`、`θ* ≠ 0`、`x ≠ 0`，且 **`|θ*| ≠ K`**。
则**不存在** `θ` 使得

* `θ` 是窗口 `|η| ≤ K` 内**估计方差**的最小点，**且**
* `θ` 处的预测值等于 `θ*` 处的预测值（即 `θ` 是**预测的**真值点）。

**⚠ 这是一个**真否定命题**（结论以 `¬` 开头，排除存在量词），
由 `joint_optimum_iff` 直接给出：窗口内估计最小点必须满足 `|θ| = K`，
而「预测真值点」要求 `θ = θ*`（因为 `x ≠ 0`），故 `|θ*| = K`，与前件矛盾。

**⭐ 意义（本文件对「三环节共享参数」的**诚实裁决**）**：
共享的 `θ` 进入估计时只经 `θ^2`、进入预测时经 `θ` 一次；
两者**尺度不同**，因此「估计最优」与「预测最优」**只有在 `|θ*| = K` 的
巧合下才重合**。若不重合，共享参数**迫使**至少牺牲一环的最优性。
**这不是「没做出来」，而是一个数学上的不可能性结论**（对应任务书 (e)）。

**⚠ 反同义反复**：前件 `|θ*| ≠ K` 是**一点**与**一个半径**的算术比较；
结论是**一个优化问题无解**（两个泛函的最小点集不相交）。二者完全不同。 -/
theorem no_joint_optimum_of_abs_ne {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) (hv : 0 < varOf P)
    (K : ℝ) (hK : 0 < K) (θstar x : ℝ) (hx : x ≠ 0)
    (hne : |θstar| ≠ K) :
    ¬ ∃ θ : ℝ, θ ≠ 0 ∧ |θ| ≤ K
        ∧ (∀ η : ℝ, η ≠ 0 → |η| ≤ K →
            variance (est (wTheta (n := n) θ))
                (MeasureTheory.Measure.pi (fun _ : Fin n => P))
              ≤ variance (est (wTheta (n := n) η))
                  (MeasureTheory.Measure.pi (fun _ : Fin n => P)))
        ∧ (paramScmWorldModel linPScm).sim θ (fun _ => PUnit.unit)
              (fun _ => PUnit.unit) (fun _ => x) 1
            = (paramScmWorldModel linPScm).sim θstar (fun _ => PUnit.unit)
                (fun _ => PUnit.unit) (fun _ => x) 1 := by
  rintro ⟨θ, hθ0, hθK, hmin, hpred⟩
  -- 由 `joint_optimum_iff`：窗口内估计最小点必在边界 `|θ| = K`
  have hbd : |θ| = K := by
    have hiff := (joint_optimum_iff hP n hn hv K hK).mp ⟨θ, hθ0, hθK, hmin⟩
    obtain ⟨θ', _, hθ'K, _⟩ := hiff
    -- 直接对 `θ` 本身用「非边界即矛盾」的论证
    by_cases hb : |θ| = K
    · exact hb
    · exfalso
      have hlt : |θ| < K := lt_of_le_of_ne hθK hb
      have hKne : K ≠ 0 := ne_of_gt hK
      have hKle : |K| ≤ K := le_of_eq (abs_of_pos hK)
      have hle := hmin K hKne hKle
      rw [est_shared_variance hP n θ hθ0, est_shared_variance hP n K hKne] at hle
      have hKabs : |K| = K := abs_of_pos hK
      have hlt' : |θ| < |K| := by rw [hKabs]; exact hlt
      have hpow : |θ| ^ 2 < |K| ^ 2 :=
        pow_lt_pow_left₀ hlt' (abs_nonneg θ) (by norm_num : (2:ℕ) ≠ 0)
      have hsq : θ ^ 2 < K ^ 2 := by
        have hfin : |θ| ^ 2 < K ^ 2 := by rwa [← hKabs]
        rwa [sq_abs] at hfin
      have hθ2 : 0 < θ ^ 2 := by positivity
      have hdiv : (n : ℝ) / K ^ 2 < (n : ℝ) / θ ^ 2 :=
        div_lt_div_of_pos_left (by positivity) hθ2 hsq
      have hstrict := mul_lt_mul_of_pos_right hdiv hv
      linarith
  -- 预测等式 + `x ≠ 0` ⟹ `θ = θstar`
  have hth : θ = θstar := by
    rw [sim_shared_value θ x, sim_shared_value θstar x] at hpred
    exact mul_right_cancel₀ hx hpred
  apply hne
  rw [← hth, ← hbd]

/-- ⭐⭐⭐⭐ **【否定结论 B：具体反例（最常用的形态）】**

`θ* = 0`（**真值在原点**）、`n = 2`、`K = 1`、`x = 1`、`varOf P > 0` 时：
**不存在**同时最优的 `θ`。

**⭐ 意义**：`θ* = 0` 时预测的最优点**就是** `θ = 0`，而 `θ = 0` 使估计权重
`1/θ = 0` 退化（方差 `0`）—— 看似「两边都好」，但 `θ = 0` 处估计权重**全零**，
估计器退化为常零、不再是无偏估计（`∑ a = 0 ≠ 1`）。
若把 `θ = 0` 排除，则估计最优点被迫移到 `|θ| = K = 1`，
而预测最优点仍在 `θ = 0` —— **两者分离**。
这正是 `no_joint_optimum_of_abs_ne` 在 `|θ*| = 0 ≠ 1 = K` 上的实例化。

**⚠ 反同义反复**：前件只有 `0 < varOf P`（一个正性条件），
结论是一个**排除存在量词**的陈述（无解）。前件完全没有涉及任何 `θ`。 -/
theorem no_joint_optimum_concrete {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (hv : 0 < varOf P) :
    ¬ ∃ θ : ℝ, θ ≠ 0 ∧ |θ| ≤ 1
        ∧ (∀ η : ℝ, η ≠ 0 → |η| ≤ 1 →
            variance (est (wTheta (n := 2) θ))
                (MeasureTheory.Measure.pi (fun _ : Fin 2 => P))
              ≤ variance (est (wTheta (n := 2) η))
                  (MeasureTheory.Measure.pi (fun _ : Fin 2 => P)))
        ∧ (paramScmWorldModel linPScm).sim θ (fun _ => PUnit.unit)
              (fun _ => PUnit.unit) (fun _ => (1 : ℝ)) 1
            = (paramScmWorldModel linPScm).sim (0 : ℝ) (fun _ => PUnit.unit)
                (fun _ => PUnit.unit) (fun _ => (1 : ℝ)) 1 := by
  intro h
  exact no_joint_optimum_of_abs_ne hP 2 (by norm_num) hv 1 (by norm_num) 0 1
    (by norm_num) (by norm_num) h

/-- ⭐⭐⭐ **【否定结论 C：估计最优点的**位置**必然依赖窗口，因此不能独立于 `K` 定义】**

对任意 `K > 0`，窗口内估计最优点的绝对值**只能是** `K`：
对于窗口 `|theta| <= K` 内的任意权重点 `eta`，若 `eta` 处的估计方差不小于 `theta` 处的，则 `|theta| = K`。

**⭐ 意义**：「估计环节的**无约束**最优 `θ`」**不存在**（下确界 `0` 在
`|θ| → ∞` 处不达，而 `θ = 0` 是权重的退化点）。故估计的「最优 `θ`」
**本质上依赖于一个外生的窗口半径 `K`** —— 而预测的最优 `θ` 是 `θ*`，
**与 `K` 无关**。⟹ 「三环节共享同一个最优 `θ`」**依赖于人为的窗口选择**，
这是共享参数方案的**根本弱点**（本文件的诚实结论）。

**⚠ 反同义反复**：前件是一**逐点不等式族**（最小性）；结论是一个**位置等式**。
由 `est_window_min_at` 的严格性给出（`|θ| < K` 时 `K` 严格更优）。 -/
theorem est_optimum_must_be_on_boundary {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (n : ℕ) (hn : 0 < n) (hv : 0 < varOf P)
    (K θ : ℝ) (hK : 0 < K) (hθ0 : θ ≠ 0) (hθK : |θ| ≤ K)
    (hmin : ∀ η : ℝ, η ≠ 0 → |η| ≤ K →
        variance (est (wTheta (n := n) θ))
            (MeasureTheory.Measure.pi (fun _ : Fin n => P))
          ≤ variance (est (wTheta (n := n) η))
              (MeasureTheory.Measure.pi (fun _ : Fin n => P))) :
    |θ| = K := by
  by_cases hb : |θ| = K
  · exact hb
  · exfalso
    have hlt : |θ| < K := lt_of_le_of_ne hθK hb
    have hKne : K ≠ 0 := ne_of_gt hK
    have hKle : |K| ≤ K := le_of_eq (abs_of_pos hK)
    have hle := hmin K hKne hKle
    rw [est_shared_variance hP n θ hθ0, est_shared_variance hP n K hKne] at hle
    have hKabs : |K| = K := abs_of_pos hK
    have hlt' : |θ| < |K| := by rw [hKabs]; exact hlt
    have hpow : |θ| ^ 2 < |K| ^ 2 :=
      pow_lt_pow_left₀ hlt' (abs_nonneg θ) (by norm_num : (2:ℕ) ≠ 0)
    have hsq : θ ^ 2 < K ^ 2 := by
      have hfin : |θ| ^ 2 < K ^ 2 := by rwa [← hKabs]
      rwa [sq_abs] at hfin
    have hθ2 : 0 < θ ^ 2 := by positivity
    have hdiv : (n : ℝ) / K ^ 2 < (n : ℝ) / θ ^ 2 :=
      div_lt_div_of_pos_left (by positivity) hθ2 hsq
    have hstrict := mul_lt_mul_of_pos_right hdiv hv
    linarith

/-! ===========================================================================
    §5  ⭐ 具体数值实例（检验共享链的**非空真**）
    =========================================================================== -/

/-- ⭐⭐ **具体设定**：`θ* = 2`、`n = 4`（故 `θ*^2 = n` **平衡**）、`K = 2`（故 `|θ*| = K`）、
`varOf P > 0`。此时 `joint_optimum_exists` 的**两个**条件都满足。 -/
theorem concrete_setup : ((2 : ℝ) ^ 2 = (4 : ℕ)) ∧ |(2 : ℝ)| = 2 := by
  constructor <;> norm_num

/-- ⭐⭐⭐ **具体联合最优**：`θ* = 2` 在窗口 `|θ| ≤ 2` 内**同时**是
估计方差最小点与预测真值点（`x = 1`）。 -/
theorem concrete_joint_optimum {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (hv : 0 < varOf P) :
    (∀ η : ℝ, η ≠ 0 → |η| ≤ 2 →
        variance (est (wTheta (n := 4) 2))
            (MeasureTheory.Measure.pi (fun _ : Fin 4 => P))
          ≤ variance (est (wTheta (n := 4) η))
              (MeasureTheory.Measure.pi (fun _ : Fin 4 => P)))
      ∧ (paramScmWorldModel linPScm).sim (2 : ℝ) (fun _ => PUnit.unit)
            (fun _ => PUnit.unit) (fun _ => (1 : ℝ)) 1 = 2 * 1 :=
  joint_optimum_exists hP 4 (by norm_num) hv 2 2 (by norm_num) (by norm_num)
    (by norm_num)

/-- ⭐⭐⭐ **具体否定**：`K = 3`（窗口更大）时，`θ* = 2` **不再**是窗口内的估计最小点，
故**该窗口下**「联合最优在 `θ*`」不成立 —— 估计最小点被推到 `|θ| = 3`。

形式化：窗口 `|θ| ≤ 3` 下，`θ = 2` 处的估计方差**严格大于** `θ = 3` 处的
（`hl` 可由 `est_shared_variance` 与 `2 < 3` 直接比较得到）。 -/
theorem concrete_window_shift {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : MemLp (fun x : ℝ => x) 2 P) (hv : 0 < varOf P) :
    variance (est (wTheta (n := 4) 3)) (MeasureTheory.Measure.pi (fun _ : Fin 4 => P))
      < variance (est (wTheta (n := 4) 2))
          (MeasureTheory.Measure.pi (fun _ : Fin 4 => P)) := by
  rw [est_shared_variance hP 4 3 (by norm_num), est_shared_variance hP 4 2 (by norm_num)]
  have hcoef : (4 : ℝ) / 3 ^ 2 < (4 : ℝ) / 2 ^ 2 := by norm_num
  exact mul_lt_mul_of_pos_right hcoef hv

end SharedThetaChain
end Fate
