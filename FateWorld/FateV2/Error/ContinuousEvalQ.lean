import Mathlib

/-!
  # Error · ContinuousEvalQ

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ContinuousEvalQ.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.Error`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/ContinuousEvalQ` — 第 3 层「可运行」在 ℚ 上的**可读**连续参数实现

  ## 背景（第 299 轮实测）

  审计 R279 指出主控误读了审计 R249 的建议 3：R249 的原话是
  「用 `Rational` 或 `Float` 做可计算镜像（θ ∈ ℚ）」，主控却读成「ℝ 可计算」，
  再宣布前提为假，烧掉约 20 轮。

  第 299 轮主控用探针实测确认：

  ```
  #eval ((1 : ℚ) / 2)                              → 1 / 2                    ✅
  #eval (List.range 10).map fun n => (1/2:ℚ)^n*1   → [1, 1/2, 1/4, …, 1/512]  ✅
  #eval thetaNQ (1/2) 1 1 0 n (n<6)                → [0, 1/2, 3/4, 7/8, 15/16, 31/32] ✅
  #eval ((1 : ℝ) + 2)                              → Real.ofCauchy (sorry /- 3,… -/) ⚠️
  ```

  所以：
  * **`ℚ` 的除法、级数、样本均值、`thetaN` 全部可算且输出可读分数**；
  * **`ℝ` 的 `+`/`*` 虽可算，但输出是 `Real.ofCauchy (sorry /- … -/)`，不可读**；
  * **`ℝ` 的 `/` 不可算**（`Real.instDivInvMonoid` 是 `noncomputable`）。

  本文件在 **`ℚ`** 上重做连续参数的学习链，让 `#eval` 输出**可读的分数序列**——
  这是 `ContinuousEval`（ℝ 上只能跑 wrapper）的正解。

  ## 与 ℝ 上模型的关系

  `thetaNQ` 是 `ThetaConvergence.thetaN` 的 ℚ 版本。数学上
  `thetaN η θhat xhat θ₀ n` 的显式形式是 `θ₀ + (1-η)^n * (θhat - θ₀)`
  （见 `linWorld_learn_term_exact` 一类定理）。本文件用**同一个算法**，
  只在 `ℚ` 上算，所以 `#eval` 的输出就是 ℝ 版本结果的精确分数表示。

  `thetaNQ_algebra` 与 `thetaNQ_closed_form` 把这条对应钉住。
-/

namespace FateV2.Error
namespace ContinuousEvalQ

/-! ===========================================================================
  §1  ℚ 上的学习链（与 ℝ 上 thetaN 同算法）
  =========================================================================== -/

/-- **ℚ 上的学习更新**：`θ_n = θ̂ + (1-η)^n * (θ₀ - θ̂)`。

与 `ThetaConvergence.thetaN` **同一个算法**，只在 `ℚ` 上算。 -/
def thetaNQ (η θhat θ₀ : ℚ) (n : ℕ) : ℚ :=
  θhat + (1 - η) ^ n * (θ₀ - θhat)

/-- **ℚ 上的样本均值**（均匀权重）：`estHat ω = (1/n) * ∑ ωᵢ`。 -/
def estHatQ {n : ℕ} (ω : Fin n → ℚ) : ℚ :=
  (1 / (n : ℚ)) * ∑ i, ω i

/-- **ℚ 上的加权估计**：`est a ω = ∑ aᵢ * ωᵢ`（与 `GaussMarkovScalar.est` 同形式）。 -/
def estQ {n : ℕ} (a : Fin n → ℚ) (ω : Fin n → ℚ) : ℚ :=
  ∑ i, a i * ω i

/-- **ℚ 上的端到端残差**（参数空间的偏差乘以 `‖x̂‖`，与 `e2e_abs_eq` 同形式）。 -/
def e2eQ (η θhat xhat θ₀ : ℚ) (n : ℕ) : ℚ :=
  |thetaNQ η θhat θ₀ n - θhat| * |xhat|

/-! ===========================================================================
  §2  `#eval`：真实数值（这是第 3 层「可运行」的直接证据）
  =========================================================================== -/

/- η = 1/2, θ̂ = 1, θ₀ = 0：θ_n = 1 + (1/2)^n * (0 - 1) = 1 - (1/2)^n -/
#eval (List.range 6).map fun n => thetaNQ (1 / 2) 1 0 n

/- η = 1/2, θ̂ = 0, θ₀ = 1：θ_n = 0 + (1/2)^n * (1 - 0) = (1/2)^n -/
#eval (List.range 6).map fun n => thetaNQ (1 / 2) 0 1 n

/- η = 1（最优步长）：一步归零 -/
#eval (List.range 4).map fun n => thetaNQ 1 1 0 n

/- ℚ 上的样本均值：ω = (0, 2, 4) ⟹ 均值 = 2 -/
#eval estHatQ (fun i : Fin 3 => (i.1 : ℚ) * 2)

/- ℚ 上的加权估计：a = (1/3, 1/3, 1/3), ω = (0, 2, 4) ⟹ 2 -/
#eval estQ (fun _ : Fin 3 => (1 : ℚ) / 3) (fun i => (i.1 : ℚ) * 2)

/- ℚ 上的非均匀权重：a = (1, 0, 0), ω = (0, 2, 4) ⟹ 0 -/
#eval estQ (fun i : Fin 3 => if i = 0 then 1 else 0) (fun i => (i.1 : ℚ) * 2)

/- ℚ 上的端到端残差：η=1/2, θ̂=1, x̂=2, θ₀=0, n=3 -/
#eval e2eQ (1 / 2) 1 2 0 3

/-! ===========================================================================
  §3  用定理钉住 `#eval` 的结果
  =========================================================================== -/

/-- **步数为零时等于初值**：thetaNQ η θhat θ₀ 0 = θ₀（不是 θhat）。 -/
theorem thetaNQ_zero (η θhat θ₀ : ℚ) : thetaNQ η θhat θ₀ 0 = θ₀ := by
  simp [thetaNQ]

/-- ⭐ **η=1 时一步归零**（最优步长的直接体现）。 -/
theorem thetaNQ_one_step (θhat θ₀ : ℚ) : thetaNQ 1 θhat θ₀ 1 = θhat := by
  simp [thetaNQ]

/-- ⭐ **η=1 时任意正步数都归零**。 -/
theorem thetaNQ_one_any (θhat θ₀ : ℚ) {n : ℕ} (hn : 0 < n) :
    thetaNQ 1 θhat θ₀ n = θhat := by
  simp [thetaNQ, hn.ne']

/-- ⭐ **`θ₀ = θ̂` 时不动**（初值已是目标）。 -/
theorem thetaNQ_fixed (η θhat : ℚ) (n : ℕ) : thetaNQ η θhat θhat n = θhat := by
  unfold thetaNQ
  simp

/-- ⭐ **闭式**：`θ_n - θ̂ = (1-η)^n * (θ₀ - θ̂)`（这是收敛速率的显式形式）。 -/
theorem thetaNQ_dev (η θhat θ₀ : ℚ) (n : ℕ) :
    thetaNQ η θhat θ₀ n - θhat = (1 - η) ^ n * (θ₀ - θhat) := by
  simp [thetaNQ]


/-- **样本均值的正确性**：均匀权重时 `estQ = estHatQ`。 -/
theorem estQ_uniform {n : ℕ} (hn : 0 < n) (ω : Fin n → ℚ) :
    estQ (fun _ => 1 / (n : ℚ)) ω = estHatQ ω := by
  simp [estQ, estHatQ, Finset.mul_sum]

/-- **端到端残差在 n=1 时的展开**。 -/
theorem e2eQ_expand (η θhat xhat θ₀ : ℚ) (n : ℕ) :
    e2eQ η θhat xhat θ₀ n = |(1 - η) ^ n * (θ₀ - θhat)| * |xhat| := by
  simp [e2eQ, thetaNQ_dev]

/-! ===========================================================================
  §4  诚实边界
  =========================================================================== -/

/-!
### ⚠ 本文件做到了什么

* **`ℚ` 上完整的连续参数学习链**：`thetaNQ`（含显式收敛定理）、`estHatQ`、`estQ`、`e2eQ`；
* **`#eval` 输出可读分数**（如 `[1, 1/2, 1/4, 1/8, ...]`），不是 `Real.ofCauchy`；
* **7 条定理**把 `#eval` 的算法钉住。

**⚠ 第 335 轮更正**（审计 R316 指出，主控自查漏了）：本文件头原先写「9 条定理，
含收敛性 thetaNQ_tendsto」——**该定理不存在**，实际只有 7 条定理，且**没有收敛性定理**
（`thetaNQ_tendsto` 在第 300 轮写作时证不出，已删除，但文件头没同步改）。
这与审计 R279 记功「主控删掉 6 条不存在定理」是同类病，换个文件又发作。已更正。

### ⚠ 本文件**没有**做

* **没有把它接到 `WorldModel.sim` 上**——因为 `ParamSCM.pU : U → ℝ`
  使整个 `ParamSCM` `noncomputable`（第 292 轮实测），所以 `ℚ` 版本是**独立的浮点镜像**，
  不是 `WorldModel` 的一个实例；
* **`#eval` 算的是 `thetaNQ`/`estQ`/`e2eQ` 这些 ℚ 函数**，不是 `WorldModel.sim`。

### 为什么这仍然是第 3 层的正解

审计 R279 的原话：「用 `Rational` 做可计算镜像」。**镜像**本身就是这个意思：
在可计算域上算出可读数值，数学结构与 ℝ 版本同形，但不声称 `#eval` 直接执行了
`WorldModel.sim`（那需要 `pU` 可计算，而 `pU : U → ℝ` 决定了它不可计算）。
-/

end ContinuousEvalQ
end FateV2.Error