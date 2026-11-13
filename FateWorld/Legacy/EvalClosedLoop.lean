/-
命运理论 · Lean 4 形式化实现
================================

模块：`Fate.EvalClosedLoop`
任务：**【Y4】端到端最小可运行示例**（X7 重做，降低难度）。

===========================================================================
本文件做什么（一句话）
===========================================================================

在 `E = F = ℝ`、`A = id`、`φ = id`、`η = 1/2`、`θ₀ = 10` 这一组**具体数值**上，
用 `WiringConvergence.iterMap` 迭代 **5 步**，用 `#eval` 打印**每一步误差的真实数值**，
并用定理证明这个数列**确实收敛到 0**。

---------------------------------------------------------------------------
具体数字（`#eval` 打印的就是这些）
---------------------------------------------------------------------------

| `k` | `θ_k` | `err_k = ‖A θ_k - x'‖` |
|---|---|---|
| 0 | `10`     | `10`     |
| 1 | `5`      | `5`      |
| 2 | `2.5`    | `2.5`    |
| 3 | `1.25`   | `1.25`   |
| 4 | `0.625`  | `0.625`  |
| 5 | `0.3125` | `0.3125` |

（`x' = 0`；`A = id`，`φ = id`，`η = 1/2` ⟹ `1 - η = 1/2`，误差每步**严格减半**。）

---------------------------------------------------------------------------
上游（只 `import`，一字未改）
---------------------------------------------------------------------------

* `Fate.WiringConvergence`：`stepMap` / `iterMap`（`BoundWriteBack.wbW` 的 `n` 步迭代）、
  `err_iterMap`（`err_n = |1-η|^n · err_0`）、`err_iterMap_le`、`err_iterMap_lt`、
  `closedLoop_rate`、`closedLoop_tendsto_zero`、`closedLoop_converges`。
* `Fate.BoundWriteBack`：`wbW`、`errA`、`Corrects`、`errA_pos_iff`。

---------------------------------------------------------------------------
⚠ 诚实边界（必读，不得含糊）
---------------------------------------------------------------------------

**H1. 本文件是「具体实例 + `#eval`」，不是新理论。**
所有收敛结论都来自 `WiringConvergence`（§5 **调用**它们，不重证）。
本文件的新内容只有：`#eval` 的具体数值、以及**这些数值与上游定理逐位对上**的
一系列 `norm_num` / `decide` 级等式（§3、§4）。

**H2. ⚠ `#eval` 的可计算性与「零 sorry」的处置（本文件最关键的技术点）。**

`ℝ` 在 Lean 里**不是可计算数据类型**：`ℝ` 值的 `#eval` 既不能给出可读数值，
本文件用到的 `iterR` 还是 `noncomputable def`（依赖连续线性算子），
**Lean 会直接拒绝编译对它的 `#eval`**（`lean.dependsOnNoncomputable`）。
（原稿曾声称「`ℝ` 的 `#eval` 会打印 `Real.ofCauchy (sorry …)`」，但那其实
**编译不过** —— 该说法已按事实修正，见 §3 `#eval` 五。）

因此本文件**两路并行**，且**用定理把它们钉在一起**：

| 路 | 载体 | 用途 | 定理 |
|---|---|---|---|
| **A（可算）** | `ℚ`（`Rat`，可计算） | `#eval` 打印**真实数值** | §3 |
| **B（理论）** | `ℝ`（上游 `iterMap` / `errA`）| 收敛到 0 的**定理**（上游主定理）；⚠ **不可 `#eval`** | §5 |
| **桥** | `ℚ → ℝ`（`Rat.cast`）| 两路的数值**逐位相同** | §4 `iterQ_cast` / `errQ_cast` |

**⟹ `#eval` 打印的 `ℚ` 数值 + 桥定理 ⟹ 上游 `ℝ` 定理的具体数值。**
这**不是**两套算法：`stepQ` 与 `stepR` 是同一个仿射映射 `θ ↦ θ * 2⁻¹` 的两处载体，
§4 的 `stepQ_cast : stepQ q = stepR (q : ℝ)` 把这一点钉死。

**H3. 收敛是「几何收敛」（极限），不是有限步归零。**
`η = 1/2` 时 `|1-η| = 1/2 ∈ (0,1)`，`err_k = (1/2)^k · 10 → 0` 但**永不等于 0**
（§6 `errR_pos` 显式证明 `∀ k, 0 < err_k`）。这与 `WiringConvergence` §8.3 的
诚实标注一致：只有 `η = 1` 才一步归零（`WiringConvergence.optimal_one_step`）。

**H4. 观测环节取的是「误差界的值」，不是估计器的构造。**
承 `WiringConvergence §2`：初始误差 `err_0 = 10` 作为**已给定的数值**接入
（`ObsEstimationStrong` 提供「存在估计器使误差 ≤ L η_max」，本文件不重造估计器，
也不声称 `chooseEstimator` 可算——见 `Fate/EvalReal.lean` H1）。

**H5. 本文件不声称任何经验结论。** 数值是形式化对象的值。

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
- **零 `sorry` / 零 `admit` / 零 `axiom`**（文末 `#print axioms` 逐条核验）。
- **只新增本文件**，不修改任何已有模块。
- 本文件**无删减项**：所有陈述的定理均已证出（本次修复见文末 §7 修复记录）。
-/

import FateWorld.Legacy.WiringConvergence
import Batteries.Data.Rat

namespace Fate

namespace EvalClosedLoop

open BoundWriteBack
open WiringConvergence

/-! ===========================================================================
    §1  A 路：可计算的 `ℚ` 版本（`#eval` 的对象）

    迭代映射取 `stepQ θ = θ * 2⁻¹`，即 `wbW id id (1/2) 0` 在 `ℝ` 上的裸读法
    （§4 `stepQ_cast_stepR` 给出与上游 `stepMap` 的逐位对应）。
    =========================================================================== -/

/-- 步长因子 `1 - η = 1/2`（`ℚ` 版，可计算）。 -/
def halfQ : ℚ := 1 / 2

/-- A 路的**一步更新**：`stepQ θ = θ * (1/2)`。

与 `wbW id id (1/2) 0 θ = θ + (1/2) * (0 - θ) = θ * (1/2)` 是**同一个仿射映射**。 -/
def stepQ (θ : ℚ) : ℚ := θ * halfQ

/-- A 路的 **`n` 步迭代**（`iterMap` 在 `ℚ` 上的可计算镜像）。 -/
def iterQ : ℕ → ℚ → ℚ
  | 0, θ => θ
  | n + 1, θ => iterQ n (stepQ θ)

/-- ⭐ `iterQ` 就是 `Nat.iterate stepQ`（上游 `iterMap` 的结构形态）。 -/
theorem iterQ_eq_iterate (n : ℕ) (θ : ℚ) : iterQ n θ = stepQ^[n] θ := by
  induction n generalizing θ with
  | zero => rfl
  | succ k ih =>
    show iterQ k (stepQ θ) = stepQ^[k + 1] θ
    rw [ih, ← Function.iterate_succ_apply]

/-- A 路的**误差镜像**：`errQ θ = |A θ - x'| = |θ|`（`x' = 0`）。 -/
def errQ (θ : ℚ) : ℚ := |θ|

/-- 初始参数 `θ₀ = 10`（`ℚ` 版）。 -/
def theta0Q : ℚ := 10

/-! ===========================================================================
    §2  B 路：`ℝ` 版本（上游定理的载体）
    =========================================================================== -/

/-- 预测器 `A`：`ℝ` 上的恒等（连续线性算子）。 -/
noncomputable def predId : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

/-- 方向映射 `φ`：`ℝ` 上的恒等（线性映射）。 -/
def phiId : ℝ →ₗ[ℝ] ℝ := LinearMap.id

/-- 步长 `η = 1/2`。 -/
noncomputable def eta : ℝ := 1 / 2

/-- 观测真值 `x' = 0`。 -/
def xObs : ℝ := 0

/-- 初始参数 `θ₀ = 10`。 -/
def theta0R : ℝ := 10

/-- B 路的 **`n` 步迭代**：**就是上游 `WiringConvergence.iterMap`**。 -/
noncomputable def iterR (n : ℕ) (θ : ℝ) : ℝ :=
  iterMap predId phiId eta xObs n θ

/-- B 路的**误差**：**就是上游 `BoundWriteBack.errA`**。

⚠ 需 `noncomputable`：`errA` 用 `‖·‖`，在 `ℝ` 上走 `RCLike.toInnerProductSpaceReal`
（非可计算实例）。这只是编译标志，**不改变陈述**。 -/
noncomputable def errR (θ : ℝ) : ℝ := errA predId xObs θ

/-- ⭐ **`Corrects` 在本实例上成立**（`A = id`、`φ = id`；承
`BoundWriteBack.corrects_id`，这里在本文件的 `predId` / `phiId` 上再钉一次）。 -/
theorem corrects_predId : Corrects predId phiId := by
  intro r
  simp [predId, phiId]

/-- ⭐ 步长在收缩窗内：`|1 - η| < 1`。 -/
theorem eta_window : |1 - eta| < 1 := by
  norm_num [eta]

/-! ===========================================================================
    §3  ⭐⭐ `#eval`：迭代 5 步，打印每一步的**真实数值**（`ℚ` 路，输出无 `sorry`）
    =========================================================================== -/

/-! **`#eval` 一：参数** `θ₀ … θ₅`。**本文件的核心数值输出。** -/
#eval (List.map (fun k => iterQ k theta0Q) [0, 1, 2, 3, 4, 5])

/-! **`#eval` 二：每步误差** `err_0 … err_5`（= `10, 5, 2.5, 1.25, 0.625, 0.3125`）。 -/
#eval (List.map (fun k => errQ (iterQ k theta0Q)) [0, 1, 2, 3, 4, 5])

/-! **`#eval` 三：整张表** `(k, θ_k, err_k)`。 -/
#eval (List.map (fun k => (k, iterQ k theta0Q, errQ (iterQ k theta0Q))) [0, 1, 2, 3, 4, 5])

/-! **`#eval` 四：误差/前一步误差**，恒为 `1/2`（收缩因子 `|1-η|` 的数值证据）。 -/
#eval (List.map (fun k => iterQ (k + 1) theta0Q / iterQ k theta0Q) [0, 1, 2, 3, 4])

/-! **`#eval` 五：`ℝ` 路 —— ⚠ 无法 `#eval`，改用 `#check` 登记（如实修正）**

原稿此处是 `#eval (List.map (fun k => iterR k theta0R) [0, 1, 2, 3, 4, 5])`，
但 `iterR` 是 `noncomputable def`（依赖 `WiringConvergence.iterMap` 里的连续线性算子），
Lean 直接拒绝编译该 `#eval`（`lean.dependsOnNoncomputable`）。
**故本文件不再声称「`ℝ` 路可 `#eval`、只是带 `sorry` 占位」**（那是错的：
它根本不可编译）。`ℝ` 路的数值一律通过 §4 的桥定理
（`iterQ_cast` / `errQ_cast`）从 `ℚ` 路**证明**迁移，而不是打印。 -/
#check @iterR
#check @errR

/-! ===========================================================================
    §4  ⭐⭐⭐ 桥：`ℚ` 路与 `ℝ` 路**逐位相同**（把 `#eval` 接到上游定理上）
    =========================================================================== -/

/-- ⭐ **步长相等**：`(1/2 : ℚ)` 在 `ℝ` 里的像是 `|1 - η|`。 -/
theorem halfQ_cast : ((halfQ : ℚ) : ℝ) = |1 - eta| := by
  unfold halfQ eta
  norm_num

/-- ⭐⭐ **一步相等**：`stepQ` 在 `ℝ` 下的像恰是 `stepMap predId phiId eta xObs`
（即 `wbW id id (1/2) 0`）。

**⟹ `ℚ` 路与 `ℝ` 路**不是**两套算法，是同一个仿射映射。 -/
theorem stepQ_cast_stepR (q : ℚ) :
    ((stepQ q : ℚ) : ℝ) = stepMap predId phiId eta xObs (q : ℝ) := by
  rw [stepMap_eq_wbW, wbW_apply]
  simp only [stepQ, predId, phiId, xObs, ContinuousLinearMap.id_apply, LinearMap.id_apply,
    map_sub, map_zero]
  push_cast
  unfold halfQ eta
  push_cast
  ring

/-- ⭐⭐⭐ **`n` 步相等**：`(iterQ n θ : ℝ) = iterR n (θ : ℝ)`。

**这是本文件的关键桥**：`#eval` 打印的 `ℚ` 迭代值，
在 `ℝ` 里**逐位等于**上游 `WiringConvergence.iterMap` 的迭代值。 -/
theorem iterQ_cast (n : ℕ) (θ : ℚ) : ((iterQ n θ : ℚ) : ℝ) = iterR n (θ : ℝ) := by
  induction n generalizing θ with
  | zero => rfl
  | succ k ih =>
    show ((iterQ k (stepQ θ) : ℚ) : ℝ) = iterR k (stepMap predId phiId eta xObs (θ : ℝ))
    rw [ih, stepQ_cast_stepR]

/-- ⭐⭐ **误差相等**：`(errQ θ : ℝ) = errR (θ : ℝ)`。 -/
theorem errQ_cast (θ : ℚ) : ((errQ θ : ℚ) : ℝ) = errR (θ : ℝ) := by
  simp only [errQ, errR, errA, predId, xObs, ContinuousLinearMap.id_apply, sub_zero]
  rw [Rat.cast_abs, Real.norm_eq_abs]

/-! ===========================================================================
    §5  ⭐⭐⭐⭐ 收敛到 0（**调用**上游定理）
    =========================================================================== -/

/-- ⭐⭐⭐ **误差 → 0（`ℝ` 路）**：`WiringConvergence.closedLoop_tendsto_zero` 的实例。

$$\lim_{n\to\infty} \mathrm{err}_n \;=\; 0 .$$

**前提**：`corrects_predId`（`Corrects`，本文件 §2 已证）与
`eta_window`（`|1-η| < 1`，本文件 §2 已证）。 -/
theorem errR_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => errR (iterR n theta0R)) Filter.atTop (nhds 0) := by
  have h : (fun n : ℕ => errR (iterR n theta0R))
      = fun n : ℕ => errA predId xObs (iterMap predId phiId eta xObs n theta0R) := rfl
  rw [h]
  exact closedLoop_tendsto_zero predId phiId eta xObs theta0R corrects_predId eta_window

/-- ⭐⭐⭐ **误差 → 0（`ℚ` 路，即 `#eval` 打印的那个量的 `ℝ` 像）**。 -/
theorem errQ_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => ((errQ (iterQ n theta0Q) : ℚ) : ℝ))
      Filter.atTop (nhds 0) := by
  have h : (fun n : ℕ => ((errQ (iterQ n theta0Q) : ℚ) : ℝ))
      = fun n : ℕ => errR (iterR n (theta0Q : ℝ)) := by
    funext n
    rw [errQ_cast, iterQ_cast]
  rw [h]
  have h0 : ((theta0Q : ℚ) : ℝ) = theta0R := by
    unfold theta0Q theta0R
    norm_num
  rw [h0]
  exact errR_tendsto_zero

/-- ⭐⭐⭐ **ε-形式**（不依赖 filter 语言）：对任意 `ε > 0`，存在 `N`，
使一切 `n ≥ N` 满足 `err_n < ε`。这是「收敛到 0」最朴素的读法。 -/
theorem errR_eventually_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → errR (iterR n theta0R) < ε := by
  have h := (Metric.tendsto_atTop.mp errR_tendsto_zero) ε hε
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  have h2 := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg] at h2
  · exact h2
  · unfold errR errA predId xObs
    simp

/-! ### §5.1  闭式与速率（全称，不止前 5 步） -/

/-- ⭐⭐ **`ℚ` 路的闭式**：`iterQ n θ = θ * (1/2)^n`。 -/
theorem iterQ_closed_form (n : ℕ) (θ : ℚ) : iterQ n θ = θ * halfQ ^ n := by
  induction n generalizing θ with
  | zero => simp [iterQ]
  | succ k ih =>
    show iterQ k (stepQ θ) = θ * halfQ ^ (k + 1)
    rw [ih, pow_succ]
    simp only [stepQ]
    ring

/-- ⭐⭐ **具体初始值的闭式**：`θ_n = (1/2)^n · 10`（`ℚ`）。 -/
theorem iterQ_theta0 (n : ℕ) : iterQ n theta0Q = halfQ ^ n * 10 := by
  rw [iterQ_closed_form]
  unfold theta0Q
  ring

/-- ⭐ **`ℝ` 路的速率**（`closedLoop_rate` 的实例）：
`err_n ≤ (1/2)^n · 10`。 -/
theorem errR_rate (n : ℕ) : errR (iterR n theta0R) ≤ (1 / 2) ^ n * 10 := by
  have h0 : errA predId xObs theta0R ≤ 10 * 1 := by
    have : errA predId xObs theta0R = 10 := by
      unfold theta0R errA predId xObs
      simp
    linarith
  have h := closedLoop_rate predId phiId eta xObs theta0R corrects_predId eta_window.le
    (L := 10) (ηmax := 1) h0 n
  have h' : |1 - eta| = 1 / 2 := by unfold eta; norm_num
  rw [h'] at h
  simpa [errR, iterR] using h

/-- ⭐ **单调不增**（`err_iterMap_le` 的实例）。 -/
theorem errR_mono (n : ℕ) : errR (iterR n theta0R) ≤ errR theta0R := by
  exact err_iterMap_le predId phiId eta xObs theta0R corrects_predId eta_window.le n

/-- ⭐⭐ **严格下降**（`err_iterMap_lt` 的实例，`n ≥ 1`）：每走一步误差都严格变小。 -/
theorem errR_strict_mono {n : ℕ} (hn : 0 < n) :
    errR (iterR n theta0R) < errR theta0R := by
  have hpos : 0 < errA predId xObs theta0R := by
    rw [errA_pos_iff]
    unfold predId xObs theta0R
    simp
  exact err_iterMap_lt predId phiId eta xObs theta0R corrects_predId eta_window hpos hn

/-- ⭐⭐⭐ **三合一（本实例）**：速率 + 收敛 + 单调，直接取
`WiringConvergence.closedLoop_converges` 在
`A = id`、`φ = id`、`η = 1/2`、`θ₀ = 10`、`L = 10`、`ηmax = 1` 上的实例。 -/
theorem closed_loop_instance :
    (∀ n : ℕ, errR (iterR n theta0R) ≤ (1 / 2) ^ n * 10)
    ∧ Filter.Tendsto (fun n : ℕ => errR (iterR n theta0R)) Filter.atTop (nhds 0)
    ∧ (∀ n : ℕ, errR (iterR n theta0R) ≤ 10) := by
  refine ⟨errR_rate, errR_tendsto_zero, fun n => ?_⟩
  refine le_trans (errR_rate n) ?_
  have hp : (1 / 2 : ℝ) ^ n ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

/-! ===========================================================================
    §6  ⚠ 「不有限步归零」+ 确切减半
    =========================================================================== -/

/-- ⭐⭐ **误差恒正**：`∀ n, 0 < err_n`（H3 的严格形式）。

**⟹ 本实例的收敛是几何极限，不是有限步归零。本文件不声称有限步归零。** -/
theorem errR_pos (n : ℕ) : 0 < errR (iterR n theta0R) := by
  have := err_iterMap predId phiId eta xObs theta0R corrects_predId n
  have h0 : errA predId xObs theta0R = 10 := by
    unfold errA predId xObs theta0R
    simp
  rw [h0] at this
  have h' : |1 - eta| = 1 / 2 := by unfold eta; norm_num
  rw [h'] at this
  rw [errR, iterR]
  rw [this]
  positivity

/-- ⭐⭐ **确切减半**：`err_{n+1} = (1/2) · err_n`（每步**恰好**减半，不是近似）。 -/
theorem errR_halves (n : ℕ) : errR (iterR (n + 1) theta0R) = (1 / 2) * errR (iterR n theta0R) := by
  rw [errR, iterR, errR, iterR, err_iterMap predId phiId eta xObs theta0R corrects_predId (n + 1),
    err_iterMap predId phiId eta xObs theta0R corrects_predId n]
  have h' : |1 - eta| = 1 / 2 := by unfold eta; norm_num
  rw [h', pow_succ]
  ring

/-! ===========================================================================
    §7  ⚠ 诚实登记：本文件**没做**的事
    =========================================================================== -/

/-!
| # | 未做项 | 原因 |
|---|---|---|
| 1 | 在 `Fate.EvalReal.eWorldModel` 上把 `EndToEnd.endToEnd` **逐值**接成本实例 | 承 `WiringConvergence §8.3` 未做项 1：`EndToEnd` 的残差（观测 − 世界模型预测，`ℤ` 载体）与本文件的线性残差（`x' - A θ`，`ℝ` 载体）**语义与载体都不同**；逐值等同需要新的 `WorldModel` 实例，超出「最小可运行示例」范围 |
| 2 | 「有限步归零」 | **数学上是假的**（§6 `errR_pos` 对一切 `n` 证 `err_n > 0`）；`η = 1/2` 只有几何收敛。`η = 1` 的一步归零见 `WiringConvergence.optimal_one_step` |
| 3 | `#eval` 直接打印 `ℝ` 值且输出无 `sorry` | **Lean 层面不可能**：`Real.ofCauchy` 的打印必带 `sorry` 占位（H2）。故本文件用 `ℚ` 路 `#eval` + §4 的桥定理把数值搬到 `ℝ`，**不**假装 `ℝ` 可 `#eval` |
| 4 | `chooseEstimator` 的可计算性 | 承 `Fate/EvalReal.lean` H1；本文件只把 `err_0 = 10` 当**已给定**的初始数值接入（H4）|
| 5 | 经验结论 | 本文件只有形式化对象的值（H5）|

**⚠ 本文件零 `sorry` / 零 `admit` / 零 `axiom`。**
共 18 条定理，全部证出（下附公理核验，均只依赖 `propext` / `Classical.choice` / `Quot.sound`）。

**修复记录（本次，如实登记，未改任何定理陈述）**：
1. `iterQ_eq_iterate`（原 122 行 `unsolved goals`）：归纳步原用 `Function.iterate_succ_apply'`，
   方向不对；改为 `← Function.iterate_succ_apply`。
2. `#eval` 五（原 156 行 `lean.dependsOnNoncomputable`）：`iterR` 不可 `#eval`，
   原稿「`ℝ` 的 `#eval` 会打印带 `sorry` 的 `Real.ofCauchy`」的说法**不成立**
   （它编译不过）。已改为 `#check @iterR` / `#check @errR` 登记，并同步修正 H2。
3. `errR`（原 186 行同上错误）：加 `noncomputable`（`errA` 经 `‖·‖` 依赖
   `RCLike.toInnerProductSpaceReal`）。**仅编译标志，陈述不变**。
4. `errQ_cast`（原 223 行 `|↑θ| = ‖↑θ‖`）：`simp` 后补 `Real.norm_eq_abs`。
5. `closed_loop_instance`（原 328 行 `linarith` 失败）：第三支需 `(1/2)^n ≤ 1`，
   补 `pow_le_one₀`。
-/

/-! ### §7.1 公理核验（每一条定理只依赖 Lean 的三条标准公理） -/

#print axioms Fate.EvalClosedLoop.iterQ_eq_iterate
#print axioms Fate.EvalClosedLoop.corrects_predId
#print axioms Fate.EvalClosedLoop.eta_window
#print axioms Fate.EvalClosedLoop.halfQ_cast
#print axioms Fate.EvalClosedLoop.stepQ_cast_stepR
#print axioms Fate.EvalClosedLoop.iterQ_cast
#print axioms Fate.EvalClosedLoop.errQ_cast
#print axioms Fate.EvalClosedLoop.errR_tendsto_zero
#print axioms Fate.EvalClosedLoop.errQ_tendsto_zero
#print axioms Fate.EvalClosedLoop.errR_eventually_lt
#print axioms Fate.EvalClosedLoop.iterQ_closed_form
#print axioms Fate.EvalClosedLoop.iterQ_theta0
#print axioms Fate.EvalClosedLoop.errR_rate
#print axioms Fate.EvalClosedLoop.errR_mono
#print axioms Fate.EvalClosedLoop.errR_strict_mono
#print axioms Fate.EvalClosedLoop.closed_loop_instance
#print axioms Fate.EvalClosedLoop.errR_pos
#print axioms Fate.EvalClosedLoop.errR_halves

end EvalClosedLoop

end Fate
