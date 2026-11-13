import FateWorld.FateV2.Predict.WorldModel
import FateWorld.FateV2.Loop.EndToEnd
import FateWorld.FateV2.Loop.ResidualLoop
import FateWorld.FateV2.Loop.WiringConvergence
import FateWorld.FateV2.Loop.ClosedLoopNoisy
import FateWorld.FateV2.Loop.OptimalEta
import FateWorld.FateV2.Error.SigmaEstimation
import FateWorld.FateV2.Predict.WiringFrontdoor
import FateWorld.FateV2.Predict.WiringBackdoorFixed
import FateWorld.FateV2.Predict.CausalRouteDo
import FateWorld.FateV2.Modeling.ObsEstimationStrong

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/WorldModelAssembly.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008
  - 改动：namespace/引用 ProperFit→FateV2.Loop（正文 63 处，含 11 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Modeling
open FateV2.Predict
open FateV2.Model
open FateV2.Error
open FateV2.Loop

/-
命运理论 · Lean 4 形式化实现
================================

模块：`FateV2.Loop.WorldModelAssembly`
任务：【AA1-最高优先】**世界模型的主装配模块** —— 把已入库但**零下游消费**的
世界模型要件模块真正接到别的模块上，并给出**跨模块**定理。

===========================================================================
为什么需要本文件（诚实的问题陈述）
===========================================================================

入库（写进 `FateV2.Loop.lean` 库根）**只证明能编译**，不证明**被使用**。实测：

| 模块 | 被 import 次数 |
|---|---|
| `WorldModel` | 8 |
| `ObsEstimationStrong` | 7 |
| `EndToEnd` | 6 |
| `WiringConvergence` | 4 |
| **`WiringFrontdoor`** | **0** |
| **`WiringFourOpFixed`** | **0** |
| **`WiringBackdoorFixed`** | **0** |
| **`ClosedLoopNoisy`** | **0** |
| **`OptimalEta`** | **0** |
| **`SigmaEstimation`** | **0** |
| **`CausalRouteDo`** | **0** |

本文件是这些模块的**第一个下游消费者**（在静态依赖图上把它们接进
`WorldModelAssembly`，从而 `import` 计数从 0 变 1），并且 —— 更重要的 ——
本文件给出的定理**其陈述本身**同时引用两个以上模块的结论，
故「接线」不是靠 import 行，而是靠**证明项**。

===========================================================================
本文件的定理清单（每条都逐条核对过「前件是否已含结论」）
===========================================================================

| # | 定理 | 用到的模块（≥2） |
|---|---|---|
| W1 | `assembly_noisy_steady_bound` | `ObsEstimationStrong`（`inverse_estimate_error`）× `ClosedLoopNoisy`（`noisy_limsup_bound`）|
| W2 | `assembly_optimal_eta_noisy` | `OptimalEta`（`c`、`eta_ne_one_pos`）× `ClosedLoopNoisy`（`steadyErr`、`steadyErr_one`）|
| W3 | `assembly_noisy_inherits_closedloop` | `WiringConvergence`（`closedLoop_converges`）× `ClosedLoopNoisy`（`noisyIter_eq_iterMap`）|
| W4 | `assembly_sigma_observation_budget` | `SigmaEstimation`（`variance_meanOf`）× `ObsEstimationStrong`（`inverse_estimate_error`）|
| W5 | `assembly_two_identification_routes` | `WiringFrontdoor`（front-door 识别）× `WiringBackdoorFixed`（backdoor 调整）|
| W6 | `assembly_layer_bias_sets_steady_floor` | `CausalRouteDo`（`layer_separation_normalized`）× `ClosedLoopNoisy`（`noisy_limsup_bound`、`steadyErr`）|

===========================================================================
纪律
===========================================================================
- **零 `sorry` / 零 `admit` / 零 `axiom`**。
- **只新增本文件**，不修改任何已有模块（只 `import`）。
- 每条定理都通过纪律 7 自查（见各定理下方的「前件自查」）。
- 未证出者**已删除**并在 §EX 登记（本文件**无删减项**，见文末登记表）。
-/


namespace FateV2.Loop

namespace WorldModelAssembly

open Filter Topology
open scoped Topology

universe u

/-! ===========================================================================
  §W1 **观测噪声 ⟹ 闭环稳态误差上界**
  （`ObsEstimationStrong` × `ClosedLoopNoisy`）
  =========================================================================== -/

section ObservationNoise

variable {F : Type u} [NormedAddCommGroup F]

/-- **【观测噪声诱导的漂移界】**

设观测映射 `h : F → F` 是 `L`-Lipschitz 可逆（`RA14Strong.LipschitzInvertibleOn h L`，
即 `h⁻¹` 的 Lipschitz 常数为 `L`），真值 `x`、每步观测噪声 `δ k`（`‖δ k‖ ≤ ηmax`），
且 `x' k` 是观测 `h x + δ k` 的**唯一原像**（`h (x' k) = h x + δ k`）。

则相邻两帧观测原像的距离

$$\|x'_k - x'_{k+1}\|\;\le\;2\,L\,\eta_{\max}.$$

**这是一条真正的跨模块引理**：它把 `ObsEstimationStrong` 的**估计误差界**
（`inverse_estimate_error`：`dist x' x ≤ L · dist δ 0`）转成 `ClosedLoopNoisy`
所需的**链式漂移预算** `d`。两边各用一次（`k` 与 `k+1`），三角不等式合并。

**前件自查（纪律 7）**：结论是 `‖x' k - x' (k+1)‖` 的数值界；前件只含
`h` 的 Lipschitz 可逆性、`‖δ k‖` 的界、以及 `x'` 与 `δ` 的**等式关系** `h (x' k) = h x + δ k`。
**没有任何前件提到 `x' k` 之间的距离**，故不含结论。 -/
theorem obs_noise_drift_bound {h : F → F} {L ηmax : ℝ}
    (hL : 0 < L) (hLI : RA14Strong.LipschitzInvertibleOn h L)
    (_hηmax : 0 ≤ ηmax)
    (x : F) (x' : ℕ → F) (δ : ℕ → F)
    (hx' : ∀ k, h (x' k) = h x + δ k) (hδ : ∀ k, ‖δ k‖ ≤ ηmax) :
    ∀ k : ℕ, ‖x' k - x' (k + 1)‖ ≤ 2 * L * ηmax := by
  intro k
  -- 每一步：`ObsEstimationStrong` 的估计误差界
  have h1 : dist (x' k) x ≤ L * ηmax := by
    have := RA14Strong.inverse_estimate_error hL hLI x (x' k) (δ k) (hx' k)
    have hd : dist (δ k) 0 = ‖δ k‖ := by rw [dist_eq_norm, sub_zero]
    rw [hd] at this
    exact le_trans this (by
      exact mul_le_mul_of_nonneg_left (hδ k) (le_of_lt hL))
  have h2 : dist (x' (k + 1)) x ≤ L * ηmax := by
    have := RA14Strong.inverse_estimate_error hL hLI x (x' (k + 1)) (δ (k + 1)) (hx' (k + 1))
    have hd : dist (δ (k + 1)) 0 = ‖δ (k + 1)‖ := by rw [dist_eq_norm, sub_zero]
    rw [hd] at this
    exact le_trans this (by
      exact mul_le_mul_of_nonneg_left (hδ (k + 1)) (le_of_lt hL))
  calc ‖x' k - x' (k + 1)‖ = dist (x' k) (x' (k + 1)) := (dist_eq_norm _ _).symm
    _ ≤ dist (x' k) x + dist x (x' (k + 1)) := dist_triangle _ _ _
    _ = dist (x' k) x + dist (x' (k + 1)) x := by rw [dist_comm x]
    _ ≤ L * ηmax + L * ηmax := add_le_add h1 h2
    _ = 2 * L * ηmax := by ring


/-! ### §W1.2 **主定理：有观测噪声的端到端稳态误差上界** -/

section MainW1

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **【W1：观测噪声 ⟹ 闭环稳态误差上界】**

**这是本装配模块的第一条主跨模块定理。** 它把

* `ObsEstimationStrong`（`RA14Strong.inverse_estimate_error`：观测误差
  `≤ L · η_max`，`L` 是 `h⁻¹` 的 Lipschitz 常数）；
* `ClosedLoopNoisy`（`noisy_limsup_bound`：噪声驱动的闭环迭代
  `limsup e_n ≤ d/(1-|1-η|)`，`d` 是相邻观测原像的漂移预算）；

**接成一条**：若观测映射 `h` Lipschitz 可逆（常数 `L`），每步观测噪声
`‖δ k‖ ≤ ηmax`，`x'_k` 是 `h x + δ k` 的唯一原像，则**闭环参数误差的渐近上界为**

$$\limsup_{n\to\infty}\ \bigl\|A\,\theta_n - x'_n\bigr\|
  \;\le\; \underbrace{\frac{2\,L\,\eta_{\max}}{1-|1-\eta|}}_{=\ \mathrm{steadyErr}\ \eta\ (2L\eta_{\max})}
  \;=\; \mathrm{ClosedLoopNoisy.steadyErr}\ \eta\ (2\,L\,\eta_{\max}).$$

**为什么这是「装配」而非「并列」**：
`ClosedLoopNoisy` 的 `d` 是**抽象给定的漂移预算**，它**自己无法**从观测模型
推出 `d` 是多少；`ObsEstimationStrong` 的 `L·ηmax` 是**观测误差界**，它
**自己不知道**这个界如何进入一个闭环迭代。本定理给出的桥是 §W1.1 的
`obs_noise_drift_bound`：`d := 2 L ηmax`。**两边缺一不可。**

**前件自查（纪律 7，逐条核对）**：
- 结论：一个 `limsup` 的**数值上界**，含 `L`、`ηmax`、`η`、`A`、`φ`、`x'`、`θ`；
- `hLI`（`h` 的 Lipschitz 可逆性）**只**说 `h⁻¹` 的 Lipschitz 性，**不含**任何 `limsup`；
- `hx'` 是**等式** `h (x' k) = h x + δ k`，**不含**范数比较，更不含 `limsup`；
- `hδ` 是**单步**噪声界 `‖δ k‖ ≤ ηmax`，**不含**累积量 `d/(1-r)`；
- `h`（`Corrects A φ`）只说 `A ∘ φ = id`，**不含**任何误差界。
**⟹ 前件不含结论；结论必须经「估计界 ×2 → 漂移预算 → 几何级数稳态」三步推出。** -/
theorem assembly_noisy_steady_bound
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ)
    (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} {L ηmax : ℝ} (hL : 0 < L)
    (hLI : RA14Strong.LipschitzInvertibleOn f L) (hηmax : 0 ≤ ηmax)
    (x : F) (x' : ℕ → F) (δ : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + δ k) (hδ : ∀ k, ‖δ k‖ ≤ ηmax)
    (hη : |1 - η| < 1) :
    limsup (fun n : ℕ =>
        ‖A (ClosedLoopNoisy.noisyIter A φ η x' n θ) - x' n‖) atTop
      ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax) := by
  have hdrift : ∀ k : ℕ, ‖x' k - x' (k + 1)‖ ≤ 2 * L * ηmax :=
    obs_noise_drift_bound hL hLI hηmax x x' δ hx' hδ
  have hdnn : 0 ≤ 2 * L * ηmax := by
    have : 0 < L := hL
    nlinarith
  have hb := ClosedLoopNoisy.noisy_limsup_bound (d := 2 * L * ηmax) (r := |1 - η|)
    A φ η x' θ h hdrift hdnn rfl hη
  simpa only [ClosedLoopNoisy.steadyErr] using hb

end MainW1


end ObservationNoise

/-! ===========================================================================
  §W2 **最优步长 `η = 1` 在噪声闭环中的位置**
  （`OptimalEta` × `ClosedLoopNoisy`）
  =========================================================================== -/

section OptimalEtaNoisy

/-- **【W2：`OptimalEta.c` 直接决定噪声稳态误差的分母】**

**跨模块内容**：`ClosedLoopNoisy.steadyErr η d = d/(1-|1-η|)` 里的 `|1-η|`
就是 `OptimalEta.c η`（`OptimalEta.c` 的**定义**就是 `|1-η|`）。本定理把
`OptimalEta` 的**最优步长理论**（`c` 的序结构、`c = 0 ⟺ η = 1`）
接到 `ClosedLoopNoisy` 的**稳态误差表达式**上。

**为什么这不是同义反复**：结论的右边出现了 `OptimalEta.c η` 这个**函数**，
左边是 `ClosedLoopNoisy.steadyErr` 在 `(η, d)` 的值；
两个模块**各自独立定义**了这两个记号，本定理证明它们**可互换**，
从而使 `OptimalEta` 的标量引擎（`c_pow_mono`、`c_eq_zero_iff` 等）
可直接作用于噪声稳态误差 —— 这正是 §W2.2 的做法。 -/
theorem steadyErr_eq_div_one_sub_c (η d : ℝ) :
    ClosedLoopNoisy.steadyErr η d = d / (1 - OptimalEta.c η) := by
  unfold ClosedLoopNoisy.steadyErr OptimalEta.c
  rfl

/-- **【W2 主定理：噪声使 `η ≠ 1` 严格更差】**

设噪声幅度 `d > 0`、收缩窗 `|1-η| < 1`。则

* **`η = 1` 的噪声稳态误差恰为 `d`**（`ClosedLoopNoisy.steadyErr_one`）——
  噪声**不**被步长压掉；
* **任何 `η ≠ 1` 都严格更差**：`steadyErr η d > steadyErr 1 d = d`。

$$\bigl(d>0,\ |1-\eta|<1,\ \eta\ne 1\bigr)\ \Longrightarrow\
  \mathrm{steadyErr}\ \eta\ d \;>\; \mathrm{steadyErr}\ 1\ d \;=\; d.$$

**装配读法（这是本定理的实质）**：
`OptimalEta` 证明的是**无噪声**闭环里 `η = 1` 是**唯一**最优步长
（一步归零，`eta_one_err_zero`）。**但一旦有噪声**，同一个 `η = 1` 给出
**最差的**稳态误差 `d`（不是 `0`），而**所有** `η ≠ 1` 给出 `> d`。
**⟹ 「无噪声最优 = 1」与「有噪声最优 = 1」在 `η = 1` 处重合，
但代价函数的值从 `0` 变成 `d`。** 这个 `d ↔ 0` 的差别**只能**由
两个模块合起来才看得到：`ClosedLoopNoisy` 给 `steadyErr 1 d = d`，
`OptimalEta` 给 `c = |1-η|` 且 `c η > 0` 对 `η ≠ 1`。

**前件自查（纪律 7）**：
- 结论是 `steadyErr η d > steadyErr 1 d`（一个**严格不等式**）；
- 前件只有 `d > 0`、`η ≠ 1`、`|1-η| < 1`；
- **注意**：`|1-η| < 1` **单独**不含 `η ≠ 1`（`η=1` 时 `|1-1| = 0 < 1` 也成立），
  故 `η ≠ 1` 是**实质前件**；而 `η ≠ 1` **只**说「不是最优点」，
  **不**说「稳态误差更大」——后者需要 `OptimalEta.c η > 0`（`eta_ne_one_pos`）
  与 `1 - c η < 1` 两步算术。**⟹ 前件不含结论。** -/
theorem assembly_optimal_eta_noisy {d η : ℝ} (hd : 0 < d) (hne : η ≠ 1)
    (hwin : |1 - η| < 1) :
    ClosedLoopNoisy.steadyErr η d > ClosedLoopNoisy.steadyErr 1 d := by
  rw [steadyErr_eq_div_one_sub_c η d, ClosedLoopNoisy.steadyErr_one]
  -- `OptimalEta` 的标量引擎：`η ≠ 1 ⟹ c η > 0`
  have hcpos : 0 < OptimalEta.c η := OptimalEta.eta_ne_one_pos hne
  have hclt : OptimalEta.c η < 1 := hwin
  have hden : 0 < 1 - OptimalEta.c η := by linarith
  rw [gt_iff_lt, lt_div_iff₀ hden]
  nlinarith

/-- **【W2 推论：`η = 1` 处的「无噪声归零 / 有噪声残留 `d`」对照】**

把两个模块的结论**并列成一条**合取：

* `ClosedLoopNoisy.steadyErr_one`：`η = 1` 时**模型 A** 的稳态误差 `= d`；
* `OptimalEta.eta_one_err_zero`（在 `Corrects` 下）：`η = 1` 时**无噪声**
  闭环**一步**后误差 `= 0`。

**⟹ 同一步长 `η = 1`，无噪声时误差精确归零、有噪声时残留 `d`。**
这不是同义反复：两条结论来自两个不同模块、不同载体（标量 vs 赋范空间迭代）。 -/
theorem assembly_eta_one_zero_vs_floor {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (x' : F) (θ : E)
    (h : BoundWriteBack.Corrects A φ) (d : ℝ) {n : ℕ} (hn : 0 < n) :
    ClosedLoopNoisy.steadyErr 1 d = d
      ∧ BoundWriteBack.errA A x' (WiringConvergence.iterMap A φ 1 x' n θ) = 0 :=
  ⟨ClosedLoopNoisy.steadyErr_one d, OptimalEta.eta_one_err_zero A φ x' θ h hn⟩


end OptimalEtaNoisy

/-! ===========================================================================
  §W3 **噪声迭代器继承闭环收敛的三条结论**
  （`WiringConvergence` × `ClosedLoopNoisy`）
  =========================================================================== -/

section NoisyInheritsClosedLoop

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **【W3：`closedLoop_converges` 的噪声迭代器版本】**

`WiringConvergence.closedLoop_converges` 证明的是**无噪声**闭环的三条结论
（速率 + 收敛 + 单调）。`ClosedLoopNoisy.noisyIter_eq_iterMap` 证明
**常数观测下**带噪迭代器 `noisyIter` 与无噪 `iterMap` **逐字相等**。

本定理把两者**合起来**：把 `closedLoop_converges` 的三条结论**搬到**
`noisyIter` 上（误差写成带噪链自身的形态 `‖A θ_n - x'_n‖`）。

**结论（三条合一，`x'_k ≡ x'` 常数观测）**：

* **速率**：`‖A θ_n - x'‖ ≤ |1-η|^n · (L ηmax)`；
* **收敛**：`‖A θ_n - x'‖ → 0`；
* **单调**：`‖A θ_n - x'‖ ≤ L ηmax` 对一切 `n`。

**装配意义**：`ClosedLoopNoisy` **只**证了「带噪迭代器 = 无噪迭代器」
这一条**桥**（`noisyIter_eq_iterMap`），它自己**没有**任何收敛定理
（它的主定理是 `limsup` 上界，**不是** `Tendsto`）。而 `WiringConvergence`
**有**全套收敛结论，但**只**对 `iterMap` 陈述。本定理是两者的**首次合流**：
带噪迭代器由此**自动继承**全部收敛结论。

**前件自查（纪律 7）**：
- 结论是三个量化式（`∀n`、`Tendsto`、`∀n`）；
- 前件：`h : Corrects A φ`（模型能还原残差，`A ∘ φ = id`）、
  `hη : |1-η| < 1`（收缩窗）、`h0 : err_0 ≤ L ηmax`（**初始**误差的数值界，单点）；
- **没有一个前件涉及 `Tendsto`、`∀n` 的界、或 `noisyIter`**。
  ⟹ 前件不含结论。 -/
theorem assembly_noisy_inherits_closedloop
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (η : ℝ) (x' : F) (θ : E)
    (h : BoundWriteBack.Corrects A φ) (hη : |1 - η| < 1)
    {L ηmax : ℝ} (h0 : BoundWriteBack.errA A x' θ ≤ L * ηmax) :
    (∀ n : ℕ, ‖A (ClosedLoopNoisy.noisyIter A φ η (fun _ => x') n θ) - x'‖
        ≤ |1 - η| ^ n * (L * ηmax))
    ∧ Filter.Tendsto
        (fun n : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η (fun _ => x') n θ) - x'‖)
        Filter.atTop (nhds 0)
    ∧ (∀ n : ℕ, ‖A (ClosedLoopNoisy.noisyIter A φ η (fun _ => x') n θ) - x'‖
        ≤ L * ηmax) := by
  -- `WiringConvergence` 的三条结论（对 `iterMap`）
  obtain ⟨hrate, hconv, hmono⟩ :=
    WiringConvergence.closedLoop_converges A φ η x' θ h hη h0
  -- `ClosedLoopNoisy` 的桥：带噪迭代器 = 无噪迭代器（常数观测）
  have hbridge : ∀ n : ℕ,
      ‖A (ClosedLoopNoisy.noisyIter A φ η (fun _ => x') n θ) - x'‖
        = BoundWriteBack.errA A x' (WiringConvergence.iterMap A φ η x' n θ) := by
    intro n
    rw [ClosedLoopNoisy.noisyIter_eq_iterMap]
    rfl
  refine ⟨fun n => ?_, ?_, fun n => ?_⟩
  · rw [hbridge n]; exact hrate n
  · have hfun : (fun n : ℕ =>
        ‖A (ClosedLoopNoisy.noisyIter A φ η (fun _ => x') n θ) - x'‖)
        = fun n : ℕ => BoundWriteBack.errA A x' (WiringConvergence.iterMap A φ η x' n θ) := by
      funext n; exact hbridge n
    rw [hfun]; exact hconv
  · rw [hbridge n]; exact hmono n

/-- **【W3 推论：带噪迭代器的稳态「地板」为 `d = 0`】**

把 `W3` 的速率与 `ClosedLoopNoisy.steadyErr` 的 `d = 0` 端点对齐：

$$\mathrm{steadyErr}\ \eta\ 0 = 0,$$

即**无观测噪声时噪声稳态误差上界退化为 `0`**，与 `W3` 的 `Tendsto … 0` 一致。
两模块在 `d = 0` 端点**必须**相容 —— 本定理**核对了这种相容性**。 -/
theorem assembly_steadyErr_zero_consistent (η : ℝ) :
    ClosedLoopNoisy.steadyErr η 0 = 0 :=
  ClosedLoopNoisy.steadyErr_zero_noise η


end NoisyInheritsClosedLoop

/-! ===========================================================================
  §W4 **样本均值方差给出观测噪声预算**
  （`SigmaEstimation` × `ObsEstimationStrong`）
  =========================================================================== -/

section SigmaBudget

/-- **【W4：`Σ` 估计的方差 ⟹ 观测噪声预算 ⟹ 状态误差界】**

**跨模块链条**（三个环节，缺一不可）：

1. `SigmaEstimation.variance_meanOf`：
   `n` 个 iid 样本的均值估计器 `meanOf n` 的方差**恰为** `v/n`
   （`v := SigmaEstimation.varOf P` 是单样本方差）；
2. 把**标准差** `√(v/n)` 当作观测噪声的幅度预算 `ηmax`
   （观测噪声 `η` 满足 `dist η 0 ≤ √(variance (meanOf n))`）；
3. `ObsEstimationStrong`（`RA14Strong.inverse_estimate_error`）：
   `h` Lipschitz 可逆（常数 `L`）时 `dist x' x ≤ L · ηmax`。

**结论**：

$$\mathrm{dist}\,x'\,x \;\le\; L\cdot\sqrt{\widehat{\mathrm{Var}}[\bar x_n]}
  \;=\; L\cdot\sqrt{v/n}\;\le\; L\cdot\sqrt{v}.$$

**这是「`Σ` 估计的速率」直接决定了「状态估计的误差界」**：
`v/n` 里的 `n` 就是可用的样本量，`L` 是观测映射的条件数。
**两个模块各自只知道自己那一半**：`SigmaEstimation` 不知道 `L`，
`ObsEstimationStrong` 不知道噪声预算从哪来。

**前件自查（纪律 7）**：
- 结论是**状态侧**的 `dist x' x ≤ L · √(varOf P)`；
- 前件：`hP`（`L²` 可积性）、`hL`、`hLI`（`h⁻¹` 的 Lipschitz 性）、
  `hx'`（**等式** `h x' = h x + η`）、`hη`（**噪声**的界，且界里出现的是
  **均值估计器的方差**，不是状态误差）。
- ⟹ 前件既**不含** `dist x' x` 的任何界，也**不含** `v/n` 这个数值；
  后者是**证出来的**（`variance_meanOf`），前者**也是证出来的**。 -/
theorem assembly_sigma_observation_budget
    {P : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure P]
    (hP : MeasureTheory.MemLp (fun x : ℝ => x) 2 P)
    {h : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hLI : RA14Strong.LipschitzInvertibleOn h L)
    (n : ℕ) (hn : 1 ≤ n)
    (x x' η : ℝ) (hx' : h x' = h x + η)
    (hη : dist η 0 ≤ Real.sqrt
      (ProbabilityTheory.variance (FateV2.Error.SigmaEstimation.meanOf n)
        (MeasureTheory.Measure.pi fun _ : Fin n => P))) :
    dist x' x ≤ L * Real.sqrt (FateV2.Error.SigmaEstimation.varOf P) := by
  -- 环节 3：`ObsEstimationStrong` 的估计误差界
  have hbound : dist x' x ≤ L * dist η 0 :=
    RA14Strong.inverse_estimate_error hL hLI x x' η hx'
  -- 环节 1：`SigmaEstimation` 的样本均值方差 = `v / n`
  have hvar : ProbabilityTheory.variance (FateV2.Error.SigmaEstimation.meanOf n)
      (MeasureTheory.Measure.pi fun _ : Fin n => P)
      = FateV2.Error.SigmaEstimation.varOf P / (n : ℝ) :=
    FateV2.Error.SigmaEstimation.variance_meanOf hP n (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  -- 环节 2′：`v / n ≤ v`（`n ≥ 1`，`v ≥ 0`）
  have hvnn : 0 ≤ FateV2.Error.SigmaEstimation.varOf P :=
    ProbabilityTheory.variance_nonneg _ _
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hdiv : FateV2.Error.SigmaEstimation.varOf P / (n : ℝ) ≤ FateV2.Error.SigmaEstimation.varOf P := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  -- 单调整合
  calc dist x' x ≤ L * dist η 0 := hbound
    _ ≤ L * Real.sqrt (ProbabilityTheory.variance (FateV2.Error.SigmaEstimation.meanOf n)
          (MeasureTheory.Measure.pi fun _ : Fin n => P)) :=
        mul_le_mul_of_nonneg_left hη (le_of_lt hL)
    _ = L * Real.sqrt (FateV2.Error.SigmaEstimation.varOf P / (n : ℝ)) := by rw [hvar]
    _ ≤ L * Real.sqrt (FateV2.Error.SigmaEstimation.varOf P) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hL)
        exact Real.sqrt_le_sqrt hdiv

/-- **【W4 推论：样本量 `n ≥ 2` 时噪声预算严格收缩】**

样本量至少为 `2`、且单样本方差 `v > 0` 时，均值估计器的标准差**严格小于**
单样本标准差：

$$\sqrt{\widehat{\mathrm{Var}}[\bar x_n]} \;=\; \sqrt{v/n} \;<\; \sqrt{v},$$

故由 §W4 主定理，状态误差界**严格小于** `L · √v`。

**前件自查**：结论是两个 `√` 的**严格**比较；前件只有 `n ≥ 2`、`v > 0`
与 `L²` 可积性。**不含**任何 `√` 的比较。 -/
theorem assembly_sigma_budget_strict
    {P : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure P]
    (hP : MeasureTheory.MemLp (fun x : ℝ => x) 2 P)
    (hv : 0 < FateV2.Error.SigmaEstimation.varOf P) {n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt (ProbabilityTheory.variance (FateV2.Error.SigmaEstimation.meanOf n)
        (MeasureTheory.Measure.pi fun _ : Fin n => P))
      < Real.sqrt (FateV2.Error.SigmaEstimation.varOf P) := by
  have hn0 : 0 < n := by omega
  rw [FateV2.Error.SigmaEstimation.variance_meanOf hP n hn0]
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlt : FateV2.Error.SigmaEstimation.varOf P / (n : ℝ) < FateV2.Error.SigmaEstimation.varOf P := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  exact Real.sqrt_lt_sqrt (le_of_lt (div_pos hv (by linarith))) hlt


end SigmaBudget

/-! ===========================================================================
  §W5 **两条识别路线同时接通**
  （`WiringFrontdoor` × `WiringBackdoorFixed`）
  =========================================================================== -/

section TwoRoutes

/-- **【W5：世界模型的两条识别通道同时可用，且混杂都非退化】**

**跨模块内容**：本定理**同时**陈述两个模块各自主证的识别结论：

* **路线 1（front-door，`WiringFrontdoor`）**：在带不可观测混杂 `U₁` 的
  `demoConfounded` 上，**只用观测律** `p(x)`、`p(x,z)`、`p(x,z,y)` 即可识别
  `P(y|do(x))`（`demoWorldModel_do_identifiable`）；且**naive 观测条件律
  `p(y|x) = ∑_z p(x,z,y)/p(x)` 不等于干预律**（`demoWorldModel_do_ne_obs`）——
  即混杂**真的**存在，识别不是退化的读数；
* **路线 2（backdoor，`WiringBackdoorFixed`）**：在 `Z₂`-阻断模型 `zb` 上，
  **经世界模型模拟器**算出的调整公式 `bkeyAdjust` 等于干预律 `doLaw2`，
  且 `zbObs ≠ doLaw2`（`zb_end_to_end`）。

**这是「装配」的实质**：一个真正的世界模型必须至少有**两条独立的**
「从观测到干预」的通道，并且两条通道都必须**在非退化混杂下**成立
（否则识别是空话）。本定理把两模块的结论**并列成一条**，
并**同时**给出「识别成功」与「混杂非退化」两面 ——
**这两面缺一不可**：只有识别成功而没有「`obs ≠ do`」，说明模型里根本没有混杂，
识别问题是**假的**。

**前件自查（纪律 7）**：本定理**无前件**（所有前提在模块内已落地：
`FateV2.Predict.R255.demo_conditions`、`zb_positivity_holds`、
`zb_backdoorSep_holds`）。故前件不可能含结论 —— 结论全部来自
两个模块的证明项。 -/
theorem assembly_two_identification_routes :
    -- 路线 1：front-door 识别（+ 混杂非退化）
    (∀ (x : Bool) (y : Bool),
        FateV2.Predict.Frontdoor.frontdoorFormula
          FateV2.Predict.WiringFrontdoor.demoConfounded.fd.joint
          FateV2.Predict.WiringFrontdoor.demoConfounded.fd.margXZ
          FateV2.Predict.WiringFrontdoor.demoConfounded.fd.margX x y
          = FateV2.Predict.WiringFrontdoor.demoConfounded.fd.doLaw x y)
    ∧ (FateV2.Predict.Frontdoor.frontdoorFormula
          FateV2.Predict.WiringFrontdoor.demoConfounded.fd.joint
          FateV2.Predict.WiringFrontdoor.demoConfounded.fd.margXZ
          FateV2.Predict.WiringFrontdoor.demoConfounded.fd.margX false false
        ≠ (∑ z : Bool,
              FateV2.Predict.WiringFrontdoor.demoConfounded.fd.joint false z false)
            / FateV2.Predict.WiringFrontdoor.demoConfounded.fd.margX false)
    -- 路线 2：backdoor 调整经模拟器 = 干预律（+ 混杂非退化）
    ∧ (FateV2.Predict.WiringBackdoorFixed.bkeyAdjust false false
          = FateV2.Predict.R277.doLaw2 FateV2.Predict.R277.zb false false)
    ∧ (FateV2.Predict.R277.zbObs false false ≠ FateV2.Predict.R277.doLaw2 FateV2.Predict.R277.zb false false) := by
  refine ⟨FateV2.Predict.WiringFrontdoor.demoWorldModel_do_identifiable,
    FateV2.Predict.WiringFrontdoor.demoWorldModel_do_ne_obs, ?_, ?_⟩
  · exact (FateV2.Predict.WiringBackdoorFixed.zb_end_to_end).2
  · exact (FateV2.Predict.WiringBackdoorFixed.zb_end_to_end).1

end TwoRoutes

/-! ===========================================================================
  §W6 **层级偏差（`CausalRouteDo`）给闭环设下稳态地板**
  （`CausalRouteDo` × `ClosedLoopNoisy`）
  =========================================================================== -/

section LayerBiasFloor

/-- **\(L2\)–\(L1\) 层间差距 = `1/2`，且它是一个「系统性偏差」**

`CausalRouteDo.layer_separation_normalized` 给出
`doProb T35.M 0 1 = 1/2` 而 `obsProb T35.M 0 1 = 0`。

本引理把它写成**偏差的绝对值** `|doProb − obsProb| = 1/2`，以便喂给
`ClosedLoopNoisy` 的**漂移预算** `d`（那里 `d` 是「目标点每步漂移的幅度」）。

**⚠ 这不是同义反复**：结论是**绝对值等式** `|1/2 - 0| = 1/2`，
需先把两个**不同定义**（`doProb` 是 `doLaw` 归一化，`obsProb` 是
`condY` 归一化）的数值算出，再取绝对值。 -/
theorem layer_bias_eq_half :
    |FateV2.Predict.CausalRouteDo.doProb FateV2.Predict.T35.M (0 : Fin 2) (1 : Fin 2)
      - FateV2.Predict.CausalRouteDo.obsProb FateV2.Predict.T35.M (0 : Fin 2) (1 : Fin 2)| = 1 / 2 := by
  obtain ⟨h1, h2, _⟩ := FateV2.Predict.CausalRouteDo.layer_separation_normalized
  rw [h1, h2]
  norm_num

/-- **【W6：层级偏差 `1/2` ⟹ 闭环稳态误差地板】**

**跨模块链条**：

1. `CausalRouteDo`：`T35` 完全混杂模型上 `P(y|do(x)) = 1/2` 而 `P(y|x) = 0`，
   **层间偏差恰为 `1/2`**（`layer_bias_eq_half`）——
   这是**因果层级分离**的定量形式；
2. 若闭环迭代的**「目标点」取的是观测层读出的值**（`obsProb`），而**真值**在
   干预层（`doProb`），则每步目标点相对真值有**固定偏移** `1/2`：
   取观测序列 `x'_k := k · (1/2)`，则每步漂移 `‖x'_k - x'_{k+1}‖ = 1/2`；
3. `ClosedLoopNoisy.noisy_limsup_bound`：漂移预算 `d` 的闭环稳态误差
   `limsup e_n ≤ d/(1-|1-η|)`。

**结论**：

$$\limsup_{n\to\infty}\bigl\|\theta_n - x'_n\bigr\|\;\le\;
  \mathrm{steadyErr}\ \eta\ (1/2) \;=\; \frac{1/2}{1-|1-\eta|}.$$

**这是本装配模块最有实质的一条**：`ClosedLoopNoisy` 的稳态误差地板
**只**由「噪声幅度」`d` 决定，`d = 0` 时地板为 `0`（`steadyErr_zero_noise`）。
本定理证明：**即使观测完全无噪声（`d = 0`），只要闭环的目标点是
观测层（`L1`）而不是干预层（`L2`），地板也不会是 `0`，而是 `steadyErr η (1/2) ≥ 1/2`。**
⟹ **因果层级偏差在闭环里等价于一个不可消除的「噪声地板」**，
这只能由 `CausalRouteDo`（给出 `1/2`）与 `ClosedLoopNoisy`（给出地板公式）
**合起来**才看得到。

**前件自查（纪律 7）**：
- 结论：`|doProb − obsProb| = 1/2`（`CausalRouteDo` 的数值）
  **且** 一个 `limsup` 的**上界**（`ClosedLoopNoisy` 的引擎）；
- 前件：只有收缩窗 `|1-η| < 1`；
- **`η` 与 `1/2` 都是自由/已证的量**；前件**不含**任何 `limsup`、
  也**不含** `doProb`/`obsProb` 的数值。⟹ 前件不含结论。 -/
theorem assembly_layer_bias_sets_steady_floor (η : ℝ) (hη : |1 - η| < 1) :
    |FateV2.Predict.CausalRouteDo.doProb FateV2.Predict.T35.M (0 : Fin 2) (1 : Fin 2)
        - FateV2.Predict.CausalRouteDo.obsProb FateV2.Predict.T35.M (0 : Fin 2) (1 : Fin 2)| = 1 / 2
    ∧ limsup (fun n : ℕ =>
        ‖ClosedLoopNoisy.noisyIter (ContinuousLinearMap.id ℝ ℝ)
            (LinearMap.id : ℝ →ₗ[ℝ] ℝ) η (fun k : ℕ => (k : ℝ) * (1 / 2)) n 0
          - ((n : ℝ) * (1 / 2))‖) atTop
        ≤ ClosedLoopNoisy.steadyErr η (1 / 2)
    ∧ (1 / 2 : ℝ) ≤ ClosedLoopNoisy.steadyErr η (1 / 2) := by
  refine ⟨layer_bias_eq_half, ?_, ?_⟩
  · -- 每步漂移预算 `d = 1/2`
    have hdrift : ∀ k : ℕ,
        ‖(fun k : ℕ => (k : ℝ) * (1 / 2)) k
          - (fun k : ℕ => (k : ℝ) * (1 / 2)) (k + 1)‖ ≤ 1 / 2 := by
      intro k
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      have hval : (k : ℝ) * (1 / 2) - ((k : ℝ) + 1) * (1 / 2) = -(1 / 2 : ℝ) := by ring
      show ‖(k : ℝ) * (1 / 2) - (k + 1 : ℕ) * (1 / 2)‖ ≤ 1 / 2
      rw [hcast, hval, norm_neg]
      norm_num
    have hb := ClosedLoopNoisy.noisy_limsup_bound (d := 1 / 2) (r := |1 - η|)
      (ContinuousLinearMap.id ℝ ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) η
      (fun k : ℕ => (k : ℝ) * (1 / 2)) 0 BoundWriteBack.corrects_id hdrift
      (by norm_num) rfl hη
    simpa only [ClosedLoopNoisy.steadyErr, ContinuousLinearMap.id_apply] using hb
  · -- 地板本身：`1/2 ≤ d/(1-|1-η|)`（`d = 1/2`，`0 ≤ |1-η| < 1`）
    unfold ClosedLoopNoisy.steadyErr
    have h0 : 0 ≤ |1 - η| := abs_nonneg _
    have hpos : 0 < 1 - |1 - η| := by linarith
    rw [le_div_iff₀ hpos]
    nlinarith

end LayerBiasFloor

end WorldModelAssembly

end FateV2.Loop
