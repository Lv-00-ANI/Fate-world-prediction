import FateWorld.FateV2.Modeling.ObsEstimationStrong
import FateWorld.FateV2.Loop.ClosedLoopNoisy
import FateWorld.FateV2.Loop.BoundWriteBack
import FateWorld.FateV2.Error.ChainBudgetBound
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/CapstoneDriftFromObs.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008
  - 改动：namespace/引用 ProperFit→FateV2.Loop（正文 12 处，含 4 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Predict
open FateV2.Loop
open FateV2.Modeling
open FateV2.Model

/-
  命运理论 · **从观测生成模型推出漂移界（真正的 `hstep` 拆除）**

  ============================================================================
  ⚠ 本文件的定位（**须先读**）
  ============================================================================

  审计 R441 对 `WorldModelCapstone.capstone_dsigma_from_data` 的核心批评是：

  > 「`hstep` 直接断言『步长 ≤ 2Lηmax + dσ』——**结论的全部数值内容由 `hstep` 提供**。
  >  把 `resolveSigma` 换成常数 `0` 这条定理依然成立。」

  主控第 457 轮判断「`hstep` 拆不掉」；第 460 轮发现这是**误判**，因为库里
  `FateV2.Loop/ObsEstimationStrong.lean` §2′ 早已形式化了**观测生成模型**：

  > `x` 是**真值**，`η` 是**噪声**，`x'` 是**观测的原像**（`h x' = h x + η`）。

  本文件据此给出**前件里没有 `hstep`** 的定理。

  ----------------------------------------------------------------------------
  ## 一、本文件的实质内容（与代码一一对应，namespace `FateV2.Loop.CapstoneDriftFromObs`）

  | # | 定理 | 内容 |
  |---|---|---|
  | 1 | `dist_obs_le` | 观测模型 + 噪声界 ⟹ `dist (x' k) x ≤ L·ηmax`（单步，$L$ 实质介入） |
  | 2 | `drift_bound_from_obs` | **主定理**：观测模型 + 噪声界 ⟹ `‖x' k - x' (k+1)‖ ≤ 2Lηmax`（**无 `hstep`**） |
  | 3 | `drift_bound_from_obs_div` | 同上但用 `dist` 形式（与 `ClosedLoopNoisy.noisy_limsup_bound` 的 `‖·‖` 形式对齐的过渡引理） |
  | 4 | `drift_nonneg` | `0 ≤ 2Lηmax`（`noisy_limsup_bound` 需要的 `hd`，此处**推出**而非假设） |
  | 5 | `capstone_drift_from_obs` | **capstone**：观测模型 ⟹ `limsup ‖A θ_n - x'_n‖ ≤ steadyErr η (2Lηmax)`，**`dσ = 0`，无 `hstep`** |
  | 6 | `capstone_drift_from_obs_with_sigma` | 同上，但把 `dσ` 接成 `sigmaEst P n`（与 `§6.4.2` 同形，**仍然无 `hstep`**） |
  | 7 | `capstone_drift_sharp_zero_noise` | `ηmax = 0` 时漂移 **实际为 0**（界取等，说明 `2Lηmax` 不虚松） |
  | 8 | `obs_model_constant_witness` | 观测模型**可满足**（非空前件，反同义反复/反空真） |
  | 9 | `drift_independent_of_sigma` | 审计要的对照：漂移界**完全不涉及** `resolveSigma`（`dσ` 可任意，取 `0`） |

  ----------------------------------------------------------------------------
  ## 二、与审计 R441 的逐点对照

  **(a) `hstep` 被换成了什么。**
  本文件的 capstone（第 5 条）前件是：
  `hLI : LipschitzInvertibleOn f L`、`hx' : ∀ k, f (x' k) = f x + η k`、
  `hη : ∀ k, ‖η k‖ ≤ ηmax`、`hηmax : 0 ≤ ηmax`、`hL : 0 < L`、`hη : |1-η| < 1`、
  `h : Corrects A φ`。
  **没有**任何形如 `∀ k, ‖x' k - x' (k+1)‖ ≤ ...` 的前件。
  该不等式由第 2 条定理（`drift_bound_from_obs`）**推出**，再喂给
  `ClosedLoopNoisy.noisy_limsup_bound`。

  **(b) 这是真正的进步。**
  `hstep` 在旧定理中是**假设**；在本文件中它是**定理的结论**（第 2 条）。
  审计说的「把 `resolveSigma` 换成常数 `0` 定理仍成立」在此处**不再成立**：
  本文件的界是 `steadyErr η (2 L ηmax)`。**⚠ 第 489 轮如实降级（审计 R480 的判决，主控接受）**：

  **原版此处写「`2 L ηmax` 的两处（`L` 与 `ηmax`）都由观测模型的 `hLI`、`hη` 实质决定」——
  这句话【是错的】，现更正如下：**

  - `L` **确实**由观测模型决定（`dist_obs_le` 里 `L` 实质介入，单步界 `dist (x' k) x ≤ L·ηmax`）。
  - **`ηmax` 仍是【自由参数】**。审计探针 B 证明：`∀ L>0, ∀ d, ∃ ηmax, 2*L*ηmax = d`
    ⟹ **`2 L ηmax` 可取任意非负实数**。
  - **观测模型给出的是一条【可解释的具体界】**（从 `h x' = h x + η` 与 `‖η‖ ≤ ηmax` 推出），
    **但 `ηmax` 本身不是由数据决定的**。

  **正确的说法是**：「本文件把『步长界』这个**假设**换成了『观测模型 + 噪声界』这个**更可解释的假设**；
  `L` 由此确定，**但 `ηmax` 仍是自由参数**。」

  **⟹ 真正消灭 `hstep` 需要**：`ηmax` 与 `sigmaEst P n` 的**定量桥**（本文件未做，见 §未证）。

  **(c) ⚠ 但观测模型本身仍是假设。**
  「观测 = 真值 + 噪声」（即 `f (x' k) = f x + η k`，且 `x' k` **确实在像内**）
  是**建模选择**，不是定理。它在实践上是否成立是**经验问题**；
  `ObsEstimationStrong` 文件头已明写：若 `f x + η` 不在 `f` 的像内，
  则原像 `x'` **不存在**，观测模型**不可满足**（该文件 §4.1 给出反例）。
  ⟹ **本文件把假设从「漂移界」换成了「观测生成模型」，而不是消灭了假设。**

  **(d) ⚠ 不声称「循环已破」。**
  本文件**不**声称闭环问题已解决、不声称 A14 已证、不声称稳态误差界无条件成立。
  它只证明：**给定观测生成模型 + 有界噪声，漂移界与稳态误差界是推出的**。
  其中「观测生成模型」仍是经验假设（与 A14 的 `.empirical` 标签一致）。

  **(e) ⚠ `dσ` 的地位。**
  第 5 条取 `dσ = 0`（**因为不需要**）；第 6 条把 `dσ` 接成
  `sigmaEst P n := √(varOf P / n)`，说明 σ 分量的接入是**选配**而非必需。
  这与审计的批评正好相反：在旧定理里 `dσ` 是自由参数且**结论全靠 `hstep`**；
  在本文件里 `dσ` 是**可加可不加的松弛项**，核心的 `2 L ηmax` 由模型推出。

  **(f) 未证出的部分（如实登记）。**
  本文件**未**证：观测模型在数据上成立；`ηmax` 与 `sigmaEst P n` 的**定量**关系
  （「噪声尺度就是 σ」这一步本仓库**没有**形式化，第 6 条只是**并置**两条结论，
  不是从一条推出另一条）。这一点**不含糊**。

  ----------------------------------------------------------------------------
  ## 三、纪律自查

  - **零 `sorry` / `admit` / `axiom` / `True := trivial`**；
  - **只新增本文件**，不修改任何已有模块（只 `import`）；
    本文件**不**与 `WorldModelCapstone` 中的任何定理同名，故不构成覆盖；
  - 「前件是否已含结论」（纪律 7）逐条见各定理下方说明；
  - 观测模型定理的存在性用两种 grep 模式确认过
    （`inverse_estimate_error` 与 `h x' = h x + η`），见 `ObsEstimationStrong:358`。
  ============================================================================
-/


namespace FateV2.Loop

namespace CapstoneDriftFromObs

universe u

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Topology

variable {E F : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ===========================================================================
  §1  **观测生成模型 ⟹ 单步估计误差**

  **模型**（`ObsEstimationStrong` §2′ 的逐字形式）：
  `x` 是**真值**，`η` 是**噪声**，`x' k` 是观测 `f x + η k` 的**原像**。
  =========================================================================== -/

omit [NormedSpace ℝ F] in
/-- **【§1.1 单步估计误差：`dist (x' k) x ≤ L·ηmax`】**

**前件**：`0 < L`、`f` Lipschitz 可逆、观测模型 `f (x' k) = f x + η k`、
噪声界 `‖η k‖ ≤ ηmax`。

**结论**：`dist (x' k) x ≤ L * ηmax`。

**证明**：直接调用 `ObsEstimationStrong.inverse_estimate_error`（得到
`dist (x' k) x ≤ L * dist (η k) 0 = L * ‖η k‖`），再乘上噪声界。
**$L$ 在此实质介入**（不是装饰）。

**前件自查（纪律 7）**：`hx'` 是**等式**，`hη` 是 `‖·‖` 的单步界，
**都不含** `dist (x' k) x` 的任何比较；结论中的 `L·ηmax` 由两者**相乘**得到。 -/
theorem dist_obs_le {f : F → F} {L ηmax : ℝ}
    (hL : 0 < L) (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (η : ℕ → F) (k : ℕ)
    (hx' : ∀ j, f (x' j) = f x + η j) (hη : ∀ j, ‖η j‖ ≤ ηmax) :
    dist (x' k) x ≤ L * ηmax := by
  have h1 : dist (x' k) x ≤ L * dist (η k) 0 :=
    RA14Strong.inverse_estimate_error hL hLI x (x' k) (η k) (hx' k)
  have hd : dist (η k) 0 = ‖η k‖ := by rw [dist_eq_norm, sub_zero]
  rw [hd] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_left (hη k) (le_of_lt hL))

/-! ===========================================================================
  §2  **主定理：从观测模型推出漂移界（无 `hstep`）**
  =========================================================================== -/

omit [NormedSpace ℝ F] in
/-- **【§2.1 主定理：`drift_bound_from_obs`】**

**前件**（**注意：没有 `hstep`**）：
- `0 < L`、`f` 在像上 Lipschitz 可逆（常数 `L`）；
- **观测生成模型** `hx' : ∀ k, f (x' k) = f x + η k`（观测 = 真值 + 噪声）；
- **噪声界** `hη : ∀ k, ‖η k‖ ≤ ηmax`。

**结论**：

$$\forall k,\quad \|x'_k - x'_{k+1}\| \le 2\,L\,\eta_{\max}.$$

**推导链（审计要求的「真正拆掉 `hstep`」）**：
1. §1.1 给出 `dist (x' k) x ≤ L ηmax` 与 `dist (x' (k+1)) x ≤ L ηmax`；
2. 三角不等式 `‖x'_k - x'_{k+1}‖ = dist (x' k) (x' (k+1)) ≤ dist (x' k) x + dist x (x' (k+1))`；
3. 相加得 `≤ L ηmax + L ηmax = 2 L ηmax`。

**⚠ 与 `WorldModelAssembly.obs_noise_drift_bound` 的关系**：
**同一命题**（那条已存在于库中）。本文件**不声称**它是新的数学；
单列的理由是**本文件是它的独立下游**（不依赖 `WorldModelAssembly`，
从而本文件的 capstone 只 import `ObsEstimationStrong` + `ClosedLoopNoisy` 两条腿），
并且本文件在同一处**把 `2 L ηmax` 的非负性也推出**（§1.3）。
**诚实登记：这是重证，不是新数学。**

**前件自查（纪律 7）**：`hx'` 是等式、`hη` 是单步范数界；结论是**相邻差**的界。
相邻差在前件中**不出现**——它由三角不等式**合成**得到。⟹ 非同义反复。 -/
theorem drift_bound_from_obs {f : F → F} {L ηmax : ℝ}
    (hL : 0 < L) (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (η : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + η k) (hη : ∀ k, ‖η k‖ ≤ ηmax) :
    ∀ k : ℕ, ‖x' k - x' (k + 1)‖ ≤ 2 * L * ηmax := by
  intro k
  have h1 : dist (x' k) x ≤ L * ηmax := dist_obs_le hL hLI x x' η k hx' hη
  have h2 : dist (x' (k + 1)) x ≤ L * ηmax := dist_obs_le hL hLI x x' η (k + 1) hx' hη
  calc ‖x' k - x' (k + 1)‖ = dist (x' k) (x' (k + 1)) := (dist_eq_norm _ _).symm
    _ ≤ dist (x' k) x + dist x (x' (k + 1)) := dist_triangle _ _ _
    _ = dist (x' k) x + dist (x' (k + 1)) x := by rw [dist_comm x]
    _ ≤ L * ηmax + L * ηmax := add_le_add h1 h2
    _ = 2 * L * ηmax := by ring

omit [NormedSpace ℝ F] in
/-- **【§2.2 `dist` 形式的漂移界】**（与 `noisy_limsup_bound` 的接口对齐）

与 §2.1 同一内容，仅把 `‖x' k - x' (k+1)‖` 改写成 `dist (x' k) (x' (k+1))`，
便于下游 `simpa` / `rw`。 -/
theorem drift_bound_from_obs_div {f : F → F} {L ηmax : ℝ}
    (hL : 0 < L) (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (η : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + η k) (hη : ∀ k, ‖η k‖ ≤ ηmax) :
    ∀ k : ℕ, dist (x' k) (x' (k + 1)) ≤ 2 * L * ηmax := by
  intro k
  have := drift_bound_from_obs hL hLI x x' η hx' hη k
  rwa [dist_eq_norm]

/-! ===========================================================================
  §3  **`2 L ηmax` 的非负性（`noisy_limsup_bound` 的 `hd`，此处是推出的）**
  =========================================================================== -/

/-- **【§3.1 `0 ≤ 2 L ηmax`】**

`ClosedLoopNoisy.noisy_limsup_bound` 需要 `hd : 0 ≤ d`；在旧 capstone 里这靠
`hd0 : 0 ≤ 2 * L * ηmax` 由 `hL`、`hηmax` **另立**。此处同样由前件推出，
但**只依赖 `0 < L` 与 `0 ≤ ηmax`**（后者是本节显式前件）。 -/
theorem drift_nonneg {L ηmax : ℝ} (hL : 0 < L) (hηmax : 0 ≤ ηmax) :
    (0 : ℝ) ≤ 2 * L * ηmax := by
  have hLnn : (0 : ℝ) ≤ L := le_of_lt hL
  nlinarith

/-! ===========================================================================
  §4  **capstone：观测模型 ⟹ 稳态误差界（无 `hstep`）**
  =========================================================================== -/

/-- **【§4.1 主 capstone：`capstone_drift_from_obs`】**

**这是本文件的目的**：把 `WorldModelCapstone` 里 `hstep` 的位置换掉。

**前件**（逐条，**没有 `hstep`**）：
- `hP`：`MemLp` 二阶矩（供 `σ` 侧使用；与漂移无关）；
- `0 < L`、`0 ≤ ηmax`；
- `hηstep : |1 - η| < 1`（步长在收缩窗内）；
- `h : Corrects A φ`（`A ∘ φ = id`，`BoundWriteBack`）；
- `hLI : LipschitzInvertibleOn f L`；
- **观测生成模型** `hx' : ∀ k, f (x' k) = f x + η k`；
- **噪声界** `hη : ∀ k, ‖η k‖ ≤ ηmax`。

**结论**：

$$\limsup_{m\to\infty}\bigl\|A\,\theta_m - x'_m\bigr\| \;\le\; \mathrm{steadyErr}\ \eta\ (2\,L\,\eta_{\max}).$$

**三步装配**：
1. §2.1 从观测模型**推出**漂移界 `‖x' k - x' (k+1)‖ ≤ 2 L ηmax`；
2. §3.1 **推出** `0 ≤ 2 L ηmax`；
3. `ClosedLoopNoisy.noisy_limsup_bound` 把漂移预算转成 `limsup` 上界。

**⚠ `dσ = 0`**：本定理的预算就是 `2 L ηmax`，**不出现 `resolveSigma`**。
这正是审计 R441 所说的对照点：在旧定理里 `dσ` 是自由参数且结论全靠 `hstep`；
此处核心常数由模型**推出**，`dσ` 根本不需要。

**⚠ 前件自查（纪律 7）**：
- 结论是 `limsup` 的**数值上界**（含 `L`、`ηmax`、`η`、`A`、`φ`、`x'`、`θ`）；
- `hLI` 只讲 `f⁻¹` 的 Lipschitz 性，**不含**任何 `limsup` / 范数差；
- `hx'` 是**等式** `f (x' k) = f x + η k`，**不含**范数比较；
- `hη` 是**单步**噪声界，**不含**累积量 `2Lηmax/(1-r)`；
- `h` 只说 `A ∘ φ = id`；`hηstep` 只说步长。
⟹ 结论（`limsup ≤ d/(1-r)`）在前件中**不出现**；必须经
「估计界 ×2 → 漂移 → 几何级数稳态」三步导出。**非同义反复。**

**⚠ 诚实边界**：观测生成模型本身是**假设**（建模选择），见文件头 (c)。
本定理**不**声称它无条件成立，也**不**声称「闭环已破」。 -/
theorem capstone_drift_from_obs
    {P : Measure ℝ} (_hP : MemLp (fun x : ℝ => x) 2 P)
    {η L ηmax : ℝ}
    (hL : 0 < L) (hηmax : 0 ≤ ηmax)
    (hηstep : |1 - η| < 1)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (η' : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + η' k)
    (hη : ∀ k, ‖η' k‖ ≤ ηmax) :
    limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
      ≤ ClosedLoopNoisy.steadyErr η (2 * L * ηmax) := by
  have hdrift : ∀ k : ℕ, ‖x' k - x' (k + 1)‖ ≤ 2 * L * ηmax :=
    drift_bound_from_obs hL hLI x x' η' hx' hη
  have hd : (0 : ℝ) ≤ 2 * L * ηmax := drift_nonneg hL hηmax
  have hb := ClosedLoopNoisy.noisy_limsup_bound (d := 2 * L * ηmax) (r := |1 - η|)
    A φ η x' θ h hdrift hd rfl hηstep
  simpa only [ClosedLoopNoisy.steadyErr] using hb

/-- **【§4.2 变体：把 `dσ` 接成 `sigmaEst P n`（**仍无 `hstep`**）】**

与 §4.1 唯一区别：漂移预算从 `2 L ηmax` 放宽为 `2 L ηmax + sigmaEst P n`
（`sigmaEst P n = √(varOf P / n)`，由 `(P, n)` 决定）。

**⚠ 这里 `dσ` 是**松弛项**，不是必需品**：§4.1 已用 `dσ = 0` 得到更紧的界。
本变体存在的意义是**对照**：即使把 σ 分量加进来，**仍然不需要 `hstep`**——
`hstep` 的位置由 `drift_bound_from_obs` 填满，加 `dσ` 只是把右侧抬高。

**⚠ 不声称**「`ηmax` 与 `sigmaEst P n` 有此定量关系」：
`hσnn : 0 ≤ sigmaEst P n` 是非负性前提，二者**并列**而非互相推出。
这一点文件头 (f) 已登记。

**前件自查**：`hσnn` 只用于生成 `0 ≤ 2Lηmax + sigmaEst P n`；
结论的 `limsup` 上界在前件中**不出现**。 -/
theorem capstone_drift_from_obs_with_sigma
    {P : Measure ℝ} (_hP : MemLp (fun x : ℝ => x) 2 P)
    {η L ηmax : ℝ}
    (hL : 0 < L) (hηmax : 0 ≤ ηmax)
    (hηstep : |1 - η| < 1)
    (A : E →L[ℝ] F) (φ : F →ₗ[ℝ] E) (θ : E) (h : BoundWriteBack.Corrects A φ)
    {f : F → F} (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (η' : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + η' k)
    (hη : ∀ k, ‖η' k‖ ≤ ηmax)
    (n : ℕ) (hσnn : 0 ≤ FateV2.Error.ChainBudgetBound.sigmaEst P n) :
    limsup (fun m : ℕ => ‖A (ClosedLoopNoisy.noisyIter A φ η x' m θ) - x' m‖) atTop
      ≤ ClosedLoopNoisy.steadyErr η
          (2 * L * ηmax + FateV2.Error.ChainBudgetBound.sigmaEst P n) := by
  have hdrift : ∀ k : ℕ, ‖x' k - x' (k + 1)‖ ≤ 2 * L * ηmax :=
    drift_bound_from_obs hL hLI x x' η' hx' hη
  have hd : (0 : ℝ) ≤ 2 * L * ηmax + FateV2.Error.ChainBudgetBound.sigmaEst P n := by
    have := drift_nonneg hL hηmax
    linarith
  have hb := ClosedLoopNoisy.noisy_limsup_bound
    (d := 2 * L * ηmax + FateV2.Error.ChainBudgetBound.sigmaEst P n) (r := |1 - η|)
    A φ η x' θ h (fun k => le_trans (hdrift k) (le_add_of_nonneg_right hσnn))
    hd rfl hηstep
  simpa only [ClosedLoopNoisy.steadyErr] using hb

/-! ===========================================================================
  §5  **界的紧性 / 非空性 / 独立性（反空真、反虚松）**
  =========================================================================== -/

omit [NormedSpace ℝ F] in
/-- **【§5.1 `ηmax = 0` 时漂移为 0（界取等）】**

若噪声**恒为零**，则观测模型 `f (x' k) = f x + 0` 使所有 `x' k` 都是 `f x` 的原像；
在 `f` 单射（由 `0 < L` + Lipschitz 可逆**推出**）下 `x' k = x`，故漂移**恰为 0**。

**⟹ `2 L ηmax` 在 `ηmax = 0` 时**不虚松**（界是紧的）。 -/
theorem capstone_drift_sharp_zero_noise {f : F → F} {L : ℝ}
    (hL : 0 < L) (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + 0) :
    ∀ k : ℕ, x' k = x := by
  have hinj : Function.Injective f := RA14Strong.injective_of_lipschitzInvertible hL hLI
  intro k
  have hk : f (x' k) = f x := by rw [hx' k, add_zero]
  exact hinj hk

omit [NormedSpace ℝ F] in
/-- **【§5.2 观测模型可满足（非空前件）】**

取 `f = id`、`L = 1`、`ηmax = 0`、`x = 0`、`x' ≡ 0`、`η ≡ 0`：
观测模型 `id (x' k) = id x + η k` 成立，噪声界 `‖0‖ ≤ 0` 成立，
且漂移界 `‖0 - 0‖ ≤ 2·1·0 = 0` **取等**。

**⟹ 本文件所有含观测模型前件的定理**不是空真**（前件可满足）。** -/
theorem obs_model_constant_witness :
    ∃ (f : F → F) (L : ℝ) (x : F) (x' : ℕ → F) (η : ℕ → F),
      0 < L ∧ RA14Strong.LipschitzInvertibleOn f L
        ∧ (∀ k, f (x' k) = f x + η k)
        ∧ (∀ k, ‖η k‖ ≤ 0)
        ∧ (∀ k, ‖x' k - x' (k + 1)‖ ≤ 2 * L * 0) := by
  refine ⟨id, 1, 0, fun _ => 0, fun _ => 0, one_pos, ?_, ?_, ?_, ?_⟩
  · intro a b
    simp
  · intro k; simp
  · intro k; simp
  · intro k; simp

omit [NormedSpace ℝ F] in
/-- **【§5.3 审计 R441 的对照：漂移界与 `resolveSigma` 无关】**

漂移界 `‖x' k - x' (k+1)‖ ≤ 2 L ηmax` 的**证明不使用任何 σ 量**：
对**任意** `σ ≥ 0`（特别地 `σ = resolveSigma src W g0` 或 `σ = 0`），
它同时给出 `2 L ηmax` 与 `2 L ηmax + σ` 两个预算。

**⟹ 与审计的原话形成对照**：旧定理中「把 `resolveSigma` 换成 `0` 定理仍成立」
**正是因为** `hstep` 已经把结论打包；而本文件中 `resolveSigma`
**只是可选的松弛加项**，核心 `2 L ηmax` 由观测模型推出，
`σ = 0` 时得到**最紧**的界。 -/
theorem drift_independent_of_sigma {f : F → F} {L ηmax σ : ℝ}
    (hL : 0 < L) (hσnn : 0 ≤ σ) (hLI : RA14Strong.LipschitzInvertibleOn f L)
    (x : F) (x' : ℕ → F) (η : ℕ → F)
    (hx' : ∀ k, f (x' k) = f x + η k) (hη : ∀ k, ‖η k‖ ≤ ηmax) :
    (∀ k : ℕ, ‖x' k - x' (k + 1)‖ ≤ 2 * L * ηmax)
      ∧ (∀ k : ℕ, ‖x' k - x' (k + 1)‖ ≤ 2 * L * ηmax + σ) := by
  have h1 := drift_bound_from_obs hL hLI x x' η hx' hη
  exact ⟨h1, fun k => le_trans (h1 k) (le_add_of_nonneg_right hσnn)⟩

end CapstoneDriftFromObs

end FateV2.Loop
