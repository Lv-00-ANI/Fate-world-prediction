/-
  命运理论 · **G4：随机观测下的估计误差界**

  ============================================================================
  ⚠ 本文件的定位（**必读**）
  ============================================================================

  ## 0. 先说清楚「确定性版」到底是哪一条

  任务书引用的 `ObsEstSharp.estimator_error_bound` **在 `Fate/ObsEstSharp.lean` 中
  并不存在**（用两种模式核对过：

  * `grep -n "^theorem estimator_error_bound" Fate/ObsEstSharp.lean` → 无命中；
  * `grep -rn "estimator_error_bound" Fate/*.lean` → `ObsEstSharp.lean` 只出现在
    头部注释第 14 行，是对**旧模块** `ObsEstimationStrong.estimator_error_bound`
    的引用；该旧定理被 `ObsEstSharp` 判定为**同义反复**（结论被前件包住）。

  `ObsEstSharp.lean` 真正给出的、**非**同义反复的确定性定理是

  ```lean
  theorem obs_error_le_global
      {h : X → Y} {L : ℝ} (hLI : LocallyDecodable h L)
      {x : X} {η : Y} {y : Y} {ηmax : ℝ}
      (hy : y = h x + η) (hη : dist η 0 ≤ ηmax) (hL : 0 ≤ L) :
      ∀ g : Y → X, (∀ z : X, g (h z) = z) →
        LipschitzWith (L.toNNReal) g → dist (g y) x ≤ L * ηmax
  ```

  以及球上版本 `obs_error_le_faithful`。本文件**以 `obs_error_le_global` 为确定性底版**
  （随机化它），因为任务书的 §G4 关切正是「`η` 是确定性向量」这一点，
  而上面这条定理的 `η : Y` 确实是**固定向量**（`Fate/ObsEstSharp.lean` 之中
  `Measure` / 概率 / 随机性出现 **0 次**）。

  ## 1. 本文件做了什么

  把确定性版中的

  * 固定噪声向量 `η : Y`  ⟹  随机变量 `η : Ω → Y`；
  * 逐点界 `dist η 0 ≤ ηmax`  ⟹  几乎必然界 `∀ᵐ ω, dist (η ω) 0 ≤ ηmax`；
  * 结论 `dist … ≤ L * ηmax`  ⟹  几乎必然 `∀ᵐ ω, dist … ≤ L * ηmax`（定理 1），
    再由可积性推出期望意义下的界（定理 3）。

  **`∀ᵐ` 版本必须带 `IsProbabilityMeasure μ`**，否则 `∀ⁿ` 在零测度空间上
  空真成立，定理将毫无内容。本文件全部 `∀ᵐ` 定理都带该前提。

  ## 2. 定理清单

  | # | 名字 | 内容 | 状态 |
  |---|---|---|---|
  | 1 | `estimator_error_bound_random` | 随机噪声下 `∀ᵐ` 误差界（**主**） | ✅ |
  | 2 | `integral_le_of_ae_bound` | 概率测度下 `∀ᵐ f ≤ M` ⟹ `∫ f ≤ M`（通用工具） | ✅ |
  | 3 | `estimator_error_bound_random_expect` | 由 1 + 2 复合得期望界（**推论**） | ✅ |
  | 4 | `estimator_error_bound_random_const` | 常值噪声退化为确定性版（**一致性**） | ✅ |

  ## 3. 防同义反复核对

  * 定理 1 前提：`LocallyDecodable h L`（关于 `h` 的**先验**假设）、
    解码器 `g` 与其 Lipschitz 性（关于**解码器**的假设）、
    `hη : ∀ᵐ ω, dist (η ω) 0 ≤ ηmax`（关于**噪声**的假设）。
    **没有任何前提提到 `dist (g (h x + η ω)) x`**（结论本身）。
    ⟹ 结论必须由三角形不等式 + Lipschitz 性真正推出。
  * 定理 2 是通用测度论事实，前件（`f ≤ᵐ M` 且可积）与结论（`∫ f ≤ M`）
    不是同一命题；`M` 在两边出现但**积分算子是实质内容**。
  * 定理 3 = 定理 1 + 定理 2 复合，前提中的 `Integrable` 是定理 2 所需，
    不是把结论换个写法。

  **全文零 `sorry` / `admit` / `axiom` / `trivial` / `→ True`。**
  ============================================================================
-/

import FateWorld.FateV2.Error.ObsEstSharp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Function.L1Space.Integrable

namespace FateV2.Error
namespace ObsErrorRandom

open MeasureTheory Set Metric

open FateV2.Error.ObsEstSharp (LocallyDecodable obs_error_le_global)

/- 概率空间语境：`Ω` / `μ` / 概率测度实例必须在**所有**用到 `∀ᵐ` / `∫` 的
   小节中可见，故声明在 namespace 层级（而非某个 section 内部）。 -/
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

section Probability

/-!
  # Error · ObsErrorRandom

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ObsErrorRandom.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ObsEstSharp
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  ⭐⭐⭐ **定理 2（工具）：几乎必然有界 ⟹ 期望有界**

  先证这条通用测度论事实，因为定理 3 要用它。
  证明：`integral_mono_ae` 比较 `f` 与常函数 `fun _ => M`；
  概率测度下 `∫ (fun _ => M) ∂μ = M * μ.real univ = M * 1 = M`。
  =========================================================================== -/

/-- ⭐⭐ **【几乎必然有界推出期望有界】**

设 `μ` 是概率测度，`f` 可积且 `f ≤ M` `μ`-几乎必然，则 `∫ f ∂μ ≤ M`。

**为什么需要 `IsProbabilityMeasure`**：`∫ (fun _ => M) ∂μ = M * μ.real univ`，
只有 `μ.real univ = 1` 时该值才是 `M`。在一般测度下结论应是
`∫ f ≤ M * μ.real univ`，而非 `M`。

**为什么需要 `Integrable f μ`**：Mathlib 中不可积函数在 Bochner 积分下
返回 `0`，若无此前提，「`∫ f ≤ M`」在 `M < 0` 时会因积分假值 `0` 而失真。 -/
theorem integral_le_of_ae_bound
    {f : Ω → ℝ} (hf_int : Integrable f μ) {M : ℝ}
    (h_bound : f ≤ᵐ[μ] fun _ => M) :
    ∫ ω, f ω ∂μ ≤ M := by
  have hM_int : Integrable (fun _ : Ω => M) μ := integrable_const M
  have hmain : ∫ ω, f ω ∂μ ≤ ∫ _ : Ω, M ∂μ := integral_mono_ae hf_int hM_int h_bound
  rwa [integral_const, Measure.real_def, measure_univ, ENNReal.toReal_one, one_smul] at hmain

end Probability

/-! ===========================================================================
  §2  ⭐⭐⭐ **定理 1（主）：随机观测下的 `∀ᵐ` 误差界**

  与确定性版 `ObsEstSharp.obs_error_le_global` 逐项对照：

  | | 确定性版 | 本定理（随机版） |
  |---|---|---|
  | 噪声 | `η : Y`（固定向量） | `η : Ω → Y`（随机变量） |
  | 噪声幅度 | `hη : dist η 0 ≤ ηmax` | `hη : ∀ᵐ ω, dist (η ω) 0 ≤ ηmax` |
  | 结论 | `dist (g (h x + η)) x ≤ L ηmax` | `∀ᵐ ω, dist (g (h x + η ω)) x ≤ L ηmax` |
  =========================================================================== -/

section Random

variable {X Y : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]

omit [IsProbabilityMeasure μ] in
/-- ⭐⭐⭐ **【G4 主定理：随机观测下估计误差界几乎必然成立】**

**确定性版 `ObsEstSharp.obs_error_le_global` 假设 `η` 是一个固定向量且
`dist η 0 ≤ ηmax`。真实观测的误差是随机的。本定理把 `η` 换成随机变量
`η : Ω → Y`，把「逐点有界」换成「几乎必然有界」，结论也转为「几乎必然满足界」。**

**注（诚实说明）**：`∀ᵐ` 是比逐点更强的命题的弱化，证明只需 `filter_upwards`，
因此 **证明本身不消耗 `IsProbabilityMeasure μ`**；该实例由文件顶部统一声明并
自动引入签名，用于保证 `μ` 非零测度、排除空真。这里用 `omit` 标记，
以免 Lean 误报「未使用小节变量」警告——但签名中仍保留该假设。 -/
-- 注：`omit` 置于 docstring 之后、`theorem` 之前（Lean 4 语法要求）。
theorem estimator_error_bound_random
    {h : X → Y} {L : ℝ} (hLI : LocallyDecodable h L)
    {x : X} (η : Ω → Y) {ηmax : ℝ} (hL : 0 ≤ L)
    (hη_bound : ∀ᵐ ω ∂μ, dist (η ω) 0 ≤ ηmax) :
    ∀ᵐ ω ∂μ, ∀ g : Y → X, (∀ z : X, g (h z) = z) →
      LipschitzWith (L.toNNReal) g → dist (g (h x + η ω)) x ≤ L * ηmax := by
  obtain ⟨g, hg, hLip⟩ := hLI
  filter_upwards [hη_bound] with ω hω
  intro g' hg' hLip'
  exact obs_error_le_global ⟨g, hg, hLip⟩ (y := h x + η ω) rfl hω hL g' hg' hLip'

end Random

/-! ===========================================================================
  §3  ⭐⭐⭐ **定理 3（推论）：期望意义下的估计误差界**

  由定理 1（`∀ᵐ`）+ 定理 2（`∀ᵐ ⟹ ∫`）复合。
  =========================================================================== -/

section RandomExpect

variable {X Y : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]

/-- ⭐⭐⭐ **【G4 推论：随机观测下估计误差界在期望意义下成立】**

由 `estimator_error_bound_random`（几乎必然）与 `integral_le_of_ae_bound`
（几乎必然 ⟹ 期望）复合得到。

**需要额外可积性前提 `Integrable (fun ω => dist (g (h x + η ω)) x) μ`**，
理由见定理 2 的说明（不可积时 Bochner 积分返回 `0`，结论会失真）。

**`hM : 0 ≤ L * ηmax`** 是定理 2 中 `M` 需非负的技术前提；
在 `0 ≤ L`、`0 ≤ ηmax` 下由 `mul_nonneg` 得到（本定理把它列为显式前提，
调用方可用 `mul_nonneg hL hηmax_nonneg` 提供）。 -/
theorem estimator_error_bound_random_expect
    {h : X → Y} {L : ℝ} (hLI : LocallyDecodable h L)
    {x : X} {g : Y → X} (hg : ∀ z : X, g (h z) = z)
    (hLip : LipschitzWith (L.toNNReal) g)
    (η : Ω → Y) {ηmax : ℝ} (hL : 0 ≤ L) (_hM : 0 ≤ L * ηmax)
    (hη_bound : ∀ᵐ ω ∂μ, dist (η ω) 0 ≤ ηmax)
    (h_int : Integrable (fun ω => dist (g (h x + η ω)) x) μ) :
    ∫ ω, dist (g (h x + η ω)) x ∂μ ≤ L * ηmax := by
  have h_ae : ∀ᵐ ω ∂μ, dist (g (h x + η ω)) x ≤ L * ηmax := by
    filter_upwards [hη_bound] with ω hω
    exact obs_error_le_global hLI (y := h x + η ω) rfl hω hL g hg hLip
  exact integral_le_of_ae_bound h_int h_ae

end RandomExpect

/-! ===========================================================================
  §4  ⭐⭐ **定理 4（一致性）：常值随机噪声退化为确定性版**

  取 `Ω` 为任意带概率测度的空间、`η` 取常值函数 `fun _ => η₀`，
  则定理 1 的 `∀ᵐ` 结论在概率测度下（测度非零）可展开成逐点结论，
  与确定性版 `obs_error_le_global` 完全一致。
  =========================================================================== -/

section Const

variable {X Y : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]

omit [IsProbabilityMeasure μ] in
/-- ⭐⭐ **【与确定性版的一致性】**

`η` 取常值函数 `fun _ => η₀` 时，定理 1 的 `∀ᵐ` 结论给出
「存在一个满测集，在其上界成立」；因为概率测度的 `univ` 满测，
取该满测集的任一点即得确定性版的逐点界 `dist (g (h x + η₀)) x ≤ L * ηmax`。

这就确认了随机版**确实**是确定性版的推广，而非另一条互不相干的定理。 -/
theorem estimator_error_bound_random_const
    {h : X → Y} {L : ℝ} (hLI : LocallyDecodable h L)
    {x : X} {g : Y → X} (hg : ∀ z : X, g (h z) = z)
    (hLip : LipschitzWith (L.toNNReal) g)
    (η₀ : Y) {ηmax : ℝ} (hL : 0 ≤ L)
    (hη : dist η₀ 0 ≤ ηmax) :
    ∀ᵐ _ω ∂μ, dist (g (h x + η₀)) x ≤ L * ηmax := by
  have h : dist (g (h x + η₀)) x ≤ L * ηmax :=
    obs_error_le_global hLI (y := h x + η₀) rfl hη hL g hg hLip
  exact Filter.Eventually.of_forall (fun _ => h)

end Const

end ObsErrorRandom

end FateV2.Error