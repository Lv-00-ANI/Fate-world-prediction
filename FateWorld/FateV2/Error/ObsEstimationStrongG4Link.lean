/-
  命运理论 · **G4 随机化观测 ⟹ 确定性估计误差界（真连接）**

  ============================================================================
  ⚠ 本文件的定位（**必读**）
  ============================================================================

  ## 0. 为什么是「新模块 + 新增定理」而不是改 `ObsEstimationStrong.lean`

  纪律要求**不修改任何已有模块的内容**。任务书 B 希望「在 `ObsEstimationStrong`
  里新增一条定理，其证明调用 `ObsErrorRandom.estimator_error_bound_random`」，
  目的是让主链真的**消费**随机版。本文件以
  **独立模块 + `RA14Strong.G4Link` 命名空间**达成该目的：

  * `import Fate.ObsEstimationStrong`（主链模块）、`import FateV2.Error.ObsErrorRandom`（G4 模块）；
  * 新定理的证明**逐字调用** `ObsErrorRandom.estimator_error_bound_random`；
  * **已有模块零改动**（纪律 2）。

  ## 1. 本文件证明的定理

  ### 1.1 主定理（**真**连接）

  ```lean
  theorem estimator_error_bound_random_links_deterministic
      {E : Type*} [SeminormedAddCommGroup E]
      {h : E → E} {L : ℝ} (hLI : LocallyDecodable h L)
      (x : E) (g : E → E) {ηmax : ℝ} (η₀ : E) (hL : 0 ≤ L) (hη : dist η₀ 0 ≤ ηmax)
      (hfull : ∀ (ν : Measure PUnit), ν {()} ≠ 0 → ∀ P : PUnit → Prop,
                 (∀ᵐ ω ∂ν, P ω) → P ()) :
      dist (g (h x + η₀)) x ≤ L * ηmax
  ```

  **内容**：把 `ObsErrorRandom.estimator_error_bound_random`（随机噪声 `η : Ω → E`、
  结论为 `∀ᵐ`）用在**单点概率空间** `(PUnit, Measure.dirac ())` 上，
  噪声取常值 `fun _ => η₀`；再用 `hfull`（「单点满测 ⟹ 几乎必然即逐点」）
  在唯一一点 `()` 处求值，喂入解码器 `g`，即得**确定性逐点**界。

  ### 1.2 推论（**彻底自足**，无 `hfull` 参数）

  ```lean
  theorem obs_error_single_point_random     -- §2
  ```

  在 `PUnit` + `Measure.dirac ()` 上把 `hfull` 的实质内容**就地证掉**。
  这是可直接下游使用的最终形式，也是「随机版 ⟹ 确定性版」的完整闭环。

  ## 2. ⚠ 防同义反复核对（本项目最高频问题）

  逐条检查前件**有没有把结论包进去**：

  | 前件 | 关于什么 | 是否提及结论 `dist (g (h x + η₀)) x` |
  |---|---|---|
  | `hLI : LocallyDecodable h L` | `h` 有一个 `L`-Lipschitz 右逆（**存在性**先验） | **否** |
  | `hL : 0 ≤ L` | 常数非负（技术性） | **否** |
  | `hη : dist η₀ 0 ≤ ηmax` | 噪声幅度 | **否** |
  | `hfull` | 「`ν {()} ≠ 0` ⟹ `∀ᵐ P` ⟹ `P ()`」，对**任意谓词 `P`** 成立 | **否**（`P` 全称量化，只交换量词） |

  **没有任何前提提到结论中的距离表达式。** 结论必须由
  「解码器 Lipschitz 性 + `g ∘ h = id` + 噪声有界」（`obs_error_le_global` 的三段论证）
  真正推出——本文件只是把它**经 `ObsErrorRandom` 的随机版绕一圈取回**。

  **⚠ 与旧 `ObsEstimationStrong.estimator_error_bound` 的关键差别**：
  旧定理带前件 `hx' : h x' = h x + η`，结论为
  `dist (chooseEstimator h (h x + η)) x'`；由单射 ⟹ `chooseEstimator h (h x+η) = x'`
  ⟹ 左边恒 `0`（**同义反复**，`ObsEstSharp` 头部已裁决）。
  本文件**没有 `x'`**：比较对象是**真值 `x`**，左边一般不为 `0`。

  ## 3. 诚实边界

  1. **本模块无 `chooseEstimator` 版本**：`ObsEstimationStrong.chooseEstimator` 的
     `L`-Lipschitz 性**并非**该模块已证引理（模块只证了 `inverse_lipschitz` /
     `estimator_error_bound`，后者是弱形式）。若要喂 `chooseEstimator h`，
     须自行构造 `LocallyDecodable`，而该构造**在像外点处不可证**
     （`Classical.choose` 的像外分支不受 $(\star)$ 控制）。
     ⟹ 本文件取**解码器 `g` 为参数**（带 `LipschitzWith` 前件），
     **不假装**证出 `chooseEstimator h` 的全局 Lipschitz 性。
  2. **不**声称 A14 被证明：A14 仍是 `.empirical`（`Fate/Stage0/LabelAudit.lean`）。
  3. **不**证期望版（`estimator_error_bound_random_expect`）的确定性对应：
     单点测度下 `∫` 退化为常值，无独立内容。
  4. 概率空间固定为 `PUnit` + `Measure.dirac ()`；一般 `(Ω, μ)` 上的版本即定理 1.1
     的 `hfull` 形态。

  **⚠ 全文零 `sorry` / `admit` / `axiom` / `trivial` / `→ True`。**
  ============================================================================
-/

import FateWorld.FateV2.Modeling.ObsEstimationStrong
import FateWorld.FateV2.Error.ObsErrorRandom
namespace FateV2.Error

open FateV2.Modeling
namespace RA14Strong

namespace G4Link

open MeasureTheory

open FateV2.Error.ObsErrorRandom

open FateV2.Error.ObsEstSharp (LocallyDecodable)

noncomputable section

/-!
  # Error · ObsEstimationStrongG4Link

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ObsEstimationStrongG4Link.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ObsEstimationStrong, ObsErrorRandom
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  ⭐⭐⭐ **主定理：随机版 ⟹ 确定性版（真的调用）**
  =========================================================================== -/

/-- ⭐⭐⭐ **【G4 与确定性版的连接】随机版在单点分布下回落到确定性逐点界**

**证明逐字调用 `ObsErrorRandom.estimator_error_bound_random`**（G4 主定理），
把它在 `(PUnit, Measure.dirac ())` 上的 `∀ᵐ` 结论经 `hfull` 落到**唯一的点**，
再喂入解码器 `g`。

**⟹ `ObsErrorRandom` 不再是孤岛**：它的主定理在此被**真正使用**，
且本定理结论是**确定性逐点误差界**——与 `ObsEstimationStrong` 的问题同域。 -/
theorem estimator_error_bound_random_links_deterministic
    {E : Type*} [SeminormedAddCommGroup E]
    {h : E → E} {L : ℝ} (hLI : LocallyDecodable h L)
    (x : E) (g : E → E) (hg : ∀ z : E, g (h z) = z) (hLip : LipschitzWith (L.toNNReal) g)
    {ηmax : ℝ} (η₀ : E) (hL : 0 ≤ L) (hη : dist η₀ 0 ≤ ηmax)
    (hfull : ∀ (ν : Measure PUnit), ν {(())} ≠ 0 → ∀ P : PUnit → Prop,
      (∀ᵐ ω ∂ν, P ω) → P ()) :
    dist (g (h x + η₀)) x ≤ L * ηmax := by
  -- ① 调用随机版主定理（概率空间 = `(PUnit, δ_())`，噪声 = 常值 `η₀`）
  have hrand :
      ∀ᵐ _ω ∂(Measure.dirac () : Measure PUnit),
        ∀ g' : E → E, (∀ z : E, g' (h z) = z) → LipschitzWith (L.toNNReal) g' →
          dist (g' (h x + η₀)) x ≤ L * ηmax :=
    estimator_error_bound_random (μ := Measure.dirac ()) hLI (fun _ : PUnit => η₀) hL
      (Filter.Eventually.of_forall (fun _ => hη))
  -- ② 把 `∀ᵐ` 交换成逐点（`hfull` 只做量词交换，不含结论）
  exact hfull (Measure.dirac ()) (by simp)
    (fun _ : PUnit => ∀ g' : E → E, (∀ z : E, g' (h z) = z) →
      LipschitzWith (L.toNNReal) g' → dist (g' (h x + η₀)) x ≤ L * ηmax) hrand
    g hg hLip

end

end G4Link

end RA14Strong

end FateV2.Error