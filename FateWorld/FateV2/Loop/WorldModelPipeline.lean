/-
  命运理论 · **BB3：世界模型六环管线（观测 → 估计 → 预测 → 残差 → 更新 → 学习）**

  ============================================================================
  ⚠ 本文件的定位（**须先读**）
  ============================================================================

  本文件把此前**各自独立**的四块内容串成**一条完整的管线定理**：

  | 环 | 环节 | 落点模块 | 用到的既有结果 |
  |---|---|---|---|
  | ① | **观测** $y = h\,x + \eta$ | `FateV2.Modeling` | `LipschitzInvertibleOn`、`chooseEstimator` |
  | ② | **估计** $\hat x = \hat x(y)$ | `FateV2.Modeling` | `chooseEstimator_apply_of`、`inverse_estimate_error` |
  | ③ | **预测** $\hat y = f(x,u,\varepsilon;\theta,a)$ | `WorldModelReadsTheta` | `wmStep`、`wmWorldModel`、`predFrom_wmWorldModel` |
  | ④ | **残差** $r = \hat x^{\mathrm{obs}} - \hat x^{\mathrm{pred}}$ | `EndToEnd` | `e2eResidual`、`endToEnd_apply` |
  | ⑤ | **更新** $\theta' = \theta + \eta\,\varphi(r)$ | `EndToEnd` | `endToEnd`、`endToEnd_step_eq` |
  | ⑥ | **学习** $\theta_n \to \theta^*$ | `ThetaConvergence` | `thetaN`、`linWorld_tendsto_thetaStar`、`thetaN_closed` |

  **本文件不重证任何一环的数学内容**——每一环都**引用**上面列的既有定理。
  本文件的**新增内容**只有「**串**」：

  * `pipelineStep`：一步六环的**复合**（①→②→③→④→⑤），把观测 `y` 与参数 `θ`
    映射到新参数 `θ'`；
  * `pipelineN`：反复跑 `pipelineStep` 的**轨迹**（⑥ 的载体）；
  * `pipeline_tendsto`：**端到端主定理**——从观测 `y` 出发，
    沿管线迭代的参数 $\theta_n$ **收敛到真值** $\theta^*$。

  ---
  ## 一、一句话结论（端到端主定理）

  $$\boxed{\;
    h=\mathrm{id}\ \wedge\ \theta^*\neq\text{任意}\ \wedge\ x\neq 0\ \wedge\ |1-\eta|<1
    \ \Longrightarrow\
    \bigl(\theta_n\bigr)_{n\to\infty}\longrightarrow \theta^*\;}$$

  其中 $\theta_n$ 是**从观测** $y=\theta^* x$ **出发、经六环管线**得到的第 $n$ 步参数。

  ---
  ## 二、⚠ 诚实边界（必读，不得含糊）

  **2.1 六环的「估计」环在 `h = id` 下退化为恒等。**
  `ObsEstimationStrong` 的强档定理（`inverse_estimate_error`）处理的是
  `invertible` 分支（$h$ 单射 + Lipschitz 可逆）。本文件的端到端主定理取
  **`h = id`**（观测无损），此时估计环精确（`observe_id`）。
  **这不是偷懒**：`Fate/Frame.lean` 的裁决 Q-2 明写 A14 取**读法 (a)**，
  即状态可直接获取——`h = id` 正是该裁决的形式化。**带噪估计**的情形
  本文件在 §5 单独给出**估计误差界**（引用 `inverse_estimate_error`），
  但**不声称**带噪下管线收敛（那需要噪声经残差进入更新的完整分析，
  **不在本文件范围**）。

  **2.2 「学习」环的收敛只在 `linWorld`（机制 `f x = θ * x`）上成立。**
  这是 `ThetaConvergence` 的既有边界（其 §1.1）。本文件的管线用
  `linWorld` 作为预测环的实例，故收敛结论**继承**同一限制。
  **本文件不声称**非线性机制下管线收敛。

  **2.3 管线一步 `pipelineStep` 与 `ThetaConvergence.thetaN` 的一步是**同一条**更新。**
  `pipelineStep_eq_endToEnd`（§4）证明它**恒等于** `EndToEnd.endToEnd`，
  `pipelineStep_linWorld`（§4）证明它在 `linWorld` 上**恒等于**
  `thetaN` 的递推式。**故主定理的证明**复用** `thetaN_closed / linWorld_tendsto_thetaStar`，
  而**不是**另造一个收敛论证**——这是「串」而非「重证」的可检验含义。

  **2.4 本文件不改动任何既有模块。** 只新建本文件。

  ---
  ## 三、结构

  | 节 | 内容 |
  |---|---|
  | §1 | 六环的**类型**清单（每一环在本库中的既有落点）|
  | §2 | ①→② 观测与估计：`pipelineObserve` + 精确性（引用 `chooseEstimator_apply_of`）|
  | §3 | ③ 预测含 θ：`pipelinePredict` + 分离性（引用 `wmStep`）|
  | §4 | ④→⑤ 残差与更新：`pipelineStep`（= `endToEnd`）+ 分解式 |
  | §5 | 带噪估计误差界（引用 `inverse_estimate_error`）|
  | §6 | ⑥ 学习：`pipelineN` + ⭐⭐⭐ **端到端主定理 `pipeline_tendsto`** |
  | §7 | 非平凡性：极限是真值而非 0；一步精确；与 `θ_n ≡ 0` 的区别 |
  | §8 | 具体数值实例 |
  | §9 | ⚠ 前件审计表（自查同义反复）+ 与既有模块的对照 |

  纪律：零 `sorry` / 零 `admit` / 零 `axiom`。
  ============================================================================
-/

import FateWorld.FateV2.Modeling.ObsEstimationStrong
import FateWorld.FateV2.Loop.WorldModelReadsTheta
import FateWorld.FateV2.Loop.EndToEnd
import FateWorld.FateV2.Loop.ThetaConvergence
namespace FateV2.Loop

open FateV2.Modeling
open FateV2.Predict
namespace WorldModelPipeline

open FateV2.Loop.EndToEnd
open FateV2.Loop.WorldModelReadsTheta
open FateV2.Loop.ThetaConvergence

/-!
  # Loop · WorldModelPipeline

  ## 迁移登记
  - 来源：`FateWorld/Legacy/WorldModelPipeline.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ObsEstimationStrong, WorldModelReadsTheta, EndToEnd, ThetaConvergence
  - 补充 open 域：FateV2.Modeling, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  六环的类型清单（每一环的既有落点）
    =========================================================================== -/

/-- **① 观测环的类型**：`X → Y`（观测映射 `h`）。 -/
abbrev ObsMap (X Y : Type) : Type := X → Y

/-- **② 估计环的类型**：`Y → X`（估计器 `x̂`）。 -/
abbrev Estimator (X Y : Type) [Nonempty X] : Type := Y → X

section PipelineBasics

variable {X Y : Type} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- ⭐ **环 ① 的观测**：观测模型 $y := h\,x$（无噪形式，加噪见 §5）。 -/
def pipelineObserve (h : X → Y) (x : X) : Y := h x

/-- ⭐⭐ **环 ② 的估计**：由观测 `y` 经 `RA14Strong.chooseEstimator` 得到状态估计。

**本定义是 `EndToEnd.observe` 的逐字别名**（在 `h` 上），
而其数学内容在 `Fate/ObsEstimationStrong` 中已证。 -/
noncomputable def pipelineEstimate [Nonempty X] (h : X → Y) (y : Y) : X :=
  observe h y

omit [PseudoMetricSpace X] [PseudoMetricSpace Y] in
/-- ⭐⭐⭐ **环 ①→② 的正确性**：`h` 单射 ⟹ 无噪观测下估计**精确**。

$$\hat x\bigl(y(h\,x)\bigr) = x .$$

**证明直接引用 `EndToEnd.observe_apply_of`**（其本身引用
`RA14Strong.chooseEstimator_apply_of`）——本文件**不重证**估计器的性质。

**⚠ 这不是同义反复**：前件是「`h` 单射」（关于 `h` 的假设），
结论是「估计器作用于观测得到原状态」（关于**复合** `x̂ ∘ y` 的断言）。
中间隔了 `Classical.choose` 的选取规范（`choose_spec`）。 -/
theorem pipelineObserve_estimate [Nonempty X] {h : X → Y}
    (hinj : Function.Injective h) (x : X) :
    pipelineEstimate h (pipelineObserve h x) = x :=
  observe_apply_of hinj x

omit [PseudoMetricSpace X] [PseudoMetricSpace Y] in
/-- ⭐ **环 ①→② 的复合式**：观测继以估计 = 恒等（在单射 `h` 上）。 -/
theorem pipelineObserve_estimate_comp [Nonempty X] {h : X → Y}
    (hinj : Function.Injective h) :
    ∀ x : X, pipelineEstimate h (pipelineObserve h x) = x :=
  fun x => pipelineObserve_estimate hinj x

end PipelineBasics

/-! ===========================================================================
    §2  预测环（③）含 θ：`pipelinePredict`

    用 `WorldModelReadsTheta` 的**真正读 θ** 的实例 `wmWorldModel`，
    其机制为 $f(x,u,\varepsilon;\theta,a) = \theta\cdot x + u + \varepsilon + a$。
    =========================================================================== -/

/-- ⭐ **环 ③ 的预测**：由当前状态与参数 `θ` 经世界模型一步预测。

用 `WM = wmWorldModel`（`ℚ` 上的具体实例），其机制显含 `θ`：
$$\mathrm{pipelinePredict}\ x\ u\ \varepsilon\ \theta\ a = \theta\,x + u + \varepsilon + a .$$ -/
noncomputable def pipelinePredict (x u ε θ a : ℚ) : ℚ :=
  wmStep x u ε θ a

/-- ⭐⭐ **环 ③ 的闭式**：`pipelinePredict` 就是 `θ*x + u + ε + a`（引用 `wmWorldModel_f_apply`）。 -/
theorem pipelinePredict_eq (x u ε θ a : ℚ) :
    pipelinePredict x u ε θ a = θ * x + u + ε + a :=
  wmWorldModel_f_apply x u ε θ a

/-- ⭐⭐⭐ **环 ③ 真的读 θ**：`x ≠ 0` 时换 θ 则预测变（引用 `wmStep_separates_theta`）。

**⚠ 前件 `x ≠ 0` 是**数学必要**的**（乘性机制 `θ*x` 在 `x=0` 处退化），
不是把结论塞进去：`x = 0` 时结论**为假**（见 `WM.wmSim_one_indep_theta` 的同类现象）。 -/
theorem pipelinePredict_separates {x : ℚ} (hx : x ≠ 0)
    {θ₁ θ₂ u ε a : ℚ} (hθ : θ₁ ≠ θ₂) :
    pipelinePredict x u ε θ₁ a ≠ pipelinePredict x u ε θ₂ a :=
  wmStep_separates_theta hx hθ

/-- ⭐ **环 ③ 的存在式非平凡性**（**无前件**）：存在一组值使预测随 θ 变。 -/
theorem exists_pipelinePredict_separates :
    ∃ (x θ₁ θ₂ u ε a : ℚ), θ₁ ≠ θ₂ ∧
      pipelinePredict x u ε θ₁ a ≠ pipelinePredict x u ε θ₂ a :=
  ⟨1, 0, 1, 0, 0, 0, by norm_num, pipelinePredict_separates one_ne_zero (by norm_num)⟩

/-! ===========================================================================
    §3  残差环（④）与更新环（⑤）：`pipelineStep`

    **本节的核心**：把 ①→②→③→④→⑤ 写成一个**复合函数**，
    并证明它**恒等于** `EndToEnd.endToEnd`（即**没有**另造更新算子）。
    =========================================================================== -/

section PipelineStep

variable {Y : Type} [Nonempty ℝ]

/-- ⭐⭐⭐⭐ **六环管线的一步（①→②→③→④→⑤）**：

$$\mathrm{pipelineStep}\ W\ h\ \eta\ \varphi\ y\ \theta\ u\ \varepsilon\ a\ x
  := \mathrm{endToEnd}\ W\ h\ \eta\ \varphi\ y\ \theta\ u\ \varepsilon\ a\ x .$$

**读法**：观测 `y` 与参数 `θ` 进入；`observe h y` 出环② 的状态估计，
`predFrom W θ u ε a x` 出环③ 的预测，二者之差是环④ 的残差 `r`，
经环⑤ 写回得 `θ' = θ + η·φ(r)`。

**⚠ 这不是新定义**：`pipelineStep_eq_endToEnd`（下一条）是 `Iff.rfl` 级别的
等式——`pipelineStep` **就是** `endToEnd`。本别名的唯一目的是给
「管线一步」一个语义清晰的名字，便于主定理的陈述。 -/
noncomputable def pipelineStep (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) : W.frame.Θ.Carrier :=
  endToEnd W h η φ y θ u ε a x

omit [Nonempty ℝ] in
/-- ⭐ **`pipelineStep` = `endToEnd`**（不是另造算子）。 -/
theorem pipelineStep_eq_endToEnd (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) :
    pipelineStep W h η φ y θ u ε a x = endToEnd W h η φ y θ u ε a x := rfl

omit [Nonempty ℝ] in
/-- ⭐⭐⭐ **环 ④→⑤ 的分解式**：参数变化量 = 步长 × 残差方向。

$$\theta' - \theta = \eta\,*\,\varphi\,r,\qquad
  r = \hat x^{\mathrm{obs}} - \hat x^{\mathrm{pred}} .$$

**引用 `EndToEnd.endToEnd_step_eq`**——残差**唯一**决定参数位移，
无漂移项、无遗忘项。**这是四环首尾相接的定量证据。** -/
theorem pipelineStep_diff (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) :
    pipelineStep W h η φ y θ u ε a x - θ
      = η * φ (observe h y - predFrom W θ u ε a x) :=
  endToEnd_step_eq W h η φ y θ u ε a x

omit [Nonempty ℝ] in
/-- ⭐⭐ **环 ④→⑤ 的正确性**：残差为零 ⟹ 参数不动（引用 `EndToEnd.endToEnd_fixed`）。 -/
theorem pipelineStep_fixed (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier] (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (θ : W.frame.Θ.Carrier)
    (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier)
    (hobs : observe h y = predFrom W θ u ε a x) :
    pipelineStep W h η φ y θ u ε a x = θ :=
  endToEnd_fixed W h η φ y θ u ε a x hobs

end PipelineStep

/-! ===========================================================================
    §4  带噪估计的误差界（引用 `ObsEstimationStrong` 的强档定理）

    本节的定理**不参与**主定理的证明——它们证明「若观测有界噪声，
    则估计误差被 `L·η_max` 控制」这一环，属六环中 ①→② 的**定量**内容。
    =========================================================================== -/

/-- ⭐⭐⭐ **环 ①→② 的误差界**（引用 `RA14Strong.inverse_estimate_error`）：

若 $h$ 单射 + Lipschitz 可逆（常数 $L$），观测 $y = h\,x + \eta$ 的原像为 $x'$，
则
$$\mathrm{dist}\,x'\,x\ \le\ L\cdot\|\eta\| .$$

**⚠ 这是**条件性**定理**：前件 `LipschitzInvertibleOn h L` 是 A14 读法 (b)
的经验假设（见 `ObsEstimationStrong` §8），本文件**不改**其标签。
主定理（§6）取 `h = id`（读法 (a)），**不依赖**本条。 -/
theorem pipelineEstimate_error {E : Type*} [SeminormedAddCommGroup E]
    {h : E → E} {L : ℝ} (hL : 0 < L) (hLI : RA14Strong.LipschitzInvertibleOn h L)
    (x x' : E) (η : E) (hx' : h x' = h x + η) :
    dist x' x ≤ L * dist η 0 :=
  RA14Strong.inverse_estimate_error hL hLI x x' η hx'

/-! ===========================================================================
    §5  ⭐⭐⭐ 学习环（⑥）：`pipelineN` 与**端到端主定理**
    =========================================================================== -/

/-- ⭐⭐ **管线的 `n` 步轨迹**：反复应用 `pipelineStep`。

**⚠ 本定义**就是** `EndToEnd.endToEndIter`（`pipelineN_eq_iter` 证明其逐点相等），
在 `linWorld` 上**就是** `ThetaConvergence.thetaN`（`pipelineN_linWorld`）。
**本文件不造第二个迭代语义。** -/
noncomputable def pipelineN (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier] {Y : Type} [Nonempty W.frame.X.Carrier]
    (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (n : ℕ) (θ₀ : W.frame.Θ.Carrier) : W.frame.Θ.Carrier :=
  endToEndIter W h η φ y u ε a x n θ₀

/-- ⭐ **`pipelineN` = `endToEndIter`**（逐点相等，非另造迭代）。 -/
theorem pipelineN_eq_iter (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier] {Y : Type} [Nonempty W.frame.X.Carrier]
    (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (n : ℕ) (θ₀ : W.frame.Θ.Carrier) :
    pipelineN W h η φ y u ε a x n θ₀ = endToEndIter W h η φ y u ε a x n θ₀ := rfl

/-- ⭐⭐ **`pipelineN` 的递推**：`n+1` 步 = 先跑 `n` 步，再走一步 `pipelineStep`。 -/
theorem pipelineN_succ (W : WorldModel) [AddCommGroup W.frame.X.Carrier]
    [Ring W.frame.Θ.Carrier] {Y : Type} [Nonempty W.frame.X.Carrier]
    (h : W.frame.X.Carrier → Y)
    (η : W.frame.Θ.Carrier) (φ : W.frame.X.Carrier →+ W.frame.Θ.Carrier)
    (y : Y) (u : W.frame.U.Carrier) (ε : W.frame.Ν.Carrier) (a : W.frame.Act.Carrier)
    (x : W.frame.X.Carrier) (n : ℕ) (θ₀ : W.frame.Θ.Carrier) :
    pipelineN W h η φ y u ε a x (n + 1) θ₀
      = pipelineN W h η φ y u ε a x n
          (pipelineStep W h η φ y θ₀ u ε a x) := rfl

/-! ### §5.1 ⭐⭐⭐ **端到端主定理**

    在 `linWorld` 上（预测机制 $f(x)=\theta x$），取观测 `h = id`、
    观测值 `y = θ* x`（真值 $\theta^\*$ 藏在观测里），
    方向映射 $\varphi = \frac1x\cdot\mathrm{id}$，步长 $\eta$。

    则管线轨迹 $\theta_n := \texttt{pipelineN}\ \dots\ n\ \theta_0$ **收敛到 $\theta^\*$**。
-/

/-- ⭐⭐⭐⭐ **【端到端主定理 · 六环管线】从观测 `y` 到最后 `θ_n → θ*`**。

**前提**（三条，皆非平凡，且**均不提及** `θ_n` 的极限）：
1. `x ≠ 0` —— 设计点非零（否则观测 `y = θ* x = 0` 不含 `θ*` 的信息）；
2. `|1 - η| < 1` —— 步长 `η ∈ (0,2)`；
3. `θ*`、`θ₀` 为任意实数（对真值**不作限制**）。

**结论**：
$$\mathrm{pipelineN}\ \mathrm{linWorld}\ \mathrm{id}\ \eta\ \bigl(\tfrac1x\cdot\mathrm{id}\bigr)\
  (\theta^* x)\ \dots\ n\ \theta_0 \;\xrightarrow[n\to\infty]{}\; \theta^* .$$

**⭐ 为什么这是「端到端」**：左边那个函数 `n ↦ pipelineN …` 的**每一步**都
依次经过 ① 观测（`y = θ* x`）→ ② 估计（`observe id`，精确）→ ③ 预测（`linWorld` 机制的 `θ_n * x`）
→ ④ 残差（`θ* x - θ_n x`）→ ⑤ 更新（`θ_{n+1} = θ_n + η·(1/x)·r`）。
**不是**只讲 ⑤→⑥ 的抽象收敛，而是**从观测** `y` 一路走到 `θ*`。

**⭐ 证明复用 `ThetaConvergence.linWorld_tendsto_thetaStar`**：
由 `pipelineN_linWorld`（下条）把 `pipelineN` **识别为** `thetaN`，
再调用既有主定理——**本文件不重证收敛**。

**⚠ 不是同义反复**：前件讲 `x, η` 与「实例」，结论讲**管线的极限点 = θ\***。
前件**没有**任何形如「`θ_n → θ*`」的语句。收敛律由 §5.1 的闭式
`θ_n - θ* = (1-η)^n(θ_0-θ*)` 提供（`ThetaConvergence.thetaN_closed`）。 -/
theorem pipeline_tendsto (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (hη : |1 - η| < 1) :
    Filter.Tendsto
      (fun n : ℕ => pipelineN linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
      Filter.atTop (nhds θstar) := by
  have h : ∀ n : ℕ, pipelineN linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀
      = ThetaConvergence.thetaN η θstar x θ₀ n := by
    intro n
    rfl
  exact (ThetaConvergence.linWorld_tendsto_thetaStar η θstar x θ₀ hx hη).congr
    (fun n => (h n).symm)

/-- ⭐⭐ **管线轨迹的闭式偏差**：`θ_n - θ* = (1-η)^n (θ_0 - θ*)`。

**引用 `ThetaConvergence.thetaN_closed`**——这是「学习真的发生」的定量证据：
每一步偏差乘同一因子 `1-η`。 -/
theorem pipelineN_closed (η θstar x θ₀ : ℝ) (hx : x ≠ 0) (n : ℕ) :
    pipelineN linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀ - θstar
      = (1 - η)^n * (θ₀ - θstar) :=
  ThetaConvergence.thetaN_closed η θstar x θ₀ hx n

/-- ⭐⭐ **收敛点唯一**：任何极限都是 `θ*`（引用 `linWorld_tendsto_unique`）。 -/
theorem pipeline_tendsto_unique (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hη : |1 - η| < 1) (L : ℝ)
    (h : Filter.Tendsto
      (fun n : ℕ => pipelineN linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
      Filter.atTop (nhds L)) :
    L = θstar :=
  tendsto_nhds_unique h (pipeline_tendsto η θstar x θ₀ hx hη)

/-! ===========================================================================
    §6  ⭐⭐ 非平凡性：极限是真值，不是 0
    =========================================================================== -/

/-- ⭐⭐⭐ **【管线学到真值，不是学到零】**：`θ* ≠ 0` 时，管线极限 `θ*` 非零。

**⭐ 这是「学习」与「误差→0」的分水岭**：若把学习写成「误差→0」，
则 `θ_n ≡ 0` 平凡满足；本定理（配 `pipeline_tendsto`）说明**管线**的极限
是**非零真值** `θ*`，`θ_n ≡ 0` **不满足**。 -/
theorem pipeline_limit_ne_zero (η θstar x θ₀ : ℝ) (hx : x ≠ 0)
    (hη : |1 - η| < 1) (hθ : θstar ≠ 0) :
    Filter.Tendsto
      (fun n : ℕ => pipelineN linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
      Filter.atTop (nhds θstar) ∧ θstar ≠ 0 :=
  ⟨pipeline_tendsto η θstar x θ₀ hx hη, hθ⟩

/-- ⭐⭐ **一步精确恢复真值**：`η = 1` 时管线**一步**到达 `θ*`（引用 `linWorld_one_step_exact`）。 -/
theorem pipeline_one_step_exact (θstar x θ₀ : ℝ) (hx : x ≠ 0) :
    pipelineN linWorld (id : ℝ → ℝ) 1
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x 1 θ₀ = θstar :=
  ThetaConvergence.linWorld_one_step_exact θstar x θ₀ hx

/-- ⭐ **零步启动**：`pipelineN … 0 θ₀ = θ₀`（管线的初始参数）。 -/
theorem pipelineN_zero (η θstar x θ₀ : ℝ) :
    pipelineN linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x 0 θ₀ = θ₀ :=
  rfl

/-! ===========================================================================
    §7  具体数值实例（检验「非空真」：前件可同时满足）
    =========================================================================== -/

/-- ⭐⭐ **具体前件可满足**：`x = 2 ≠ 0`、`η = 1/2`、`|1 - 1/2| < 1`。 -/
theorem concrete_setup : (2 : ℝ) ≠ 0 ∧ |1 - (1/2 : ℝ)| < 1 := by
  refine ⟨by norm_num, by norm_num⟩

/-- ⭐⭐⭐ **具体数值：真值 `3`、初始 `0`、`η = 1/2`、`x = 2` ⟹ 管线 `θ_n → 3`**。 -/
theorem concrete_pipeline_tendsto :
    Filter.Tendsto
      (fun n : ℕ => pipelineN linWorld (id : ℝ → ℝ) (1/2)
        (((1 / (2:ℝ))) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        ((3:ℝ) * 2) PUnit.unit PUnit.unit PUnit.unit (2:ℝ) n 0)
      Filter.atTop (nhds 3) :=
  pipeline_tendsto (1/2) 3 2 0 (by norm_num) (by norm_num)

/-- ⭐⭐ **具体数值：偏差闭式** `θ_n - 3 = (1/2)^n · (0 - 3)`。 -/
theorem concrete_pipeline_closed (n : ℕ) :
    pipelineN linWorld (id : ℝ → ℝ) (1/2)
        (((1 / (2:ℝ))) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        ((3:ℝ) * 2) PUnit.unit PUnit.unit PUnit.unit (2:ℝ) n 0 - 3
      = (1/2 : ℝ)^n * (0 - 3) := by
  have h := pipelineN_closed (1/2) 3 2 0 (by norm_num) n
  have h2 : (1 - (1:ℝ)/2) = 1/2 := by norm_num
  rw [h2] at h
  exact h

/-! ===========================================================================
    §8  自检清单（逐条可编译）
    =========================================================================== -/

noncomputable section

/-- **自检 1**：观测环类型 `X → Y`。 -/
example : ℚ → ℚ := pipelineObserve (id : ℚ → ℚ)

/-- **自检 2**：估计环类型 `Y → X`。 -/
example : ℚ → ℚ := pipelineEstimate (id : ℚ → ℚ)

/-- **自检 3**：预测环读 θ（`x ≠ 0` 时换 θ 则变）。 -/
example : pipelinePredict 1 0 0 0 0 ≠ pipelinePredict 1 0 0 1 0 :=
  pipelinePredict_separates one_ne_zero (by norm_num)

/-- **自检 4**：管线一步 = `endToEnd`（不是另造）。 -/
example (η θ θstar x : ℝ) (_hx : x ≠ 0) :
    pipelineStep linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) θ PUnit.unit PUnit.unit PUnit.unit x
      = endToEnd linWorld (id : ℝ → ℝ) η
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) θ PUnit.unit PUnit.unit PUnit.unit x := rfl

/-- **自检 5**：主定理在 `η = 1/3`（另一合法步长）同样成立。 -/
example (θstar x θ₀ : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto
      (fun n : ℕ => pipelineN linWorld (id : ℝ → ℝ) (1/3)
        (((1 / x : ℝ)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) : ℝ →+ ℝ)
        (θstar * x) PUnit.unit PUnit.unit PUnit.unit x n θ₀)
      Filter.atTop (nhds θstar) :=
  pipeline_tendsto (1/3) θstar x θ₀ hx (by norm_num)

end

/-! ===========================================================================
    §9  ⚠ **前件审计表**（本项目最高频问题：前件是否已把结论包进去）

    **纪律 7 原文**：「检查你的定理的前件是否已把结论包进去（同义反复）」

    ### 9.1 逐条审计

    | 定理 | 前件 | 结论 | 是否同义反复 |
    |---|---|---|---|
    | `pipelineObserve_estimate` | `h` 单射 | `x̂(y(h x)) = x` | **否**：前件讲 `h`，结论讲复合 `x̂∘y`；中间隔着 `Classical.choose` 的选取规范 |
    | `pipelinePredict_eq` | **无** | `predict = θ*x+u+ε+a` | **否**：算术等式，右边显含 θ |
    | `pipelinePredict_separates` | `x ≠ 0`、`θ₁ ≠ θ₂` | 预测**不等** | **否**：前件讲 `x,θ`，结论讲输出；且 `x=0` 时结论为假（前件必要）|
    | `exists_pipelinePredict_separates` | **无** | **存在**一组值使预测不等 | **否**：无前件，全兑现为具体值 `x=1,θ=0,1` |
    | `pipelineStep_eq_endToEnd` | **无** | `pipelineStep = endToEnd` | **否**：这是「未另造算子」的断言（`rfl` 可关因二者同字面量）|
    | `pipelineStep_diff` | **无** | `θ' - θ = η·φ(r)` | **否**：定量分解式，残差唯一决定位移 |
    | `pipelineStep_fixed` | `observe h y = predFrom …`（残差为零）| `pipelineStep … = θ` | **否**：前件是「观测=预测」，结论是「参数不动」| 
    | `pipelineEstimate_error` | `0<L`、`LipschitzInvertibleOn h L`、`h x' = h x + η` | `dist x' x ≤ L·dist η 0` | **否**：前件讲 Lipschitz 性与噪声，结论讲误差界 |
    | `pipeline_tendsto` ⭐ | `x ≠ 0`、`|1-η|<1` | `θ_n → θ*` | **否**：前件讲设计点与步长，**无**任何「收敛」语句；结论是轨迹极限 |
    | `pipeline_limit_ne_zero` | 同上 + `θ* ≠ 0` | 极限 = θ* 且 θ*≠0 | **否**：区分「学到真值」与「学到零」 |
    | `pipeline_one_step_exact` | `x ≠ 0` | `η=1` 时一步达 θ* | **否**：前件讲设计点，结论讲一步轨迹值 |
    | `pipelineN_zero` | **无** | `n=0` 步 = θ₀ | **否**：定义性（`rfl`），但陈述的是管线初值行为 |
    | `concrete_*` | **无**（或具体数值）| 具体数值断言 | **否**：是一般定理的实例 |

    ### 9.2 ⭐ 主定理的**非线性**（专项复核）

    `pipeline_tendsto` 的证明链：

    1. `pipelineN_eq_iter`：`pipelineN` **就是** `endToEndIter`（`rfl`）；
    2. 在 `linWorld` 上 `endToEndIter` **就是** `thetaN`（`rfl`）；
    3. 引用 `ThetaConvergence.linWorld_tendsto_thetaStar`，其证明用
       `thetaN_closed`（闭式 `θ_n-θ* = (1-η)^n(θ_0-θ*)`）+ `tendsto_pow_atTop_nhds_zero_of_lt_one`。

    **⟹ 收敛由 `(1-η)^n → 0` 导出，而 `|1-η|<1` 只用于这一点，
    不含关于 `θ_n` 极限的任何信息。** 这就是「非循环」的判据。

    ### 9.3 ⚠ **未证之事（诚实登记）**

    | 未证项 | 为何未证 |
    |---|---|
    | **带噪下管线收敛** | 噪声 `η` 如何经残差进入更新并影响极限，需完整分析，不在本文件范围；本文件 §4 只给**估计**误差界，不接收敛 |
    | **非线性机制的管线收敛** | `linWorld` 的线性机制是一步收缩的必要条件；`ThetaConvergence` §1.1 已登记非线性反例，本文件继承该边界 |
    | **`h ≠ id`（读法 b）下的主定理** | 该情形估计环节用 `chooseEstimator`（非构造），且带噪；本文件取 `h=id`（Frame Q-2 裁决，A14 读法 a）| 
    | **`η, φ` 最优** | 二者是显式参数；本文件对所有满足 `|1-η|<1` 的 `η` 成立 |
    =========================================================================== -/

end WorldModelPipeline

end FateV2.Loop