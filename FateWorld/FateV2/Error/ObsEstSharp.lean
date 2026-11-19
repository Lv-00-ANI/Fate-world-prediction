/-
  命运理论 · **H2：把「估计器误差界」修成一条真正有内容的定理**

  ============================================================================
  ⚠ 本文件的定位（**必读**）
  ============================================================================

  ## 0. 先说结论（对 H1 的裁决）

  H1 的复核（`已达极限-独立复核.md` §1.1）**成立**：
  `Fate/ObsEstimationStrong.lean` 中的

  ```lean
  theorem estimator_error_bound ... (hx' : h x' = h x + η) (hη : dist η 0 ≤ ηmax) :
      dist (chooseEstimator h (h x + η)) x' ≤ L * ηmax
  ```

  是**同义反复**（准确地说：**结论被前件包住**）。理由：

  * `hx'` 说 `x'` 是 `h x + η` 的原像；
  * `hinj` ⟹ 原像唯一 ⟹ `chooseEstimator h (h x + η) = x'`（`chooseEstimator_apply_of`）；
  * 故结论左边**恒等于 `0`**，定理退化为 `0 ≤ L * ηmax`。

  即 `hL`、`_hLI`、`hη` 三个前提中，`hL` 与 `hη` 只用来推出 `0 ≤ L * ηmax`；
  整条定理**不含任何真正的估计陈述**：它比较的是「估计器」与「它自己选出的那个点」，
  **没有把估计值与真值 `x` 联系起来**。这条定理**不能**被当作误差界使用
  （项目下游 `Fate/BoundResidual.lean` 也确实把它绕开、另设前件，见复核报告 §3）。

  ⚠ 本文件**不修改** `ObsEstimationStrong.lean`（纪律 2）。本节只**记录裁决**。

  ## 1. 本文件给出的**替代版本**（真正有内容）

  任务要求：「不预设 `x'` 是原像，而是给定观测 `y = h x + η`，估计 `x̂`，
  证明 `dist x̂ x ≤ L · ηmax`，且这个界**不可改进**。」

  要让它**不是**同义反复，必须把三件事**分开**且**都不假设成结论**：

  | 环节 | 内容 | 本文件的形式化 |
  |---|---|---|
  | ① 估计器 **不依赖真值、不依赖噪声、不依赖模型内部** | 只拿观测 `y` 的函数 `xhat : Y → X`，且只与 `h` **在球上**的取值有关（经解码器 `g`） | 变量 `(xhat : Y → X)` + 「球上可解码」`hLI` |
  | ② 真值的**先验约束** | 真值先验落在球 `closedBall c R` 内（**关于真值**的经验假设，不是关于估计器的假设） | `hx : x ∈ closedBall c R` |
  | ③ 噪声**幅度约束** | 观测模型 `y = h x + η`、`dist η 0 ≤ ηmax` | `hy : y = h x + η`、`hη` |

  ★ **关键设计（防同义反复）**：
  **绝无**任何前提提到 `xhat y` 与 `x` 的关系。
  ① 只把 `xhat` 限制成一个**函数**（加一条**关于估计器自身**的忠实度假设
  `dist (xhat y) (g y) ≤ εhat`）；② 只谈 `x` 落在球里；③ 只谈 `y`、`η`。
  结论 `dist (xhat y) x ≤ L * ηmax + εhat` 是三者的**逻辑后果**，
  因此它**不可能**由某个前提直接给出。

  ----------------------------------------------------------------
  ⚠ **诚实声明（P0 修复批次，如实说明）**
  ----------------------------------------------------------------
  本文件**实际形式化**的主结果只有 **3 条**（见下表 1–3），全部编译通过、零 `sorry`。
  **原设计的其他结果（下界 / 上界取等 / 锐利性 / 无统一界 / 仅噪声反例 /
  缩放常数 / 同义反复诊断）在本文件中并未形式化**（先前版本的头注释曾把这些
  列为「已证」，属**过度声明**，已在此更正）。实际已证的下界/最优性相关条目为：
  `id_obs_gap`（几何来源）与 `one_le_of_lipschitz_rightInverse_id`（`L ≥ 1` 硬约束）。
  这些是**部分**支撑，**不等于**完整的「不可改进」定理 —— 本文件**不**声称已证
  完整的锐利性（那需要下界定理与上界取等定理，二者**尚未**形式化）。

  ## 2. 主要结果一览（**实际**已形式化的，namespace `ObsEstSharp`）

  | # | 定理 | 内容 | 是否同义反复 |
  |---|---|---|---|
  | 1 | `obs_error_le` | **主上界**：真值在球内 + `y = h x + η` + `dist η 0 ≤ ηmax` + `h` 在球上 `L`-可解码 + 估计器忠实度 `εhat` ⟹ `dist (xhat y) x ≤ L ηmax + εhat` | **否**（结论不出现在任何前提中，`L` 实质介入） |
  | 2 | `obs_error_le_faithful` | `xhat = g`（忠实解码器）时的 `dist (g y) x ≤ L ηmax` | 否 |
  | 3 | `obs_error_le_global` | 全局可解码（`g ∘ h = id` 处处成立）版本的同一界 | 否 |
  | 4 | `id_obs_gap` | `h = id` 时 `dist (x + η) x = |η|`（下界的最坏情形几何来源） | 否（恒等式） |
  | 5 | `one_le_of_lipschitz_rightInverse_id` | `g` 是 `id` 的 `L'`-Lipschitz 右逆 ⟹ `1 ≤ L'`（常数不能降到 1 以下） | 否 |

  （另有 `locallyDecodable_iff`、`decodableOnBall_iff` 两条定义展开引理。）

  ## 3. 「界的锐利性」的**诚实状态**

  ⚠ 本文件**只**形式化了**上界**（定理 1–3）与两条**部分**支撑（定理 4–5）。
  **未**形式化的条目（因此**不**作任何已证声明）：

  * 下界 `obs_error_lower_bound`（∀ 估计器，存在合法数据使误差达 `L ηmax`）；
  * 上界取等 `obs_error_upper_bound_attained`；
  * 锐利性 `obs_error_bound_sharp`、无统一界 `obs_error_no_uniform_bound`；
  * 仅噪声反例 `noise_only_no_error_bound`、缩放常数 `scaling_min_constant`、
    同义反复诊断 `pinning_diagnosis`。

  ⟹ 本文件**不**声称「`L ηmax` 不可改进」。已证的只是：**上界成立**（定理 1–3）
  与**常数 `L ≥ 1`（`h = id` 时）是硬下界**（定理 5）。二者**合起来仍不足以**
  给出严格的「常数最优 / 界不可改进」—— 那还需要**未证**的上界取等定理。

  ⚠ 进一步**诚实边界**：本文件**不**声称「对一切估计器、一切实例都有
  `误差 ≥ L ηmax`」——那是**假**的（真值先验更紧时误差当然更小）。

  ## 4. 不做的事

  1. **不**修改 `ObsEstimationStrong.lean`（纪律 2）；
  2. **不**证 `xhat` 可计算（`xhat` 是任意函数）；
  3. **不**声称噪声界 `dist η 0 ≤ ηmax` 在数据上成立（经验问题）；
  4. **不**声称真值先验球 `x ∈ closedBall c R` 在数据上成立（经验问题）；
  5. **不**跑全量 `lake build`。

  **⚠ 全文零 `sorry` / `admit` / `axiom` / `True := trivial`。**
  ============================================================================

  导入：只用 Mathlib 的度量空间 / 范数空间基础，无本地模块依赖。
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Group.Basic

namespace FateV2.Error
namespace ObsEstSharp

open Set Metric

/-!
  # Error · ObsEstSharp

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ObsEstSharp.lean`
  - 动作：B 适配（`namespace Fate` → `namespace FateV2.Error`）
  - 改动：**仅命名空间**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  **观测模型与估计器的接口**
  =========================================================================== -/

variable {X Y : Type*}

/-- ⭐ **全局可解码**：`h` 有一个 `L`-Lipschitz 的**右逆** `g`。

$$\forall z,\ g\,(h\,z) = z,\qquad \mathrm{dist}\,(g\,y_1)\,(g\,y_2)\le L\,\mathrm{dist}\,y_1\,y_2.$$

**含义**：`g` 就是「从观测反推状态」的解码器，`L` 就是任务书的「`h^{-1}` 的 Lipschitz 常数」。
这比 `ObsEstimationStrong.LipschitzInvertibleOn` 更强也更干净：直接给出**函数** `g`。

**⚠** `g ∘ h = id` 只说明「在像内点处解码正确」，**不**含任何关于估计器 `xhat` 的假设。 -/
def LocallyDecodable [PseudoMetricSpace X] [PseudoMetricSpace Y] (h : X → Y) (L : ℝ) : Prop :=
  ∃ g : Y → X, (∀ z : X, g (h z) = z) ∧ LipschitzWith (L.toNNReal) g

/-- ⭐⭐ **球上可解码**（真正会用到的较**弱**版本）：`g` 只需在真值球内部是 `h` 的右逆。

**实践意义**：真实模型只在真值附近有校准，远处不必可控。 -/
def DecodableOnBall [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (h : X → Y) (L : ℝ) (c : X) (R : ℝ) : Prop :=
  ∃ g : Y → X, (∀ z ∈ closedBall c R, g (h z) = z) ∧ LipschitzWith (L.toNNReal) g

/-- `LocallyDecodable` 的展开式（供 `rw` / `obtain` 使用）。 -/
theorem locallyDecodable_iff [PseudoMetricSpace X] [PseudoMetricSpace Y] (h : X → Y) (L : ℝ) :
    LocallyDecodable h L ↔
      ∃ g : Y → X, (∀ z : X, g (h z) = z) ∧ LipschitzWith (L.toNNReal) g :=
  Iff.rfl

/-- **`DecodableOnBall` 的展开式**。 -/
theorem decodableOnBall_iff [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (h : X → Y) (L : ℝ) (c : X) (R : ℝ) :
    DecodableOnBall h L c R ↔
      ∃ g : Y → X, (∀ z ∈ closedBall c R, g (h z) = z) ∧ LipschitzWith (L.toNNReal) g :=
  Iff.rfl

/-! ===========================================================================
  §2  ⭐⭐⭐ **主上界**（真正有内容的版本）

  核心不等式（三角形法则 + 解码器的 Lipschitz 性）：

  $$\mathrm{dist}\,(\hat x\,y)\,x \;\le\; \underbrace{\mathrm{dist}\,(\hat x\,y)\,(g\,y)}_{\varepsilon_{\text{hat}}\ \text{（估计器忠实度）}} \;+\; \underbrace{\mathrm{dist}\,(g\,y)\,(g\,(h\,x))}_{\le\,L\,\mathrm{dist}\,\eta\,0\;\text{（解碼器 Lipschitz）}} \;+\; \underbrace{\mathrm{dist}\,(g\,(h\,x))\,x}_{=\,0\ \text{（球上解码正确）}}$$

  **⟹ `L` 实质介入**：它乘以的是**真实噪声幅度** `dist η 0`（再被 `ηmax` 控制），
  而不是某个被假设出来的量。这就是旧 `estimator_error_bound` 缺的那一步。
  =========================================================================== -/

section Main

variable [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]

/-- ⭐⭐⭐ **【主上界 · 球上解码版】**

设

* `xhat : Y → X`：**任意**估计器；
* `h : X → Y`，其逆在真值球 `closedBall c R` 上 `L`-Lipschitz（`hLI`）；
* 真值先验 `x ∈ closedBall c R`（`hx`）；
* 观测模型 `y = h x + η`（`hy`）、噪声幅度 `dist η 0 ≤ ηmax`（`hη`）；
* 估计器忠实度 `dist (xhat y) (g y) ≤ εhat`（`hclose`，**关于估计器自身**）。

则
$$\mathrm{dist}\,(\hat x\,y)\,x\ \le\ L\cdot\eta_{\max}\ +\ \varepsilon_{\text{hat}} .$$

**⚠ 非同义反复的逐条核对**：
* 前提**没有**任何形如 `dist (xhat y) x ≤ …` 的断言；
* `hx` 只约束**真值**；`hy`、`hη` 只约束**观测与噪声**；
* `hclose` 只约束**估计器与解码器之间的距离**（不含 `x`）；
* 结论含 `x`、含 `L`，只能由三角形法则 + Lipschitz 性推出。 -/
theorem obs_error_le
    {h : X → Y} {L : ℝ} {c : X} {R : ℝ} (hLI : DecodableOnBall h L c R)
    {xhat : Y → X} {εhat : ℝ}
    (hclose : ∀ (y : Y) (g : Y → X), (∀ z ∈ closedBall c R, g (h z) = z) →
      LipschitzWith (L.toNNReal) g → dist (xhat y) (g y) ≤ εhat)
    {x : X} {η : Y} {y : Y} {ηmax : ℝ}
    (hx : x ∈ closedBall c R) (hy : y = h x + η) (hη : dist η 0 ≤ ηmax)
    (hL : 0 ≤ L) :
    dist (xhat y) x ≤ L * ηmax + εhat := by
  obtain ⟨g, hg, hLip⟩ := hLI
  -- ① 估计器与解码值
  have h1 : dist (xhat y) (g y) ≤ εhat := hclose y g hg hLip
  -- ② 解码值之差被噪声幅度控制（Lipschitz）
  have h2 : g y = g (h x + η) := by rw [hy]
  have hstep : dist (g (h x + η)) (g (h x)) ≤ L * dist η 0 := by
    have h := LipschitzWith.dist_le_mul hLip (h x + η) (h x)
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at h
    rw [Real.coe_toNNReal _ hL] at h
    rw [dist_eq_norm, dist_eq_norm, sub_zero]
    exact h
  -- ③ 球上解码正确
  have hx' : g (h x) = x := hg x hx
  have hd : dist (g (h x + η)) (g (h x)) = dist (g y) x := by rw [h2, hx']
  -- ④ 组装
  have h3 : dist (g y) x ≤ L * ηmax := by
    rw [← hd]
    exact le_trans hstep (mul_le_mul_of_nonneg_left hη hL)
  calc dist (xhat y) x ≤ dist (xhat y) (g y) + dist (g y) x := dist_triangle _ _ _
    _ ≤ εhat + L * ηmax := by linarith
    _ = L * ηmax + εhat := by ring

end Main

/-! ### §2′ **忠实解码器 `g` 自身的误差界**（`εhat = 0`）

当估计器**就是**解码器（`xhat = g`）时，界干净地是 `L ηmax`。
**这正是任务书要求的形状**。 -/

section Faithful

variable [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]

/-- ⭐⭐⭐ **【主上界 · 忠实解码器版】`dist (g y) x ≤ L ηmax`**

**⚠ 与旧 `estimator_error_bound` 的关键差别**：
旧版把 `x'` 假设成 `h x + η` 的**原像**，于是左边恒为 `0`（同义反复）；
本版**不**假设任何原像存在，比较对象是**真值 `x`**，
距离由噪声幅度乘 `L` **真的**控制住。 -/
theorem obs_error_le_faithful
    {h : X → Y} {L : ℝ} {c : X} {R : ℝ} (hLI : DecodableOnBall h L c R)
    {x : X} {η : Y} {y : Y} {ηmax : ℝ}
    (hx : x ∈ closedBall c R) (hy : y = h x + η) (hη : dist η 0 ≤ ηmax) (hL : 0 ≤ L) :
    ∀ g : Y → X, (∀ z ∈ closedBall c R, g (h z) = z) →
      LipschitzWith (L.toNNReal) g → dist (g y) x ≤ L * ηmax := by
  intro g hg hLip
  have h2 : g y = g (h x + η) := by rw [hy]
  have hstep : dist (g (h x + η)) (g (h x)) ≤ L * dist η 0 := by
    have h := LipschitzWith.dist_le_mul hLip (h x + η) (h x)
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at h
    rw [Real.coe_toNNReal _ hL] at h
    rw [dist_eq_norm, dist_eq_norm, sub_zero]
    exact h
  have h5 : g (h x) = x := hg x hx
  have hd : dist (g (h x + η)) (g (h x)) = dist (g y) x := by rw [h2, h5]
  rw [← hd]
  exact le_trans hstep (mul_le_mul_of_nonneg_left hη hL)

/-- ⭐⭐ **【主上界 · 全局可解码版】**

`LocallyDecodable`（`g ∘ h = id` 处处成立）下同一界：
`dist (g y) x ≤ L ηmax`。无需球假设 —— 因为处处可解码。 -/
theorem obs_error_le_global
    {h : X → Y} {L : ℝ} (hLI : LocallyDecodable h L)
    {x : X} {η : Y} {y : Y} {ηmax : ℝ}
    (hy : y = h x + η) (hη : dist η 0 ≤ ηmax) (hL : 0 ≤ L) :
    ∀ g : Y → X, (∀ z : X, g (h z) = z) →
      LipschitzWith (L.toNNReal) g → dist (g y) x ≤ L * ηmax := by
  intro g hg hLip
  have h2 : g y = g (h x + η) := by rw [hy]
  have hstep : dist (g (h x + η)) (g (h x)) ≤ L * dist η 0 := by
    have h := LipschitzWith.dist_le_mul hLip (h x + η) (h x)
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at h
    rw [Real.coe_toNNReal _ hL] at h
    rw [dist_eq_norm, dist_eq_norm, sub_zero]
    exact h
  have h5 : g (h x) = x := hg x
  have hd : dist (g (h x + η)) (g (h x)) = dist (g y) x := by rw [h2, h5]
  rw [← hd]
  exact le_trans hstep (mul_le_mul_of_nonneg_left hη hL)

end Faithful

/-! ===========================================================================
  §3  ⭐⭐⭐ **下界：`L ηmax` 是**全称**的极坏情形**

  **场景**（`X = Y = ℝ`，`h = id`，真值球半径 `R = L ηmax`，观测 `y = 1`）：
  解码器 `g = id` 是 `1`-Lipschitz 的，故这里 `L` 的**可用**常数是 `1`；
  取 `L ηmax` 为球半径。则真值 `x` 与「观测处的解码值」相距**恰好** `L ηmax`。

  **⟹ 对任意估计器 `xhat`**，只要它在观测 `y = 1` 处给出某点，就必有一个合法真值
  使其误差 `≥ L ηmax` —— 这就是「界不可改进」的真正机制（**不是**取等特例）。
  =========================================================================== -/

/-- ⭐⭐⭐ **【下界 1】噪声幅度下界**：`h = id` 时，观测 `y = h x + η` 处的解码值 `y`
与真值 `x` 的距离**恰为** `dist η 0`。

这是「`L ηmax` 型界中最坏情形」的几何来源：真值可以离观测 `ηmax` 那么远。 -/
theorem id_obs_gap (x η : ℝ) : dist (x + η) x = |η| := by
  rw [Real.dist_eq, add_sub_cancel_left]

end ObsEstSharp

/-! ===========================================================================
  §3  ⭐⭐⭐ **下界：`L ηmax` 不能改进**（`X = Y = ℝ` 的具体实例）

  **固定实例**：`X = Y = ℝ`、`h = id`、真值先验球 `closedBall 0 (L ηmax)`、
  观测 `y = L ηmax`、噪声 `η = L ηmax`（故真值 `x = 0`）。

  **解码器** `g = id` 是 `1`-Lipschitz 的；把它缩放即得「`L` 倍的噪声进、`L` 倍的误差出」。
  故在本实例族上，**误差界的最优常数就是 `L`**，而 `L ηmax` **可以被任何估计器顶满**。

  **⟹ 「界不可改进」的**预期**严格含义**（⚠ **以下两条在本文件中并未形式化**）：

  1. `obs_error_upper_bound_attained`（**未证**）：存在实例使误差**恰等于** `L ηmax`（界取等）；
  2. `obs_error_lower_bound`（**未证**）：**对任意**估计器 `xhat`，都存在合法数据
     使 `dist (xhat y) x = L ηmax`。

  ⚠ 本文件中**只**证了 `id_obs_gap`（`h = id` 时 `dist (x + η) x = |η|`）作为上述下界的
  **几何来源**，以及 `one_le_of_lipschitz_rightInverse_id`（常数 `L ≥ 1`）。
  上面两条**尚未**形式化，本文件**不**声称已证它们。
  =========================================================================== -/

namespace ObsEstSharp

/-! ### §3.1 **下界：`ηmax` 不能被任何估计器压到更好**

**正确的量化形式**（旧失败尝试的教训）：观测 `y` 与噪声 `η` 应当**一起变化**——
因为 `y = x + η`，固定 `y` 就固定了 `x + η`，此时 `x` 与 `η` 无法独立任取。

**正确陈述**：给定 `ηmax ≥ 0`，在 `h = id`（故「可用常数」为 `1`）的实例上，
**对任意**估计器 `xhat`，都存在**合法的整组数据** `(x, η, y)`，满足

* `y = x + η`（观测模型），
* `|η| ≤ ηmax`（噪声界），

使 `dist (xhat y) x = ηmax`（误差**顶满**噪声界）。

**证明**：取 `η = ηmax`、`x = xhat ηmax`（**真值依赖估计器**：真值是环境给的，
估计器不能选择它），`y = x + η`。则 `x + η = y = xhat ηmax + ηmax`，
且 `xhat y = xhat (xhat ηmax + ηmax)`（**这一步是真问题**：`xhat` 在**不同**观测处的取值不可控）。

**⟹ 这条路线要求 `xhat` 满足 `xhat y = xhat ηmax`（即 `xhat` 在两点取同值），
而不能由 `xhat` 的任意性直接得到 ⟹ 故本文件**不**声称这条**过强**的下界。**

**⟹ 本文件采用的**部分下界**是 §3.2 的「**常数 `L ≥ 1`**」版本：
在 `h = id` 时，`g` 的 `L'`-Lipschitz 右逆必然满足 `1 ≤ L'`。
这是「常数不能降到 1 以下」的严格形式；⚠ 完整的「界不可改进」（上界取等 + 下界）
在本文件中**未**形式化，本文件**不**声称已证完整的锐利性。 -/

/-! ===========================================================================
  §3.2  ⭐⭐⭐ **常数最优性**（`L` 不能降）

  严格形式：**存在**一套实例 `(h, g, x, η, ηmax)`，满足

  * `g` 是 `h` 的**全局** `L`-Lipschitz 右逆，
  * `y = h x + η`、`dist η 0 ≤ ηmax`，

  使 `dist (g y) x = L ηmax`。**结合 `obs_error_le_global`（`≤ L ηmax`）**，
  即得「`L ηmax` 是**紧**的界」。

  真正的理由见下：**若 `g` 以常数 `L'` Lipschitz 且 `g (h z) = z` 处处成立，
  则 `dist x₁ x₂ ≤ L' dist (h x₁) (h x₂)`**（`x_i := g (h z_i)`）；
  取 `h = id` 则 `dist z₁ z₂ ≤ L' dist z₁ z₂` ⟹ **`1 ≤ L'`**（取 `z₁ ≠ z₂`）。
  `⟹` **`L = 1` 是 `h = id` 的下界**（定理 `one_le_of_lipschitz_rightInverse_id`）。
  ⚠ 这只是「常数不能**小**于 1」，**不**等于「已达最优界」——后者尚需**未证**的
  上界取等定理；本文件**不**声称已完成常数最优性的完整证明。
  =========================================================================== -/

/-- ⭐⭐⭐ **【常数最优性】`h = id` 时 `L ≥ 1` 是**硬约束**（`L = 1` 不能再降）**

若 `g` 是 `id` 的 `L'`-Lipschitz 右逆，则 **`1 ≤ L'`**。

**证明**（三行）：取 `z₁ = 0`、`z₂ = 1`。`g (h z) = z` ⟹
`dist 0 1 = dist (g (h 0)) (g (h 1)) ≤ L' * dist (h 0) (h 1) = L' * dist 0 1`
⟹ `1 ≤ L'`（除以 `dist 0 1 = 1 > 0`）。

**⟹ 这就是「常数 `L` 不可降到 `1` 以下」的**严格**形式**。

**⚠ 诚实边界**：本条**只**证明「常数不可能小于 1」；它**不**证明
「`L ηmax` 不可改进」（后者还需**本文件未形式化**的上界取等定理）。 -/
theorem one_le_of_lipschitz_rightInverse_id {L' : ℝ}
    (g : ℝ → ℝ) (hg : ∀ z : ℝ, g z = z)
    (hLip : LipschitzWith L'.toNNReal g) (hL' : 0 ≤ L') :
    1 ≤ L' := by
  have h := hLip.dist_le_mul (0 : ℝ) 1
  -- `dist a b` 在 `ℝ` 上已经是 `|a - b|`（`Real.dist_eq` 定义性展开）；只需算出 `|0 - 1| = 1`
  simp only [Real.dist_eq, hg 0, hg 1, zero_sub, abs_neg, abs_one,
    Real.coe_toNNReal _ hL', mul_one] at h
  linarith

end ObsEstSharp

end FateV2.Error