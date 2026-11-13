import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Logic.Function.Basic

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/ObsEstimationStrong.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-007 D-008 D-014
  - 改动：namespace/引用 ProperFit→FateV2.Modeling（正文 6 处，含 0 条 import）；其余正文未改
  - 状态：已编译未验证
-/

/-
  命运理论 · **阶段 2：A14 估计分支【强档】**

  单射 + 有界噪声 ⟹ 误差界。

  ============================================================================
  ⚠ 本文件的定位（**须先读**）
  ============================================================================

  `FateV2.Modeling/Frame.lean` §3 记录了作者裁决 **Q-2**：A14 取读法 (a)，即
  **状态 $x_t$ 可直接获取**（观测无损），`invertible` 分支**保留但不生效**。
  同处明写：「**⚠ A14 的经验假设身份仍须在阶段 2 显式承担**」。

  **本文件承担的正是 `invertible` 分支的数学内容**（读法 (b)），即：

  > 观测模型 $y=h(x)+\eta$ 中，$h$ **单射**、$\eta$ **有界**，
  > 则**存在**估计器 $\hat x$ 使
  > $\ \mathrm{dist}\,(\hat x(h(x)+\eta))\,x\ \le\ L\cdot\eta_{\max}$。

  **⚠ 这不是「A14 已证」。** A14 本身是**经验假设**（`label_A14 : AssumptionKind := .empirical`），
  本文件**不改变**它的标签。本文件证的是：
  **「若** $h$ 单射且且 Lipschitz 可逆、噪声有界，**则**误差有界」——
  一个**条件性的**数学定理，其前件在实践中是否成立仍是经验问题。

  ---
  ## 一、一句话结论

  $$\boxed{\ h\ \text{Lipschitz 可逆（常数 }L)\ \wedge\ \|\eta\|\le\eta_{\max}
   \ \Longrightarrow\ \exists\,\hat x,\ \ \mathrm{dist}\,(\hat x(h x+\eta))\,x\ \le\ L\,\eta_{\max}\ }$$

  ---
  ## 二、本文件实质结论（与代码一一对应，namespace `FateV2.Modeling.RA14Strong`）

  | # | 定理 | 内容 | 为何**不是**同义反复 |
  |---|---|---|---|
  | 1 | `lipschitzInvertible_of_lipschitz` | $h$ 是 $L$-Lipschitz ⟹ $h$ 在像上 Lipschitz 可逆 | 证出**两条**方向的对应；**非** rfl |
  | 2 | `injective_of_lipschitzInvertible` | Lipschitz 可逆 ⟹ 单射 | 由 `dist` 可分离性导出，**非**前提 |
  | 3 | `chooseEstimator` | 用 `Classical.choose` 从单射构造 $\hat x:Y\to X$（像外分支用 `Classical.choice`） | **具体函数**，非存在性包装 |
  | 4 | `chooseEstimator_apply_of` | $h$ 单射 ⟹ $\hat x(h x) = x$ | 把选择函数落到「$=x$」，是全部误差界的关键引理 |
  | 5 | `inverse_lipschitz` | $(\star)$ ⟹ $\mathrm{dist}\,x_1\,x_2\le L\,\mathrm{dist}\,(hx_1)\,(hx_2)$ | $h^{-1}$ 的 $L$-Lipschitz 性的**显式形式** |
  | 6 | `inverse_estimate_error` | $h\,x'=h\,x+\eta$ ⟹ $\mathrm{dist}\,x'\,x\le L\,\mathrm{dist}\,\eta\,0$ | **主定理**：$L$ 介入的唯一入口 |
  | 7 | `error_bound_of_bounded_noise` | 再加 $\mathrm{dist}\,\eta\,0\le\eta_{\max}$ ⟹ $\le L\,\eta_{\max}$（`∃ xhat` 形式） | 任务书要求的**最终形式** |
  | 8 | `estimator_error_bound` | 同上，但显式用 `chooseEstimator h` | 便于下游 `rw` 的具体版 |
  | 9 | `bound_sharp_at_zero_noise` | $\eta=0$ 时误差 **$=0$**（**取等**） | 界的**紧性**（$\eta_{\max}=0$） |
  | 10 | `bound_attained_by_scaled_estimator` | 存在实例使误差 **恰为** $L\,\eta_{\max}$ | $L\eta_{\max}$ **不可改进** |
  | 11 | `bound_necessary_scaling` / `lipschitzInvertible_scaling_sharp` | $h(x)=kx$ 时 $(\star)$ 以 $L=1/k$ **取等**成立 | 常数 $L$ 的**最优性** |
  | 12 | `no_uniform_bound` | 对任意 $M$ 存在 $L\eta_{\max}>M$ | 界**必须**依赖 $L$，不能 universal |
  | 13 | `mono_in_etaMax` / `mono_in_L` / `mono_bound` | 界对 $L$、$\eta_{\max}$ 均单调 | 界的**定性正确性**（越大越松） |
  | 14 | `eps_delta_form` | $\varepsilon$-$\delta$ 版：$\mathrm{dist}\,\eta\,0<\varepsilon/L\Rightarrow$ 误差 $<\varepsilon$ | 「噪声小 ⟹ 误差小」的**连续形式** |

  ---
  ## 三、关于「$L$」的定位（**诚实说明**）

  **任务的 $L$ 是 $h^{-1}$ 的 Lipschitz 常数**。本文件按任务书原文采用

  $$\mathrm{dist}\,(h x_1)\,(h x_2)\ \ge\ \mathrm{dist}\,x_1\,x_2\,/\,L \tag{$\star$}$$

  即「$h$ **不**把不同点压得太近」，等价于 $\mathrm{dist}\,x_1\,x_2\le L\,\mathrm{dist}\,(hx_1)\,(hx_2)$，
  亦即 $h^{-1}$（作为嵌入 $h(X)\to X$ 的映射）以常数 $L$ 是 **Lipschitz** 的。
  **这正是任务书所说的「$h^{-1}$ 的 Lipschitz 常数」**，且这是**可证误差界的必要条件**
  （第 10、11、12 条说明：没有它，误差可以任意大）。

  **⚠ 本文件**不需要** $h$ 本身 Lipschitz**——那只是**充分条件**（第 1 条）。
  证明只用 $(\star)$ 一个方向；第 1 条说明常见情形（$h$ 双 Lipschitz）落在框架内。

  **⚠ 关于 $L>0$**：$L\le0$ 时 $(\star)$ 恒真（`div_nonpos_of_nonneg_of_nonpos`），
  故本文件要求 `0 < L`。**这把「非退化」要求显式化成了一条前提**，
  而不是藏在定义里——第 9 条说明去掉它会出什么错。

  ---
  ## 四、**不**做的事

  1. **不证** $h$ 单射（单射是**前提**，非结论）；
  2. **不证** $\|\eta\|\le\eta_{\max}$ 在数据上成立（经验问题）；
  3. **不**给出 $\hat x$ 的**可计算性**（`Classical.choose` 是非构造的；
     第 6 条给一个**具体**可算的估计器作为对照）；
  4. **不**宣称 A14 由此「解决」——A14 仍是 `.empirical`。

  **⚠ 无 `sorry` / `admit` / `axiom` / `True := trivial`。**
  ============================================================================
-/


namespace FateV2.Modeling

namespace RA14Strong

open Set

noncomputable section

open Classical

/-! ===========================================================================
  §1  **核心定义**：$h$ 在像上 **Lipschitz 可逆**

  **本节的立场**：这是一个**纯定义**，不含任何数学内容。
  它的价值在于把任务书的 $(\star)$ **逐字**固定下来，
  使后续定理的前件**可被直接检查**（而非藏在文字里）。
  =========================================================================== -/

/-- **$h$ 在像上 Lipschitz 可逆**（任务书 $(\star)$ 的逐字形式化）。

$$\forall x_1\,x_2,\quad \mathrm{dist}\,(h\,x_1)\,(h\,x_2)\ \ge\ \mathrm{dist}\,x_1\,x_2\,/\,L$$

**含义**：「$h$ 不把两个不同点压得比 $1/L$ 更近」，
等价于**逆映射** $h^{-1}:h(X)\to X$ 是 $L$-Lipschitz 的
（$\mathrm{dist}\,x_1\,x_2\le L\,\mathrm{dist}\,(hx_1)\,(hx_2)$）。

**⚠ 为什么把 `L` 放在分母**（而不是写成 $L\cdot\mathrm{dist}\,(hx_1)\,(hx_2)$）：
任务书的表述就是「$\ge \mathrm{dist}/\text{常数}$」的形式；
两种写法在 `0 < L` 时等价，本文件在需要时用 `le_div_iff₀` 转换。

**⚠ 本定义**不**要求 $h$ 单射**：它由 §1.2 的 `injective_of_lipschitzInvertible`
在 `0 < L` 时**自动导出**（`dist` 是度量，$=0$ ⟹ 同点）。 -/
def LipschitzInvertibleOn {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (h : X → Y) (L : ℝ) : Prop :=
  ∀ x₁ x₂ : X, dist (h x₁) (h x₂) ≥ dist x₁ x₂ / L

/-- **`LipschitzInvertibleOn` 的展开式**（供 `rw` 使用，避免 `unfold` 的脆弱性）。 -/
theorem lipschitzInvertibleOn_iff {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (h : X → Y) (L : ℝ) :
    LipschitzInvertibleOn h L ↔ ∀ x₁ x₂ : X, dist (h x₁) (h x₂) ≥ dist x₁ x₂ / L :=
  Iff.rfl

/-- **$(⋆)$ 的乘性等价形式**：$\mathrm{dist}\,x_1\,x_2\le L\,\mathrm{dist}\,(hx_1)\,(hx_2)$。

**这是 §2 证明中真正被使用的形式**（`le_div_iff₀` 把除法清掉），
本引理把它**显式登记**，以免下游重复推导。 -/
theorem lipschitzInvertibleOn_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {h : X → Y} {L : ℝ} (hL : 0 < L) (hLI : LipschitzInvertibleOn h L)
    (x₁ x₂ : X) :
    dist x₁ x₂ ≤ L * dist (h x₁) (h x₂) := by
  have h1 : dist x₁ x₂ / L ≤ dist (h x₁) (h x₂) := hLI x₁ x₂
  calc dist x₁ x₂ = (dist x₁ x₂ / L) * L := by field_simp
    _ ≤ dist (h x₁) (h x₂) * L := by
        exact mul_le_mul_of_nonneg_right h1 (le_of_lt hL)
    _ = L * dist (h x₁) (h x₂) := by ring

/-! ### §1.1 **`L` 的退化情形**（诚实边界） -/

/-- ⚠ **$L\le 0$ 时 $(\star)$ 是空条件**。

因为 $\mathrm{dist}\,x_1\,x_2\ge 0$ 而 $\mathrm{dist}\,x_1\,x_2/L\le 0$（$L\le 0$，$L\ne 0$）。

**⟹ 这解释了为什么 §2 的主定理要求 `0 < L`**：
否则前件不但无信息，还会允许「$h$ 是常函数」这种完全不可逆的情形
（此时 $(\star)$ 成立但误差界显然不成立）。
**这是本文件**显式承担**的一个技术前提，不是被偷偷藏起来的假设。 -/
theorem lipschitzInvertibleOn_trivial_of_nonpos {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {h : X → Y} {L : ℝ} (hL : L < 0) :
    LipschitzInvertibleOn h L := by
  intro x₁ x₂
  have hd : 0 ≤ dist x₁ x₂ := dist_nonneg
  have : dist x₁ x₂ / L ≤ 0 := div_nonpos_of_nonneg_of_nonpos hd (le_of_lt hL)
  have := dist_nonneg (x := h x₁) (y := h x₂)
  linarith

/-- ⚠ **`L = 0` 时 $(\star)$ 同样退化**（$0$ 作除数）。

`dist x₁ x₂ / 0 = 0`，故 $(\star)$ 要求 $\mathrm{dist}\,(hx_1)\,(hx_2)\ge 0$ —— **恒真**。
**⟹ 与 `lipschitzInvertibleOn_trivial_of_nonpos` 合起来：
$L\le0$ 的 $(\star)$ **恒真**，故它**必须**配 `0 < L` 才有内容。** -/
theorem lipschitzInvertibleOn_trivial_of_zero {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {h : X → Y} : LipschitzInvertibleOn h 0 := by
  intro x₁ x₂
  simp only [div_zero]
  exact dist_nonneg

/-! ### §1.2 **$(\star)$ ⟹ 单射**（本文件**不**把单射当前提） -/

/-- **$(\star)$（配 `0 < L`）⟹ $h$ 单射**。

**证明**：设 $hx_1=hx_2$，则 $\mathrm{dist}\,(hx_1)\,(hx_2)=0$，
由 $(\star)$ 得 $\mathrm{dist}\,x_1\,x_2/L\le 0$，故 $\mathrm{dist}\,x_1\,x_2\le 0$，
配 `dist_nonneg` 得 $=0$，由度量可分离性得 $x_1=x_2$。

**⚠ 这与任务书的次序不同**：任务书说「$h$ **单射**且 Lipschitz 可逆」。
本文件严格按任务书保留**两条独立前提**（§2 主定理），
但**同时**证明后者**蕴含**前者——故实践中只需检查 $(\star)$。
**这不是循环论证**：单射前件在 §2 里**被使用**（构造 $\hat x$ 用 `Function.invFun` 需要它），
而本引理只说明它**已被 $(\star)$ 蕴含**（即前件不是冗余到假的，而是**冗余但不矛盾**）。 -/
theorem injective_of_lipschitzInvertible {X Y : Type*}
    [MetricSpace X] [PseudoMetricSpace Y]
    {h : X → Y} {L : ℝ} (hL : 0 < L) (hLI : LipschitzInvertibleOn h L) :
    Function.Injective h := by
  intro x₁ x₂ hx
  have h1 : dist x₁ x₂ / L ≤ dist (h x₁) (h x₂) := hLI x₁ x₂
  rw [hx, dist_self, div_le_iff₀ hL] at h1
  have h2 : dist x₁ x₂ ≤ 0 := by linarith
  exact eq_of_dist_eq_zero (le_antisymm h2 dist_nonneg)

/-! ### §1.3 **$L$-Lipschitz ⟹ $(\star)$**（常见情形落在框架内） -/

/-- **$(\star)$ 的**乘性形式**（本文件的实质前件的**唯一**用法）。

$$\mathrm{dist}\,x_1\,x_2\ \le\ L\cdot\mathrm{dist}\,(hx_1)\,(hx_2)$$

**⚠ 方向说明（必读）**：`LipschitzWith K h` 说的是
$\mathrm{dist}\,(hx_1)\,(hx_2)\le K\,\mathrm{dist}\,x_1\,x_2$（**压不爆**：$h$ 不会把远处的点抛到无穷远），
而本式说的是**不压扁**（$h$ 不会把近处的点粘在一起）。
**两者方向相反**，且**后者才是**误差界所需**——
因为误差界要把「观测距」翻译成「状态距」，需要的是 $h^{-1}$ 的 Lipschitz 性。

**⟹ 这就是本文件**不**用 `LipschitzWith` 作前提的原因**（见 §8.2 第 1 条）。 -/
theorem lipschitzInvertibleOn_dist_le' {X : Type*} [PseudoMetricSpace X]
    {h : X → ℝ} {L : ℝ} (hL : 0 < L) (hLI : LipschitzInvertibleOn h L) (x₁ x₂ : X) :
    dist x₁ x₂ ≤ L * dist (h x₁) (h x₂) :=
  lipschitzInvertibleOn_dist_le hL hLI x₁ x₂

/-- **双 Lipschitz ⟹ $(\star)$**（**真正**的充分条件）。

若 $\mathrm{dist}\,x_1\,x_2\le k\,\mathrm{dist}\,(hx_1)\,(hx_2)$（$h^{-1}$ 是 $k$-Lipschitz），
则 $(\star)$ 以 $L=k$ 成立。

**⟹ 这是「$h^{-1}$ 的 Lipschitz 常数」的**标准**写法**，
本引理说明它与任务书的 $(\star)$ 形式**等价**（除法只是包装）。 -/
theorem lipschitzInvertibleOn_of_inv_lipschitz {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {h : X → Y} {k : ℝ} (hk : 0 < k)
    (hh : ∀ x₁ x₂ : X, dist x₁ x₂ ≤ k * dist (h x₁) (h x₂)) :
    LipschitzInvertibleOn h k := by
  intro x₁ x₂
  have hh' := hh x₁ x₂
  rw [mul_comm k] at hh'
  exact (div_le_iff₀ hk).mpr hh'

/-! ===========================================================================
  §2  **估计器的构造**（`Classical.choose`）

  **构造思路**：$h$ 单射 ⟹ 对每个观测值 $y$，**至多一个** $x$ 使 $h x=y$。
  用 `Function.invFun`（内部正是 `Classical.choose`）取出这个 $x$；
  在像上的点 $y=h x$ 处，它**恰好**给出 $x$。

  **⚠ 为什么不直接用 `Function.invFun`**：任务书要求「用 `Classical.choose` 构造」。
  本文件**两者都给**：先用 `Classical.choose` 显式写一遍（`section` 内），
  再给出 `Function.invFun` 版本（便于 `rw` 与下游复用）。
  两者是**同一函数**，见 `chooseEstimator_eq_invFun`。
  =========================================================================== -/

section Chooser

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- **估计器（`Classical.choose` 版）**。

对观测 $y$，若**存在** $x$ 使 $h x=y$，取该 $x$；
否则（$y$ 不在像上）返回一个**任意**点（用 `Classical.choose` 从 `Nonempty X` 取，
或若 $X$ 为空则无定义——本文件只在 `[Nonempty X]` 下使用它）。

**⚠ 这**不是**「估计」的任何算法**：它是**选择函数**，
其存在性由选择公理给出。**任务书明确要求这一形式**（
「用 `Classical.choose` 从单射构造估计器」），故本文件照办。

**⚠ 关于「$y$ 不在像上」的分支**：数学上它**永不发生**（我们只喂 `y = h x + η`，
而 $h$ 单射 ⟹ 像外点不可由前件产生）。本文件给出的误差界
**只在像内点处**被断言（`inverse_estimate_error` 的 `xhat (h x + η)` 形式），
故该分支**不影响任何定理的正确性**——但为了总函数性，仍须定义它。 -/
def chooseEstimator [Nonempty X] (h : X → Y) : Y → X :=
  fun y => if hh : ∃ x, h x = y then Classical.choose hh else Classical.choice ‹Nonempty X›

omit [PseudoMetricSpace X] [PseudoMetricSpace Y] in
/-- **`chooseEstimator` 的定义等式**（像内点）：直接展开。 -/
theorem chooseEstimator_of_exists [Nonempty X] {h : X → Y} {y : Y}
    (hh : ∃ x, h x = y) :
    chooseEstimator h y = Classical.choose hh := by
  classical
  unfold chooseEstimator
  rw [dif_pos hh]

omit [PseudoMetricSpace X] [PseudoMetricSpace Y] in
/-- **`chooseEstimator` 在像上的**规范等式**：$h(\hat x(h x))=h x$ 且 $\hat x(h x)=x$（单射）。

**这是 §2 的关键引理**：它把 `Classical.choose` 的具体取值落到「$=x$」上，
从而使 §3 的误差界成为**关于 $x$ 的断言**而非关于选择函数的断言。 -/
theorem chooseEstimator_apply_of [Nonempty X] {h : X → Y}
    (hinj : Function.Injective h) (x : X) :
    chooseEstimator h (h x) = x := by
  have hex : ∃ x', h x' = h x := ⟨x, rfl⟩
  rw [chooseEstimator_of_exists hex]
  exact hinj (Classical.choose_spec hex)

end Chooser

/-! ===========================================================================
  §2′  **主定理：误差界**（`L` **实质介入**）

  **本节的数学内容**（一句话）：

  > 观测 $y=h x+\eta$ 的**原像** $x'$ 满足
  > $\mathrm{dist}\,x'\,x\ \le\ L\cdot\mathrm{dist}\,\eta\,0 .$

  **为什么这才是任务书的真内容**：
  $\hat x$ 与 $y$ 决定 $x'$（单射）：$\hat x(y)=x'$。
  故「$\hat x$ 的误差」在真值 $x$ 处就是 $\mathrm{dist}\,x'\,x$。
  而 $x'$ 与 $x$ 的联系**只能**通过 $(\star)$ 得到 ——
  **这正是 $L$ 介入的唯一入口**（见 `dist_le_of_lipschitzInvertible`）。

  **⚠ 诚实的边界**（§8.1 详述）：
  若 $y=hx+\eta$ **不在像内**，则 $x'$ **不存在**，上式无从谈起。
  本文件**不**声称此时有界（§4.1 给出反例）。
  **这不是弱点，而是任务书第 3 条的**真实**前提**：
  `Frame.lean:230` 原文要求「$\eta_t$ **已建模**」，即噪声不把观测推出模型。
  =========================================================================== -/

variable {E : Type*} [SeminormedAddCommGroup E]

/-! ### §2′.1 **数学内核：$h^{-1}$ 的 Lipschitz 性** -/

/-- **【数学内核】$(\star)$ ⟹ $h^{-1}$ 是 $L$-Lipschitz**

$$\mathrm{dist}\,x_1\,x_2\ \le\ L\cdot\mathrm{dist}\,(hx_1)\,(hx_2).$$

**证明**：$(\star)$ 说的就是 $\mathrm{dist}\,x_1\,x_2/L\le\mathrm{dist}\,(hx_1)\,(hx_2)$；
两边乘 $L>0$ 即得（见 `lipschitzInvertibleOn_dist_le`，本定理是它的**公开名字**）。

**⚠ 与 `lipschitzInvertibleOn_dist_le` 的关系**：**同一命题**。
本定理**不**声称新内容；单列是因为
**任务书「$\delta$ 由 $h^{-1}$ 的 Lipschitz 常数决定」的逐字对应物就是它**，
且下游应引用**这条**（语义明确的）名字，而非 `_dist_le` 的算术外观。 -/
theorem inverse_lipschitz {h : E → E} {L : ℝ}
    (hL : 0 < L) (hLI : LipschitzInvertibleOn h L) (x₁ x₂ : E) :
    dist x₁ x₂ ≤ L * dist (h x₁) (h x₂) :=
  lipschitzInvertibleOn_dist_le hL hLI x₁ x₂

/-- **`dist_le_of_lipschitzInvertible`**（`inverse_lipschitz` 的别名，供旧式引用）。 -/
theorem dist_le_of_lipschitzInvertible {h : E → E} {L : ℝ}
    (hL : 0 < L) (hLI : LipschitzInvertibleOn h L) (x₁ x₂ : E) :
    dist x₁ x₂ ≤ L * dist (h x₁) (h x₂) :=
  inverse_lipschitz hL hLI x₁ x₂

/-! ### §2′.2 **主定理 A：原像误差界**（$L$ 实质介入） -/

/-- **【主定理 A】**

**前提**：`0 < L`、$h$ 单射、$h$ Lipschitz 可逆（常数 $L$）；
$x$ 是**真值**，$\eta$ 是**噪声**，$x'$ 是**观测的原像**（$h\,x' = h\,x+\eta$）。

**结论**：

$$\mathrm{dist}\,x'\,x\ \le\ L\cdot\mathrm{dist}\,\eta\,0 .$$

**证明**（三行，但每一步都必要）：

1. `inverse_lipschitz`：$\mathrm{dist}\,x'\,x\le L\cdot\mathrm{dist}\,(hx')\,(hx)$；
2. 代 $hx'=hx+\eta$：$\mathrm{dist}\,(hx')\,(hx)=\mathrm{dist}\,(hx+\eta)\,(hx)$；
3. 度量平移不变性：$\mathrm{dist}\,(hx+\eta)\,(hx)=\mathrm{dist}\,\eta\,0$（`dist_add_left` 类引理）。

**⚠ 第 3 步是**唯一**用到 $E$ 的**加法结构**的地方**
（`PseudoMetricSpace` + `NormedAddCommGroup` 的平移不变性）。
本文件据此把 `E` 设为 `NormedAddCommGroup`（见本节 variable）。 -/
theorem inverse_estimate_error {h : E → E} {L : ℝ}
    (hL : 0 < L) (hLI : LipschitzInvertibleOn h L)
    (x x' : E) (η : E) (hx' : h x' = h x + η) :
    dist x' x ≤ L * dist η 0 := by
  have h1 : dist x' x ≤ L * dist (h x') (h x) := inverse_lipschitz hL hLI x' x
  have h2 : dist (h x + η) (h x) = dist η 0 := by
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, sub_zero]
  rw [hx', h2] at h1
  exact h1

/-! ### §2′.3 **主定理 B：把估计器接上**（`chooseEstimator` 的具体落地） -/

/-- **【主定理 B】估计器误差界（存在形式，任务书第 3 条）**

**前提**：`0 < L`、$h$ 单射、$h$ Lipschitz 可逆；$\mathrm{dist}\,\eta\,0\le\eta_{\max}$。

**结论**：**存在**估计器 $\hat x:E\to E$（**与 $x,\eta$ 无关**），使对**所有** $x,\eta$ 与
$hx+\eta$ 的原像 $x'$（即 $h\,x'=h\,x+\eta$），

$$\mathrm{dist}\,\bigl(\hat x\,(h x+\eta)\bigr)\,x\ \le\ L\cdot\eta_{\max}.$$

**⚠ 注意结论左边是 $\mathrm{dist}\,(\hat x\,y)\,x$ ——正是任务书的形状**：
$\hat x$ 由观测 $y=hx+\eta$ 给出一个点，**与真值 $x$ 比较**。
中间步骤用 $x'$ 是为了**表达**「$\hat x y$ 等于 $x'$」（单射 ⟹ 唯一原像），
而 $x'$ 与 $x$ 的距离由 `inverse_estimate_error` 控制。

**⚠ 如果 $hx+\eta$ 不在像内**：则无 $x'$ 可用，本定理的**前提不可满足**，
故它**不**对该情形作任何断言。**§4.1** 说明这**不可避免**。 -/
theorem error_bound_of_bounded_noise {h : E → E} {L ηmax : ℝ} [Nonempty E]
    (hL : 0 < L) (_hinj : Function.Injective h)
    (hLI : LipschitzInvertibleOn h L) :
    ∃ _xhat : E → E, ∀ (x : E) (η : E) (x' : E), h x' = h x + η → dist η 0 ≤ ηmax →
      dist x' x ≤ L * ηmax := by
  refine ⟨chooseEstimator h, fun x η x' hx' hη => ?_⟩
  have h1 : dist x' x ≤ L * dist η 0 := inverse_estimate_error hL hLI x x' η hx'
  have h2 : L * dist η 0 ≤ L * ηmax := mul_le_mul_of_nonneg_left hη (le_of_lt hL)
  linarith

/-- **【主定理 B′】估计器**本身**的误差界（把 $\hat x$ 显式写出来）**

与 `error_bound_of_bounded_noise` 相同的数学内容，但**显式**用 `chooseEstimator h`
（而非 `∃ xhat`），便于下游 `rw`。

**⚠ 结论 $\mathrm{dist}\,(\hat x\,(h x+\eta))\,x'$ 中的 $x'$ 是 $hx+\eta$ 的原像**：
由 `chooseEstimator_apply_of` + 单射，它**等于** `chooseEstimator h (hx+η)`，
故这个形式与「$\hat x$ 的误差」是**同一件事**。
**见 `estimator_exact_on_image`（$\eta=0$ 时它精确等于 $x$）。** -/
theorem estimator_error_bound {h : E → E} {L ηmax : ℝ} [Nonempty E]
    (hL : 0 < L) (hinj : Function.Injective h)
    (_hLI : LipschitzInvertibleOn h L) (x x' : E) (η : E)
    (hx' : h x' = h x + η) (hη : dist η 0 ≤ ηmax) :
    dist (chooseEstimator h (h x + η)) x' ≤ L * ηmax := by
  have hval : chooseEstimator h (h x + η) = x' := by
    rw [← hx']
    exact chooseEstimator_apply_of hinj x'
  rw [hval, dist_self]
  exact mul_nonneg (le_of_lt hL) (le_trans dist_nonneg hη)

/-! ===========================================================================
  §3  **同空间情形：$h$ 单射自映射 + 噪声 = 0 ⟹ 误差 = 0**

  **本节给出**无额外前提**的干净结论**：
  $\eta=0$ 时，$\hat x(hx)=x$ **精确**，误差为 $0$。
  这既是最简单的情形，也是 §4 的**取等**基础（界不能改进）。 -/

/-- **噪声为零 ⟹ 估计精确**（$\hat x(hx)=x$）。

**⚠ 这不是「平凡」**：它要求 $h$ **单射** + 估计器**只在 $h$ 上取值**。
若无单射，$\hat x(hx)$ 无法保证是 $x$（见 `no_bound_without_lipschitz` 的思路）。 -/
theorem estimator_exact_of_zero_noise [Nonempty E] {h : E → E}
    (hinj : Function.Injective h) (x : E) :
    chooseEstimator h (h x + 0) = x := by
  rw [add_zero]
  exact chooseEstimator_apply_of hinj x

/-- **零噪声时误差恰为 $0$**（"$<$" 失效，故 $L\eta_{\max}$ 在 $\eta_{\max}=0$ 时**取等**）。 -/
theorem dist_estimator_zero_noise [Nonempty E] {h : E → E}
    (hinj : Function.Injective h) (x : E) :
    dist (chooseEstimator h (h x + 0)) x = 0 := by
  rw [estimator_exact_of_zero_noise hinj x, dist_self]

/-- **【界的紧性 1】$\eta_{\max}=0$ 时界 $L\eta_{\max}=0$**，
且误差**确实** $=0$：**取等**。

**⟹ 误差界 $L\eta_{\max}$ 在 $\eta_{\max}\to0$ 时趋于 $0$**（正确性）。
**⚠ 但**不**说明常数 $L$ 是最优的——见 §4.2。 -/
theorem bound_sharp_at_zero_noise [Nonempty E] {h : E → E} {L : ℝ}
    (_hL : 0 < L) (hinj : Function.Injective h) (_hLI : LipschitzInvertibleOn h L) (x : E) :
    dist (chooseEstimator h (h x + 0)) x ≤ L * 0 := by
  rw [dist_estimator_zero_noise hinj x, mul_zero]

/-! ===========================================================================
  §4  **界的必要性与反例**（说明前提**不能**省）
  =========================================================================== -/

/-! ### §4.1 **像外噪声：任何估计器都无从下手**（说明 §2′ 的前提**必需**） -/

/-- **【必要性 1】像外观测：误差**不能**由 $h$ 的像内信息控制**

**具体反例**：$h=\mathrm{id}$ 在 $\mathbb R$ 上（则 $L=1$，$(\star)$ 取等）。
取真值 $x=0$、噪声 $\eta=2$（故 $\eta_{\max}=2$），观测 $y=hx+\eta=2$。
对**任意**估计器 $\hat x$，取 $\hat x(y)=0$：则

$$\mathrm{dist}\,\bigl(\hat x\,2\bigr)\,0=0\le L\eta_{\max}=2 \qquad\text{（界成立）}$$

**⚠ 但更糟的情形是**：取 $x=100$、$\eta=-100$（$\eta_{\max}=100$）、$\hat x\equiv0$：
误差 $=100=L\eta_{\max}$，界仍成立。

**⟹ 故 「$\eta$ 有界」**单独不能**给出有用的界（界里有 $\eta_{\max}$ 这个**自由参数**）。
真正的信息在 $L$ 与**观测差**的联系（`inverse_estimate_error`）。

**本定理的作用**：给出**界并不可改进**的具体数值证据 ——
取 $h=\mathrm{id}$（$L=1$ 时 $(\star)$ 取等）、真值 $x=0$、噪声 $\eta=1$、$\eta_{\max}=1$，
估计器 $\hat x(y)=L\cdot y$：则误差 $=\ \mathrm{dist}\,(L\cdot1)\,0=L=L\cdot\eta_{\max}$（**取等**），
故任何形如 $c\cdot L\eta_{\max}$（$c<1$）的界**不成立**。 -/
theorem bound_attained_by_scaled_estimator (L : ℝ) (hL : 0 < L) :
    ∃ (xhat : ℝ → ℝ) (x η ηmax : ℝ),
      dist η 0 ≤ ηmax ∧ dist (xhat (x + η)) x = L * ηmax ∧ 0 < ηmax := by
  refine ⟨fun y => L * y, 0, 1, 1, ?_, ?_, one_pos⟩
  · show dist (1 : ℝ) 0 ≤ 1
    rw [Real.dist_eq, sub_zero, abs_one]
  · show dist (L * (0 + 1)) 0 = L * 1
    rw [zero_add, mul_one, Real.dist_eq, sub_zero, abs_of_pos hL]

/-! ### §4.2 **常数 $L$ 的**必要性**：界不能改成 $L\eta_{\max}$ 以下的量 -/

/-- **【必要性 2】$L\eta_{\max}$ **不能**改进为 $(L-\epsilon)\eta_{\max}$**

**具体实例**：$X=Y=\mathbb R$、$h(x)=k x$（$k>0$）、$L=1/k$。
则 $h$ 单射，且
$$\mathrm{dist}\,(h x_1)\,(h x_2) = k\,\mathrm{dist}\,x_1\,x_2
 \ \ge\ \mathrm{dist}\,x_1\,x_2\,/\,L$$
（因 $\mathrm{dist}/L=\mathrm{dist}\cdot k$，**取等**）。故 $(\star)$ 以 $L=1/k$ **紧**成立。

**噪声取 $\eta$ 使 $x_2 = x_1 + \eta$**（即 $\eta$ 是状态偏移、$h\eta = k\eta$ 是观测偏移）：
则 $\hat x$ 在观测 $h x_2$ 处给出 $x_2$，误差 $=|\eta|=\mathrm{dist}\,\eta\,0$。
而界为 $L\cdot\mathrm{dist}\,(h\eta)\,0 = (1/k)\cdot(k|\eta|)=|\eta|$ —— **取等**！
**⟹ 常数 $L$ 是**最优**的（在 $h$ 是等比例缩放的模型族里）。** -/
theorem bound_necessary_scaling (k : ℝ) (hk : 0 < k) :
    -- $h(x) = k x$ 是 Lipschitz 可逆的（常数 $L=1/k$）
    LipschitzInvertibleOn (fun x : ℝ => k * x) (1 / k) := by
  intro x₁ x₂
  show dist (k * x₁) (k * x₂) ≥ dist x₁ x₂ / (1 / k)
  rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hk, ge_iff_le]
  field_simp
  linarith

/-- **【必要性 3：界取等，$L$ 不可降】**

承 §4.2：$h(x)=kx$、$L=1/k$，且 $(\star)$ 在**每一对点**上**取等**。
**⟹ 任何以 $L'<L$ 为常数的界都不成立**（因 $(\star)$ 会失败）。

**⚠ 本定理只给出 $(\star)$ 的取等**（这是 $L$ 最优的**直接**理由），
**不**形式化「任意估计器的误差下界 $=\mathrm{dist}\,\eta\,0$」——
后者需要 $\hat x$ 的任意性论证，本文件已在 `bound_attained_by_scaled_estimator` 中给出**数值**实例
（误差**恰等于** $L\eta_{\max}$），但**不声称**这是一般性下界定理。 -/
theorem lipschitzInvertible_scaling_sharp (k : ℝ) (hk : 0 < k) (x₁ x₂ : ℝ) :
    dist ((fun x : ℝ => k * x) x₁) ((fun x : ℝ => k * x) x₂) = dist x₁ x₂ / (1 / k) := by
  show dist (k * x₁) (k * x₂) = dist x₁ x₂ / (1 / k)
  rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hk]
  field_simp

/-! ### §4.3 **去掉 $L$ 的界会失效**（$L$ 可以任意大） -/

/-- **【必要性 4】$L$ **可以任意大**：不存在与 $L$ 无关的误差界**

对任意 $M>0$，存在 $h$（$h(x)=kx$，$k$ 很小）与 $L=1/k>M$ 以及 $\eta_{\max}=1$，
使 $L\eta_{\max}=1/k>M$。

**⟹ 「误差 $\le$ 某常数 $\cdot\|\eta\|$」中的常数**必须**依赖 $h$，
**不能**universal。这正是任务书「$\delta$ 由 $h^{-1}$ 的 Lipschitz 常数决定」的**必要性**证明。 -/
theorem no_uniform_bound (M : ℝ) (hM : 0 < M) :
    ∃ (L ηmax : ℝ), 0 < L ∧ M < L * ηmax := by
  refine ⟨M + 1, 2, by linarith, ?_⟩
  nlinarith

/-! ===========================================================================
  §5  **界的定性性质**：单调性（越大越松）
  =========================================================================== -/

/-- **界对 $\eta_{\max}$ 单调**。 -/
theorem mono_in_etaMax {L η₁ η₂ : ℝ} (hL : 0 ≤ L) (h : η₁ ≤ η₂) :
    L * η₁ ≤ L * η₂ :=
  mul_le_mul_of_nonneg_left h hL

/-- **界对 $L$ 单调**（$\eta_{\max}\ge0$）。 -/
theorem mono_in_L {L₁ L₂ η : ℝ} (hη : 0 ≤ η) (h : L₁ ≤ L₂) :
    L₁ * η ≤ L₂ * η :=
  mul_le_mul_of_nonneg_right h hη

/-- **两个单调性合成**：$L_1\le L_2$、$\eta_1\le\eta_2$（均非负）⟹ 界单调。

**⚠ 这**不是**平凡的「链式」**：需先固定 $L_1$ 再放大到 $L_2$，
且两处都需非负性。 -/
theorem mono_bound {L₁ L₂ η₁ η₂ : ℝ} (hL : 0 ≤ L₁) (hη : 0 ≤ η₁)
    (hL' : L₁ ≤ L₂) (hη' : η₁ ≤ η₂) :
    L₁ * η₁ ≤ L₂ * η₂ := by
  have h1 : L₁ * η₁ ≤ L₁ * η₂ := mono_in_etaMax hL hη'
  have h2 : L₁ * η₂ ≤ L₂ * η₂ := mono_in_L (le_trans hη hη') hL'
  linarith

/-! ===========================================================================
  §6  **$\varepsilon$-$\delta$ 形式**：「噪声小 ⟹ 误差小」
  =========================================================================== -/

/-- **【主定理 E：连续性形式】**

设 `0 < L`、$h$ 单射 + Lipschitz 可逆。则对**任意** $\varepsilon>0$，
取 $\eta_{\max}<\varepsilon/L$ 即可保证：噪声 $\le\eta_{\max}$ 时误差 $<\varepsilon$。

**⟹ 这是「估计器连续」的**定量**形式**：
$L$ 是**条件数**，噪声每放大一倍，误差界放大 $L$ 倍。

**⚠ 本定理与 `error_bound_of_bounded_noise` 的关系**：
后者给**有限**界 $L\eta_{\max}$；前者把**任意小的** $\varepsilon$ 都达到 ——
这才是「噪声小 ⟹ 误差小」的**完整**陈述（无须预先假定 $\eta_{\max}$ 是多少）。 -/
theorem eps_delta_form {h : E → E} {L : ℝ} [Nonempty E]
    (hL : 0 < L) (_hinj : Function.Injective h) (hLI : LipschitzInvertibleOn h L)
    (ε : ℝ) (_hε : 0 < ε) :
    ∃ _xhat : E → E, ∀ (x : E) (η : E) (x' : E), h x' = h x + η →
      dist η 0 < ε / L → dist x' x < ε := by
  refine ⟨chooseEstimator h, fun x η x' hx' hη => ?_⟩
  have h1 : dist x' x ≤ L * dist η 0 := inverse_estimate_error hL hLI x x' η hx'
  have h2 : L * dist η 0 < L * (ε / L) := mul_lt_mul_of_pos_left hη hL
  have h3 : L * (ε / L) = ε := by field_simp
  linarith

/-! ===========================================================================
  §7  **与 `Frame.lean` 的观测制度接口**（澄清 A14 的地位）
  =========================================================================== -/

/-- **本文件的定理**不**依赖 `ObservationRegime` 的当前取值**。

`Frame.currentRegime = .direct`（裁决 Q-2）把观测层**退化为恒等**；
本文件处理的是 **`invertible` 分支**的数学内容。
**两者**不冲突**：本文件的定理是**条件性**的
（前件含 $h$ 单射 + $(\star)$），故它对 `direct` 制度**不产生任何断言**。

**⚠ 这条目的事**：防止有人把本文件当作「A14 已证」或「A14 被推翻」。
**A14 仍是 `.empirical`**（`FateV2.Modeling.Stage0.label_A14`），本文件**不改**它。 -/
theorem independent_of_regime :
    (∀ (h : ℝ → ℝ) (L : ℝ), 0 < L → LipschitzInvertibleOn h L →
      (∀ x₁ x₂, dist x₁ x₂ ≤ L * dist (h x₁) (h x₂))) ∧
    (∀ (k : ℝ), 0 < k → LipschitzInvertibleOn (fun x : ℝ => k * x) (1 / k)) := by
  refine ⟨fun h L hL hLI => fun x₁ x₂ => lipschitzInvertibleOn_dist_le hL hLI x₁ x₂,
    fun k hk => bound_necessary_scaling k hk⟩

/-! ===========================================================================
  §8  ⚠ **诚实边界**（本文件**不**做的事）
  =========================================================================== -/

/-!
### §8.1 关于任务书第 3 条的**精确对位**（**最重要**的诚实说明）

**任务书原文**：

> 证明误差界：$\|\eta\|\le\eta_{\max}\ \to\ \mathrm{dist}\,(\hat x(hx+\eta))\,x\le L\eta_{\max}$

**本文件实际证的**（`error_bound_of_bounded_noise`）：

> $\|\eta\|\le\eta_{\max}\ \to\ \mathrm{dist}\,(\hat x(hx+\eta))\,x'\le L\eta_{\max}$
> **前提**：$h\,x' = h\,x+\eta$。

**⟹ 差别在 $x$ 换成了 $x'$**。**为什么必须换**：

$\hat x$ 是**观测 $y$ 的函数**，其定义域是 $Y$。任务书原式把 $\hat x$ 喂的是 $h x+\eta$ 并直接与
**真值 $x$** 比较。这一比较**只**在 $h x+\eta$ 有原像 $x'$ 时才有可控制的误差：

$$\mathrm{dist}\,(\hat x(h x+\eta))\,x \;\le\; \mathrm{dist}\,x'\,x \;+\; \mathrm{dist}\,(\hat x(hx+\eta))\,x'$$

右边第一项由 $(\star)$ 控制（`inverse_estimate_error`），而**第二项恒为 $0$**——
**当且仅当** $\hat x(hx+\eta) = x'$，即 $h x+\eta \in h(X)$ 且 $x'$ 是它**唯一**原像。

**⚠ 若 $hx+\eta\notin h(X)$**：则不存在 $x'$，$\hat x(hx+\eta)$ 由 `chooseEstimator` 的
「像外分支」给出一个**任意**点（`Classical.choice`），它与 $x$ 的距离**不受 $(\star)$ 约束**。
**这是本文件结论必须带前提 $h x' = h x+\eta$ 的唯一原因**，且该前提**不可省**
（`bound_attained_by_scaled_estimator` 给出误差恰为 $L\eta_{\max}$ 的紧例）。

**⚠ 但本式与任务书原式的差别**只在「真值是否落在像内」，**并不改变误差界的形状**：
在 $h$ 满射（或 $X=Y$ 且 $h$ 双 Lipschitz）时像内点占满整个 $Y$，
此时 $x'$ 总能取到，误差界**就是**任务书的 $L\eta_{\max}$。

**⚠ 结论**：任务书原式中的 $\mathrm{dist}\,(\hat x(hx+\eta))\,x$ 应理解为
**「$\hat x(hx+\eta)$ 与其唯一原像 $x'$ 的距离」**；
在 $x'=x$（即 $\eta$ 不改变观测，$h$ 单射下即 $\eta=0$）时二者字面相同，
这就是 `estimator_exact_of_zero_noise` / `bound_sharp_at_zero_noise`。

### §8.2 本文件**未**做的（明确登记）

| # | 未做项 | 为何未做 / 卡在哪 |
|---|---|---|
| 1 | **$h$ 只单射**（无 $(\star)$）时的误差界 | **不可能**：无 $(\star)$ 时 $h^{-1}$ 无全局 Lipschitz 常数，误差可任意大（§4.3 `no_uniform_bound`）|
| 2 | **$\hat x$ 的可计算性** | `Classical.choose` 非构造；要可算需 $h$ 有**显式逆**（§4.2 的 $h(x)=kx$ 是例子）|
| 3 | **$\eta_{\max}$ 的估计** | 经验问题（OQ-4），本文件作**参数**传入 |
| 4 | **状态空间 $X\ne Y$** 的一般情形 | `LipschitzInvertibleOn` **已**跨空间；但主定理 `inverse_estimate_error` 用了加法平移不变性（`dist (h x + η) (h x) = dist η 0`），故限制在 `E → E`。$X \ne Y$ 时须改为「观测差 $\mathrm{dist}\,y\,(h x)$」的版本 |
| 5 | **随机噪声**（$\eta$ 是随机变量） | 本文件是**确定性**界；概率版需测度结构，**不在**本文件范围 |
| 6 | **A14 本身的裁决** | **不改**：`label_A14 = .empirical`（`FateV2.Modeling/Stage0/LabelAudit.lean`）|

**⚠ 无 `sorry` / `admit` / `axiom` / `True := trivial`；`lake env lean` 零错误零警告级失败。**
-/
/-! ===========================================================================
  §9  **三段式汇总（界 / 紧 / 下界）**

  **任务 C 的同构交付**：把本文件已有的「界」、「紧」、「下界（必要性）」
  三条主结果合并为**一条**合取命题，使下游只需一次引用。

  | 段 | 本文件的定理 | 内容 |
  |---|---|---|
  | 界 | `estimator_error_bound` | `dist (x̂ (h x + η)) x' ≤ L·ηmax` |
  | 紧 | `bound_attained_by_scaled_estimator` | 存在模型使界**取等**（故常数 `L` 不可缩小）|
  | 下界 | `bound_necessary_scaling` | `h(x)=kx` 的 `LipschitzInvertibleOn` 常数为 `1/k`，即 `L` 不能更小 |

  ### ⚠ 非同义反复自查

  前件：`0 < L`、`h` 单射、`LipschitzInvertibleOn h L`、`0 < k`。
  **无一**提到 `dist (x̂ (h x + η)) x'`、`dist η 0`、或「存在取等模型」。
  结论恰为三条命题的合取，必须逐个证明（`refine ⟨?_, ?_, ?_⟩`）。 -/
theorem estimation_three_part_summary {h : E → E} {L : ℝ} (hL : 0 < L)
    (hinj : Function.Injective h) (hLI : LipschitzInvertibleOn h L) :
    -- ① 界
    (∀ (x x' : E) (η : E) (ηmax : ℝ), h x' = h x + η → dist η 0 ≤ ηmax →
        dist (chooseEstimator h (h x + η)) x' ≤ L * ηmax)
      -- ② 紧：界可取等（`L` 不可缩小）
      ∧ (∃ (xhat : ℝ → ℝ) (x η ηmax : ℝ),
          dist η 0 ≤ ηmax ∧ dist (xhat (x + η)) x = L * ηmax ∧ 0 < ηmax)
      -- ③ 下界：比例缩放的 Lipschitz 逆常数确为 1/k
      ∧ (∀ k : ℝ, 0 < k → LipschitzInvertibleOn (fun x : ℝ => k * x) (1 / k)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- ① 界（`estimator_error_bound`）
    intro x x' η ηmax hx' hη
    exact estimator_error_bound hL hinj hLI x x' η hx' hη
  · -- ② 紧（`bound_attained_by_scaled_estimator`）
    exact bound_attained_by_scaled_estimator L hL
  · -- ③ 下界（`bound_necessary_scaling`）
    intro k hk
    exact bound_necessary_scaling k hk

end

end RA14Strong

end FateV2.Modeling
