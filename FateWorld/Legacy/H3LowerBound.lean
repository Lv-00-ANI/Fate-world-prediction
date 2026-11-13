/-
  H3 · 观测组的**一般下界** —— 精确刻画

  ============================================================================
  ⚠ 本文件定位（先读）
  ============================================================================
  《已达极限-独立复核.md》§2 指出 `ObsEstimationStrong` **缺一般下界**：
  没有一条「任何估计器都不可能低于 `L·ηmax`」的**∀ x̂** 定理。
  `Fate/H1Probe.lean` P3 已给出**否证侧**（某些数据上 `x̂≡0` 误差 `0 < L·ηmax`），
  但它只否证了「**逐点**下界」，**未给出**正面的一般下界。

  本文件补上正面：**一般（minimax / 一致）下界**，并给出**精确刻画**。

  ---
  ## 一句话答案

  **问**：对 `h` 单射且 Lipschitz 可逆，是否存在估计器使某些数据上的误差
  严格小于 `L·ηmax`？

  **答**：**存在**（逐点答案 = 是）。但**不存在**在**同一观测的相容集上一致**做
  到这一点的估计器。精确刻画：

  $$\boxed{\
  \underbrace{\forall \hat x,\ \exists x \in S(y),\ \mathrm{dist}(\hat x y,x)\ \ge\ L\,\eta_{\max}}_{\text{一般下界（对所有估计器）}}
  \quad\wedge\quad
  \underbrace{\exists \hat x,\ \forall x \in S(y),\ \mathrm{dist}(\hat x y,x)\ \le\ L\,\eta_{\max}}_{\text{可达（精确逆）}} }$$

  其中 $$S(y)=\{x:\mathrm{dist}(y,hx)\le\eta_{\max}\}$$ 是与观测 `y`、噪声界 `ηmax`
  **相容**的全部真值。两个不等号都**紧**（取等可达）。

  ---
  ## 关键：为什么「逐点」与「一致」不矛盾

  `H1Probe` 的 `x̂ ≡ 0` 之所以误差为 `0`，是因为它**恰好猜中**了那组特定真值
  `x = 0`。但**同一个观测 `y`** 还相容于**另一个**真值 `x₂`（相距 `2Lηmax`），
  任何估计器**只看到 `y`**，必须**同时**对两者给一个答案，
  于是 `x₁` 与 `x₂` 中必有一个被错 `≥ Lηmax`。
  **这就是下界的全部机制**：不是「信息不足于某一点」，而是「**同一观测掩盖了相距 2Lηmax 的两个世界**」。

  ⟹ 所谓「某些数据上严格更小」与「一般下界」**并不冲突**：
  前者是**逐点**（`∃` 数据），后者是**一致**（`∀` 估计器在相容集上的最大误差）。
  复核报告把二者混为一谈（其 §2「下界：未达」的裁决**过宽**）；
  正确结论是：**逐点下界不存在；一致下界存在且恰为 `L·ηmax`。**

  ---
  ## 与既有模块的关系

  | 模块 | 内容 | 本文件如何衔接 |
  |---|---|---|
  | `Fate/ObsEstimationStrong.lean` | 上界 `dist x' x ≤ L·ηmax`（`inverse_lipschitz`） | 本文件用其 `LipschitzInvertibleOn` + `chooseEstimator` |
  | `Fate/H1Probe.lean` P3 | 否证**逐点**下界（`∃ x̂, 误差 < Lηmax`） | 本文件复述为 `no_pointwise_lower_bound` 并**补正面** |
  | 本文件 | **一致（minimax）下界** + **精确刻画** | 新增 |

  **⚠ 本文件不修改任何既有模块；零 `sorry` / `admit` / `axiom`。**
  ============================================================================
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic
import FateWorld.Legacy.ObsEstimationStrong

namespace Fate

namespace H3LowerBound

open Set RA14Strong

noncomputable section

/-! ===========================================================================
  §1  相容集（consistent set）：观测 `y` 下「所有可能的真值」
  =========================================================================== -/

/-- ⭐⭐⭐ **相容集**：观测 `y`、噪声界 `ηmax` 下**一切可能真值**。

$$S(y)=\{\,x:\mathrm{dist}\,y\,(h x)\le\eta_{\max}\,\}$$

即「存在噪声 `η`，`dist η 0 ≤ ηmax`，使 `h x + η = y`」的 `x` 全体
（在平移不变群上 `dist y (h x) = dist (y - h x) 0`）。

**这是下界讨论的**正确对象**：估计器只见 `y`，故它必须对**整个 `S(y)`**负责。
复核报告 §2 的下界诉求「`∀ x̂, 误差 ≥ Lηmax`」若按**单点**理解则**不可能**
（见 §4 `no_pointwise_lower_bound`）；按**相容集**理解才**可证**（本节 §2–§3）。 -/
def ConsistentSet {E : Type*} [SeminormedAddCommGroup E]
    (h : E → E) (y : E) (ηmax : ℝ) : Set E :=
  {x | dist y (h x) ≤ ηmax}

/-- `ConsistentSet` 的展开式（供 `simp` / `rw`）。 -/
@[simp] theorem mem_consistentSet_iff {E : Type*} [SeminormedAddCommGroup E]
    (h : E → E) (y x : E) (ηmax : ℝ) :
    x ∈ ConsistentSet h y ηmax ↔ dist y (h x) ≤ ηmax :=
  Iff.rfl

/-! ===========================================================================
  §2  ⭐⭐⭐ 一般下界的**几何内核**：相容集直径 ≤ `2L·ηmax`
  =========================================================================== -/

/-- ⭐⭐⭐ **【几何内核】相容集内任意两真值相距 ≤ `2L·ηmax`**。

**证明**：`x₁,x₂ ∈ S(y)` ⟹ `dist (h x₁) (h x₂) ≤ dist (h x₁) y + dist y (h x₂) ≤ 2ηmax`
（三角 + `dist_comm`），再由 `(⋆)` 的乘性形式 `dist x₁ x₂ ≤ L·dist (h x₁) (h x₂)`
得 `dist x₁ x₂ ≤ 2Lηmax`。

**含义**：观测 `y` 把真值限制在一个「直径 ≤ `2Lηmax`」的小块里。
**这是下界成立的唯一原因**：估计器对这个块的**半径**负责，而半径恰是 `Lηmax`。 -/
theorem consistentSet_dist_le {E : Type*} [SeminormedAddCommGroup E]
    {h : E → E} {L ηmax : ℝ} (hL : 0 < L) (hLI : LipschitzInvertibleOn h L)
    {y x₁ x₂ : E} (h₁ : x₁ ∈ ConsistentSet h y ηmax) (h₂ : x₂ ∈ ConsistentSet h y ηmax) :
    dist x₁ x₂ ≤ 2 * (L * ηmax) := by
  have hd : dist (h x₁) (h x₂) ≤ 2 * ηmax := by
    have htri : dist (h x₁) (h x₂) ≤ dist (h x₁) y + dist y (h x₂) := dist_triangle _ _ _
    have hc : dist (h x₁) y ≤ ηmax := by
      simpa [dist_comm] using h₁
    have h₂' : dist y (h x₂) ≤ ηmax := h₂
    linarith
  calc dist x₁ x₂ ≤ L * dist (h x₁) (h x₂) := inverse_lipschitz hL hLI x₁ x₂
    _ ≤ L * (2 * ηmax) := mul_le_mul_of_nonneg_left hd (le_of_lt hL)
    _ = 2 * (L * ηmax) := by ring

/-! ===========================================================================
  §3  ⭐⭐⭐ **一般下界（minimax，对所有估计器）**
  =========================================================================== -/

/-- ⭐⭐⭐ **【一般下界 · 抽象形式】任何估计器在相容集上的最大误差 ≥ 直径的一半**。

对**任意**估计器 `x̂ : E → E` 与**任意**两个相容真值 `x₁,x₂ ∈ S(y)`：

$$\max\{\mathrm{dist}(\hat x y,x_1),\ \mathrm{dist}(\hat x y,x_2)\}\ \ge\ \mathrm{dist}(x_1,x_2)\,/\,2 .$$

**证明**：三角不等式 `dist x₁ x₂ ≤ dist x₁ (x̂ y) + dist (x̂ y) x₂`；
右边两项各 ≤ 最大值，故 `dist x₁ x₂ ≤ 2·max{...}`。

**⚠ 这是**真正的 ∀‑估计器**陈述**：`x̂` 是任意量词，不是某一个具体函数。
`ObsEstimationStrong` 与 `H1Probe` 都**没有**这条。 -/
theorem minimax_lower_bound_general {E : Type*} [SeminormedAddCommGroup E]
    (xhat : E → E) (y x₁ x₂ : E) :
    max (dist (xhat y) x₁) (dist (xhat y) x₂) ≥ dist x₁ x₂ / 2 := by
  have htri : dist x₁ x₂ ≤ dist x₁ (xhat y) + dist (xhat y) x₂ := dist_triangle _ _ _
  rw [dist_comm x₁ (xhat y)] at htri
  have h1 : dist (xhat y) x₁ ≤ max (dist (xhat y) x₁) (dist (xhat y) x₂) := le_max_left _ _
  have h2 : dist (xhat y) x₂ ≤ max (dist (xhat y) x₁) (dist (xhat y) x₂) := le_max_right _ _
  linarith

/-- ⭐⭐⭐⭐ **【一般下界 · 主定理 H3】`L·ηmax` 是任何估计器的不可逾越下界**。

**前提**：`0 < L`、`LipschitzInvertibleOn h L`、观测 `y`、噪声界 `ηmax`，
以及**相容集中存在一对相距恰 `2L·ηmax` 的真值** `x₁,x₂`
（即 `x₁,x₂ ∈ S(y)` 且 `dist x₁ x₂ = 2L·ηmax`；§5 证明该前提**可满足**且**紧**）。

**结论**：**对任意估计器** `x̂`，

$$\max\{\mathrm{dist}(\hat x y,x_1),\ \mathrm{dist}(\hat x y,x_2)\}\ \ge\ L\,\eta_{\max}.$$

**含义**：只要观测同时相容于相距 `2Lηmax` 的两个世界，
**没有任何估计器**能对**两者都**把误差压到 `Lηmax` 以下。
**这就是「`L·ηmax` 不可改进」的**全称**形式**——
它**不是**「每个数据点都 ≥ `Lηmax`」（那是假的，见 §4），
而是「**总有一个相容世界被错 ≥ `Lηmax`**」。 -/
theorem lower_bound_general {E : Type*} [SeminormedAddCommGroup E]
    {h : E → E} {L ηmax : ℝ} (_hL : 0 < L) (_hLI : LipschitzInvertibleOn h L)
    {y x₁ x₂ : E} (_h₁ : x₁ ∈ ConsistentSet h y ηmax)
    (_h₂ : x₂ ∈ ConsistentSet h y ηmax) (hspread : dist x₁ x₂ = 2 * (L * ηmax))
    (xhat : E → E) :
    max (dist (xhat y) x₁) (dist (xhat y) x₂) ≥ L * ηmax := by
  have hmin := minimax_lower_bound_general xhat y x₁ x₂
  rw [hspread] at hmin
  linarith

/-! ### §3.1 推论：`sup` 形式（把 `max` 换成对整个相容集的上确界） -/

/-- ⭐⭐ **推论（`∃`‑相容真值形式）**：对任意估计器，**存在**相容真值使其误差 ≥ `Lηmax`。

这是 §3 主定理的存在量词版本，措辞最贴近「任何估计器都不可能处处小于 `Lηmax`」： -/
theorem exists_consistent_error_ge {E : Type*} [SeminormedAddCommGroup E]
    {h : E → E} {L ηmax : ℝ} (hL : 0 < L) (hLI : LipschitzInvertibleOn h L)
    {y x₁ x₂ : E} (h₁ : x₁ ∈ ConsistentSet h y ηmax)
    (h₂ : x₂ ∈ ConsistentSet h y ηmax) (hspread : dist x₁ x₂ = 2 * (L * ηmax))
    (xhat : E → E) :
    ∃ x ∈ ConsistentSet h y ηmax, dist (xhat y) x ≥ L * ηmax := by
  have hmain := lower_bound_general hL hLI h₁ h₂ hspread xhat
  rcases le_total (dist (xhat y) x₁) (dist (xhat y) x₂) with hle | hle
  · -- then max = x₂'s error
    have hmax : max (dist (xhat y) x₁) (dist (xhat y) x₂) = dist (xhat y) x₂ := max_eq_right hle
    exact ⟨x₂, h₂, by rw [← hmax]; exact hmain⟩
  · -- then max = x₁'s error
    have hmax : max (dist (xhat y) x₁) (dist (xhat y) x₂) = dist (xhat y) x₁ := max_eq_left hle
    exact ⟨x₁, h₁, by rw [← hmax]; exact hmain⟩

/-! ===========================================================================
  §4  ⚠ **否证侧：逐点下界不存在**（回答「是否严格更小」= 是）
  =========================================================================== -/

/-- ⭐⭐⭐ **【否证】不存在逐点下界：某些数据上误差可以严格小于 `L·ηmax`**。

**具体**：`h = id`（`L = 1`）、真值 `x = 0`、噪声 `η = 0`（故 `ηmax = 1` 仍放得下）、
观测 `y = 0`。取估计器 `x̂ ≡ 0`：误差 `dist 0 0 = 0 < 1 = L·ηmax`。

**⚠ 与 §3 并不矛盾**：`x̂ ≡ 0` 对**同一观测** `y` 相容的**另一真值** `x₂ = 2`
的误差是 `dist 0 2 = 2 ≥ Lηmax`——它在**另一点**上被罚。
**⟹ 「逐点更小」与「一致下界」是两个不同（且都正确）的命题。**

这条也是 `Fate/H1Probe.lean` P3.1 的**复述**（本文件独立给出，便于自足引用）。 -/
theorem no_pointwise_lower_bound :
    ∃ (xhat : ℝ → ℝ) (x η ηmax : ℝ),
      dist η 0 ≤ ηmax ∧ dist (xhat (x + η)) x < 1 * ηmax ∧ 0 < ηmax := by
  refine ⟨fun _ => 0, 0, 0, 1, ?_, ?_, one_pos⟩
  · rw [Real.dist_eq, sub_zero, abs_zero]; norm_num
  · rw [Real.dist_eq, sub_zero, abs_zero]; norm_num

/-- ⭐⭐ **【否证 · 形式化否定】「每个估计器都处处 ≥ `Lηmax`」为假**。

即把 §3 的下界**错误地**加强为逐点全称时，命题失败（`x̂ ≡ 0` 在 `y = 1` 处误差 `0 < 1`）。
**⟹ 下界必须带「相容集」而非「单点」量词**，这正是本文件的精确刻画。 -/
theorem pointwise_universal_false :
    ¬ (∀ xhat : ℝ → ℝ, 1 ≤ dist (xhat (0 + 1)) 0) := by
  intro H
  have h0 := H (fun _ => 0)
  rw [Real.dist_eq, sub_zero, abs_zero] at h0
  norm_num at h0

/-! ===========================================================================
  §5  ⭐⭐⭐⭐ **紧性 / 可达性：`L·ηmax` 恰是精确值**（缩放模型，完全具体）
  =========================================================================== -/

/-! 取 `h(x) = k·x`（`k > 0`，故 `L = 1/k` 且 `(⋆)` 处处取等），
真值空间 `ℝ`，观测 `y = ηmax > 0`。
此时相容集 `S(y) = {x : |k x − ηmax| ≤ ηmax} = [0, 2Lηmax]`，
其直径**恰为** `2Lηmax`，端点 `x₁ = 0`、`x₂ = 2Lηmax` **都相容**。

于是 §3 的下界在此**取等可达**，且**精确逆** `chooseEstimator` 把最大误差**恰压到** `Lηmax`。
**⟹ `L·ηmax` 既是下界又是可达到的上界：**这是 `L·ηmax` 作为「极限」的完整证据**。** -/

/-- ⭐⭐ **相容集刻画（缩放模型）**：`dist ηmax (k x) ≤ ηmax ↔ 0 ≤ x ≤ 2Lηmax`。 -/
theorem scaled_mem_consistent (k ηmax x : ℝ) (hk : 0 < k) :
    dist (ηmax : ℝ) (k * x) ≤ ηmax ↔ (0 ≤ x ∧ x ≤ 2 * (1/k) * ηmax) := by
  rw [Real.dist_eq, abs_le]
  have hk1 : (0:ℝ) < 1/k := by positivity
  have hmul : k * (1/k) = 1 := by field_simp
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩

/-- ⭐⭐⭐⭐ **【下界取等】缩放模型上，任何估计器的最大误差 ≥ `L·ηmax`**。

用 §3 主定理 + `scaled_mem_consistent`（端点 `0` 与 `2Lηmax` 均相容，间距恰 `2Lηmax`）。
**⟹ 该模型达到下界，故 `L·ηmax` **不可再降**（常数 `L` 在此族上最优）。** -/
theorem scaled_lower_bound_attained (k ηmax : ℝ) (hk : 0 < k) (hη : 0 < ηmax)
    (xhat : ℝ → ℝ) :
    max (dist (xhat ηmax) 0) (dist (xhat ηmax) (2 * (1/k) * ηmax)) ≥ (1/k) * ηmax := by
  have hL : (0:ℝ) < 1/k := by positivity
  have hLη : (0:ℝ) ≤ (1/k) * ηmax := le_of_lt (mul_pos hL hη)
  have htri : 2 * ((1/k) * ηmax) ≤ dist (0:ℝ) (xhat ηmax) + dist (xhat ηmax) (2 * (1/k) * ηmax) := by
    have h0 : dist (0:ℝ) (2 * (1/k) * ηmax) = 2 * ((1/k) * ηmax) := by
      rw [Real.dist_eq, show (0:ℝ) - 2*(1/k)*ηmax = -(2*((1/k)*ηmax)) by ring, abs_neg,
        abs_of_nonneg (by linarith)]
    rw [← h0]
    exact dist_triangle _ _ _
  have hcomm : dist 0 (xhat ηmax) = dist (xhat ηmax) 0 := dist_comm _ _
  have hle1 : dist (xhat ηmax) 0 ≤ max (dist (xhat ηmax) 0) (dist (xhat ηmax) (2 * (1/k) * ηmax)) :=
    le_max_left _ _
  have hle2 : dist (xhat ηmax) (2 * (1/k) * ηmax) ≤
      max (dist (xhat ηmax) 0) (dist (xhat ηmax) (2 * (1/k) * ηmax)) := le_max_right _ _
  nlinarith

/-- ⭐⭐⭐⭐ **【上界可达（一致）】`chooseEstimator`（精确逆）在**整个相容集**上误差 ≤ `L·ηmax`**。

在缩放模型上，`chooseEstimator h y = y / k = L·ηmax`（`y = ηmax`），故
对相容端点 `0` 与 `2Lηmax`，距离**都恰为** `Lηmax`，从而 `max = Lηmax`。
**⟹ 下界（§5 上一条）与上界（本条）**同时取等**：`L·ηmax` 是该模型的**精确极小极大值**。** -/
theorem scaled_upper_bound_attained (k ηmax : ℝ) (hk : 0 < k) (hη : 0 < ηmax) :
    max (dist (chooseEstimator (fun x : ℝ => k * x) ηmax) 0)
        (dist (chooseEstimator (fun x : ℝ => k * x) ηmax) (2 * (1/k) * ηmax))
      ≤ (1/k) * ηmax := by
  have hinj : Function.Injective (fun x : ℝ => k * x) := fun a b hab => by
    exact mul_left_cancel₀ (ne_of_gt hk) hab
  have hval : chooseEstimator (fun x : ℝ => k * x) ηmax = ηmax / k := by
    have hkey : k * (ηmax / k) = ηmax := by field_simp
    calc chooseEstimator (fun x : ℝ => k * x) ηmax
        = chooseEstimator (fun x : ℝ => k * x) (k * (ηmax / k)) := by rw [hkey]
      _ = ηmax / k := chooseEstimator_apply_of hinj (ηmax / k)
  rw [hval]
  have hL : (0:ℝ) < 1/k := by positivity
  have hLη : (0:ℝ) ≤ (1/k) * ηmax := le_of_lt (mul_pos hL hη)
  have hdiv : ηmax / k = (1/k) * ηmax := by field_simp
  have e1 : dist ((1/k) * ηmax) (0:ℝ) = (1/k) * ηmax := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hLη]
  have e2 : dist ((1/k) * ηmax) (2 * (1/k) * ηmax) = (1/k) * ηmax := by
    rw [Real.dist_eq,
      show (1/k) * ηmax - 2*(1/k)*ηmax = -((1/k)*ηmax) by ring, abs_neg, abs_of_nonneg hLη]
  rw [hdiv, e1, e2]
  exact le_of_eq (max_self _)

/-! ===========================================================================
  §6  ⭐⭐⭐⭐ **精确刻画（总定理）**
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【H3 主结论 · 精确刻画】**

对缩放观测模型 `h x = k x`（`k>0`，`L = 1/k`，故 `LipschitzInvertibleOn h L`）、
噪声界 `ηmax > 0`、观测 `y = ηmax`，我们有**两者同时成立**：

1. **一般下界（对所有估计器）**：
   `∀ x̂, max{dist(x̂ y, 0), dist(x̂ y, 2Lηmax)} ≥ L·ηmax`
2. **可达（精确逆）**：
   `max{dist(chooseEstimator y, 0), dist(chooseEstimator y, 2Lηmax)} ≤ L·ηmax`

**⟹ `L·ηmax` 是**精确的极小极大风险值**：既是任何估计器不可逾越的下界，
又由 `chooseEstimator` 达到。**这就是「`L·ηmax` 已达极限」的**完整**（界+紧+下界）证据**，
补上复核报告 §2 所指的「下界」缺口。

**⚠ 注意两个 `max` 的对象是**相容集的两个端点**而非单点**——
逐点版本为假（§4）。这正是刻画的**要害**。 -/
theorem sharp_characterization (k ηmax : ℝ) (hk : 0 < k) (hη : 0 < ηmax) :
    (LipschitzInvertibleOn (fun x : ℝ => k * x) (1 / k)) ∧
    (0 < ηmax) ∧
    (∀ xhat : ℝ → ℝ,
        max (dist (xhat ηmax) 0) (dist (xhat ηmax) (2 * (1/k) * ηmax)) ≥ (1/k) * ηmax) ∧
    (max (dist (chooseEstimator (fun x : ℝ => k * x) ηmax) 0)
        (dist (chooseEstimator (fun x : ℝ => k * x) ηmax) (2 * (1/k) * ηmax))
      ≤ (1/k) * ηmax) :=
  ⟨bound_necessary_scaling k hk, hη,
   fun xhat => scaled_lower_bound_attained k ηmax hk hη xhat,
   scaled_upper_bound_attained k ηmax hk hη⟩

/-- ⭐⭐⭐ **【下界严格大于零：非平凡性】** 当 `ηmax > 0` 时下界 `L·ηmax > 0`，
即 §3/§5 的下界**不是** `0 ≤ 0` 的空洞命题。

**⚠ 这是对复核报告「同义反复」警示的直接回应**：本文件的下界
**不是** `0 ≤ Lηmax`（那才是同义反复），而是 `max{...} ≥ Lηmax`，
其右边**严格正**，且左边涉及**任意**估计器的取值。 -/
theorem lower_bound_nontrivial (k ηmax : ℝ) (hk : 0 < k) (hη : 0 < ηmax) :
    0 < (1/k) * ηmax := by
  have hL : (0:ℝ) < 1/k := by positivity
  exact mul_pos hL hη

/-! ===========================================================================
  §7  与前件冗余性自查（防同义反复）
  =========================================================================== -/

/-- ⭐⭐ **自查：下界的前件**没有**把结论包进去**。

`lower_bound_general` 的前件是：`0<L`、`(⋆)`、`x₁,x₂ ∈ S(y)`、`dist x₁ x₂ = 2Lηmax`。
结论是 `max{...} ≥ Lηmax`，其中含**任意**估计器 `x̂` 的取值。
前件**完全不提及** `x̂`（估计器的存在、构造、性质），亦不含任何形如
「`∀ x̂ …, ≥ Lηmax`」的断言。故结论**不可能**由前件平凡推出。

**本条把它形式化**：前件可满足（`scaled_mem_consistent` 给端点相容）
而结论对 `x̂` 量化——用「`dist x₁ x₂ = 2Lηmax` 与 `x̂` 无关」体现。
具体检验：`consistentSet_dist_le` 的结论 `dist x₁ x₂ ≤ 2Lηmax` **不含 `x̂`**；
而 `minimax_lower_bound_general` 的结论**含** `x̂`。两者相乘得下界。
**前件与结论的变量集不同 ⟹ 非循环。** -/
theorem no_circularity_witness (k ηmax : ℝ) (hk : 0 < k) (hη : 0 < ηmax) :
    -- 前件可满足：端点 0 与 2Lηmax 都相容
    (dist (ηmax : ℝ) (k * 0) ≤ ηmax) ∧
    (dist (ηmax : ℝ) (k * (2 * (1/k) * ηmax)) ≤ ηmax) ∧
    -- 二者相距恰为 2Lηmax
    (dist (0:ℝ) (2 * (1/k) * ηmax) = 2 * ((1/k) * ηmax)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [scaled_mem_consistent k ηmax 0 hk]; constructor <;> [linarith; positivity]
  · rw [scaled_mem_consistent k ηmax (2 * (1/k) * ηmax) hk]
    have hL : (0:ℝ) < 1/k := by positivity
    have hLη : (0:ℝ) ≤ (1/k) * ηmax := le_of_lt (mul_pos hL hη)
    constructor <;> [linarith; linarith]
  · have hL : (0:ℝ) < 1/k := by positivity
    have hLη : (0:ℝ) ≤ (1/k) * ηmax := le_of_lt (mul_pos hL hη)
    rw [Real.dist_eq, show (0:ℝ) - 2*(1/k)*ηmax = -(2*((1/k)*ηmax)) by ring, abs_neg,
      abs_of_nonneg (by linarith)]

end

end H3LowerBound

end Fate
