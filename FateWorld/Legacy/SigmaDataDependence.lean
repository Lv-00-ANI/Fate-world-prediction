/-
  命运理论 · **σ 的数值依赖外部数据（`SigmaDataDependence`）**

  ============================================================================
  ⚠⚠ 本文件的定位与诚实边界（**必读，不得略过**）
  ============================================================================

  **背景**：⑨（σ 的数值）在 `Fate/SigmaUnified.lean` 中已有 6 条定理
  （`resolveSigma_sourceOfDomain` / `_sourceOfAIC` / `_sourceOfInfoGain` /
  `_sourceOfUnknown` / `resolveSigma_provider_nonneg` /
  `sourceOfAIC_zero_is_unknown_route`），在 `Fate/SigmaLandscape.lean` 中有
  `e_optimal_sigma`（`Var[meanOf n] = varOf P / n`），在
  `Fate/WorldModelCapstone.lean` 中有 `exists_sigma_errorAcceptable`。
  **⟹ ⑨ 不是「0%」。**

  **但**：「σ 的**具体数值**等于多少」**不可能**在本框架内证明。
  本文件的唯一目的是把这句话**机械化**，而不是用散文宣称它。

  ----

  **本文件到底证了什么（一句话）**：
  在**固定**的框架内部数据（误差剖面 `W` 与默认分辨率 `g0`）下，
  统一入口 `resolveSigma · W g0` 能取到的 σ 值集合**恰好是全部正实数
  外加一个可能不可达的 `0`**（`obtainable_sigma_set`）。
  ⟹ 框架内部**完全没有**把 σ 收窄到一个点。
  ⟹ **σ 的具体数值必须由外部数据（领域知识 / 独立估计）补齐。**

  ----

  **本文件没有证什么**（逐条登记，防止过度声称）：

  * **没有**证「σ 等于某个真实噪声尺度」。那是**建模断言**，
    不是本框架的定理（`SigmaUnified` 文件头 §二、`SigmaFromAIC` §二.4 已登记）。
  * **没有**证「给定某数据集 D，σ = f(D) 的某个具体值」。
    理由见下面 §三 的**可证性论证**。
  * **没有**给出任何 σ 的**数值**。本文件不产生任何具体数字
    （除 `profBiasOnly` 的 `E(0) = 0` 这一**反例见证**）。
  * **没有**修改任何已有模块（纪律：只新建）。

  ----

  **§三（前置写出）为什么「σ = 具体值」在本框架内不可证**

  1. `SigmaSource` 的 `domain` / `estimated` 两支携带的 σ 是**构造参数**
     （`Fate/SigmaFromDomain.lean:159-165`），`resolveSigma` 在 `rfl` 级
     **原样返回**它（`:221-226`）。
  2. 故 σ 的取值在类型层面就是一个**自由的** `ℝ`（仅受 `0 < σ` 约束）。
     见本文件 `obtainable_sigma_set` 与 `every_positive_sigma_attainable`。
  3. 一个「σ = 具体值」的命题若要在本框架内可证，必须由某个**已固定的**
     定义算出该值；但 `resolveSigma` 的三支里没有一支**计算**σ
     （`domain`/`estimated` 是传参，`unknown` 返回 `W.err g0`，
     而 `W` 与 `g0` 本身又是自由参数 —— `resolveSigma_unknown_not_unique`
     已证其**不唯一**）。
  4. ⟹ 任何「σ = 3.7」式的陈述在本框架内**既不可证也不可否证**
     （可满足性由 `every_positive_sigma_attainable` 给出：
     对任意 `c > 0` 都存在一个 `SigmaSource` 把它变成 σ）。
     **这正是「需要外部数据」的精确含义。**

  ----

  **§四 纪律**
  零 `sorry` / 零 `admit` / 零 `axiom`；只新建本文件；
  所有被调用的标识符均经源码核对；交付前 `lake env lean` 两遍。
  -/

import FateWorld.Legacy.SigmaUnified
import Mathlib.Tactic

namespace Fate

namespace SigmaDataDependence

open Fate.SigmaFromDomain (SigmaSource resolveSigma)

/-! ===========================================================================
  §1  框架内部数据**决定不了** σ
  =========================================================================== -/

/-- ⭐ **`domain` 路线的 σ 与框架内部数据（`W`、`g0`）**完全无关**。

结论：同一个 `SigmaSource.domain σ hpos`，在**任意两个**不同的
内部设定 `(W₁, g₁)` 与 `(W₂, g₂)` 下，`resolveSigma` 都返回**同一个** σ。

**为何这是「σ 依赖外部数据」的形式载体**：它把「内部数据对 σ 无影响」
写成一条 `∀ W₁ W₂ g₁ g₂` 的等式。

**⚠ 强度如实登记（纪律 7 自查）**：前件**没有**任何关于 `resolveSigma`
输出值的假设；结论是被 `resolveSigma_domain`（`rfl` 级）**算出**的。
内容**确实很薄**（`rfl`），但它**不是**同义反复：
前件只断言「这是 `domain` 分支」，结论是**跨两个任意内部设定**的等式，
需要用 `resolveSigma` 的**定义展开**才知道两支相等。 -/
theorem sigma_domain_independent_of_internal_data
    (σ : ℝ) (hpos : 0 < σ)
    (W₁ W₂ : R238E3.ErrProfileWeak) (g₁ g₂ : ℝ) :
    resolveSigma (SigmaSource.domain σ hpos) W₁ g₁
      = resolveSigma (SigmaSource.domain σ hpos) W₂ g₂ := by
  rw [Fate.SigmaFromDomain.resolveSigma_domain,
    Fate.SigmaFromDomain.resolveSigma_domain]

/-- ⭐⭐ **【主定理】σ 的数值不由框架内部决定**。

存在**同一份**框架内部数据 `(W, g0)`（同一个误差剖面、同一个默认分辨率），
使两个不同的 σ 提供者给出**不同**的 σ。

**⟹ 给定框架内部的一切，σ 仍不是唯一的 ⟹ 必须补外部数据。**

**⚠ 与已有定理的区别（防重复）**：
`SigmaFromDomain.resolveSigma_unknown_not_unique` 变化的是 **`g0`**
（同一分支、两个默认分辨率）；本定理变化的是 **`SigmaSource` 分支**
（`domain` vs `unknown`），**固定** `(W, g0)`。
`SigmaUnified.resolveSigma_provider_nonneg` 只断言**非负**，不断言不唯一。

**⚠ 前件自查（纪律 7）**：本定理**无前件**（是全称存在命题），
故不可能把结论包进前件。反例是**显式构造**的：
`W := profBiasOnly`、`g0 := 0`、`src₁ := domain 1`、`src₂ := unknown`；
数值来自 `profBiasOnly` 的定义（`bias γ = max 0 γ`, `var = 0`
⟹ `E(0) = 0`，见 `Fate/FitBoundary.lean:219-229`），**非重言**。 -/
theorem sigma_value_not_determined_by_framework :
    ∃ (W : R238E3.ErrProfileWeak) (g0 : ℝ) (src₁ src₂ : SigmaSource),
      resolveSigma src₁ W g0 ≠ resolveSigma src₂ W g0 := by
  refine ⟨R238E3.ErrProfile.profBiasOnly.toErrProfileWeak, 0,
    SigmaSource.domain 1 (by norm_num), SigmaSource.unknown, ?_⟩
  show (1 : ℝ) ≠ R238E3.ErrProfile.profBiasOnly.toErrProfileWeak.err 0
  simp only [R238E3.ErrProfileWeak.err, R238E3.ErrProfile.profBiasOnly]
  norm_num

/-! ===========================================================================
  §2  ⭐⭐ σ 的**可达值集合**的精确刻画（本文件的实质内容）
  =========================================================================== -/

/-- ⭐⭐⭐ **【核心定理】固定内部数据时，σ 的可达值集合的精确刻画。**

$$\bigl(\exists\,\mathrm{src},\ \mathrm{resolveSigma}\ \mathrm{src}\ W\ g_0 = x\bigr)
  \iff \bigl(0 < x \ \lor\ (x = 0 \wedge E_W(g_0) = 0)\bigr).$$

**读法**：在**固定**的 `W`、`g0` 下，`resolveSigma` 能取到的值是
**整个正半轴**（`domain`/`estimated` 两支遍历 `0 < σ` 的全部），
**至多**再加一个 `0`（且仅当兜底值 `E_W g0` 恰为 `0` 时可取）。
⟹ **框架内部没有把 σ 收窄到任何真子集**。

**为何这不是同义反复（纪律 7）**：
- 前件（左端）是**存在量词**：∃ src 使输出相等；
- 结论（右端）是**关于 `W` 和 `g0` 的符号条件**（含 `E_W(g0) = 0`）；
- 二者之间**没有**蕴含关系可用 `rfl` 得到：正向需**按三个构造子分类讨论**
  并用 `ErrProfileWeak.err_nonneg`（`0 ≤ E_W γ`）**排序** `E_W(g0)` 与 `0`
  （`lt_or_eq_of_le`）；反向需在两个世界里**构造** `SigmaSource`
  （`domain x hx` 或 `unknown`）。
- 这一步用到的 `err_nonneg` 是 `ErrProfileWeak` 的**公理**（`FitBoundary:161`），
  是本定理**真正的数学输入**：没有它，`0 < x ∨ (x=0 ∧ E=0)` 这一支写不出来
  （`E_W g0` 可能为负则三支全不覆盖）。

**作用**：把 §三 的「σ 是自由参数」从散文变成**定理**。 -/
theorem obtainable_sigma_set (W : R238E3.ErrProfileWeak) (g0 x : ℝ) :
    (∃ src : SigmaSource, resolveSigma src W g0 = x)
      ↔ (0 < x ∨ (x = 0 ∧ W.err g0 = 0)) := by
  constructor
  · rintro ⟨src, rfl⟩
    cases src with
    | domain σ h => exact Or.inl h
    | estimated σ h => exact Or.inl h
    | unknown =>
        show 0 < W.err g0 ∨ (W.err g0 = 0 ∧ W.err g0 = 0)
        rcases lt_or_eq_of_le (R238E3.ErrProfileWeak.err_nonneg W g0) with hlt | heq
        · exact Or.inl hlt
        · exact Or.inr ⟨heq.symm, heq.symm⟩
  · rintro (hpos | ⟨hx, h0⟩)
    · exact ⟨SigmaSource.domain x hpos, rfl⟩
    · refine ⟨SigmaSource.unknown, ?_⟩
      rw [hx]
      exact h0

/-- ⭐⭐ **推论：零 σ 可达 ⟺ 兜底值为零**（即 `W.err g0 = 0`）。

由 `obtainable_sigma_set` 直接代数化（`¬ 0 < 0` 是 `norm_num` 级）。 -/
theorem sigma_zero_attainable_iff (W : R238E3.ErrProfileWeak) (g0 : ℝ) :
    (∃ src : SigmaSource, resolveSigma src W g0 = 0) ↔ W.err g0 = 0 := by
  rw [obtainable_sigma_set]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact absurd h (lt_irrefl 0)
    · exact h
  · intro h
    exact Or.inr ⟨rfl, h⟩

/-- ⭐⭐ **推论：每一个正 σ 都能被某个提供者给出，且该提供者对内部数据不敏感。**

$$\forall \sigma > 0,\ \exists\,\mathrm{src},\ \forall W\ g_0,\
  \mathrm{resolveSigma}\ \mathrm{src}\ W\ g_0 = \sigma.$$

**⟹ 「σ 的取值被框架钉死」这一类断言是假的**：
任何正值都可由一个对**全部**内部数据都返回同一值的提供者实现。
这是「σ 的具体数值必须由外部" data 补齐」的正向形式。 -/
theorem every_positive_sigma_attainable (σ : ℝ) (hpos : 0 < σ) :
    ∃ src : SigmaSource,
      ∀ (W : R238E3.ErrProfileWeak) (g0 : ℝ), resolveSigma src W g0 = σ :=
  ⟨SigmaSource.domain σ hpos, fun _ _ => rfl⟩

/-- ⭐ **推论（不可区分性）**：任意两个正 σ 之间存在**同一份**内部数据，
使它们**同时**可达。

$$\forall \sigma_1 > 0,\ \forall \sigma_2 > 0,\ \exists W\ g_0,
  \bigl(\exists \mathrm{src}_1, \mathrm{resolveSigma}\ \mathrm{src}_1\ W\ g_0 = \sigma_1\bigr)
  \wedge \bigl(\exists \mathrm{src}_2, \mathrm{resolveSigma}\ \mathrm{src}_2\ W\ g_0 = \sigma_2\bigr).$$

**⟹ 框架内部数据**无法区分**两个候选 σ**：同一份 `(W, g0)` 与两者都相容。
这就是「σ 需要外部数据」的最强形式（不是「有反例」，而是「处处都不可区分」）。 -/
theorem two_sigmas_indistinguishable_internally (σ₁ σ₂ : ℝ)
    (h₁ : 0 < σ₁) (h₂ : 0 < σ₂) :
    ∃ (W : R238E3.ErrProfileWeak) (g0 : ℝ),
      (∃ src₁ : SigmaSource, resolveSigma src₁ W g0 = σ₁) ∧
      (∃ src₂ : SigmaSource, resolveSigma src₂ W g0 = σ₂) := by
  refine ⟨R238E3.ErrProfile.profBiasOnly.toErrProfileWeak, 0, ?_, ?_⟩
  · exact ⟨SigmaSource.domain σ₁ h₁, rfl⟩
  · exact ⟨SigmaSource.domain σ₂ h₂, rfl⟩

/-! ===========================================================================
  §3  与「σ 的数值」相关的、本框架内**不可**证的东西（形式化不了的部分）
  =========================================================================== -/

/-!
以下三条**不是**定理，而是**登记**（纪律：不写 `sorry`、不写空壳定理）。

**(N1) 「σ 等于真实噪声尺度」** —— 不可证。
`sigmaAIC W γ = W.err γ`（`SigmaFromAIC:457`）是**定义**；
把它认同为「真实噪声」是**建模断言**，其真值取决于物理/统计世界，不是 Lean 命题。

**(N2) 「给定数据集 D，σ = f(D)」的具体数值** —— 不可证。
数据集 `D` 不在本框架的类型里。若要把 `D` 接入，必须**先**定义
`f : Data → ℝ`（例如某个具体的 MLE / 交叉验证 / AIC 选择器），
而那个定义本身是**外部输入的建模选择**。
**逻辑地位**：一旦 `f` 被定义为某个**具体**的 `Data → ℝ`，
`σ = f D` 就变成可证的（`rfl`）—— 但那时「数值」来自 `f` 的定义，
**不是**来自本框架的数学。本文件用 `obtainable_sigma_set` 说明：
本框架对 σ 的**唯一**约束是 `0 ≤ σ`（且在 `errorAcceptable` 处还有判据约束）。

**(N3) 「σ 的具体值」在本框架内**不可否证** —— 这是**（N2）的补集**。
由 `every_positive_sigma_attainable`：对**任意** `c > 0`，都存在一个
`SigmaSource` 把 σ 变成 `c`，且该 `SigmaSource` 对**所有** `(W, g0)` 都这样。
⟹ 本框架对 σ 的取值**不施加任何上界/下界（除 `0 < σ`）**
⟹ 任何「σ = c」的断言与本框架的全部定理**相容**
⟹ 故它**不可能**由本框架**否证**，也就**不可能**由本框架**证成**。
**这是「σ 必须外部给定」的精确、机械化含义。**
-/

end SigmaDataDependence

end Fate
