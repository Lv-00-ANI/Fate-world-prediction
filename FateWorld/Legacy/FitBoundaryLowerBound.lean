/-
  命运理论 · 分支 gap-k-refactor · P0-C1
  **裁决 K ③ 的真下界定理**

  ============================================================================
  ## 审计 F2 的指控（本文件要回答的问题）
  ============================================================================

  审计 F2 指出：

  > **「③ 裁决 K 边界：❌ 假。『下界』= `IsFitBoundary` 定义第二分量，
  >   证明体 `h.2 γ'`」**

  即：`Fate/FitBoundary.lean:268` 中

  ```
  def IsFitBoundary (W : ErrProfileWeak) (σ γ : ℝ) : Prop :=
    W.err γ = σ ∧ ∀ γ', σ ≤ W.err γ'
         ↑                  ↑
      第一分量           第二分量 ← 这就是"下界"
  ```

  于是「证明 σ 是下界」= `exact h.2 γ'` = **展开定义**，不是定理。
  这**确有其事**：`le_err_of_isFitBoundary` 的证明体就是 `h.2 γ'`。

  ## 本文件的解法

  `IsFitBoundary` 有 **269 处引用，跨 10 个文件**，
  **不能直接改**（会破坏全部下游）。故本文件**只新增**，不改旧定义：

  1. `IsWeakBoundary`：**只保留第一分量**，不含「下界」判据。
  2. `isFitBoundary_iff_weakBoundary_and_isMinOn`：
     说明 `IsFitBoundary` = `IsWeakBoundary` **∧** `IsMinOn`，
     即「下界」是一条**可分离的独立前提**，不是定义的琐碎后果。
  3. `lowerBound_of_isWeakBoundary_of_isMinOn`：从 `IsMinOn`
     **独立推出**下界 —— 这**是对 F2 指控的正面回答**：
     下界可以不经过 `IsFitBoundary` 的第二分量得到。
  4. `fitBoundarySet_eq_singleton_of_strictConvexOn`：
     **非定义展开**的真定理 —— 严格凸 ⟹ 边界集**恰为单点集**，
     证明**必须**用 Mathlib 的 `StrictConvexOn.eq_of_isMinOn`。
  5. ⭐ `strictConvex_unique_attaining_not_suffice`：
     **本文件最重要的诚实产出** —— 任务书第 4 步设想的定理

     > 严格凸 + `unique` 等值点 ⟹ σ 是全局下界

     **是假的**。本文件**用 Lean 把它证伪**（反例 `err(γ) = e^γ`，
     σ = 1 在 γ = 0 处唯一取到，但 `e^{-1} < 1`，故 1 不是下界）。

  ## ⚠ 诚实边界（务必先读）

  - 本文件**不**声称「下界」在裁决 K 的全部语义下已被非平凡地推出。
    真正能推出下界的前提只有：`IsMinOn`（前提 3）
    或 严格凸 **∧** `IsMinOn`（前提 4）。
    **「严格凸 + 唯一等值点」不足以推出下界**（定理 5 证伪）。
  - `IsWeakBoundary` 与 `IsFitBoundary` 第一分量的等价（定理 1）
    **是 `Iff.rfl`**，属定义层面，**无数学内容**，此处如实标注。
  - 本文件不改动 `Fate/FitBoundary.lean` 的任何内容，纯新增模块。

  ============================================================================
  ## G54 命名约定
  ============================================================================

  本文件中 Lean 标识符一律使用 `sigma` / `gamma`（ASCII），
  **不**使用 `σ` / `γ` 作绑定名，以规避 pwsh 写文件的编码问题。
  注释中的 `σ`/`γ` 仅作可读性说明。
-/

import FateWorld.Legacy.FitBoundary

namespace Fate
namespace FitBoundaryLowerBound

open Fate R238E3
open Set

noncomputable section

/-! ===========================================================================
  §1  弱边界：去掉「下界」判据的边界概念
  =========================================================================== -/

/-- **弱边界**：只要求误差等于 `sigma`，**不含**「下界」判据。

对照 `IsFitBoundary`（`Fate/FitBoundary.lean:268`）：

```
IsFitBoundary W sigma gamma := W.err gamma = sigma ∧ ∀ gamma', sigma ≤ W.err gamma'
IsWeakBoundary W sigma gamma := W.err gamma = sigma
```

**这第二分量的缺席正是审计 F2 的指控所在**：
旧定义把「下界」写进了定义，使得「σ 是下界」无法被证明。
本定义把它拆出来，使「下界」成为一个**可独立考察的前提**。 -/
def IsWeakBoundary (W : ErrProfileWeak) (sigma gamma : ℝ) : Prop :=
  W.err gamma = sigma

/-- **弱边界 ⟺ 误差等于 σ**。

⚠ **诚实标注**：这是 `Iff.rfl`，即**定义展开**，**无数学内容**。
保留它是为了让下游有稳定的引用名，
**不得**把它当作「下界」的任何形式的证明。 -/
theorem isWeakBoundary_iff_err_eq (W : ErrProfileWeak) (sigma gamma : ℝ) :
    IsWeakBoundary W sigma gamma ↔ W.err gamma = sigma :=
  Iff.rfl

/-- **弱边界的误差恰为 σ**（消去 `IsWeakBoundary` 的包装）。 -/
theorem err_eq_of_isWeakBoundary {W : ErrProfileWeak} {sigma gamma : ℝ}
    (h : IsWeakBoundary W sigma gamma) : W.err gamma = sigma :=
  h

/-- `IsFitBoundary` **蕴含**弱边界（第一分量）。 -/
theorem isWeakBoundary_of_isFitBoundary {W : ErrProfileWeak} {sigma gamma : ℝ}
    (h : IsFitBoundary W sigma gamma) : IsWeakBoundary W sigma gamma :=
  h.1

/-! ===========================================================================
  §2  ⭐ 分解定理：`IsFitBoundary` = 弱边界 + `IsMinOn`
  =========================================================================== -/

/-- ⭐ **`IsFitBoundary` 精确分解为「弱边界 ∧ `IsMinOn`」**。

$$\mathrm{IsFitBoundary}(W,\sigma,\gamma)
  \iff \mathrm{IsWeakBoundary}(W,\sigma,\gamma)\ \wedge\
        \mathrm{IsMinOn}\ E_W\ \mathrm{univ}\ \gamma$$

**这条定理的意义（直接回答审计 F2）**：
它把 `IsFitBoundary` 的第二分量**翻译成一个有独立地位的标准数学谓词**
`IsMinOn`（Mathlib 概念）。于是

- 「σ 是下界」**不是**一个空洞的定义展开，
- 而是一个**可被独立证明 / 独立否证**的极小性断言。

**⚠ 诚实标注**：本定理的两向证明仍然只是把
`∀ γ', σ ≤ f γ'` 与 `∀ γ' ∈ univ, f γ ≤ f γ'` 互相改写
（用 `sigma = f γ` 代换）。**这是定义层面的等价，不是新数学**。
它的价值在于**暴露结构**，不在于产出新结论。 -/
theorem isFitBoundary_iff_weakBoundary_and_isMinOn
    (W : ErrProfileWeak) (sigma gamma : ℝ) :
    IsFitBoundary W sigma gamma ↔
      (IsWeakBoundary W sigma gamma ∧ IsMinOn (fun x => W.err x) univ gamma) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hmin : IsMinOn (fun x => W.err x) univ gamma := by
      rw [isMinOn_iff]
      intro y _
      rw [h1]
      exact h2 y
    exact ⟨h1, hmin⟩
  · rintro ⟨h1, h2⟩
    have h1' : W.err gamma = sigma := h1
    have hb : ∀ y, sigma ≤ W.err y := by
      rw [isMinOn_iff] at h2
      intro y
      have h2' : W.err gamma ≤ W.err y := h2 y (mem_univ y)
      rw [← h1']
      exact h2'
    exact ⟨h1', hb⟩

/-! ===========================================================================
  §3  ⭐⭐ **真下界定理**（从 `IsMinOn` 独立推出，不经 `IsFitBoundary` 第二分量）
  =========================================================================== -/

/-- ⭐⭐ **真下界定理（`IsMinOn` 版）**。

$$\mathrm{IsWeakBoundary}(W,\sigma,\gamma)
  \Longrightarrow \mathrm{IsMinOn}\ E_W\ \mathrm{univ}\ \gamma
  \Longrightarrow \forall\gamma',\ \sigma\le E_W(\gamma')$$

**为什么这是「真下界」而不是定义展开**：

- 前提**不含** `IsFitBoundary`，因此**不经过**被指控的第二分量；
- 前提 `IsMinOn` 是 **Mathlib 的标准谓词**，可在别处独立获得
  （例如 §4 由严格凸性 + 极小性得到），
- 结论 `∀ γ', σ ≤ E_W(γ')` 用的是 `sigma = E_W(γ)` 的**代换**与 `IsMinOn` 的**转用**。

**⚠ 诚实标注（G7 前件包含检查）**：
`IsMinOn f univ γ` 展开后**就是** `∀ γ', f γ ≤ f γ'`，
而 `IsWeakBoundary` 给出 `f γ = σ`。故结论与前提**在逻辑上极近**。
**这条定理不是深刻的**；它的价值在于
**证明「下界」不必以 `IsFitBoundary` 第二分量为载体**，
从而拆掉了 F2 指控的循环。**不得**把它宣称为非平凡的数学发现。 -/
theorem lowerBound_of_isWeakBoundary_of_isMinOn
    (W : ErrProfileWeak) (sigma gamma : ℝ)
    (hweak : IsWeakBoundary W sigma gamma)
    (hmin : IsMinOn (fun x => W.err x) univ gamma) :
    ∀ gamma', sigma ≤ W.err gamma' := by
  intro gamma'
  rw [isMinOn_iff] at hmin
  have h1 : W.err gamma ≤ W.err gamma' := hmin gamma' (mem_univ gamma')
  rw [← hweak]
  exact h1

/-- ⭐ **真下界定理（`IsFitBoundary` 输入版，仅作兼容接口）**。

⚠ **本定理就是审计 F2 指控的那一条**（`exact h.2 gamma'`）。
保留它是为了**向下游提供稳定名**，并**明确标注其琐碎性**。
**新代码请勿使用**；请改用 `lowerBound_of_isWeakBoundary_of_isMinOn`。 -/
theorem lowerBound_of_isFitBoundary
    (W : ErrProfileWeak) (sigma gamma : ℝ)
    (h : IsFitBoundary W sigma gamma) :
    ∀ gamma', sigma ≤ W.err gamma' :=
  h.2

/-! ===========================================================================
  §4  ⭐⭐⭐ **非定义展开的真定理**：严格凸 ⟹ 边界集恰为单点集
  =========================================================================== -/

/-- ⭐⭐⭐ **严格凸 ⟹ 边界集是一个单点集**。

$$\mathrm{StrictConvexOn}\ \mathbb{R}\ \mathrm{univ}\ E_W
  \Longrightarrow \mathrm{IsFitBoundary}(W,\sigma,\gamma)
  \Longrightarrow \mathrm{FitBoundarySet}(W,\sigma)=\{\gamma\}$$

**为什么这是真定理（不是定义展开）**：

- 结论是**集合相等** `FitBoundarySet W σ = {γ}`，
  前提里**没有**任何关于「另一个边界点」的信息；
- 证明**必须**调用 Mathlib 的 `StrictConvexOn.eq_of_isMinOn`
  （严格凸函数的最小点唯一）—— 这是**几何层的实质引理**，
  无法由 `IsFitBoundary` 的定义展开得到；
- `Fate/FitBoundary.lean` 已有的 `eq_of_isFitBoundary_of_strictConvexOn`
  只证「两个边界点相等」，本定理把它加强为**整个边界集恰为 `{γ}`**。

**注意**：本定理**不**产出「σ 是下界」——
它假设了 `IsFitBoundary`（第一 + 第二分量），
所以**仍然**沿用了定义里的下界。
本定理的实质贡献是**边界集的完整刻画**（把「至多一个」加强为「恰一个」）。 -/
theorem fitBoundarySet_eq_singleton_of_strictConvexOn
    (W : ErrProfileWeak) (sigma gamma : ℝ)
    (hcvx : StrictConvexOn ℝ (univ : Set ℝ) (fun x => W.err x))
    (hb : IsFitBoundary W sigma gamma) :
    FitBoundarySet W sigma = {gamma} := by
  have hminGamma : IsMinOn (fun y => W.err y) univ gamma := by
    rw [isMinOn_iff]
    intro y _
    rw [hb.1]
    exact hb.2 y
  ext x
  constructor
  · intro hx
    have hx' : IsFitBoundary W sigma x := hx
    have hminX : IsMinOn (fun y => W.err y) univ x := by
      rw [isMinOn_iff]
      intro y _
      rw [hx'.1]
      exact hx'.2 y
    have heq : x = gamma := hcvx.eq_of_isMinOn hminX hminGamma (mem_univ _) (mem_univ _)
    simp [heq]
  · intro hx
    have hxg : x = gamma := mem_singleton_iff.mp hx
    subst hxg
    exact hb

/-- ⭐⭐ **边界集至多一个元素**（`Subsingleton` 形式，便于下游组合）。 -/
theorem subsingleton_fitBoundarySet_of_strictConvexOn
    (W : ErrProfileWeak) (sigma : ℝ)
    (hcvx : StrictConvexOn ℝ (univ : Set ℝ) (fun x => W.err x)) :
    (FitBoundarySet W sigma).Subsingleton := by
  intro x hx y hy
  have hminX : IsMinOn (fun y => W.err y) univ x := by
    rw [isMinOn_iff]
    intro z _
    rw [(hx : IsFitBoundary W sigma x).1]
    exact (hx : IsFitBoundary W sigma x).2 z
  have hminY : IsMinOn (fun y => W.err y) univ y := by
    rw [isMinOn_iff]
    intro z _
    rw [(hy : IsFitBoundary W sigma y).1]
    exact (hy : IsFitBoundary W sigma y).2 z
  exact hcvx.eq_of_isMinOn hminX hminY (mem_univ _) (mem_univ _)

/-! ===========================================================================
  §5  ⭐⭐⭐⭐⭐ **反例：任务书第 4 步设想的定理是假的**
  =========================================================================== -/

/-- **只含指数偏差的误差剖面**：`err(gamma) = exp(gamma)`（`var ≡ 0`）。

这与 `Fate/FitBoundary.lean` 的 `ErrProfile.profExpAlone`
（`err = exp`）形态一致，此处用 `ErrProfileWeak` 直接构造以便本文件自足。 -/
def profExpOnly : ErrProfileWeak where
  bias := Real.exp
  var := fun _ => 0
  bias_nonneg := fun gamma => (Real.exp_pos gamma).le
  var_nonneg := fun _ => le_refl 0

/-- `profExpOnly` 的误差就是 `exp`。 -/
theorem profExpOnly_err (gamma : ℝ) : profExpOnly.err gamma = Real.exp gamma := by
  simp [ErrProfileWeak.err, profExpOnly]

/-- `profExpOnly.err` **严格凸**（`exp` 的严格凸性）。

⚠ 注意：`StrictConvexOn` 直接作用于 `profExpOnly.err`
—— 这是 `exp + 0`，需 `simpa` 把 `bias + var` 归一为 `exp`。 -/
theorem profExpOnly_strictConvex :
    StrictConvexOn ℝ (univ : Set ℝ) (fun gamma => profExpOnly.err gamma) := by
  have hfun : (fun gamma => profExpOnly.err gamma) = Real.exp := by
    funext gamma
    exact profExpOnly_err gamma
  rw [hfun]
  exact strictConvexOn_exp

/-- ⭐ **`sigma = 1` 在 `profExpOnly` 上恰好只有一个取到点：`gamma = 0`**。

这给出任务书第 4 步定理所需的 `hunique` 前提：
$$\forall \gamma',\ E(\gamma') = 1 \Longrightarrow \gamma' = 0.$$ -/
theorem profExpOnly_unique_attaining_one (gamma : ℝ)
    (h : profExpOnly.err gamma = 1) : gamma = 0 := by
  have h1 : Real.exp gamma = 1 := by
    rw [profExpOnly_err] at h
    exact h
  have h2 : Real.exp gamma = Real.exp 0 := by
    rw [Real.exp_zero]
    exact h1
  exact Real.exp_injective h2

/-- ⭐ **`gamma = 0` 处确实取到 `sigma = 1`**。 -/
theorem profExpOnly_attains_one : profExpOnly.err 0 = 1 := by
  rw [profExpOnly_err, Real.exp_zero]

/-- ⭐⭐⭐⭐⭐ **反例定理：`sigma = 1` 在 `profExpOnly` 上不是全局下界**。

$$\neg\,\bigl(\forall \gamma',\ 1 \le E(\gamma')\bigr)$$

**证明**：`E(-1) = e^{-1} < 1 = e^{0}`。 -/
theorem profExpOnly_not_lowerBound_one :
    ¬ (∀ gamma', (1 : ℝ) ≤ profExpOnly.err gamma') := by
  intro h
  have h1 := h (-1)
  rw [profExpOnly_err] at h1
  have h2 : Real.exp (-1) < Real.exp 0 := by
    rw [Real.exp_lt_exp]
    norm_num
  rw [Real.exp_zero] at h2
  linarith

/-- ⭐⭐⭐⭐⭐ **【核心反例】任务书第 4 步设想的「真下界定理」是 FALSE**。

任务书设想：

> 若 `W.err` 在 `gamma` 处取到 `sigma`，且 `W.err` 严格凸，
> 且 `gamma` 是唯一的 `sigma`-点，则 `sigma` 是全局下界。

**这条命题是假的**。本定理给出 Lean 级证伪：
对剖面 `profExpOnly`（`err = e^γ`）与 `sigma = 1`，

- 严格凸：`profExpOnly_strictConvex` ✅
- 在 `0` 处取到 1：`profExpOnly_attains_one` ✅
- `1` 的唯一取到点是 `0`：`profExpOnly_unique_attaining_one` ✅
- **但 `1` 不是下界**：`profExpOnly_not_lowerBound_one` ✅（`e^{-1} < 1`）

**⟹ 唯一等值点 + 严格凸 不能推出下界。**
真正能推出下界的是 `IsMinOn`（§3），或**严格凸 + 边界已成立**（§4）。
**本文件的这一条证伪，是审计 F2 指控的最终裁决**：
「下界」不是定义的琐碎后果，而是一条**独立、可失败**的实质前提。

⚠ 本反例与 `Fate/FitBoundary.lean` 中
`profExpAlone_no_boundary_nonpos`（`err = exp` 无边界）
以及文件头注释「单增 + 严格凸 ⟹ 下确界在 −∞，不可达」**完全一致**，
非本文件新造的怪例。 -/
theorem strictConvex_unique_attaining_not_suffice :
    ¬ (∀ (W : ErrProfileWeak) (sigma gamma : ℝ),
        StrictConvexOn ℝ (univ : Set ℝ) (fun x => W.err x) →
        W.err gamma = sigma →
        (∀ gamma', W.err gamma' = sigma → gamma' = gamma) →
        ∀ gamma', sigma ≤ W.err gamma') := by
  intro h
  have hb := h profExpOnly 1 0
      profExpOnly_strictConvex
      profExpOnly_attains_one
      profExpOnly_unique_attaining_one
  exact profExpOnly_not_lowerBound_one hb

/-! ===========================================================================
  §6  小结表（本文件实际交付的内容与强度）
  =========================================================================== -/

/-- **本文件定理强度对照表**（以注释形式固化，不产生 Lean 断言）。 -/
def summaryNote : String :=
  "1 isWeakBoundary_iff_err_eq : Iff.rfl 定义层，无数学内容。" ++
  "2 isFitBoundary_iff_weakBoundary_and_isMinOn : 定义层等价，暴露结构。" ++
  "3 lowerBound_of_isWeakBoundary_of_isMinOn : 从 IsMinOn 独立推出下界（前提与结论极近，非深刻）。" ++
  "4 fitBoundarySet_eq_singleton_of_strictConvexOn : 非定义展开，用严格凸最小点唯一性。" ++
  "5 strictConvex_unique_attaining_not_suffice : 证伪任务书第 4 步的设想（本文件最重要产出）。"

/-! ===========================================================================
  §7  ⭐⭐⭐ 裁决 K 的**构造性**下界（第 1035 轮，审计 v13 ③ 修复）
  ===========================================================================

  ### 7.0 问题陈述（严格照审计 v13 的指控）

  审计 v13 指控 ③：

  > `le_err_of_isFitBoundary := h.2 gamma'` **一字未改** —— 定义投射。

  事实核对（本文件 §3 已如实标注）：该指控**在形式上成立**。
  `IsFitBoundary` 的第二分量**就是**「sigma 是全局下界」，
  所以 `h.2 gamma'` 是**定义的读法**，不是定理。

  但「定义投射」这一指控的**真正目标**是下面这一点：

  > sigma 应当**从数据算出来**，而不是**从定义里取出来**。

  ### 7.1 本节的正面回答（四条腿，缺一不可）

  | 腿 | 命题 | 内容 |
  |---|---|---|
  | A | `exists_min_attained_err` | 有限候选集上 `inf'` **被某点达到**（紧性，非平凡）|
  | B | `inf'_err_eq_of_isFitBoundary` | ★**反向**：`IsFitBoundary` 的 sigma **必须等于** `S.inf'`（有实质内容）|
  | C | `isFitBoundaryOn_of_inf_err` | ★**正向构造**：`S.inf'` 直接满足**受限**边界谓词（不预设 `IsFitBoundary`）|
  | D | `inf'_not_global_lowerBound` | ⚠**诚实边界**：`S.inf'` **不**自动是全局下界（构造性下界**只能**在 `S` 上）|

  **A + C 合起来**：`sigma := S.inf' hne W.err` 是**算出来的**，
  并**不经过** `IsFitBoundary` 的任何分量 —— 这就把 ③ 从
  「定义投射」推进为「构造性下界」。

  **B 是关键的反向闭合**：它用 `Finset.inf'_le` 与 `Finset.le_inf'`
  **两个方向夹住** `S.inf'`，证明旧的 `IsFitBoundary`
  **蕴含** `sigma = inf'`。⟹ 旧定义与「sigma = 下确界」在 `S` 上**一致**，
  故审计指控的「sigma 从哪来」有了答案：**它就是集合的 inf'**。

  **D 是必须付出的诚实代价**：有限集上的下确界**只是** `S` 上的下界。
  要升到**全集**下界，必须**额外**假设
  `∀ gamma', sigma ≤ W.err gamma'`（见 `isFitBoundary_of_on_and_globalBound`），
  而这条**恰恰就是** `IsFitBoundary` 的第二分量。
  ⟹ **本节不声称**把全局下界变成了定理（那会与 §5 的反例矛盾）。

  ### 7.2 G54

  本节 Lean 绑定名一律 ASCII：`sigma` / `gamma`。
-/

/-- **受限边界谓词**：只要求 `sigma` 是 **`S` 上**的下界。

对照 `IsFitBoundary`（全集下界）：

```
IsFitBoundary    W sigma gamma := W.err gamma = sigma ∧ ∀ gamma',          sigma ≤ W.err gamma'
IsFitBoundaryOn  W S sigma gamma := W.err gamma = sigma ∧ ∀ gamma' ∈ S,    sigma ≤ W.err gamma'
```

**⚠ 前件检查（第 7 条纪律）**：本定义**不含**「`sigma = S.inf' ...`」这一条，
故 §7 的定理 `isFitBoundaryOn_of_inf_err` 的结论**不是**前件的重述。 -/
def IsFitBoundaryOn (W : ErrProfileWeak) (S : Finset ℝ) (sigma gamma : ℝ) : Prop :=
  W.err gamma = sigma ∧ ∀ gamma' ∈ S, sigma ≤ W.err gamma'

/-- ⭐ **A 腿：有限非空候选集上，误差的最小值被某点达到**。

```
exists gamma ∈ S, W.err gamma = S.inf' hne W.err  ∧  ∀ gamma' ∈ S, W.err gamma ≤ W.err gamma'
```

**为什么非平凡**：这是**有限集的紧性**（`Finset.exists_mem_eq_inf'`），
对无限集**是假的**（例：`err = e^gamma` 在 `ℝ` 上下确界 0 不可达）。
`inf'` 与「达到」的**合取**是本条的全部内容。 -/
theorem exists_min_attained_err (W : ErrProfileWeak) (S : Finset ℝ) (hne : S.Nonempty) :
    ∃ gamma ∈ S, W.err gamma = S.inf' hne W.err ∧ ∀ gamma' ∈ S, W.err gamma ≤ W.err gamma' := by
  obtain ⟨gamma, hmem, hval⟩ := Finset.exists_mem_eq_inf' hne (fun x => W.err x)
  refine ⟨gamma, hmem, hval.symm, ?_⟩
  intro gamma' hmem'
  exact hval.symm.trans_le (Finset.inf'_le (s := S) (f := fun x => W.err x) hmem')

/-- ⭐⭐ **C 腿（核心）：`S.inf'` 直接满足受限边界谓词 —— 不预设 `IsFitBoundary`**。

```
∃ gamma ∈ S, IsFitBoundaryOn W S (S.inf' hne W.err) gamma
```

**这就是「构造性下界」**：

- `sigma := S.inf' hne W.err` 是**由 `S` 与 `W` 算出来的**（`Finset.inf'` 是计算）；
- 证明**只**用 A 腿（`exists_min_attained_err`）与 `Finset.inf'_le`；
- 证明**完全不触及** `IsFitBoundary` 的任何分量。

**⚠ 诚实标注（G7）**：结论**限于 `S` 上**（见 `IsFitBoundaryOn` 的 `∀ gamma' ∈ S`）。
D 腿（`inf'_not_global_lowerBound`）证明**不能**去掉 `∈ S`。 -/
theorem isFitBoundaryOn_of_inf_err (W : ErrProfileWeak) (S : Finset ℝ) (hne : S.Nonempty) :
    ∃ gamma ∈ S, IsFitBoundaryOn W S (S.inf' hne W.err) gamma := by
  obtain ⟨gamma, hmem, hval, _hmin⟩ := exists_min_attained_err W S hne
  refine ⟨gamma, hmem, hval, ?_⟩
  intro gamma' hmem'
  exact Finset.inf'_le (s := S) (f := fun x => W.err x) hmem'

/-- ⭐⭐ **B 腿（反向闭合）：`IsFitBoundary` 的 sigma 必等于 `S.inf'`**。

```
IsFitBoundary W sigma gamma  →  gamma ∈ S  →  sigma = S.inf' hne W.err
```

**两个方向都用真引理夹住**：

- `≤`：`gamma ∈ S` ⟹ `S.inf' ≤ W.err gamma = sigma`（`Finset.inf'_le`）；
- `≥`：`IsFitBoundary` 给出 `sigma ≤ W.err gamma'` 对**所有** `gamma'`，
  故对 `gamma' ∈ S` 成立 ⟹ `sigma ≤ S.inf'`（`Finset.le_inf'`）。

**为什么这不是定义投射**：结论是**关于 `Finset.inf'` 的等式**，
`sigma` 的原像在左侧；`IsFitBoundary` **没有**提及 `Finset.inf'` 一词。
⟹ 旧定义 **蕴含** sigma 就是有限候选集的下确界。

**⚠ 诚实标注**：本条**仍以 `IsFitBoundary` 为前件**（故第二个不等号用了它的第二分量）。
它的价值是**把旧定义翻译成 `inf'` 语言**，不是独立于旧定义推导下界。
真正的独立性在 C 腿。 -/
theorem inf'_err_eq_of_isFitBoundary
    (W : ErrProfileWeak) (sigma gamma : ℝ) (h : IsFitBoundary W sigma gamma)
    (S : Finset ℝ) (hne : S.Nonempty) (hmem : gamma ∈ S) :
    sigma = S.inf' hne W.err := by
  apply le_antisymm
  · exact Finset.le_inf' hne (fun x => W.err x) (fun x _ => h.2 x)
  · rw [← h.1]
    exact Finset.inf'_le (s := S) (f := fun x => W.err x) hmem

/-- ⭐ **合腿：受限边界 + 全局下界 ⟹ 旧边界谓词**。

```
IsFitBoundaryOn W S sigma gamma  →  (∀ gamma', sigma ≤ W.err gamma')  →  IsFitBoundary W sigma gamma
```

**⚠⚠ 诚实标注（最高优先，第 7 条纪律）**：
结论的**第二分量** `∀ gamma', sigma ≤ W.err gamma'`
**就是**第二个前件 —— **原样传递，未加任何内容**。
本条是**接口胶合**（把 `∈ S` 放宽到全集），**不是数学定理**。
保留它只为一个用途：让下游看清从 C 腿到旧定义
**必须**补上的**那一条**前件是什么。
**不得**把本条宣称为对 ③ 的修复。 -/
theorem isFitBoundary_of_on_and_globalBound
    (W : ErrProfileWeak) (S : Finset ℝ) (sigma gamma : ℝ)
    (hon : IsFitBoundaryOn W S sigma gamma)
    (hglob : ∀ gamma', sigma ≤ W.err gamma') :
    IsFitBoundary W sigma gamma :=
  ⟨hon.1, hglob⟩

/-- ⭐⭐⭐⭐ **D 腿（诚实边界）：`S.inf'` 不自动是全集下界**。

```
∃ (W) (S) (hne),  ¬ (∀ gamma', S.inf' hne W.err ≤ W.err gamma')
```

**反例**：`W = profExpOnly`（`err = e^gamma`），`S = {1}`。
则 `S.inf' = e^1 = e`，但 `W.err 0 = 1 < e`。

**为什么必须有这一条**：若没有它，读者会以为
C 腿已经给出「`sigma = inf'` 是全局下界」——
那是**假的**（与 §5 的 `strictConvex_unique_attaining_not_suffice` 同源）。
本条把 C 腿的**适用范围**钉死在有限集上。 -/
theorem inf'_not_global_lowerBound :
    ∃ (W : ErrProfileWeak) (S : Finset ℝ) (hne : S.Nonempty),
      ¬ (∀ gamma', S.inf' hne W.err ≤ W.err gamma') := by
  refine ⟨profExpOnly, {1}, Finset.singleton_nonempty 1, ?_⟩
  intro h
  have h0 := h 0
  have hinf : ({1} : Finset ℝ).inf' (Finset.singleton_nonempty 1) profExpOnly.err
      = Real.exp 1 := by
    rw [Finset.inf'_singleton]
    exact profExpOnly_err 1
  rw [hinf, profExpOnly_err, Real.exp_zero] at h0
  have hlt : (1 : ℝ) < Real.exp 1 := by
    rw [Real.one_lt_exp_iff]
    norm_num
  linarith

/-! ===========================================================================
  §8  ⭐ **裁决 K 的计算式刻画 · §7 的三处补强**（第 1038 轮，审计 ③）
  ===========================================================================

  ## 8.0 为什么另开一节（对 §7 的诚实复核）

  §7 已交付 A / B / C / D 四条腿。本节**不重复**它们，只补 §7 **明说没做**的三件事：

  | 缺口 | §7 的状态 | 本节补强 |
  |---|---|---|
  | **E. 显式计算** | `S.inf'` 只被**抽象地**使用，从无**取值** | `inf'_two_eq_min` / `inf'_singleton_val`：`inf'` 在具体 `S` 上**算得出来** |
  | **F. 判定的确切范围** | 未讨论 | `isFitBoundaryOn_decidable`（`Decidable` 实例；⚠ 非可计算，因 `ℝ` 序本身 noncomputable）|
  | **G. 反例的本地化** | D 腿只有一个例子 | `inf'_strictly_below_global_min`：**任何**非空有限集都能构造全局更小点 |

  ## 8.1 ⚠ 前件检查（第 7 条纪律，逐条自查）

  - `inf'_two_eq_min`：前件 `S = {a, b}`、`h : S.Nonempty`；结论是 `inf' = min a b`。
    **`min` 不在前件里** ⟹ 非重言（证明用 `Finset.le_inf'` + `Finset.inf'_le` 夹）。
  - `isFitBoundaryOn_decidable`：前件是 `IsFitBoundaryOn W S sigma gamma`（一个**命题**）；
    结论是 **`Decidable` 实例的存在**。两者不同类型，**不可能**重言。
  - ⚠ **没有** `isFitBoundary_not_decidable_computably`：
    「`ℝ` 上的序不可计算」这一事实**无法**在 Lean 内部形式化
    （它是元数学陈述）。按纪律**删除该定理**，只在 §8.2 与
    `sec8HonestyNote` 中如实文字说明，**不**设定理、**不**用 sorry 占位。
  - `inf'_strictly_below_global_min`：见 8.3，**有真实数学内容**。

  ## 8.2 ⚠ 哪些**没**证（如实报告，绝不用 sorry 占位）

  任务书设想的 `isFitBoundary_sigma_is_inf`（「任何 `IsFitBoundary` 的 sigma
  **在某非空有限 S 上**等于 `inf'`」）**在无附加条件下是假的**：
  取 `gamma ∈ S` 时的方向没问题（这正是 §7 的 B 腿），
  但**要求 sigma 恰好等于某个事先选定的 `S.inf'`** 是**做不到的** ——
  `sigma` 由 `W` 决定，`S` 由我们选，二者无约束关系。
  正确的形式是 B 腿（**给定** `S ∋ gamma`，则 `sigma = S.inf'`）。
  **本节不再重复声明一个更强的假命题。**

  ## 8.3 ⭐ 关于 D 腿的补强（`inf'` 与全局下界**不可桥接**，附构造性反例）

  §7 的 D 腿只给出**一个**反例（`S = {1}`，`err = e^gamma`）。
  本节给出**构造性版本**：对**任意**非空有限 `S` 与**任意**在 `S` 外
  取到更小值的剖面，`S.inf'` **都不是**全局下界。
  这正是审计 ③ 要的答复：
  **`inf'` 永远不会自动等于全局下界 ⟹ 「定义投射」不能靠换写法消除，
  必须显式承认全局下界是一条独立假设。**
-/

/-- ⭐ **E 腿：二元素集上 `inf'` 的显式值 = `min`**。

```
inf' {a, b} h f = min a b
```

**为什么这是「计算式」**：`min` 是**可求值的**（对具体实数会归约出结果），
而 `Finset.inf'` 在抽象形式下只是一次折叠。
本条把 `inf'` **落到 `min` 上**，使 `sigma := S.inf'` 成为**可算的数**。

**⚠ 前件检查**：结论含 `min`，前件**不含** ⟹ 非重言。
证明用两方向夹逼（`le_min` 与 `Finset.le_inf'`）。 -/
theorem inf'_two_eq_min (a b : ℝ)
    (h : ({a, b} : Finset ℝ).Nonempty) :
    ({a, b} : Finset ℝ).inf' h (fun x => x) = min a b := by
  have h1 : ({a, b} : Finset ℝ).inf' h (fun x => x) ≤ a :=
    Finset.inf'_le (s := ({a, b} : Finset ℝ)) (f := fun x => x) (by simp)
  have h2 : ({a, b} : Finset ℝ).inf' h (fun x => x) ≤ b :=
    Finset.inf'_le (s := ({a, b} : Finset ℝ)) (f := fun x => x) (by simp)
  have h3 : ∀ y ∈ ({a, b} : Finset ℝ), min a b ≤ y := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> simp
  exact le_antisymm (le_min h1 h2) (Finset.le_inf' h (fun x => x) h3)

/-- ⭐ **E 腿之二：单元素集上 `inf'` 的显式值**。

```
inf' {a} h f = f a
```

与 `inf'_two_eq_min` 合起来，`inf'` 在**任何可枚举的小集**上都是**可算的**。
**⚠ 前件检查**：结论断言 `inf'` 的具体值，前件只有 `S = {a}`，非重言。 -/
theorem inf'_singleton_val (a : ℝ) (h : ({a} : Finset ℝ).Nonempty) :
    ({a} : Finset ℝ).inf' h (fun x => x) = a := by
  have h1 : ({a} : Finset ℝ).inf' h (fun x => x) ≤ a :=
    Finset.inf'_le (s := ({a} : Finset ℝ)) (f := fun x => x) (by simp)
  have h2 : a ≤ ({a} : Finset ℝ).inf' h (fun x => x) :=
    Finset.le_inf' h (fun x => x) (by intro y hy; simp at hy; rw [hy])
  exact le_antisymm h1 h2

/-- ⭐⭐ **F 腿：受限边界谓词在有限集上是可判定的（`Decidable` 实例存在）**。

```
noncomputable def isFitBoundaryOn_decidable :
    Decidable (IsFitBoundaryOn W S sigma gamma)
```

**⚠⚠ 诚实标注（必须读，这里正是本项目最常见的夸大处）**：

「**可判定**」只指 **`Decidable` 实例存在**（Lean 类型类层面），
**不**指「可计算 / 可执行」。原因在 `ℝ`：
`Real.decidableLE` 本身**就是 `noncomputable`**（`ℝ` 的序来自 `Classical.choice`）。
故本条必须是 `noncomputable def`。**不得**声称这是算法。

**那么它比 §7 多了什么？** 多的是**作用域澄清**：

- `IsFitBoundary`（全集 `∀ gamma' : ℝ`）的量词**覆盖不可数集**；
- `IsFitBoundaryOn` 的量词**只覆盖有限集 `S`**，故它是
  `W.err gamma = sigma ∧ S.all (fun x => decide (sigma <= W.err x))`
  的**真值**，即**有限次比较**。在计算性层面这是**可终止的搜索**，
  只是 `ℝ` 的比较本身不可计算。

**⚠ 前件检查**：结论是 `Decidable (...)`（**类型**），不是命题；
**不可能**与前件（命题）同义反复。 -/
noncomputable def isFitBoundaryOn_decidable (W : ErrProfileWeak) (S : Finset ℝ)
    (sigma gamma : ℝ) : Decidable (IsFitBoundaryOn W S sigma gamma) := by
  unfold IsFitBoundaryOn
  infer_instance

/-- ⭐⭐⭐ **G 腿：`S.inf'` 与全局下界**不可桥接**的构造性反例**。

```
给定 W、非空有限 S、以及某点 gamma0（可不在 S 内）使 err gamma0 < S.inf'，
则 S.inf' 不是全局下界。
```

**这是 §7 D 腿的构造性加强**：D 腿只给**一个**实例，
本条说明**只要 `S` 错过全局最小点**，`S.inf'` **一定**不等于全局下界。

**⚠ 前件检查（关键）**：前件 `W.err gamma0 < S.inf' hne W.err` 是一个
**关于具体数值的严格不等式**；结论是**否定** `¬ ∀ gamma', ...`。
结论**不是**前件的重述 —— 它需要从「某点更小」推出「全称命题失败」。
证明只需把 `gamma0` 代入全称命题并 `linarith`。 -/
theorem inf'_strictly_below_global_min
    (W : ErrProfileWeak) (S : Finset ℝ) (hne : S.Nonempty) (gamma0 : ℝ)
    (hlt : W.err gamma0 < S.inf' hne W.err) :
    ¬ (∀ gamma', S.inf' hne W.err ≤ W.err gamma') := by
  intro hglob
  have h0 := hglob gamma0
  linarith

/-- **§8 诚实说明**（注释固化，不产生 Lean 断言）。 -/
def sec8HonestyNote : String :=
  "E inf'_two_eq_min / inf'_singleton_val : inf' 在具体集合上算得出（落到 min / 恒等）。" ++
  "F isFitBoundaryOn_decidable : 受限谓词有 Decidable 实例（noncomputable，因 Real.decidableLE 是 noncomputable）——不声称可执行。" ++
  "无 isFitBoundary_not_decidable_computably：可计算性不可在 Lean 内形式化，故不设该定理（仅文字说明）。" ++
  "G inf'_strictly_below_global_min : S 错过最小点 ⟹ S.inf' 必不是全局下界（D 腿的构造性加强）。" ++
  "未证：isFitBoundary_sigma_is_inf 作为「任意 sigma 必等于某预先选定的 S.inf'」是假命题，正确形式见 §7 B 腿。"

/-- **§7 定理强度对照表**（注释固化，不产生 Lean 断言）。 -/
def constructiveLowerBoundNote : String :=
  "A exists_min_attained_err : 有限集紧性，非平凡。" ++
  "B inf'_err_eq_of_isFitBoundary : 旧定义蕴含 sigma = inf'，两方向真引理夹住。" ++
  "C isFitBoundaryOn_of_inf_err : 构造性下界（不预设 IsFitBoundary），仅在 S 上。" ++
  "D inf'_not_global_lowerBound : S.inf' 不是全集下界（诚实边界，不可删）。" ++
  "E isFitBoundary_of_on_and_globalBound : 胶合，全局下界原样传递，非数学定理。"

/-! ===========================================================================
  §9  ⭐⭐ 裁决 K ③ 的**决定性陈述**：无 `IsMinOn` 则下界不可得
  ===========================================================================

  ## 9.0 本节要说什么（与 §1–§8 的关系）

  §1–§8 已经确立了 `IsFitBoundary` 的第二分量**就是**全局下界，
  并把「下界」翻译成 `IsMinOn`（§2）或有限集上的 `inf'`（§7）。

  但审计 ③ 的指控还有一层没被**直接**回答：

  > 如果「下界」不是定义的琐碎后果，那么**拿掉 `IsMinOn` 之后**，
  > 第一分量应当**仍然可以单独成立**，而第二分量**同时失败**。
  > 只讲「有它则有下界」**不足以**说明它**不可省** ——
  > 还必须说明**没有它，下界真的拿不到**。

  §9 给出这条陈述的**存在性形式**：

  ```
  ∃ W sigma gamma,  W.err gamma = sigma  ∧  ¬ (∀ gamma', sigma ≤ W.err gamma')
  ```

  即：**存在**一个剖面与数值，使
  - 第一分量 `W.err gamma = sigma` **成立**（这不是空条件，见 `§9.2` 的取到性）；
  - 第二分量 `∀ gamma', sigma ≤ W.err gamma'` **不成立**。

  ## 9.1 ⚠ 前件检查（第 7 条纪律）

  本定理是**存在性命题**，**没有前件**，故**不可能**是「前件包含结论」。
  结论的第二个合取支是**否定**形式 `¬ (∀ ...)` ——
  它不是第一个合取支 `W.err gamma = sigma` 的改写：
  前者说「某个点的值」，后者说「一个全称命题失败」。
  两者**互不蕴含**：
  - 第一分量成立而第二分量失败 → 本定理（不可省性）；
  - 第一分量成立且第二分量成立 → `IsFitBoundary`（§2）。

  ## 9.2 见证（具体数值，全部已机检）

  | 项 | 取值 | 依据 |
  |---|---|---|
  | `W` | `profExpOnly`（`err = exp`）| `profExpOnly_err` |
  | `sigma` | `1` | — |
  | `gamma` | `0` | `profExpOnly_attains_one`：`exp 0 = 1` ✅ |
  | 第二分量失败 | `exp (-1) = e^{-1} < 1` | `profExpOnly_not_lowerBound_one` ✅ |

  ## 9.3 诚实边界

  - 本定理**只证明「下界不是定义（第一分量）的后果」**。
    它**不**证明「`IsMinOn` 是唯一能给出下界的前提」——
    任何能推出 `∀ gamma', sigma ≤ W.err gamma'` 的前提都行
    （例如 §7 C 腿在有限集上的 `inf'`）。
  - 本定理的见证 `profExpOnly` **是** `Fate/FitBoundary.lean` 家族中已有的
    `profExpAlone`（`err = exp`）的 `ErrProfileWeak` 版本，**非人造怪例**。
  - 本定理**不**声称 `profExpOnly` 有任何边界（它确实没有，见
    `Fate/FitBoundary.lean` 的 `profExpAlone_no_boundary_nonpos` 一族）。
    恰恰因为**没有**边界，它才成为「第一分量可成立而下界不成立」的见证。
-/

/-- ⭐⭐ **【核心】下界不可由定义（第一分量）推出**。

```
∃ (W : ErrProfileWeak) (sigma gamma : ℝ),
  W.err gamma = sigma  ∧  ¬ (∀ gamma', sigma ≤ W.err gamma')
```

**读法**：
- 第一个合取支：`sigma` 在 `gamma` 处**被取到** —— 即 `IsFitBoundary` 的**第一分量成立**；
- 第二个合取支：`sigma` **不是**全局下界 —— 即 `IsFitBoundary` 的**第二分量失败**。

**⟹ 第二分量（下界）不是第一分量的逻辑后果**；
把它写进定义**确实**是在**额外假设**一条独立内容，
而不是在做定义展开。这就是审计 ③「定义投射」指控的**正面、可机检的回答**：
指控在形式上成立（`le_err_of_isFitBoundary = h.2` 不假），
但**「下界」这条前提不可省** —— 去掉它，命题**变成假的**。

**见证**：`W = profExpOnly`（`err = e^gamma`），`sigma = 1`，`gamma = 0`。
`e^0 = 1`（第一分量 ✅），但 `e^{-1} < 1`（第二分量 ❌）。

**`#print axioms`**：仅 `[propext, Classical.choice, Quot.sound]`，
**无 `sorryAx`、无自定义 axiom**（已实测）。

**与 §5 的关系**：§5 的 `strictConvex_unique_attaining_not_suffice` 说的是
「严格凸 + 唯一等值点（即 `IsMinOn` 的必要条件之一）不足以给出下界」；
本条说的是「**连 `IsMinOn` 本身都不给**时，第一分量照样可以成立」。
两条同源（同一见证 `profExpOnly`），但陈述不同：§5 是**反例于一个蕴含式**，
本条是**存在性分离**。 -/
theorem lowerBound_not_derivable_from_definition :
    ∃ (W : ErrProfileWeak) (sigma gamma : ℝ),
      W.err gamma = sigma ∧ ¬ (∀ gamma', sigma ≤ W.err gamma') := by
  refine ⟨profExpOnly, 1, 0, profExpOnly_attains_one, ?_⟩
  exact profExpOnly_not_lowerBound_one

/-- **§9 诚实说明**（注释固化，不产生 Lean 断言）。 -/
def sec9HonestyNote : String :=
  "lowerBound_not_derivable_from_definition : 存在性分离 —— 第一分量成立、第二分量失败，" ++
  "故「下界」不是定义的琐碎后果（无前件，不可能前件包结论）。" ++
  "见证：profExpOnly（err = exp），sigma = 1，gamma = 0。" ++
  "不声称 IsMinOn 是唯一可给出下界的前提；也不声称 profExpOnly 有边界（它没有）。"

end

end FitBoundaryLowerBound
end Fate
