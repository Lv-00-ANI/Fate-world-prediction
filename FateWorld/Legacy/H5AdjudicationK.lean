/-
  H5 · **裁决 K 组同义反复检查**（可验证的补强）

  ============================================================================
  ⚠ 本文件的定位（先读）
  ============================================================================

  任务：检查 `Fate/FitBoundary.lean` 的两条裁决 K 组定理

  - `R238E3.existsUnique_isFitBoundary_of_strictConvexOn`
  - `R238E3.boundary_not_unique`

  的**前件是否已把结论包进去**（同义反复），若是，给出**真正有内容**的版本。

  **本文件的结论（详见 `H5-裁决K检查.md`）**：
  - `existsUnique_...` **不是严格逻辑同义反复**（结论 γ₁=γ₂ 不在前件中），
    但它是**`hex`（存在）+ 唯一性核心**的**薄包装**：`∃!` 的「存在」分量
    直接来自前件 `hex : HasFitBoundary W σ`，只有「唯一」是真正证的。
    **⟹ 真正的补强方向：把存在性也从更弱、独立可验证的前件推出**（不假设 `hex`）。
  - `boundary_not_unique` **不是同义反复**（`1 ≠ -1` 不在前件），
    但它用的反例 `profW` 是 **W 形（非凸且非单调）** 的弱剖面，
    故它**只**证明「边界概念单凭自身不唯一」，
    **不能**说明「严格凸性是必要的」——
    因为反驳「严格凸 ⟹ 唯一」需要展示一个**凸但非严格凸**的反例，`profW` 不满足凸性。
    **⟹ 真正的补强方向：给出一个 `ConvexOn` 但非 `StrictConvexOn` 的反例。**

  **本文件交付三条有内容的新定理（均非原子定理的重述）**：

  1. `isFitBoundary_iff_isMinOn` —— **审计性恒等式**：
     `IsFitBoundary W σ γ ↔ (IsMinOn err univ γ ∧ err γ = σ)`。
     这把「唯一性内容到底来自哪里」**显式化**：
     它**完全**来自「全局最小点唯一」（`StrictConvexOn.eq_of_isMinOn`），
     而 `IsFitBoundary` 的第二分量恰是「γ 是全局最小点」。这**正证明**
     「原定理的实质内容 = 严格凸下最小点唯一」，**不是**循环论证。

  2. `existsUnique_isFitBoundary_of_strictConvexOn_coercive` —— **去 `hex`**：
     把 `hex : HasFitBoundary W σ` 换成**独立、更弱、可单独验证**的前件
     （连续 + 强制 coercive），**推出**存在性；唯一性由严格凸得。
     结论为「存在**唯一**的 `γ*` 是 `err` 的最小点，且
     `HasFitBoundary W σ ↔ σ = err γ*`」——
     存在性**不再来自前件**，是全称刻画（对任意 σ）。

  3. `boundary_not_unique_with_convex` —— **更强的必要性证据**：
     给出一个**凸但非严格凸**的剖面 `profHinge`（`err γ = max 0 (|γ|-1)`，
     等价于 `max 0 (max (γ-1) (-(γ+1)))`，两个仿射函数之 max，**必凸**），
     它在 `γ = ±1` **两个**点都是边界点。**⟹ `ConvexOn` 单凭自身不足以保证唯一，
     必须 `StrictConvexOn`。** 这**严格强于** `boundary_not_unique`。

  **⚠ 无 `sorry` / `admit` / `axiom`。**
  ============================================================================
-/

import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import FateWorld.Legacy.FitBoundary

namespace Fate
namespace H5K

open Set Filter

noncomputable section

set_option linter.unusedVariables false

/-! ===========================================================================
  §1  **审计性恒等式**：`IsFitBoundary` 就是「全局最小点 + 值 = σ」
  =========================================================================== -/

/-- ⭐⭐ **审计恒等式**（H5 的核心发现，机械可核验）：

$$\mathrm{IsFitBoundary}(W,\sigma,\gamma)
  \iff \mathrm{IsMinOn}\ E_W\ \mathrm{univ}\ \gamma
       \ \wedge\ E_W(\gamma)=\sigma$$

**证明**：`IsFitBoundary` 的第二分量 `∀γ', σ ≤ E(γ')` 配上第一分量
`E(γ)=σ` 就**恰是** `∀γ', E(γ) ≤ E(γ')`（`IsMinOn` 的定义，`isMinOn_univ_iff`）。

**为什么这条重要（H5 的裁决依据）**：
它说明 `eq_of_isFitBoundary_of_strictConvexOn` 的**全部唯一性内容**
来自 `StrictConvexOn.eq_of_isMinOn`——
即「严格凸 ⟹ 全局最小点唯一」这一 Mathlib 定理。
**⟹ 原定理不是逻辑同义反复**（γ₁=γ₂ 不在前件），
但它的内容**完全**寄生于「最小点唯一性」，而这一点由 `StrictConvexOn` 提供。
**这条恒等式把「寄生于哪里」显式化，供后续审计引用。** -/
theorem isFitBoundary_iff_isMinOn {W : R238E3.ErrProfileWeak} {σ γ : ℝ} :
    R238E3.IsFitBoundary W σ γ ↔
      (IsMinOn (fun γ' => W.err γ') univ γ ∧ W.err γ = σ) := by
  unfold R238E3.IsFitBoundary
  constructor
  · rintro ⟨hval, hlb⟩
    refine ⟨?_, hval⟩
    intro γ' _
    show W.err γ ≤ W.err γ'
    rw [hval]; exact hlb γ'
  · rintro ⟨hmin, hval⟩
    refine ⟨hval, fun γ' => ?_⟩
    have hle : W.err γ ≤ W.err γ' := hmin (mem_univ γ')
    linarith [hval, hle]

/-! ===========================================================================
  §2  ⭐⭐⭐ **去掉 `hex`：从独立前件推出存在唯一性**

  原定理 `existsUnique_isFitBoundary_of_strictConvexOn` 的「存在」分量
  直接来自前件 `hex : HasFitBoundary W σ`。
  本节的补强：把 `hex` 换成**两条独立、更弱、可单独验证**的前件

  - `hcont`：`E_W` 连续；
  - `hcoer`：`E_W` **强制**（两端趋于 +∞）——这是「误差随粒度发散」的建模内容。

  **⟹ 存在性被真正证出来**，唯一性由严格凸得。
  =========================================================================== -/

/-- ⭐ **强制 ⟹ 最小值可达**（辅助引理）。

`E_W` 连续 + 两端趋于 `+∞` ⟹ `∃ γ*, ∀ γ, E(γ*) ≤ E(γ)`。

**证明**：两端 `+∞` 给出 `Tendsto f (cocompact ℝ) atTop`
（`cocompact_eq_atBot_atTop` + `Tendsto.sup`），
再用 `Continuous.exists_forall_le`。 -/
theorem exists_min_of_coercive {f : ℝ → ℝ} (hcont : Continuous f)
    (htop : Tendsto f atTop atTop) (hbot : Tendsto f atBot atTop) :
    ∃ x, ∀ y, f x ≤ f y := by
  have hc : Tendsto f (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact hbot.sup htop
  exact hcont.exists_forall_le hc

/-- ⭐⭐⭐ **严格凸 + 连续 + 强制 ⟹ 存在唯一最小点**（`∃!` 且有值刻画）。

$$\Bigl(\mathrm{StrictConvexOn}\ \mathbb{R}\ \mathrm{univ}\ f\Bigr)
  \wedge \mathrm{Continuous}\ f
  \wedge f\to+\infty\ (\gamma\to\pm\infty)
  \Longrightarrow
  \exists!\,\gamma^*,\ \mathrm{IsMinOn}\ f\ \mathrm{univ}\ \gamma^*$$

**这是有内容的**：存在性用**强制 + 连续**（`exists_min_of_coercive`）证，
唯一性用**严格凸**（`StrictConvexOn.eq_of_isMinOn`）证——
**两条前件各管一半，互不包含**，且都**不假设**任何最小点已存在。 -/
theorem existsUnique_isMinOn_of_strictConvexOn_coercive
    {f : ℝ → ℝ}
    (hcvx : StrictConvexOn ℝ (univ : Set ℝ) f)
    (hcont : Continuous f)
    (htop : Tendsto f atTop atTop) (hbot : Tendsto f atBot atTop) :
    ∃! γ, IsMinOn f univ γ := by
  obtain ⟨γ₀, hmin₀⟩ := exists_min_of_coercive hcont htop hbot
  have hmin₀' : IsMinOn f univ γ₀ := fun γ _ => hmin₀ γ
  refine ⟨γ₀, hmin₀', fun γ hmin => ?_⟩
  exact hcvx.eq_of_isMinOn hmin hmin₀' (mem_univ _) (mem_univ _)

/-- ⭐⭐⭐ **边界版本：去 `hex` 的 `∃!` 定理（本文件的实质交付）**。

$$\Bigl(\mathrm{StrictConvexOn}\ \mathbb{R}\ \mathrm{univ}\ E_W\Bigr)
  \wedge \mathrm{Continuous}\ E_W
  \wedge E_W\to+\infty\ (\gamma\to\pm\infty)
  \Longrightarrow
  \exists!\,\gamma^*,\ \bigl(\forall\sigma,\
     \mathrm{HasFitBoundary}(W,\sigma)\iff\sigma = E_W(\gamma^*)\bigr)$$

**与原子定理 `existsUnique_isFitBoundary_of_strictConvexOn` 的区别（逐点）**：

| | 原定理 | 本定理 |
|---|---|---|
| 存在性来源 | **前件 `hex : HasFitBoundary W σ`**（同义重复结论的一半） | **连续 + 强制**（`exists_min_of_coercive`） |
| σ 的量词 | **固定任意但单个** | **`∀σ` 全称刻画** |
| 唯一性来源 | 严格凸（实质） | 严格凸（实质） |

**⟹ 原定理是「`hex` + 唯一性核心」的包装；本定理把 `hex` 换成一个
真正独立的条件并**证出**存在性，同时给出对**任意 σ** 的完整刻画。
这就是「真正有内容的版本」。** -/
theorem existsUnique_isFitBoundary_of_strictConvexOn_coercive
    {W : R238E3.ErrProfileWeak}
    (hcvx : StrictConvexOn ℝ (univ : Set ℝ) (fun γ => W.err γ))
    (hcont : Continuous (fun γ => W.err γ))
    (htop : Tendsto (fun γ => W.err γ) atTop atTop)
    (hbot : Tendsto (fun γ => W.err γ) atBot atTop) :
    ∃! γ_, R238E3.IsFitBoundary W (W.err γ_) γ_ ∧
      ∀ σ : ℝ, (R238E3.HasFitBoundary W σ ↔ σ = W.err γ_) := by
  obtain ⟨γ₀, hmin₀, huniq⟩ :=
    existsUnique_isMinOn_of_strictConvexOn_coercive hcvx hcont htop hbot
  refine ⟨γ₀, ⟨?_, ?_⟩, ?_⟩
  · -- IsFitBoundary W (err γ₀) γ₀
    refine ⟨rfl, fun γ' => ?_⟩
    exact hmin₀ (mem_univ γ')
  · -- ∀σ, HasFitBoundary W σ ↔ σ = err γ₀
    intro σ
    constructor
    · rintro ⟨γ, hγ⟩
      obtain ⟨hminγ, hval⟩ :=
        (isFitBoundary_iff_isMinOn (W := W) (σ := σ) (γ := γ)).mp hγ
      have : γ = γ₀ := huniq γ hminγ
      rw [this] at hval; exact hval.symm
    · rintro rfl
      exact ⟨γ₀, rfl, fun γ' => hmin₀ (mem_univ γ')⟩
  · -- 唯一性：`γ` 满足「对自身值有界」⟹ 是最小点 ⟹ = γ₀
    rintro γ ⟨hγ, _⟩
    obtain ⟨hminγ, hval⟩ :=
      (isFitBoundary_iff_isMinOn (W := W) (σ := W.err γ) (γ := γ)).mp hγ
    exact huniq γ hminγ

/-! ===========================================================================
  §3  ⭐⭐⭐ **更强的必要性证据：凸但非严格凸 ⟹ 边界不唯一**

  `boundary_not_unique` 用 `profW`（W 形 `(γ²-1)²`）——它**既非凸也非单调**，
  故**只**证明「边界概念单凭自身不唯一」，
  不足以说明「严格凸性是必要的」——要否定「凸 ⟹ 唯一」需要一个**凸**反例。

  本节给出 `profHinge`：`err γ = max 0 (max (γ-1) (-(γ+1)))`
  = `max 0 (|γ| - 1)`（两个仿射函数之 max 再与 0 取 max），**必凸**。
  它在 `[-1,1]` 上取最小值 0，故 `γ=1` 与 `γ=-1` **都是**边界点。
  **⟹ `ConvexOn` 不足以保证唯一，`StrictConvexOn` 是真正需要的。**
  =========================================================================== -/

/-- `profHinge` 的误差：`γ ↦ max 0 (max (γ-1) (-(γ+1)))`（= `max 0 (|γ|-1)`）。 -/
def hingeErr (γ : ℝ) : ℝ := max 0 (max (γ - 1) (-(γ + 1)))

/-- **凸但非严格凸的弱剖面**（`bias = hingeErr`，`var = 0`）。 -/
def profHinge : R238E3.ErrProfileWeak where
  bias := hingeErr
  var := fun _ => 0
  bias_nonneg := fun γ => le_max_left _ _
  var_nonneg := fun _ => le_refl 0

/-- `profHinge` 的误差就是 `hingeErr`。 -/
theorem profHinge_err (γ : ℝ) : profHinge.err γ = hingeErr γ := by
  simp only [R238E3.ErrProfileWeak.err, profHinge]; ring

/-- **仿射函数凸**（辅助）。 -/
theorem affine_convexOn (c d : ℝ) :
    ConvexOn ℝ (univ : Set ℝ) (fun γ : ℝ => c * γ + d) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b _ _ hab
  simp only [smul_eq_mul]
  have key : a * (c * x + d) + b * (c * y + d) = c * (a * x + b * y) + d := by
    linear_combination d * hab
  linarith [key]

/-- ⭐ **`hingeErr` 凸**（`0`、`γ-1`、`-(γ+1)` 三段仿射之 max）。 -/
theorem hingeErr_convexOn : ConvexOn ℝ (univ : Set ℝ) hingeErr := by
  have h0 : ConvexOn ℝ (univ : Set ℝ) (fun _ : ℝ => (0:ℝ)) :=
    convexOn_const _ convex_univ
  have ha : ConvexOn ℝ (univ : Set ℝ) (fun γ : ℝ => γ - 1) := by
    have h := affine_convexOn 1 (-1)
    have he : (fun γ : ℝ => (1:ℝ) * γ + (-1)) = (fun γ : ℝ => γ - 1) :=
      funext fun γ => by ring
    rw [he] at h; exact h
  have hb : ConvexOn ℝ (univ : Set ℝ) (fun γ : ℝ => -(γ + 1)) := by
    have h := affine_convexOn (-1) (-1)
    have he : (fun γ : ℝ => (-1:ℝ) * γ + (-1)) = (fun γ : ℝ => -(γ + 1)) :=
      funext fun γ => by ring
    rw [he] at h; exact h
  have hinner : ConvexOn ℝ (univ : Set ℝ)
      (fun γ : ℝ => max (γ - 1) (-(γ + 1))) := ha.sup hb
  have hone : hingeErr =
      (fun _ : ℝ => (0:ℝ)) ⊔ (fun γ : ℝ => max (γ - 1) (-(γ + 1))) := rfl
  rw [hone]; exact h0.sup hinner

/-- **`hingeErr` 在 `±1` 处取 0**。 -/
theorem hingeErr_one : hingeErr 1 = 0 := by norm_num [hingeErr]
theorem hingeErr_neg_one : hingeErr (-1) = 0 := by norm_num [hingeErr]

/-- **`hingeErr` 非负**（`max 0 _ ≥ 0`）。 -/
theorem hingeErr_nonneg (γ : ℝ) : 0 ≤ hingeErr γ := le_max_left _ _

/-- ⭐ **`hingeErr` 非严格凸**（在 `±1` 之间取常值 0）。 -/
theorem hingeErr_not_strictConvex : ¬ StrictConvexOn ℝ (univ : Set ℝ) hingeErr := by
  intro h
  have hh := h.2 (mem_univ (-1)) (mem_univ 1) (by norm_num : (-1:ℝ) ≠ 1)
    (show (0:ℝ) < 1/2 by norm_num) (show (0:ℝ) < 1/2 by norm_num)
    (show (1/2:ℝ) + 1/2 = 1 by norm_num)
  simp only [smul_eq_mul] at hh
  rw [show (1/2:ℝ)*(-1) + 1/2*1 = 0 by norm_num] at hh
  norm_num [hingeErr] at hh

/-- ⭐⭐⭐ **凸但非严格凸 ⟹ 边界不唯一**（本文件最强内容）。

$$\mathrm{ConvexOn}\ \mathbb{R}\ \mathrm{univ}\ (\mathrm{err\ profHinge})
  \ \wedge\ \neg\,\mathrm{StrictConvexOn}\ \dots
  \ \wedge\ \mathrm{IsFitBoundary}(\mathrm{profHinge},0,1)
  \ \wedge\ \mathrm{IsFitBoundary}(\mathrm{profHinge},0,-1)
  \ \wedge\ (1\neq-1)$$

**⟹ 严格凸前件不可弱化为凸前件**：存在**凸**剖面其边界有**两个**点。
这**严格强于** `boundary_not_unique`（后者用的 `profW` 连凸性都不满足，
故**不能**反驳「凸 ⟹ 唯一」）。 -/
theorem boundary_not_unique_with_convex :
    ConvexOn ℝ (univ : Set ℝ) (fun γ => profHinge.err γ) ∧
    ¬ StrictConvexOn ℝ (univ : Set ℝ) (fun γ => profHinge.err γ) ∧
    R238E3.IsFitBoundary profHinge 0 1 ∧
    R238E3.IsFitBoundary profHinge 0 (-1) ∧
    (1 : ℝ) ≠ -1 := by
  have hconv : ConvexOn ℝ (univ : Set ℝ) (fun γ => profHinge.err γ) := by
    have he : (fun γ => profHinge.err γ) = hingeErr :=
      funext fun γ => profHinge_err γ
    rw [he]; exact hingeErr_convexOn
  have hnstrict : ¬ StrictConvexOn ℝ (univ : Set ℝ) (fun γ => profHinge.err γ) := by
    intro h
    have he : (fun γ => profHinge.err γ) = hingeErr :=
      funext fun γ => profHinge_err γ
    rw [he] at h
    exact hingeErr_not_strictConvex h
  refine ⟨hconv, hnstrict, ⟨?_, ?_⟩, ⟨?_, ?_⟩, by norm_num⟩
  · rw [profHinge_err]; exact hingeErr_one
  · intro γ'; rw [profHinge_err]; exact hingeErr_nonneg γ'
  · rw [profHinge_err]; exact hingeErr_neg_one
  · intro γ'; rw [profHinge_err]; exact hingeErr_nonneg γ'

/-- **读法**：`profHinge` 有边界，但边界点**不唯一**——
即使 `err` **凸**。 -/
theorem profHinge_hasBoundary_not_unique :
    R238E3.HasFitBoundary profHinge 0 ∧
      ¬ ∃! γ, R238E3.IsFitBoundary profHinge 0 γ := by
  refine ⟨⟨1, boundary_not_unique_with_convex.2.2.1⟩, ?_⟩
  rintro ⟨γ, _, huniq⟩
  have h1 : (1 : ℝ) = γ := huniq 1 boundary_not_unique_with_convex.2.2.1
  have h2 : ((-1 : ℝ)) = γ := huniq (-1) boundary_not_unique_with_convex.2.2.2.1
  have h3 : ((-1 : ℝ)) = 1 := by rw [h2, h1]
  norm_num at h3

end

end H5K
end Fate
