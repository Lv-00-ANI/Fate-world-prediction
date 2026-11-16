import FateWorld.FateV2.Error.FitBoundary

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/OptimalFit.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 3 处，含 1 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Modeling
/-
  参数无关判据：最小点刻画（对应论文 §3.3）

  边界定义 IsFitBoundary 把噪声尺度 σ 作为外部参数传入，于是判据的可用性依赖一个
  来源不明的标定量。本模块证明该依赖是虚假的：只要存在边界点，σ 就被强制等于误差
  曲线的下确界 sInf (range E_W)；反之在 σ := sInf (range E_W) 处，「是边界点」与
  「误差取到下确界」完全等价。由此得到一个不含任何外部参数的判据

    IsOptimalFit W γ := E_W(γ) = sInf (range E_W)，

  它只读到误差曲线自身，因而对任意 ℝ → ℝ 的误差剖面同样成立。

  内容：bddBelow_range_err（下确界存在）、sInf_range_err_eq_of_isFitBoundary
  （σ 被下确界强制）、isOptimalFit_iff_isFitBoundary（两个判据的等价）、
  hasFitBoundary_iff_exists_isOptimalFit（存在性的等价翻译，由此可知 σ ≠ inf E 时
  边界集必为空）。

  （下文 §n 指本文件内部分节，与论文节次无关。）

  注：本模块的结果不依赖凸性、连续性或单调性，仅用到误差两分量非负；
     下确界未必被取到（如 E_W γ = exp γ），故 IsOptimalFit 可能为空，存在性由后续
     模块单独处理。本模块亦不声称 sInf (range E_W) 就是统计学意义上的噪声尺度——
     那是一个经验命题，本文不作断言。

  不取 `sorry` / `admit` / 自定义 `axiom`。
-/


open Set

namespace FateV2.Error.Core

/-! ### §1  下确界存在（只用到两分量非负） -/

/-- **误差曲线的值域有下界**（下界为 `0`）。

    只需「两分量非负」，**不需要**任何凸性、连续性或单调性。 -/
theorem bddBelow_range_err (W : ErrProfileWeak) : BddBelow (range W.err) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨γ, rfl⟩
  exact W.err_nonneg γ

/-- **值域非空**（任一取值都在其中）。 -/
theorem range_err_nonempty (W : ErrProfileWeak) (γ : ℝ) : (range W.err).Nonempty :=
  ⟨W.err γ, γ, rfl⟩

/-! ### §2  σ 被下确界强制（主定理） -/

/-- 边界点存在时，`σ` 是误差值域的下界。 -/
theorem sigma_le_err_of_isFitBoundary {W : ErrProfileWeak} {σ γ : ℝ}
    (h : IsFitBoundary W σ γ) : ∀ x ∈ range W.err, σ ≤ x := by
  rintro _ ⟨γ', rfl⟩
  exact h.2 γ'

/-- **主定理：`σ` 由剖面唯一决定。**

    若 `γ` 是一个边界点，则 `sInf (range W.err) = σ`。

    **意义**：`σ` **不是**自由参数。它一旦与某个剖面配对，就被该剖面的
    误差下确界**锁定**。原定义中「`σ` 作参数传入」的自由度，只在
    **不存在边界点**时才真实存在。

    **证明**：两方向。
    - `sInf ≤ σ`：`σ` 落在值域中，下确界不超过其中任一元素；
    - `σ ≤ sInf`：`σ` 是值域的（已被证明的）下界，而下确界是最大的下界。 -/
theorem sInf_range_err_eq_of_isFitBoundary {W : ErrProfileWeak} {σ γ : ℝ}
    (h : IsFitBoundary W σ γ) : sInf (range W.err) = σ := by
  refine le_antisymm ?_ ?_
  · exact csInf_le (bddBelow_range_err W) ⟨γ, h.1⟩
  · exact le_csInf (range_err_nonempty W γ) (sigma_le_err_of_isFitBoundary h)

/-- **推论：两个边界点的误差值相同。** -/
theorem err_eq_of_two_isFitBoundary {W : ErrProfileWeak} {σ γ₁ γ₂ : ℝ}
    (h₁ : IsFitBoundary W σ γ₁) (h₂ : IsFitBoundary W σ γ₂) :
    W.err γ₁ = W.err γ₂ :=
  h₁.1.trans h₂.1.symm

/-! ### §3  参数无关判据 -/

/-- **参数无关的恰当拟合判据**：误差在 `γ` 处取到其**下确界**。

    与 `IsFitBoundary` 的区别：**不含任何外部参数**，只读到误差曲线自身。
    由 `isOptimalFit_iff_isFitBoundary`，它就是 `IsFitBoundary` 在
    `σ := sInf (range W.err)` 处的值。 -/
def IsOptimalFit (W : ErrProfileWeak) (γ : ℝ) : Prop :=
  W.err γ = sInf (range W.err)

/-- **恰当拟合点集**（`σ` 由剖面决定，不再传入）。 -/
def OptimalFitSet (W : ErrProfileWeak) : Set ℝ :=
  {γ | IsOptimalFit W γ}

/-- **桥：参数无关判据 ⟺ 原判据在 `σ := sInf` 处。**

    - 正向：`IsOptimalFit` 直接给出第一分量；
      第二分量由「下确界是下界」逐点得出。
    - 反向：`IsFitBoundary` 的第一分量即是 `IsOptimalFit`（在 `σ := sInf` 处）。

    即：`IsOptimalFit W γ ↔ IsFitBoundary W (sInf (range W.err)) γ`。 -/
theorem isOptimalFit_iff_isFitBoundary (W : ErrProfileWeak) (γ : ℝ) :
    IsOptimalFit W γ ↔ IsFitBoundary W (sInf (range W.err)) γ := by
  constructor
  · intro h
    refine ⟨h, ?_⟩
    intro γ'
    have hle : sInf (range W.err) ≤ W.err γ' :=
      csInf_le (bddBelow_range_err W) ⟨γ', rfl⟩
    linarith [h]
  · intro h
    exact h.1

/-- 参数无关判据**蕴含**原判据（`σ` 取下确界）。 -/
theorem isFitBoundary_of_isOptimalFit {W : ErrProfileWeak} {γ : ℝ}
    (h : IsOptimalFit W γ) : IsFitBoundary W (sInf (range W.err)) γ :=
  (isOptimalFit_iff_isFitBoundary W γ).1 h

/-- 原判据（`σ` 取下确界）**蕴含**参数无关判据。 -/
theorem isOptimalFit_of_isFitBoundary {W : ErrProfileWeak} {γ : ℝ}
    (h : IsFitBoundary W (sInf (range W.err)) γ) : IsOptimalFit W γ :=
  (isOptimalFit_iff_isFitBoundary W γ).2 h

/-! ### §4  与原定义的兼容性 -/

/-- **`σ` 显式化版本与最小点版本等价**：

    `IsFitBoundary W σ γ` 成立**蕴含** `IsOptimalFit`，且此时 `σ = sInf`。

    这条把「原定义」完整地翻译到新视角下，**不丢失任何内容**：
    原定义 = 最小点条件 + 「`σ` 恰为该下确界」（后者由 `sInf_...` 自动成立）。 -/
theorem isOptimalFit_of_isFitBoundary_of_sigma {W : ErrProfileWeak} {σ γ : ℝ}
    (h : IsFitBoundary W σ γ) : IsOptimalFit W γ := by
  have hs : sInf (range W.err) = σ := sInf_range_err_eq_of_isFitBoundary h
  rw [IsOptimalFit, hs]
  exact h.1

/-- **存在性的等价翻译**：`σ` 显式版有边界 ⟺ 最小点存在 **且** `σ = sInf`。 -/
theorem hasFitBoundary_iff_exists_isOptimalFit (W : ErrProfileWeak) (σ : ℝ) :
    HasFitBoundary W σ ↔ (∃ γ, IsOptimalFit W γ) ∧ σ = sInf (range W.err) := by
  constructor
  · rintro ⟨γ, h⟩
    exact ⟨⟨γ, isOptimalFit_of_isFitBoundary_of_sigma h⟩,
      (sInf_range_err_eq_of_isFitBoundary h).symm⟩
  · rintro ⟨⟨γ, hγ⟩, rfl⟩
    exact ⟨γ, isFitBoundary_of_isOptimalFit hγ⟩

end FateV2.Error.Core
