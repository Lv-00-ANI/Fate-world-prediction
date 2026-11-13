import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic
import FateWorld.FateV2.Modeling.ObsEstimationStrong
import FateWorld.FateV2.Error.ErrorBound
import FateWorld.FateV2.Error.FitBoundary

/-!
  ## 迁移登记
  - 来源：Legacy/ProperFit-6e03674/AudUnivLayer2.lean
  - 动作：B（适配）
  - 对应环节：—
  - 依赖裁决：D-008 D-020
  - 改动：namespace/引用 ProperFit→FateV2.Error（正文 5 处，含 3 条 import）；其余正文未改
  - 状态：已编译未验证
-/

open FateV2.Error
open FateV2.Loop
open FateV2.Modeling

/-
  全称形式的补强（对应论文 §5）

  把观测估计、误差界与边界三个模块中的代表性定理升级或显式化为全称（∀）形式，
  以便判定其全称性层级。

  注：本模块只做形式升级，不引入新的数学假设。

  不取 `sorry` / `admit` / 自定义 `axiom`。
-/


namespace FateV2.Error
namespace AudUniv2

open Classical
open Set (univ)

set_option linter.unusedVariables false

/-! ## A. ObsEstimationStrong：全称形式补强 -/

/-- ∀-形式：对**所有** x, η, ηmax 以及 hx+η 的**任意**原像 x'，误差有界。 -/
theorem univ_estimator_error_bound {E : Type*} [SeminormedAddCommGroup E] [Nonempty E]
    {h : E → E} {L ηmax : ℝ} (hL : 0 < L) (_hinj : Function.Injective h)
    (hLI : RA14Strong.LipschitzInvertibleOn h L) :
    ∀ (x : E) (η : E) (x' : E), h x' = h x + η → dist η 0 ≤ ηmax →
      dist x' x ≤ L * ηmax := by
  intro x η x' hx' hη
  have h1 : dist x' x ≤ L * dist η 0 :=
    RA14Strong.inverse_estimate_error hL hLI x x' η hx'
  have h2 : L * dist η 0 ≤ L * ηmax := mul_le_mul_of_nonneg_left hη (le_of_lt hL)
  linarith

/-- ∀-形式：`chooseEstimator` 版本（结论显式含估计器）。 -/
theorem univ_estimator_error_bound_on_image {E : Type*} [SeminormedAddCommGroup E] [Nonempty E]
    {h : E → E} {L ηmax : ℝ} (hL : 0 < L) (hinj : Function.Injective h)
    (_hLI : RA14Strong.LipschitzInvertibleOn h L) :
    ∀ (x : E) (η : E) (x' : E), h x' = h x + η → dist η 0 ≤ ηmax →
      dist (RA14Strong.chooseEstimator h (h x + η)) x' ≤ L * ηmax := by
  intro x η x' hx' hη
  have hval : RA14Strong.chooseEstimator h (h x + η) = x' := by
    rw [← hx']
    exact RA14Strong.chooseEstimator_apply_of hinj x'
  calc dist (RA14Strong.chooseEstimator h (h x + η)) x'
      = dist x' x' := by rw [hval]
    _ = 0 := dist_self x'
    _ ≤ L * ηmax := mul_nonneg (le_of_lt hL) (le_trans dist_nonneg hη)

/-- ∀-形式：`LipschitzInvertibleOn` 对**所有** k>0 成立。 -/
theorem univ_bound_necessary_scaling :
    ∀ k : ℝ, 0 < k → RA14Strong.LipschitzInvertibleOn (fun x : ℝ => k * x) (1 / k) :=
  fun k hk => RA14Strong.bound_necessary_scaling k hk

/-- ∀-形式：`(⋆)` 对**所有** k>0 与**所有**点对取等。 -/
theorem univ_scale_sharp :
    ∀ k : ℝ, 0 < k → ∀ x₁ x₂ : ℝ,
      dist ((fun x : ℝ => k * x) x₁) ((fun x : ℝ => k * x) x₂) = dist x₁ x₂ / (1 / k) :=
  fun k hk x₁ x₂ => RA14Strong.lipschitzInvertible_scaling_sharp k hk x₁ x₂

/-! ## B. 决策稳定性：全称形式补强 -/

/-- ∀-形式：对**所有** s δ ε 满足前提，分类不变。 -/
theorem univ_error_bound_gives_correct_classification :
    ∀ s δ ε : ℝ, |δ| ≤ ε → 2 * ε < |s| →
      R250ErrorBound.sgn (s + δ) = R250ErrorBound.sgn s :=
  fun s δ ε hδ h2 => R250ErrorBound.error_bound_gives_correct_classification hδ h2

/-- ∀-形式：逐点 ε 的**全称**（函数级）形式。 -/
theorem univ_learning_bound {X : Type*} (f δ : X → ℝ) (ε : X → ℝ)
    (hδ : ∀ x, |δ x| ≤ ε x) (h2 : ∀ x, 2 * ε x < |f x|) :
    ∀ x, R250ErrorBound.sgn (f x + δ x) = R250ErrorBound.sgn (f x) :=
  R250ErrorBound.learning_bound_general f δ ε hδ h2

/-- ∀-形式：ε = m 时决策消失 对**所有** m>0 成立。 -/
theorem univ_tight_bound_epsilon_eq_m :
    ∀ m : ℝ, 0 < m → R250ErrorBound.sgn (m + (-m)) = 0 ∧ R250ErrorBound.sgn m = 1 ∧
      R250ErrorBound.sgn (m + (-m)) ≠ R250ErrorBound.sgn m :=
  fun m hm => R250ErrorBound.tight_bound_epsilon_eq_m m hm

/-! ## C. 全称形式补强 -/

/-- ∀-形式：严格凸 ⟹ 边界点唯一（对**所有** W, σ）。 -/
theorem univ_existsUnique_isFitBoundary_of_strictConvexOn {W : Core.ErrProfileWeak} {σ : ℝ}
    (hcvx : StrictConvexOn ℝ (univ : Set ℝ) (fun γ => W.err γ)) :
    Core.HasFitBoundary W σ → ∃! γ, Core.IsFitBoundary W σ γ :=
  fun hex => Core.existsUnique_isFitBoundary_of_strictConvexOn hcvx hex

/-- ∀-形式：严格凸 ⟹ **任意**两边界点相等（纯 ∀，无 ∃）。 -/
theorem univ_eq_of_isFitBoundary {W : Core.ErrProfileWeak} {σ : ℝ}
    (hcvx : StrictConvexOn ℝ (univ : Set ℝ) (fun γ => W.err γ)) :
    ∀ γ₁ γ₂ : ℝ, Core.IsFitBoundary W σ γ₁ → Core.IsFitBoundary W σ γ₂ → γ₁ = γ₂ :=
  fun γ₁ γ₂ h₁ h₂ => Core.eq_of_isFitBoundary_of_strictConvexOn hcvx h₁ h₂

/-- **关键**：`boundary_not_unique` 只是**一个实例**（∃），其**全称**形式不成立。 -/
theorem boundary_uniqueness_fails_without_convex :
    ∃ W : Core.ErrProfileWeak, ∃ σ γ₁ γ₂ : ℝ,
      Core.IsFitBoundary W σ γ₁ ∧ Core.IsFitBoundary W σ γ₂ ∧ γ₁ ≠ γ₂ :=
  ⟨Core.profW, 0, 1, -1, Core.boundary_not_unique.1,
    Core.boundary_not_unique.2.1, Core.boundary_not_unique.2.2⟩

/-- **关键**：`profExp_unique_boundary_two` 的 σ 是**固定值** 2（非全称）。
    这里给出 `profExp` 在 **任意** σ 上边界的完整刻划（全称形式）。 -/
theorem univ_profExp_boundary_iff :
    ∀ σ : ℝ, Core.HasFitBoundary Core.profExp.toErrProfileWeak σ ↔ σ = 2 := by
  intro σ
  constructor
  · rintro ⟨γ, hγ⟩
    have h1 : Core.profExp.toErrProfileWeak.err γ = Real.exp γ + Real.exp (-γ) :=
      Core.profExp_err γ
    have h0 : Core.profExp.toErrProfileWeak.err 0 = 2 := by
      have := Core.profExp_err 0
      rw [this]; norm_num
    have hlow : σ ≤ Core.profExp.toErrProfileWeak.err 0 := hγ.2 0
    rw [h0] at hlow
    have heq : σ = Core.profExp.toErrProfileWeak.err γ := hγ.1.symm
    have h1' := Core.profExp_err γ
    rw [h1'] at heq
    have hprod : Real.exp γ * Real.exp (-γ) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    have hp : 0 < Real.exp γ := Real.exp_pos γ
    have hge : 2 ≤ Real.exp γ + Real.exp (-γ) := by
      have hsq : 0 ≤ (Real.exp γ - 1) ^ 2 := sq_nonneg _
      have hkey : 0 ≤ (Real.exp γ + Real.exp (-γ) - 2) * Real.exp γ := by
        nlinarith [hsq, hprod]
      nlinarith [hkey, hp]
    linarith [hge, hlow, heq]
  · rintro rfl
    obtain ⟨γ, hγ, -⟩ := Core.profExp_unique_boundary_two
    exact ⟨γ, hγ⟩

end AudUniv2
end FateV2.Error
