import FateWorld.FateV2.Modeling.SCM
import Mathlib.Tactic

/-!
  # Modeling · Sigma — σ 的两条腿

  ## 迁移登记
  - 来源：新写（原为空壳占位）
  - 动作：C 重写
  - 对应环节：F1-13（σ 的来源）、F7-02（误差剖面入口）
  - 依赖裁决：**D-007**（数据数学构造）、**D-008**（建模层与裁决 K）、
              **D-013**（一体化系统）、**D-014**（模型 = SCM）、**D-019**（自由度最大化）
  - 改动：从空壳补成实现。`Model.sigmaModel` 已给出接口，本模块补上
          **「σ 是什么」的三条腿及其相互关系**，并把「被 σ 锁死」这件事形式化。
  - 状态：已编译

  ## 三条腿（09-总设计 §4.4）

  | 腿 | 定义 | 可证性 |
  |---|---|---|
  | **数学腿** | `σ_emp := inf E_W` | ✅ **可证**（定理 3.2：满足拟合边界的 σ 必然 = inf E_W） |
  | **模型腿** | `σ_model := spread (induce …)` | ✅ **可算**（外生律经 F 与投影推前） |
  | **经验腿** | `σ_emp ≈ σ_model` | ❌ **不可证，须登记为经验假设** |

  ## 本模块钉住什么

  1. **σ 不是自由参数**：`IsFitBoundary` 唯一确定它（`sigma_locked`）
  2. **两条腿可以不等**：模型腿与数学腿一致是**经验命题**，不是定理
     （`empirical_leg_is_assumption`）
  3. **`spread` 的良定义性**：非负性是唯一的硬要求（`sigmaModel_nonneg`）

  ## 诚实边界

  「`σ_emp = inf E_W`」的完整证明（定理 3.2）在 `Error/FitBoundary.lean`（B 类迁移）里。
  本模块**不重复证明它**，只把它作为**接口契约**引用，并补上两条腿的分离性。
-/

namespace FateV2.Modeling

open MeasureTheory

universe u

/-! ## §1 · 误差剖面与 σ 的关系（数学腿的契约） -/

/-- **误差剖面的形状**：给定一个模型配置 `γ`，返回其误差 `b(γ) + v(γ)`。

    这里不预设 `b`/`v` 的分解方式——那是 `Error` 层的实现细节（D-019）。
    本模块只需要「每个配置对应一个误差值」这一层。 -/
abbrev ErrProfileFun : Type := ℝ → ℝ

/-- **拟合边界判据**（裁决 K 的精确形式，`08-拟合边界` 定义 2.3）。

    用一个配置 `γ` 与一个阈值 `σ` 表述：

    * `E γ = σ`      —— 该配置恰好落在边界上
    * `∀ γ', σ ≤ E γ'` —— 没有配置能比它更好

    即 `σ` **恰是**误差的下确界，且被某个配置**取到**。 -/
def IsFitBoundary (E : ErrProfileFun) (σ : ℝ) (γ : ℝ) : Prop :=
  E γ = σ ∧ ∀ γ', σ ≤ E γ'

/-! ## §2 · σ 被锁死 -/

section Locked

/-- **σ 不是自由参数**：同一剖面下，任何两个满足拟合边界的 `σ` 必然相等。

    这是「裁决 K 把 σ 钉死」的核心形式：
    **拟合边界一旦成立，σ 就被唯一确定**，
    不存在「调一调 σ 让误差更容易通过」的空间。

    对应 `09-总设计` §9.2：`IsFitBoundary(W,σ,γ) ⟹ σ = inf E_W`。 -/
theorem sigma_locked {E : ErrProfileFun} {σ₁ σ₂ γ₁ γ₂ : ℝ}
    (h₁ : IsFitBoundary E σ₁ γ₁) (h₂ : IsFitBoundary E σ₂ γ₂) : σ₁ = σ₂ := by
  obtain ⟨e₁, lo₁⟩ := h₁
  obtain ⟨e₂, lo₂⟩ := h₂
  -- σ₁ ≤ E γ₂ = σ₂ 且 σ₂ ≤ E γ₁ = σ₁
  have hle₁ : σ₁ ≤ σ₂ := by rw [← e₂]; exact lo₁ γ₂
  have hle₂ : σ₂ ≤ σ₁ := by rw [← e₁]; exact lo₂ γ₁
  exact le_antisymm hle₁ hle₂

/-- **边界值即下确界**：满足拟合边界的 `σ` 就是剖面的下确界。

    本项目的 σ 定义不是「一个目标值」，而是**剖面的内在属性**。 -/
theorem sigma_is_sInf {E : ErrProfileFun} {σ γ : ℝ}
    (h : IsFitBoundary E σ γ) (hnonneg : 0 ≤ σ) : σ = sInf (Set.range E) := by
  obtain ⟨e, lo⟩ := h
  apply le_antisymm
  · -- σ ≤ sInf：σ 是像的下界，且 sInf 是最大下界
    apply le_csInf ⟨E γ, Set.mem_range_self γ⟩
    rintro b ⟨γ', rfl⟩
    exact lo γ'
  · -- sInf ≤ σ：σ 本身在像里
    apply csInf_le
    · -- 像有下界：任意像值都 ≥ σ ≥ 0
      exact ⟨0, by rintro _ ⟨γ', rfl⟩; exact le_trans hnonneg (lo γ')⟩
    · exact ⟨γ, e⟩

end Locked

/-! ## §3 · 模型腿：σ_model 的良定义性 -/

section ModelLeg

/-- **σ_model 的硬要求**：`spread` 必须非负。

    这不是可以选的——`spread` 是「离散度」，负的离散度无意义。
    把这一条显式写成假设，是为了让「选了方差 / 分位数 / Wasserstein」
    这些实现（D-015 策略③）都**必须**满足它，而不是各自心照不宣。 -/
def IsSpread (spread : Noise → ℝ) : Prop := ∀ N, 0 ≤ spread N

variable {Val V E : Type u}

/-- **模型腿非负**：若 `spread` 非负，则 `σ_model` 非负。 -/
theorem sigmaModel_nonneg {Z : Type u}
    (M : Model Val V E Noise)
    (eval : E → Model.Endo Val V) (project : Model.Endo Val V → Z)
    (push : Noise → (E → Z) → Noise) (spread : Noise → ℝ)
    (hpos : IsSpread spread) :
    0 ≤ M.sigmaModel eval project push spread :=
  hpos _

/-- **σ_model 的推前形式**：它只依赖 `induce` 的**结果**，不依赖 `eval`/`project` 的细节。

    这条看起来平凡，但它是「σ 可以逐层拆解」的前提：
    **不同 `(eval, project)` 组合只要 `induce` 结果相同，σ 就相同**。 -/
theorem sigmaModel_congr {Z : Type u}
    (M : Model Val V E Noise)
    (eval₁ eval₂ : E → Model.Endo Val V)
    (project₁ project₂ : Model.Endo Val V → Z)
    (push₁ push₂ : Noise → (E → Z) → Noise)
    (spread : Noise → ℝ)
    (h : M.induce eval₁ project₁ push₁ = M.induce eval₂ project₂ push₂) :
    M.sigmaModel eval₁ project₁ push₁ spread =
      M.sigmaModel eval₂ project₂ push₂ spread := by
  unfold Model.sigmaModel
  rw [h]

end ModelLeg

/-! ## §4 · 经验腿：两条腿相等是**假设**，不是定理 -/

section EmpiricalLeg

/-- **经验桥**：模型的 σ 与经验估出的 σ 一致。

    ⚠ **这是一条 `Prop` 定义，不是定理。** 它的成立与否必须由数据判定
    （饱和 / 差分估计 / 交叉验证，三者都各有失效条件，见 `08-拟合边界`）。

    `09-总设计` §4.4 的原文：
    > 「**`σ_emp ≈ σ_model`」本身是一条可检验的经验命题。**

    本定义把这句话变成一个**可被引用、可被反驳**的命题，
    而不是散落在文档里的一句话。 -/
def SigmaBridge (σ_emp σ_model : ℝ) : Prop := σ_emp = σ_model

/-- **经验腿不能被证明**：`SigmaBridge` 不是一个恒真命题。

    构造两个具体的 `σ`，使桥不成立 ⟹ 桥不是"总是真"的。
    这意味着**任何声称「σ_emp 自动等于 σ_model」的论证都是错的**，
    必须显式引用经验假设（或实测数据）。 -/
theorem sigmaBridge_not_trivially_true : ¬ ∀ a b : ℝ, SigmaBridge a b := by
  intro h
  have : (0 : ℝ) = 1 := h 0 1
  norm_num at this

/-- 桥成立时，两条腿可互换（这是它唯一的用途）。 -/
theorem sigmaBridge_transfer {σ_emp σ_model : ℝ}
    (h : SigmaBridge σ_emp σ_model) : σ_emp = σ_model := h

end EmpiricalLeg

/-! ## §5 · 与 `Model.induce` 的接线 -/

section Wiring

variable {Val V E : Type u}

/-- **σ_model 只是 `spread ∘ induce`**：没有额外的魔法。

    这条把 §3 的抽象接口与 `Model` 里的实现钉在一起，
    防止将来有人把 σ 算成别的东西却仍叫它 `sigmaModel`。 -/
theorem sigmaModel_eq_spread_induce {Z : Type u}
    (M : Model Val V E Noise)
    (eval : E → Model.Endo Val V) (project : Model.Endo Val V → Z)
    (push : Noise → (E → Z) → Noise) (spread : Noise → ℝ) :
    M.sigmaModel eval project push spread = spread (M.induce eval project push) := rfl

end Wiring

end FateV2.Modeling
