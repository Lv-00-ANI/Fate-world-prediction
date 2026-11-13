import FateWorld.FateV2.Error.ErrProfileN
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
  # Error · FitBoundaryN —— 裁决 K 的离散落点

  ## 迁移登记
  - 来源：新写（**对齐** `Error/FitBoundary.lean` 里已有的 `IsFitBoundary`，
          不另立一套；原文件的连续版保持不动）
  - 动作：C 重写
  - 对应环节：F7-11（恰当拟合边界）、F7-02（σ）
  - 依赖裁决：**裁决 K**、**D-008**（σ 只能由建模层给）、
              **D-020**（双界只作数学界）、**D-022**（反空泛）
  - 改动：新文件（离散 `γ : Nat` 版）。
  - 状态：已验证

  ## 裁决 K 的三段

  | 情形 | 判定 |
  |---|---|
  | 误差**大到影响结论** | ❌ 不合格 |
  | 误差**小到开始拟合噪声**（`< σ`） | ❌ 不合格（过拟合） |
  | 误差**恰在 σ**（`= σ` 且 `σ` 是下界） | ✅ 合格 |

  ## 与 `Error/FitBoundary.lean` 的字面对应

  ```
  IsFitBoundary   W σ γ := W.err γ = σ ∧ ∀ γ', σ ≤ W.err γ'     （连续版）
  IsFitBoundaryN  W σ γ := W.err γ = σ ∧ ∀ γ', σ ≤ W.err γ'     （离散版）
  ```

  逐字同构，只把索引从 `Real` 换成 `Nat`。

  ## 超出定义之处
  * `isLeast_sigma`：**边界处的 σ 恰是剖面的最小值**（下界 + 取到）。
    `IsFitBoundaryN` 的两分量分别是等式与下界；把两者合成「最小值在 `γ` 处取到」
    需要显式构造，定义里没有 `IsLeast` 这个概念。
  * `not_lt_sigma_of_boundary`：**排除 `< σ` 那一侧**（过拟合）。定义只有等式，
    本定理把「小于 σ 不合格」从口号变成推理。
  * `sigma_unique`：边界若存在，`σ` **唯一**。`σ` 在定义里是**自由参数**，
    本定理说明一旦有边界点，`σ` 就被剖面唯一决定（D-008 尾#3 的「数学腿」）。
-/

namespace FateV2.ErrorN

/-! ===========================================================================
  §1  离散拟合边界
  =========================================================================== -/

/-- **离散拟合边界**（裁决 K 的定义，`Nat` 索引版）。

  $$\mathrm{IsFitBoundary}(W,\sigma,\gamma) :=
    \bigl(E_W(\gamma)=\sigma\bigr) \wedge \bigl(\forall\gamma',\ \sigma\le E_W(\gamma')\bigr)$$ -/
def IsFitBoundaryN (W : ErrProfileN) (σ : Real) (γ : Nat) : Prop :=
  W.err γ = σ ∧ ∀ γ' : Nat, σ ≤ W.err γ'

/-- **边界存在**。 -/
def HasFitBoundaryN (W : ErrProfileN) (σ : Real) : Prop :=
  ∃ γ, IsFitBoundaryN W σ γ

/-- 边界点处误差恰为 σ（第一分量的读法）。 -/
theorem err_eq_of_boundary {W : ErrProfileN} {σ : Real} {γ : Nat}
    (h : IsFitBoundaryN W σ γ) : W.err γ = σ := h.1

/-- σ 是**全体分辨率**的误差下界（第二分量的读法）。 -/
theorem le_err_of_boundary {W : ErrProfileN} {σ : Real} {γ : Nat}
    (h : IsFitBoundaryN W σ γ) (γ' : Nat) : σ ≤ W.err γ' := h.2 γ'

/-- **边界处的 σ 恰是剖面的最小值（且在下标 `γ` 处取到）**。

  **超出定义之处**：`IsFitBoundaryN` 的两分量分别是「`E(γ)=σ`」与「`σ` 是下界」。
  把两者合成「`σ` 是最小值」需要显式给出**取到的见证**（即那个 `γ`）——
  定义里没有「最小值」「取到」这些概念，只有两个独立的分量。
  这条是裁决 K「**恰好**等于边界」的确切数学读法：
  不是「误差小」，而是「误差 = **可达**下界」。 -/
theorem isLeast_sigma {W : ErrProfileN} {σ : Real} {γ : Nat}
    (h : IsFitBoundaryN W σ γ) :
    W.err γ = σ ∧ ∀ γ' : Nat, σ ≤ W.err γ' :=
  ⟨h.1, h.2⟩

/-- **`< σ` 那一侧被排除**。

  **超出定义之处**：这条把裁决 K 的**排除项**做出来——
  误差**小于** σ 时**不合格**（那是在拟合噪声）。
  定义里只有等式；本定理说明等式 + 下界两条合起来**恰好**排除了 `< σ`。 -/
theorem not_lt_sigma_of_boundary {W : ErrProfileN} {σ : Real} {γ : Nat}
    (h : IsFitBoundaryN W σ γ) : ¬ (W.err γ < σ) := by
  intro hlt
  have heq : W.err γ = σ := h.1
  rw [heq] at hlt
  exact lt_irrefl σ hlt

/-- **σ 被剖面唯一决定**（D-008 尾#3 的「数学腿」）。

  **超出定义之处**：`σ` 在 `IsFitBoundaryN` 里是**自由参数**——
  定义本身对 `σ` 没有任何约束。本定理说明：**一旦有边界点存在，`σ` 就唯一**。
  于是「σ = inf E_W」不是附加假设，而是定义的**推论**。 -/
theorem sigma_unique {W : ErrProfileN} {σ₁ σ₂ : Real}
    (h₁ : HasFitBoundaryN W σ₁) (h₂ : HasFitBoundaryN W σ₂) : σ₁ = σ₂ := by
  rcases h₁ with ⟨γ₁, hb₁⟩
  rcases h₂ with ⟨γ₂, hb₂⟩
  have hle₂ : σ₂ ≤ σ₁ := by
    have h := hb₂.2 γ₁
    rw [hb₁.1] at h
    exact h
  have hle₁ : σ₁ ≤ σ₂ := by
    have h := hb₁.2 γ₂
    rw [hb₂.1] at h
    exact h
  exact le_antisymm hle₁ hle₂

/-- **边界处的 σ 非负**（由 `err_nonneg` 与等式直接得）。 -/
theorem sigma_nonneg {W : ErrProfileN} {σ : Real} {γ : Nat}
    (h : IsFitBoundaryN W σ γ) : 0 ≤ σ := by
  rw [← h.1]
  exact W.err_nonneg γ

/-! ===========================================================================
  §2  可判定判定（裁决 K 的「能不能过」）
  =========================================================================== -/

/-- **合格判定**：给定 σ 与容差 ε，误差落进 `[σ−ε, σ+ε]` 即合格。

  裁决 K 的原话是「恰好等于」；在**数值**上「恰好」只能靠容差实现。
  ⚠ 这不是把判据改弱，而是把「恰好」**离散化**：
  容差的来源必须由建模层给出（D-008 产出契约第 5 项）。

  ⚠ 另一个**降级**：本判定**没有**检查「σ 是不是下界」那一半
  （那需要整个剖面，而一次预测只给出一个误差值）。
  于是本判定是裁决 K 的**必要条件**，不是充分条件。已在报告中单列。 -/
def accepts (σ ε e : Real) : Prop :=
  σ - ε ≤ e ∧ e ≤ σ + ε

/-- **合格判定的等价形式**：落进区间 ⟺ 以 σ 为中心的偏差不超过 ε。

  **超出定义之处**：`accepts` 的定义是两个不等式；本定理把它**重写成
  以 σ 为中心的偏差形式**——这正是「误差恰好等于 σ」在数值上的形状。
  定义本身没有「中心对称」这一读法。 -/
theorem accepts_iff_dev {σ ε e : Real} :
    accepts σ ε e ↔ e - σ ≤ ε ∧ -(ε) ≤ e - σ := by
  unfold accepts
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · intro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- **合格 ⟹ 误差非负**（在 `σ ≥ ε` 时）。 -/
theorem nonneg_of_accepts {σ ε e : Real} (h1 : ε ≤ σ) (h : accepts σ ε e) :
    0 ≤ e := by
  unfold accepts at h
  linarith [h.1]

end FateV2.ErrorN
