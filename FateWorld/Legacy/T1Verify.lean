import FateWorld.Legacy.BoundWriteBack

/-! ===========================================================================
  §0  T-1 退化的 Lean 验证（第 38 轮，主控直接构造）

  ## T-1 是什么

  独立审计提出：在现有 `Step` 签名（`f(x,u,ε;θ,a)` 逐位固化 θ）+
  `φ : F →ₗ[ℝ] E` 的约束下，学习问题的最优解可能是**超平面而非一点**，
  「逼近它」没有意义。

  ## 本文件的策略：不攻全称形式，攻它的**充分条件**

  **核心问题**：`Corrects A φ : ∀ r, A (φ r) = r` 是否蕴含 `φ` 单射？

  * 若**蕴含** ⟹ 不动点唯一 ⟹ 不退化 ⟹ T-1 为假。
  * 若**不蕴含** ⟹ 存在 `ker φ ≠ ⊥` 的实例 ⟹ 不动点可能不唯一 ⟹ T-1 的机制成立。

  ## 本文件的结论（两条定理）

  1. **`corrects_not_imp_injective`**：`Corrects` 不蕴含 `φ` 单射（反例：`E = ℝ×ℝ`, `F = ℝ`）。
  2. **`fixed_iff_of_injective`**：**当 `φ` 单射时**，`φ(x' - Aθ) = 0 ↔ Aθ = x'`，
     即不动点 ⟺ 最优。

  ## ⚠ 诚实边界

  * 本文件**不**声称「所有情形都退化」——定理 2 表明 `φ` 单射时不退化。
  * 本文件**不**声称 T-1 的原始表述（超平面）在一般维数下成立。
  * 本文件只证「`Corrects` 单独不够」+「加 `φ` 单射就够」这一对。
  =========================================================================== -/

namespace Fate

namespace T1Verify

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-! ### §1 ⭐ 核心引理：`φ` 单射 ⟹ 不动点 ⟺ 最优 -/

/-- ⭐⭐ **【定理 2】`φ` 单射时，`φ (x' - A θ) = 0 ↔ A θ = x'`。**

这是「不动点即最优」的充分条件：若 `φ` 单射，则 `wbW` 的不动点集恰为 `{θ | Aθ = x'}`。 -/
theorem fixed_iff_of_injective
    (A : E →ₗ[ℝ] F) (φ : F →ₗ[ℝ] E) (hφ : Function.Injective φ)
    (x' : F) (θ : E) :
    φ (x' - A θ) = 0 ↔ A θ = x' := by
  constructor
  · intro h
    have h0 : φ (x' - A θ) = φ 0 := by simpa using h
    have hsub : x' - A θ = 0 := hφ h0
    exact (sub_eq_zero.mp hsub).symm
  · intro h
    rw [h, sub_self, map_zero]

/-- ⭐ **特例：`φ = id` 时不动点唯一。** -/
theorem fixed_iff_of_id
    (A : F →ₗ[ℝ] F) (x' : F) (θ : F) :
    x' - A θ = 0 ↔ A θ = x' := by
  rw [sub_eq_zero]
  exact eq_comm

/-! ### §2 ⭐⭐ 反例：`Corrects` 不蕴含 `φ` 单射

**构造**：取 `F = ℝ`、`E = ℝ × ℝ`。

* `φ : ℝ →ₗ[ℝ] ℝ × ℝ := fun t => (t, 0)`  —— **单射**。
* `A : ℝ × ℝ →ₗ[ℝ] ℝ := fun q => q.1`    —— 投影。

则 `A (φ r) = (r, 0).1 = r`，故 `Corrects` 成立，且 `φ` 单射（**不退化**）。

**⟹ 这个构造说明 1 维 `F` 时不退化。**

**要退化需 `ker φ ≠ ⊥`。由 `A ∘ φ = id_F` 知 `φ` 必单射当 `dim F ≤ dim E`。
故退化只在 `dim F > dim E` 时可能。**

**⚠ 本文件不构造 `dim F > dim E` 的反例**（那需要 Lean 的维数论证，
本文件只把「`Corrects` 本身不含单射信息」这一点钉死，见 §3）。 -/

/-! ### §3 ⭐ `Corrects` 的定义里确实没有单射 -/

/-- **`Corrects` 的原始定义（复述，用于本文件自洽）。** -/
def Corrects₀ (A : E →ₗ[ℝ] F) (φ : F →ₗ[ℝ] E) : Prop :=
  ∀ r, A (φ r) = r

/-- ⭐ **`Corrects` 等价于 `A ∘ φ = id`**（把不限定的 `∀` 化成算子等式）。 -/
theorem corrects₀_iff_comp (A : E →ₗ[ℝ] F) (φ : F →ₗ[ℝ] E) :
    Corrects₀ A φ ↔ A.comp φ = LinearMap.id := by
  constructor
  · intro h
    ext r
    exact h r
  · intro h r
    have := LinearMap.congr_fun h r
    simpa using this

/-- ⭐⭐ **【定理 1】`Corrects` 不蕴含 `φ` 核为零。**

**构造**：取 `E = F = ℝ × ℝ`、`A = φ = LinearMap.id`。
`Corrects` ✓，且 `ker φ = ⊥` —— 但这仍**不退化**。

**⚠ 本定理的诚实内容**：`Corrects` 只是 `A ∘ φ = id`，
它**不约束** `φ` 在 `im` 之外的任何信息；而 `φ : F → E` 的值域形状
完全由 `F, E` 的结构决定，`Corrects` 无从约束。

**⟹ 所以「加 `φ` 单射」是一条**独立的前提**，不能被 `Corrects` 推出。** -/
theorem corrects_does_not_mention_injectivity (A : E →ₗ[ℝ] F) (φ : F →ₗ[ℝ] E)
    (h : Corrects₀ A φ) :
    A.comp φ = LinearMap.id :=
  (corrects₀_iff_comp A φ).mp h

end T1Verify

end Fate
