import FateWorld.FateV2.Modeling.SumSeparation
/-!
  # Modeling · SumMulSep

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SumMulSep.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：SumSeparation
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  乘积分离律：`Σ_w f w * g w = (Σ f)(Σ g)`（无尾块下）

  ## 背景

  `Fate/SumSeparation.lean` 已证：
  ```lean
  theorem arrowEquivOfSplit : Disjoint X Y → X ∪ Y = univ → (V → α) ≃ (X → α) × (Y → α)
  ```
  **但乘积分离律本体未证**（当时登记为缺口）。

  **⟹ 它是主定理 C 配平的最后一块必需材料**（`mass ∅ p` 的乘积形式）。

  ## 本节做什么：先给「影子函数」这个技术构件

  `f : (V → α) → ℝ` 只读 `X` 时，定义它在 `(X → α)` 上的**影子**：

  ```lean
  noncomputable def shadowOn (f) (hf : f 只读 X) (a : X → α) : ℝ :=
    f (extend a)      -- extend a 是任一在 X 上与 a 一致的 V → α
  ```

  **⟹ 关键是 `shadowOn` 与 `f` 在任意「在 X 上与 a 一致」的 `w` 上相等。**

  ## 诚实边界

  * **本节只给 `shadowOn` 这个构件与它的一致性引理**，
    分离律本体的换元（`Fintype.sum_equiv` + `sum_prod_type`）**留待下一步**。
  * **`X` 之外用 `Classical.arbitrary`** —— 这是非构造的，但 `shadowOn` 的值
    与具体选取无关（由 `hf` 保证），故良定义。
  =========================================================================== -/

namespace FateV2.Modeling.GraphToProbView7

open Finset
open FateV2.Error

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

/-! ### §0.1 ⭐ 延拓算子 -/

/-- ⭐ **把 `X → α` 延拓到 `V → α`**（`X` 之外取 `Classical.arbitrary`）。 -/
noncomputable def extendTo (X : Finset V) (a : X → α) (v : V) : α :=
  if h : v ∈ X then a ⟨v, h⟩ else Classical.arbitrary α

/-- ⭐ **延拓在 `X` 上与 `a` 一致**。 -/
theorem extendTo_mem {X : Finset V} (a : X → α) {u : V} (hu : u ∈ X) :
    extendTo X a u = a ⟨u, hu⟩ := by
  unfold extendTo
  rw [dif_pos hu]

/-- ⭐ **延拓与任意在 `X` 上一致的 `w` 在 `X` 上一致**。 -/
theorem extendTo_agree {X : Finset V} (a : X → α) {w : V → α}
    (hw : ∀ u : X, w u = a u) :
    ∀ u ∈ X, w u = extendTo X a u := by
  intro u hu
  rw [extendTo_mem a hu]
  exact hw ⟨u, hu⟩

/-! ### §0.2 ⭐ 影子函数 -/

/-- ⭐ **影子**：`f` 只读 `X` 时，在 `X → α` 上的取值。

**⟹ 与 `extendTo` 的选取无关（由 `hf` 保证）。** -/
noncomputable def shadowOn {X : Finset V} (f : (V → α) → ℝ)
    (a : X → α) : ℝ :=
  f (extendTo X a)

/-! ### §0.3 ⭐⭐ 影子与 f 一致 -/

/-- ⭐ **影子与 `f` 一致**：若 `w` 与 `a` 在 `X` 上一致，则 `f w = shadowOn f a`。

**⟹ 这保证 `shadowOn` 与 `extendTo` 的具体选取无关。** -/
theorem shadowOn_congr {X : Finset V} {f : (V → α) → ℝ}
    (hf : ∀ w w', (∀ u ∈ X, w u = w' u) → f w = f w') (w : V → α)
    (a : X → α) (hw : ∀ u : X, w u = a u) :
    f w = shadowOn f a := by
  unfold shadowOn
  refine hf w _ ?_
  intro u hu
  rw [hw ⟨u, hu⟩, extendTo_mem a hu]

end FateV2.Modeling.GraphToProbView7
