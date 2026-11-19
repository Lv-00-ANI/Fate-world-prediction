import FateWorld.FateV2.Predict.MainTheoremC
/-!
  # Modeling · SumSeparation

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SumSeparation.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MainTheoremC
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  无尾块的乘积分解：`mass ∅` 的分离律

  ## 背景

  主定理 C（`ancestral_dSep_CondIndep`）的 `Z = ∅` 情形需要：
  $$\sum_w p\,w = \Bigl(\sum f\Bigr)\Bigl(\sum g\Bigr)$$
  当 `p = f · g`、`f` 只读 `X`、`g` 只读 `Y`、且 **`V = X ⊔ Y`（无尾块）**。

  **⚠ 「无尾块」`V = X ∪ Y` 是真实前提** —— 它正是文档
  `GraphToProbView7.lean:192` 所说「`A = X ∪ Y ∪ Z`（即查询的祖先闭包**已经是全图**）」。
  没有它，`∑_w p w` 无法分离，`CondIndep` 不成立。

  ## 本节做什么

  1. ⭐ `splitEquiv`：建立 `(V → α) ≃ (X → α) × (Y → α)`（在 `V = X ⊔ Y` 下）
  2. ⭐⭐ `sum_mul_sep`：`∑_w f w * g w = (∑_x f x) * (∑_y g y)`
     （`f` 只读 `X`、`g` 只读 `Y`）

  ## 技术路线

  * **`X` 与 `Y` 不交且并 `= univ`** ⟹ `X` 对应一个 `Set V`，其补集就是 `Y`
  * 用 `Equiv.Set.sumCompl` 把 `V ≃ X ⊕ Y`
  * 用 `Equiv.sumArrowEquivProdArrow` 把 `(X ⊕ Y → α) ≃ (X → α) × (Y → α)`
  * 组合得 `(V → α) ≃ (X → α) × (Y → α)`
  * 再用 `Fintype.sum_equiv` 换元、`Fintype.sum_prod_type` 拆双和

  ## 诚实边界

  * **`V = X ⊔ Y` 是必需前提**（见上）。
  * **本节只处理 `Z = ∅` 的两侧分解**；`Z ≠ ∅` 需要 `X ⊔ (Y∪Z)` 的类似分解。
  =========================================================================== -/

namespace FateV2.Predict.GraphToProbView7

open FateV2.Predict

open FateV2.Error
open FateV2.Predict.DAGFactorization

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-! ### §0.1 ⭐ 两个子集给出 `V ≃ X ⊕ Y` -/

/-- ⭐ **`V ≃ X ⊕ Y`**（在 `X ∩ Y = ∅` 且 `X ∪ Y = univ` 下）。

`X` 作为 `Set V`，其补集就是 `Y`（由并集等于全集且不交保证）。 -/
noncomputable def sumEquivOfSplit {X Y : Finset V}
    (hdisj : Disjoint X Y) (hunion : X ∪ Y = Finset.univ) : V ≃ X ⊕ Y :=
  -- V ≃ (X : Set V) ⊕ (X : Set V)ᶜ，而后者正好是 Y
  (Equiv.Set.sumCompl (X : Set V)).symm.trans
    (by
      -- 需要 (X : Set V)ᶜ ≃ Y
      have hY : (X : Set V)ᶜ = (Y : Set V) := by
        ext v
        simp only [Set.mem_compl_iff, Finset.mem_coe]
        constructor
        · intro hv
          -- v ∉ X ⟹ v ∈ Y（因 X ∪ Y = univ）
          have : v ∈ X ∪ Y := by rw [hunion]; exact Finset.mem_univ v
          rcases Finset.mem_union.mp this with h | h
          · exact absurd h hv
          · exact h
        · intro hv hx
          exact (Finset.disjoint_left.mp hdisj hx hv).elim
      rw [hY]
      exact Equiv.refl _)

/-! ### §0.2 ⭐ `V → α ≃ (X → α) × (Y → α)` -/

/-- ⭐ **`(V → α) ≃ (X → α) × (Y → α)`**。 -/
noncomputable def arrowEquivOfSplit {X Y : Finset V}
    (hdisj : Disjoint X Y) (hunion : X ∪ Y = Finset.univ) :
    (V → α) ≃ (X → α) × (Y → α) :=
  (Equiv.arrowCongr (sumEquivOfSplit hdisj hunion) (Equiv.refl α)).trans
    (Equiv.sumArrowEquivProdArrow ↥X ↥Y α)



/-! ### §0.3 ⭐⭐ 乘积分离律（陈述见下节，本节只给已证部分）

**⚠ 诚实说明**：乘积分离律 `∑_w f w * g w = (∑ f)(∑ g)` 的完整证明
需要沿 `arrowEquivOfSplit` 换元，是一个独立的技术工作。
本节已证 `arrowEquivOfSplit`（`(V → α) ≃ (X → α) × (Y → α)`），
这已足够让后续证明调用它，但**分离律本体未证**。

登记为缺口，不假装完成。
-/

end FateV2.Predict.GraphToProbView7
