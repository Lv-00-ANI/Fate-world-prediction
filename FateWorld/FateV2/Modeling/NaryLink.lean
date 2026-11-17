import FateWorld.FateV2.Modeling.NaryCancel
import FateWorld.FateV2.Modeling.NaryFiberDecomp
import FateWorld.FateV2.Modeling.NaryMargSum
import FateWorld.FateV2.Modeling.NaryFinalBridge
import FateWorld.FateV2.Modeling.NaryBridge
/-!
  # Modeling · NaryLink

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NaryLink.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NaryCancel, NaryFiberDecomp, NaryMargSum, NaryFinalBridge, NaryBridge
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenNLink  set identity for the joint set (round 201)

  Agent P1's verification of the bridge chain identified the connection lemma

  **(c)** `(xs, z) in iInter i, coordSet i (S i)  <=>  forall i, xs i in S i`

  which turns the measure-theoretic sum
  `sum w, [(w, z) in iInter i, coordSet i (S i)] * p (w, z)`
  (obtained from `real_eq_sum_of_fiber`) into the indicator sum
  `sum xs, [forall i, xs i in S i] * p (xs, z)`
  that `product_factorize` (round 198) consumes.

  Both the `Set` and the `Finset`-indexed versions are recorded.
  =========================================================================== -/

namespace FateV2.Modeling.GenN

open MeasureTheory ProbabilityTheory

section SetIdentity

variable {ι : Type*}
variable {fam : ι → Type*}
variable {γ : Type*}

/-- ⭐⭐⭐ **(c)** the membership identity for the joint set.

`(xs, z) in iInter i, coordSet i (S i)  <=>  forall i, xs i in S i`. -/
theorem mem_iInter_coordSet {S : ∀ i, Set (fam i)} (xs : ∀ j, fam j) (z : γ) :
    ((xs, z) ∈ (⋂ i, coordSet i (S i) : Set ((∀ j, fam j) × γ)))
      ↔ ∀ i, xs i ∈ S i := by
  simp [coordSet, Set.mem_iInter]

end SetIdentity

section FinsetIdentity

variable {ι : Type*} [Fintype ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*}

omit [Fintype ι] [∀ i, Fintype (fam i)] in
/-- ⭐ **(c')** the `Finset`-indexed membership. -/
theorem mem_iInter_coordSet_finset {Sf : ∀ i, Finset (fam i)} (xs : ∀ j, fam j) (z : γ) :
    ((xs, z) ∈ (⋂ i, coordSet i ((Sf i : Set (fam i))) : Set ((∀ j, fam j) × γ)))
      ↔ ∀ i, xs i ∈ Sf i := by
  rw [mem_iInter_coordSet]
  constructor
  · intro h i; exact Finset.mem_coe.mpr (h i)
  · intro h i; exact Finset.mem_coe.mp (h i)

end FinsetIdentity

end FateV2.Modeling.GenN
