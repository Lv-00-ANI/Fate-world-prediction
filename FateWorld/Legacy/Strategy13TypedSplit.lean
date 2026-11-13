import FateWorld.Legacy.DAGFactorization
import FateWorld.Legacy.FactorMarkov
import FateWorld.Legacy.View20GraphToProb
import Mathlib.Tactic

/-!
# 视角 13：『图 ⟹ 概率』桥的第 13 种策略 —— 三元划分因子分解（typed split）

数学说明见 `STRATEGY13_TYPED_SPLIT.md`。
-/

namespace Fate.Strategy13

open Finset
open Causalean.Graph

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false

/-! ## §1 可分离划分 -/

/-- **D13.1（`Disjoinable`）：可分离划分。** -/
def Disjoinable (G : Causalean.Graph.DAG V) (X Y Z : Finset V) : Prop :=
  ∃ A : Finset V, A ∩ Y = ∅ ∧ X ⊆ A ∧ ∀ v ∈ A, G.parents v ⊆ A ∪ Z

theorem disjoint_left_of_disjoinable {G : Causalean.Graph.DAG V} {X Y Z : Finset V}
    (h : Disjoinable G X Y Z) : Disjoint X Y := by
  obtain ⟨A, hAY, hXA, -⟩ := h
  rw [Finset.disjoint_left]
  intro v hvX hvY
  have hvA : v ∈ A := hXA hvX
  exact (Finset.eq_empty_iff_forall_notMem.mp hAY) v (Finset.mem_inter.mpr ⟨hvA, hvY⟩)

/-! ## §2 图做的功：`A` 内因子只读 `A ∪ Z` -/

variable {G : Causalean.Graph.DAG V}

theorem localTo_eq_of_eq_on_AZ {φ : V → (V → α) → ℝ}
    (hloc : Fate.FactorMarkov.LocalTo G φ)
    {A Z : Finset V} (hdis : ∀ v ∈ A, G.parents v ⊆ A ∪ Z)
    {x y : V → α} (hxy : ∀ u ∈ A ∪ Z, x u = y u)
    {v : V} (hv : v ∈ A) : φ v x = φ v y := by
  refine hloc v x y fun u hu => ?_
  rcases hu with rfl | hu
  · exact hxy u (Finset.mem_union_left _ hv)
  · exact hxy u (hdis v hv hu)

/-! ## §3 纯代数：块拆分 -/

theorem prod_split_block (φ : V → (V → α) → ℝ) (A : Finset V) (x : V → α) :
    (∏ v, φ v x) = (∏ v ∈ A, φ v x) * (∏ v ∈ (univ \ A), φ v x) :=
  (Finset.prod_mul_prod_compl A (fun v => φ v x)).symm

/-- **D13.3（`NoInflow`）：`A` 的补集不「回流」`A`。**

`Aᶜ` 中每个点的父代都仍在 `Aᶜ` 里 ⟹ `Aᶜ` 内的因子不读 `A` 上的坐标。 -/
def NoInflow (G : Causalean.Graph.DAG V) (A : Finset V) : Prop :=
  ∀ v : V, v ∉ A → G.parents v ⊆ (univ \ A)

/-! ## §4 主定理 -/

/-- **T13.1（`typed_split`）：联合律按块 `A` 分裂（零缺口）。**

1. `F := ∏_{v∈A} φ v` **只读 `A ∪ Z`**（⭐ 图做功：`pa(A) ⊆ A ∪ Z`）；
2. `G₂ := ∏_{v∉A} φ v` **只读 `Aᶜ`**（由 `NoInflow`）；
3. `p = F · G₂`（纯代数）。

**⚠ 不用塔性质**：全程无 `mass`，更无 `mass ∘ mass`。 -/
theorem typed_split {φ : V → (V → α) → ℝ}
    (hloc : Fate.FactorMarkov.LocalTo G φ)
    {A Z : Finset V} (hdis : ∀ v ∈ A, G.parents v ⊆ A ∪ Z)
    (hA : NoInflow G A) :
    (∀ x y : V → α, (∀ u ∈ A ∪ Z, x u = y u) →
      (∏ v ∈ A, φ v x) = (∏ v ∈ A, φ v y)) ∧
    (∀ x y : V → α, (∀ u, u ∉ A → x u = y u) →
      (∏ v ∈ (univ \ A), φ v x) = (∏ v ∈ (univ \ A), φ v y)) ∧
    (∀ x, (∏ v, φ v x) = (∏ v ∈ A, φ v x) * (∏ v ∈ (univ \ A), φ v x)) := by
  refine ⟨?_, ?_, prod_split_block φ A⟩
  · intro x y hxy
    exact Finset.prod_congr rfl fun v hv => localTo_eq_of_eq_on_AZ hloc hdis hxy hv
  · intro x y hxy
    refine Finset.prod_congr rfl fun v hv => ?_
    have hvA : v ∉ A := (Finset.mem_sdiff.mp hv).2
    refine hloc v x y fun u hu => ?_
    rcases hu with rfl | hu
    · exact hxy u hvA
    · exact hxy u (Finset.mem_sdiff.mp (hA v hvA hu)).2

end Fate.Strategy13
