import FateWorld.FateV2.Predict.G1ParentNonDescendant
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
  # Predict · ViewTenThreeBlock

  ## 迁移登记
  - 来源：`FateWorld/Legacy/ViewTenThreeBlock.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：G1ParentNonDescendant
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/ViewTenThreeBlock` —— **视角 10：三层分解策略（TBF）**
  =========================================================================== -/

namespace FateV2.Predict.ViewTen

open FateV2.Modeling

open Finset Fate.DAGFactorization FateV2.Modeling.Graph.DAG

variable {V : Type} [DecidableEq V] [Fintype V]
variable {α : Type} [Fintype α] [DecidableEq α]

/-! ## §1 图论输入（零缺口） -/

/-- **V10-G1**：非后代的前驱也是非后代。 -/
theorem pa_subset_nonDesc_of_mem {G : FateV2.Modeling.Graph.DAG V} {v w : V}
    (hw : w ∈ G.nonDescendants v) : pa G w ⊆ G.nonDescendants v := by
  intro u hu
  rw [mem_pa] at hu
  rw [nonDescendants, Finset.mem_filter]
  refine ⟨Finset.mem_univ u, ?_, ?_⟩
  · intro hanc
    exact (Finset.mem_filter.mp hw).2.1 (isAncestor_trans G hanc (isAncestor.edge hu))
  · intro huv; subst huv
    exact (Finset.mem_filter.mp hw).2.1 (isAncestor.edge (G := G) hu)

/-- **V10-G2**：`v` 不在自己的非后代集中。 -/
theorem not_mem_nonDesc_self (G : FateV2.Modeling.Graph.DAG V) (v : V) : v ∉ G.nonDescendants v := by
  rw [nonDescendants, Finset.mem_filter]
  intro h; exact h.2.2 rfl

/-- **V10-G3**：`pa v ⊆ nd v`（引用已证的 G1 判定）。 -/
theorem pa_subset_nonDesc (G : FateV2.Modeling.Graph.DAG V) (v : V) : pa G v ⊆ G.nonDescendants v :=
  FateV2.Predict.FactorRecursionRouteB.pa_subset_nonDescendants G v

/-- **V10-G4**：`v ∉ pa v`。 -/
theorem not_mem_pa_self' (G : FateV2.Modeling.Graph.DAG V) (v : V) : v ∉ pa G v := not_mem_pa_self G v

end FateV2.Predict.ViewTen

namespace FateV2.Predict.ViewTen

open Finset Fate.DAGFactorization FateV2.Modeling.Graph.DAG

variable {V : Type} [DecidableEq V] [Fintype V]
variable {α : Type} [Fintype α] [DecidableEq α]

/-! ## §2 `mass` 的自由坐标重索引（视角 10 的载体） -/

/-- **V10-R1**：`mass S p x` 的纤维等价于「自由坐标上的函数」。 -/
def fiberEquiv (S : Finset V) (x : V → α) :
    {w : V → α // ∀ u ∈ S, w u = x u} ≃ ({u : V // u ∉ S} → α) where
  toFun w := fun u => w.1 u.1
  invFun f := ⟨fun u => if h : u ∈ S then x u else f ⟨u, h⟩, by
    intro u hu; simp [dif_pos hu]⟩
  left_inv w := by
    ext u; dsimp only
    by_cases hu : u ∈ S
    · simp [hu, w.2 u hu]
    · simp [hu]
  right_inv f := by funext u; dsimp only; simp [u.2]

/-- **V10-R2**：`mass` 写成自由坐标上的求和（**非嵌套**，视角 10 的基础）。 -/
theorem mass_as_sum (S : Finset V) (p : (V → α) → ℝ) (x : V → α) :
    mass S p x = ∑ f : {u : V // u ∉ S} → α,
      p (fun u => if h : u ∈ S then x u else f ⟨u, h⟩) := by
  have h1 : mass S p x = ∑ w : {w : V → α // ∀ u ∈ S, w u = x u}, p w.1 := by
    unfold mass; rw [← Finset.sum_filter]; exact Finset.sum_subtype _ (by intro w; simp) _
  rw [h1]
  exact Fintype.sum_equiv (fiberEquiv S x) _ _ (fun w => by
    dsimp [fiberEquiv]; congr 1; funext u
    by_cases hu : u ∈ S
    · simp [hu, w.2 u hu]
    · simp [hu])

/-! ## §3 因子提出律（**唯一**的"塔替代品"） -/

/-- **V10-P1**：若 `f` 只读 `S`，则 `mass S (f·g) = f x · mass S g`。

**这是视角 10 取代 mass 塔的唯一工具**：它只是 `Finset.mul_sum` + 纤维上 `f` 为常数。 -/
theorem mass_mul_of_dependsOn (S : Finset V) (f g : (V → α) → ℝ)
    (hf : ∀ x y : V → α, (∀ u ∈ S, x u = y u) → f x = f y) (x : V → α) :
    mass S (fun w => f w * g w) x = f x * mass S g x := by
  unfold mass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  show (if ∀ u ∈ S, w u = x u then f w * g w else 0)
      = f x * (if ∀ u ∈ S, w u = x u then g w else 0)
  by_cases hw : ∀ u ∈ S, w u = x u
  · rw [if_pos hw, if_pos hw, hf w x hw]
  · rw [if_neg hw, if_neg hw, mul_zero]

/-- **V10-P2**：只读 `S` 的密度，其 `mass S` = `|α|^(|V|-|S|) · f x`。 -/
theorem mass_of_dependsOn (S : Finset V) (f : (V → α) → ℝ)
    (hf : ∀ x y : V → α, (∀ u ∈ S, x u = y u) → f x = f y) (x : V → α) :
    mass S f x = (Fintype.card α : ℝ) ^ (Fintype.card V - S.card) * f x := by
  rw [mass_as_sum]
  rw [Finset.sum_congr rfl (fun g _ => hf _ x (by
    intro u hu; simp [dif_pos hu]))]
  have hc : Fintype.card { u : V // u ∉ S } = Fintype.card V - S.card := by
    rw [Fintype.card_subtype_compl]; simp
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fun, hc]
  push_cast
  ring

end FateV2.Predict.ViewTen

namespace FateV2.Predict.ViewTen

open Finset Fate.DAGFactorization FateV2.Modeling.Graph.DAG

variable {V : Type} [DecidableEq V] [Fintype V]
variable {α : Type} [Fintype α] [DecidableEq α]

/-! ## §4 三层块：`A`（读 `pa`）、`B`（读 `nd`）、`C`（其余） -/

/-- **V10-B-A**：`v` 的因子块（读 `pa v`）。 -/
noncomputable def blockA {G : FateV2.Modeling.Graph.DAG V} (φ : V → (V → α) → ℝ)
    (v : V) (x : V → α) : ℝ := φ v x

/-- **V10-B-B**：非后代因子块（读 `nd v`，**不读 `v`**）。 -/
noncomputable def blockB {G : FateV2.Modeling.Graph.DAG V} (φ : V → (V → α) → ℝ)
    (v : V) (x : V → α) : ℝ := ∏ u ∈ G.nonDescendants v, φ u x

/-- **V10-B-C**：其余因子块（严格后代）。 -/
noncomputable def blockC {G : FateV2.Modeling.Graph.DAG V} (φ : V → (V → α) → ℝ)
    (v : V) (x : V → α) : ℝ := ∏ u ∈ (Finset.univ \ insert v (G.nonDescendants v)), φ u x

/-- **V10-B1**：`p = A · B · C`（按 `v`/`nd`/`其余` 三分坐标）。 -/
theorem prod_three_split {G : FateV2.Modeling.Graph.DAG V} (φ : V → (V → α) → ℝ)
    (v : V) (x : V → α) :
    (∏ u, φ u x) = blockA (G := G) φ v x * blockB (G := G) φ v x
      * blockC (G := G) φ v x := by
  unfold blockA blockB blockC
  have hv : v ∉ G.nonDescendants v := not_mem_nonDesc_self G v
  have hdisj : Disjoint (insert v (G.nonDescendants v))
      (Finset.univ \ insert v (G.nonDescendants v)) := Finset.disjoint_sdiff
  have hunion : insert v (G.nonDescendants v)
      ∪ (Finset.univ \ insert v (G.nonDescendants v)) = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hC : (insert v (G.nonDescendants v)
      ∪ (Finset.univ \ insert v (G.nonDescendants v))) \ insert v (G.nonDescendants v)
      = Finset.univ \ insert v (G.nonDescendants v) := by
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  rw [← hunion, Finset.prod_union hdisj, Finset.prod_insert hv, hC]

/-- **V10-B2**：`blockB` 只读 `nd v`。 -/
theorem blockB_dependsOn {G : FateV2.Modeling.Graph.DAG V} {φ : V → (V → α) → ℝ}
    (hφ : ∀ v x y, (∀ u ∈ pa G v, x u = y u) → φ v x = φ v y)
    (v : V) {x y : V → α} (hxy : ∀ u ∈ G.nonDescendants v, x u = y u) :
    blockB (G := G) φ v x = blockB (G := G) φ v y := by
  unfold blockB
  refine Finset.prod_congr rfl (fun u hu => ?_)
  exact hφ u x y (fun w hw => hxy w (pa_subset_nonDesc_of_mem hu hw))

/-- **V10-B3**：`blockA` 只读 `pa v`。 -/
theorem blockA_dependsOn {G : FateV2.Modeling.Graph.DAG V} {φ : V → (V → α) → ℝ}
    (hφ : ∀ v x y, (∀ u ∈ pa G v, x u = y u) → φ v x = φ v y)
    (v : V) {x y : V → α} (hxy : ∀ u ∈ pa G v, x u = y u) :
    blockA (G := G) φ v x = blockA (G := G) φ v y := hφ v x y hxy

end FateV2.Predict.ViewTen
