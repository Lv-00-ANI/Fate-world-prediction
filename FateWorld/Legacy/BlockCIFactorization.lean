import FateWorld.Legacy.BlockCIGeneralC
import FateWorld.Legacy.CondIndepGeneralNZ

/-! ===========================================================================
  §0  `BlockCI_Gap` 的完整链路

  ## 结果

  ```lean
  namespace Fate.C5h

open Finset Fate Fate.View19 Fate.DAGFactorization Fate.AncestralInheritanceRouteB

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

theorem blockCI_of_factorization (hfac) (hread) (hsplit : Split R X Y Z)
      (hXY hXZ hYZ) (hcover : X ∪ Y ∪ Z = univ) (hZX : Z ⊆ X) (G) :
      BlockCI_Gap p G X Y Z
  ```

  从**因子分解 + `Split` + `Z ⊆ X`** 直接得 `BlockCI_Gap`。

  ## 链路

  1. `condIndep_general`：`Split + 因子分解 + hcover ⟹ CondIndep p X Y Z`
  2. `blockCI_of_condIndep`（`Fate/BlockCIGeneralC.lean`）：
     `CondIndep p X Y Z + X∪Y = univ + Z ⊆ X ⟹ BlockCI_Gap p G X Y Z`
  3. 由 `Z ⊆ X` 与 `X∪Y∪Z = univ` 得 `X∪Y = univ`

  ## 诚实边界

  需要 `Z ⊆ X`（条件集被 X 包含）。这是本会话 R114 发现的
  「`dSep` 结构刻画」的一个自然特例。若无此条件，`BlockCI_Gap` 不成立
  （见 `Fate/BlockCIGeneralC.lean` 的推导：需要 `A ∪ C = A`）。
  =========================================================================== -/

-- ⭐ 完整定理：从因子分解 + Split 直接得 BlockCI_Gap（一般 C = Z 情形）
namespace Fate.C5h

open Finset Fate Fate.View19 Fate.DAGFactorization Fate.AncestralInheritanceRouteB

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

theorem blockCI_of_factorization {ψ : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : Fate.View19.ReadSet ψ R)
    (hsplit : Fate.View19.Split R X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hcover : X ∪ Y ∪ Z = Finset.univ)
    (hZX : Z ⊆ X)
    (G : Causalean.Graph.DAG V) :
    BlockCI_Gap p G X Y Z := by
  -- X ∪ Y = univ（因 X∪Y∪Z = univ 且 Z ⊆ X）
  have hXYuni : X ∪ Y = Finset.univ := by
    -- Z ⊆ X ⊆ X ∪ Y，故 (X ∪ Y) ∪ Z = X ∪ Y
    have hZsub : Z ⊆ X ∪ Y := fun u hu => Finset.mem_union.mpr (Or.inl (hZX hu))
    have hunion : (X ∪ Y) ∪ Z = X ∪ Y := Finset.union_eq_left.mpr hZsub
    -- hcover : X ∪ Y ∪ Z = univ，且 (X ∪ Y) ∪ Z 就是 X ∪ Y ∪ Z（结合律）
    rw [← hunion, hcover]
  -- CondIndep p X Y Z
  have hci := Fate.GraphToProbView7.condIndep_general ψ p hfac hread hsplit hXY hXZ hYZ hcover
  -- 用 BlockCIGeneralC
  exact Fate.C5g.blockCI_of_condIndep hXYuni hZX hci

end Fate.C5h
