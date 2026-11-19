import FateWorld.FateV2.Predict.BlockCIGeneralC
import FateWorld.FateV2.Modeling.CondIndepGeneralNZ
/-!
  # Predict · BlockCIFactorization

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BlockCIFactorization.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BlockCIGeneralC, CondIndepGeneralNZ
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `BlockCI_Gap` 的完整链路

  ## 结果

  ```lean
  namespace FateV2.Predict.C5h

open Finset FateV2.Error FateV2.Predict.View19 FateV2.Predict.DAGFactorization FateV2.Predict.AncestralInheritanceRouteB

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
namespace FateV2.Predict.C5h

open FateV2.Modeling

open Finset FateV2.Error FateV2.Predict.View19 FateV2.Predict.DAGFactorization FateV2.Predict.AncestralInheritanceRouteB

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

theorem blockCI_of_factorization {ψ : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hsplit : FateV2.Predict.View19.Split R X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hcover : X ∪ Y ∪ Z = Finset.univ)
    (hZX : Z ⊆ X)
    (G : FateV2.Modeling.Graph.DAG V) :
    BlockCI_Gap p G X Y Z := by
  -- X ∪ Y = univ（因 X∪Y∪Z = univ 且 Z ⊆ X）
  have hXYuni : X ∪ Y = Finset.univ := by
    -- Z ⊆ X ⊆ X ∪ Y，故 (X ∪ Y) ∪ Z = X ∪ Y
    have hZsub : Z ⊆ X ∪ Y := fun u hu => Finset.mem_union.mpr (Or.inl (hZX hu))
    have hunion : (X ∪ Y) ∪ Z = X ∪ Y := Finset.union_eq_left.mpr hZsub
    -- hcover : X ∪ Y ∪ Z = univ，且 (X ∪ Y) ∪ Z 就是 X ∪ Y ∪ Z（结合律）
    rw [← hunion, hcover]
  -- CondIndep p X Y Z
  have hci := FateV2.Predict.GraphToProbView7.condIndep_general ψ p hfac hread hsplit hXY hXZ hYZ hcover
  -- 用 BlockCIGeneralC
  exact FateV2.Predict.C5g.blockCI_of_condIndep hXYuni hZX hci

end FateV2.Predict.C5h
