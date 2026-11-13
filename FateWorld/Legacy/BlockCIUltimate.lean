import FateWorld.Legacy.BlockCIGeneralC
import FateWorld.Legacy.BridgeDSepGeneral

/-! ===========================================================================
  §0  ⭐⭐⭐ 终极组合：Pearl 因子化 + d-分离 ⟹ BlockCI_Gap

  ## 结果

  theorem blockCI_of_factorizes_dSep
      (p : Joint V α) (G : DAG V) (hfac : Factorizes p G)
      (hdsep : G.dSep X Y Z)
      (hcover : X ∪ Y ∪ Z = univ)
      (hZX : Z ⊆ X) :
      BlockCI_Gap p G X Y Z

  ## 链路（全部已证，本文件只做组合）

  1. condIndep_of_factorizes_dSep_general（BridgeDSepGeneral.lean，R44）：
     Factorizes p G + dSep X Y Z + hcover ⟹ CondIndep p X Y Z
  2. blockCI_of_condIndep（BlockCIGeneralC.lean，R129）：
     CondIndep p X Y Z + X∪Y = univ + Z ⊆ X ⟹ BlockCI_Gap p G X Y Z
  3. 由 dSep 得三个 Disjoint；由 Z ⊆ X 与 hcover 得 X∪Y = univ

  ## 条件 Z ⊆ X 的地位

  这是 R114 发现的「dSep 结构刻画」的自然特例：
  * dSep 的三个 Disjoint 是 CondIndep 配平必需的（R26）
  * 但三个 Disjoint 不充分（R114 机检反例 disjointQuotient_not_free）
  * Z ⊆ X 是使 BlockCI_Gap（而非仅 CondIndep）成立所需的额外结构

  ## 这是 BridgeStrategy5FiberBijection.lean §4 声称内容的完整实现
  =========================================================================== -/

namespace Fate.C5i

open Finset Fate Fate.View19 Fate.DAGFactorization Fate.AncestralInheritanceRouteB

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

-- ⭐⭐⭐ 终极组合：Pearl 因子化 + dSep + Z ⊆ X ⟹ BlockCI_Gap
theorem blockCI_of_factorizes_dSep
    (p : Fate.FactorMarkov.Joint V α) (G : Causalean.Graph.DAG V)
    (hfac : Fate.FactorMarkov.Factorizes p G) {X Y Z : Finset V}
    (hdsep : G.dSep X Y Z)
    (hcover : X ∪ Y ∪ Z = Finset.univ)
    (hZX : Z ⊆ X) :
    BlockCI_Gap p G X Y Z := by
  -- 先得 CondIndep
  have hci := Fate.BridgeDSepGeneral.condIndep_of_factorizes_dSep_general p G hfac hdsep hcover
  -- dSep 给出三个 Disjoint
  obtain ⟨hXY, _, _⟩ := (hdsep : _ ∧ _ ∧ _ ∧ _)
  -- X ∪ Y = univ
  have hXYuni : X ∪ Y = Finset.univ := by
    have hZsub : Z ⊆ X ∪ Y := fun u hu => Finset.mem_union.mpr (Or.inl (hZX hu))
    have hunion : (X ∪ Y) ∪ Z = X ∪ Y := Finset.union_eq_left.mpr hZsub
    rw [← hunion, hcover]
  exact Fate.C5g.blockCI_of_condIndep hXYuni hZX hci

end Fate.C5i
