import FateWorld.FateV2.Predict.BlockCIGeneralC
import FateWorld.FateV2.Predict.BridgeDSepGeneral
/-!
  # Predict · BlockCIUltimate

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BlockCIUltimate.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BlockCIGeneralC, BridgeDSepGeneral
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

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

namespace FateV2.Predict.C5i

open FateV2.Modeling

open Finset FateV2.Error Fate.View19 Fate.DAGFactorization Fate.AncestralInheritanceRouteB

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

-- ⭐⭐⭐ 终极组合：Pearl 因子化 + dSep + Z ⊆ X ⟹ BlockCI_Gap
theorem blockCI_of_factorizes_dSep
    (p : Fate.FactorMarkov.Joint V α) (G : FateV2.Modeling.Graph.DAG V)
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

end FateV2.Predict.C5i
