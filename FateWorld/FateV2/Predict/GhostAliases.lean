import FateWorld.FateV2.Predict.ProdSplitSides
import FateWorld.FateV2.Predict.BlockCIOfBlockSplitFinal
import FateWorld.FateV2.Modeling.CondIndepCondMulBridge
import FateWorld.FateV2.Predict.GraphToProbView7
import FateWorld.FateV2.Predict.MainTheoremCFinal
import FateWorld.FateV2.Predict.TailBlockAssemble
import FateWorld.FateV2.Predict.BridgeDSepGeneral
/-!
  # Predict · GhostAliases

  ## 迁移登记
  - 来源：`FateWorld/Legacy/GhostAliases.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：ProdSplitSides, BlockCIOfBlockSplitFinal, CondIndepCondMulBridge, GraphToProbView7, MainTheoremCFinal, TailBlockAssemble, BridgeDSepGeneral
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  幽灵定理的规范名别名

  ## 背景

  审计发现 19 条「幽灵定理」：文档声称存在、但 Lean 里查不到的定理名。
  其中若干条**内容其实已经证出**，只是名字不同。

  本文件为它们补上**规范名的别名**，使得：
  * 文档里的引用能真正解析
  * 审计脚本按名字查能找到

  ## 诚实边界

  **这些别名不引入新数学**，只是给已有定理换个名字。
  真正的实现文件写在每个别名的注释里。
  =========================================================================== -/

namespace FateV2.Predict.View19

open FateV2.Modeling

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]

/-- ⭐ **`prod_split_sides`**（幽灵名）：`Split` 下的乘积拆分引理。

**真实实现**：`FateV2.Predict.View19.prod_split_sides_XYZ_statement`
（`Fate/ProdSplitSides.lean`）。 -/
theorem prod_split_sides (ψ : V → (V → α) → ℝ) (p : (V → α) → ℝ) {R : V → Finset V}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : ReadSet ψ R) {X Y Z : Finset V} (hsplit : Split R X Y Z) (x : V → α) :
    FateV2.Predict.DAGFactorization.mass (X ∪ Y ∪ Z) p x
      = (∏ v, ψ v x) * FateV2.Predict.DAGFactorization.mass (X ∪ Y ∪ Z) (fun _ => (1 : ℝ)) x :=
  prod_split_sides_XYZ_statement ψ p hfac hread hsplit x

end FateV2.Predict.View19

namespace FateV2.Predict.GraphToProbView7

open FateV2.Error FateV2.Predict.View19

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

/-- ⭐ **`ancestral_dSep_CondIndep`**（幽灵名）：主定理 C。

**真实实现**：`FateV2.Predict.GraphToProbView7.condIndep_general`
（`Fate/CondIndepGeneralNZ.lean`）。 -/
theorem ancestral_dSep_CondIndep {ψ : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    {R : V → Finset V} {X Y Z : Finset V}
    (hfac : ∀ w, p w = ∏ v, ψ v w)
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hsplit : FateV2.Predict.View19.Split R X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hcover : X ∪ Y ∪ Z = Finset.univ) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z :=
  condIndep_general ψ p hfac hread hsplit hXY hXZ hYZ hcover

/-- ⭐ **`tail_block`**（幽灵名）：有尾块情形（真正版）。

**真实实现**：`FateV2.Predict.GraphToProbView7.condIndep_tail_HA`
（`Fate/TailBlockAssemble.lean`）。 -/
theorem tail_block {ψ : V → (V → α) → ℝ} {p : (V → α) → ℝ}
    {R : V → Finset V} {X Y Z : Finset V}
    (hfacA : ∀ w, p w = ∏ v ∈ X ∪ Y ∪ Z, ψ v w)
    (hread : FateV2.Predict.View19.ReadSet ψ R)
    (hA : ∀ v, R v ⊆ X ∪ Y ∪ Z)
    (hsplit : FateV2.Predict.View19.Split R X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z :=
  condIndep_tail_HA hfacA hread hA hsplit hXY hXZ hYZ

/-- ⭐ **`ancestral_shadow`**（幽灵名）：声影分解（主定理 A）。

**真实实现**：`FateV2.Predict.GraphToProbView7.shadow_decomp`（`Fate/GraphToProbView7.lean`）。 -/
theorem ancestral_shadow {A T : Finset V} (hTA : T ⊆ A)
    {p f g : (V → α) → ℝ} (hfac : ∀ w, p w = f w * g w)
    (hf : ∀ w w', (∀ u ∈ T, w u = w' u) → f w = f w') :
    ∀ x : V → α, FateV2.Predict.DAGFactorization.mass A p x = f x * FateV2.Predict.DAGFactorization.mass A g x :=
  FateV2.Predict.GraphToProbView7.shadow_decomp hTA hfac hf

end FateV2.Predict.GraphToProbView7


namespace FateV2.Predict.FactorizesToHyper

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

/-- ⭐ **`bridge_separated`**（幽灵名）：桥主定理（无尾块）。

**真实实现**：`FateV2.Predict.GraphToProbView7.condIndep_of_factorizes_dSep_general`
（`Fate/BridgeDSepGeneral.lean`）。 -/
theorem bridge_separated
    (p : FateV2.Predict.FactorMarkov.Joint V α) (G : FateV2.Modeling.Graph.DAG V)
    (hfac : FateV2.Predict.FactorMarkov.Factorizes p G) {X Y Z : Finset V}
    (hdsep : G.dSep X Y Z) (hcover : X ∪ Y ∪ Z = Finset.univ) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z :=
  FateV2.Predict.BridgeDSepGeneral.condIndep_of_factorizes_dSep_general p G hfac hdsep hcover

end FateV2.Predict.FactorizesToHyper

namespace FateV2.Modeling.CondIndepCondMulBridge

/-- ⭐ **`factorizesOn_of_components`**（幽灵名）：无正性因子分解 ⟹ 条件独立。

**真实实现**：`FateV2.Modeling.CondIndepCondMulBridge.condIndep_fin3_of_factorization`
（`Fate/CondIndepCondMulBridge.lean`）。
一般版是 `condIndep_general`（`Fate/CondIndepGeneralNZ.lean`）。 -/
theorem factorizesOn_of_components {α : Type} [Fintype α] [DecidableEq α]
    (p : (Fin 3 → α) → ℝ) (f g h : α → ℝ)
    (hfac : ∀ x y z, p (enc ((x, y), z)) = f x * g y * h z) :
    FateV2.Predict.FactorMarkov.CondIndep p {0} {1} {2} :=
  condIndep_fin3_of_factorization p f g h hfac

/-- ⭐ **`factorizesOn_to_components`**（幽灵名）：因子分解到分量 ⟹ `CondMul`。

**真实实现**：`FateV2.Modeling.CondIndepCondMulBridge.condMul_fin3_of_factorization`。 -/
theorem factorizesOn_to_components {α : Type} [Fintype α] [DecidableEq α]
    (p : (Fin 3 → α) → ℝ) (f g h : α → ℝ)
    (hfac : ∀ x y z, p (enc ((x, y), z)) = f x * g y * h z) :
    FateV2.Predict.FinCondIndep.CondMul (gamma p) :=
  condMul_fin3_of_factorization p f g h hfac

/-- ⭐ **`factorizesOn_implies_condMul_fork`**（幽灵名）：因子分解 ⟹ `CondMul`（两路版本）。

**真实实现**：`FateV2.Modeling.CondIndepCondMulBridge.condMul_fin3_of_factorization`。
与 `factorizesOn_to_components` 同一定理，文档里是两个名字。 -/
theorem factorizesOn_implies_condMul_fork {α : Type} [Fintype α] [DecidableEq α]
    (p : (Fin 3 → α) → ℝ) (f g h : α → ℝ)
    (hfac : ∀ x y z, p (enc ((x, y), z)) = f x * g y * h z) :
    FateV2.Predict.FinCondIndep.CondMul (gamma p) :=
  condMul_fin3_of_factorization p f g h hfac

end FateV2.Modeling.CondIndepCondMulBridge
