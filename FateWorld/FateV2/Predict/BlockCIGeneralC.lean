import FateWorld.FateV2.Predict.MassFactorOfReads
import FateWorld.FateV2.Predict.AncestralInheritanceRouteB
/-!
  # Predict · BlockCIGeneralC

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BlockCIGeneralC.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：MassFactorOfReads, AncestralInheritanceRouteB
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §0  `BlockCI_Gap` 的一般 `C` 情形

  ## 背景

  `BlockCI_Gap p G A B C := ∀ x, p x * mass C p x = mass A p x * mass (B ∪ C) p x`

  `Fate/BlockCIOfBlockSplitFinal.lean` 只做了 `C = ∅` 情形。
  本文件推广到**一般 `C`**（只需 `C ⊆ A`）。

  ## 关键推导

  `CondIndep p A B C` 给出
    `mass (A∪B∪C) · mass C = mass (A∪C) · mass (B∪C)`。

  若 `A ∪ B = univ`，则 `mass (A∪B∪C) = mass univ = p x`。
  若 `C ⊆ A`，则 `A ∪ C = A`。

  代入即得 `p x · mass C = mass A · mass (B∪C)`，正是 `BlockCI_Gap`。

  ## 诚实边界

  本文件给的是**从 `CondIndep` 到 `BlockCI_Gap` 的桥接**。
  把 `CondIndep` 从因子分解 + `Split` 推出，需用 `condIndep_general`
  （`Fate/CondIndepGeneralNZ.lean`），那一环本文件不重复，见
  `Fate/BlockCIOfBlockSplitFinal.lean` 的 `C = ∅` 版本。
  =========================================================================== -/

-- 一般 C 情形：BlockCI_Gap p G A B C := ∀ x, p x * mass C p x = mass A p x * mass (B ∪ C) p x
-- 
-- 若 p 只读 A，A ∩ B = ∅，A ∪ B = univ，C ⊆ B：
--   mass (B ∪ C) = mass B（因 C ⊆ B）
--   而 mass A * mass B = p x * mass ∅（由 CondIndep p A B ∅）
--   ⟹ 需要 p x * mass C = p x * mass ∅，即 mass C = mass ∅
--   但一般 C ≠ ∅，不成立！

-- 所以 CondIndep p A B ∅ 不足以推出 BlockCI_Gap（一般 C）

-- 正确的连接：CondIndep p A B C 才是对的
-- CondIndep p A B C : ∀ x, mass (A∪B∪C) * mass C = mass (A∪C) * mass (B∪C)
-- 若 A ∪ B = univ：mass (A∪B∪C) = mass univ = p x
-- ⟹ p x * mass C = mass (A∪C) * mass (B∪C)
-- 而 BlockCI_Gap 是 p x * mass C = mass A * mass (B∪C)
-- ⟹ 需要 mass (A∪C) = mass A
-- ⟹ 若 C ⊆ A 则成立！

-- ⭐ 所以：CondIndep p A B C + A∪B=univ + C ⊆ A ⟹ BlockCI_Gap p G A B C
namespace FateV2.Predict.C5g

open FateV2.Modeling

open Finset FateV2.Error FateV2.Predict.View19 Fate.DAGFactorization FateV2.Predict.AncestralInheritanceRouteB

universe u

variable {V : Type u} {α : Type u} [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α] [Nonempty α]

theorem blockCI_of_condIndep {p : (V → α) → ℝ} {G : FateV2.Modeling.Graph.DAG V}
    {A B C : Finset V} (hAB : A ∪ B = Finset.univ) (hCA : C ⊆ A)
    (hci : FateV2.Predict.FactorMarkov.CondIndep p A B C) :
    BlockCI_Gap p G A B C := by
  intro x
  have hz := hci x
  rw [hAB] at hz
  have hAC : A ∪ C = A := Finset.union_eq_left.mpr hCA
  rw [hAC] at hz
  have hun : (Finset.univ ∪ C : Finset V) = Finset.univ := Finset.union_eq_left.mpr (Finset.subset_univ C)
  rw [hun] at hz
  rw [Fate.DAGFactorization.mass_univ] at hz
  exact hz

end FateV2.Predict.C5g
