/-
  Fate_agent_staging/BridgeIntegrated.lean

  【桥的最终整合】把已证的三段接起来。

  ## 内容

  | # | 名称 | 陈述 |
  |---|---|---|
  | 1 | `parentClosed G S` | `∀ v ∈ S, G.parents v ⊆ S`（父闭） |
  | 2 | `readSetOf_subset_of_parentClosed` | 父闭 ⟹ `readSetOf G v ⊆ S`（对 `v ∈ S`） |
  | 3 | `condIndep_of_factorizes_general` | `Factorizes` + `Split` ⟹ `CondIndep p X Y Z`（一般 `Z`） |
  | 4 | `split_of_parentClosed` | 两块父闭 + 覆盖 ⟹ `Split (readSetOf G) X Y Z` |
  | 5 | `condIndep_of_factorizes_parentClosed` | 上两者串联（缺口 A 的可证部分） |

  ## 依赖（全部已入库、零 `sorry`）

  * `FateV2.Predict.FactorizesToHyper.factorizes_to_hyper` —— `Fate/FactorizesToHyper.lean`
  * `FateV2.Predict.GraphToProbView7.condIndep_general` —— `Fate/CondIndepGeneralNZ.lean`
  * `FateV2.Predict.FactorMarkov.Factorizes` / `CondIndep` —— `Fate/FactorMarkov.lean`
  * `FateV2.Predict.View19.Split` / `ReadSet` —— `Fate/View19FactorGraphSplit.lean`
  * `Causalean.Graph.DAG.parents` —— `CausDAG.lean`

  **零 `sorry` / `admit` / `axiom`**；不修改任何既有模块。
-/

import FateWorld.FateV2.Predict.FactorizesToHyper
import FateWorld.FateV2.Modeling.CondIndepGeneralNZ
import Mathlib.Tactic.Ring

namespace FateV2.Predict

open FateV2.Modeling
namespace BridgeIntegrated

open Finset
open FateV2.Modeling.Graph

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {α : Type u} [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false

/-!
  # Predict · BridgeIntegrated

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeIntegrated.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorizesToHyper, CondIndepGeneralNZ
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1  主整合：一般 `Z` 的 `condIndep_of_factorizes_general`
  =========================================================================== -/

section General

variable [Nonempty α]

/-- ⭐⭐⭐⭐⭐ **整合版（一般 `Z`）**：DAG 因子分解 + 因子图分离 ⟹ 条件独立。

证明只有一行：`factorizes_to_hyper` 把 `Factorizes p G` 拆成
「同族因子 `f` + 读集约束 + `HyperFactorizes`」，直接喂给 `condIndep_general`。 -/
theorem condIndep_of_factorizes_general
    (p : FateV2.Predict.FactorMarkov.Joint V α) (G : DAG V)
    (hfac : FateV2.Predict.FactorMarkov.Factorizes p G)
    {X Y Z : Finset V}
    (hsplit : FateV2.Predict.View19.Split (FactorizesToHyper.readSetOf G) X Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hcover : X ∪ Y ∪ Z = Finset.univ) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z := by
  obtain ⟨f, hread, hhyper⟩ := FactorizesToHyper.factorizes_to_hyper p G hfac
  exact FateV2.Predict.GraphToProbView7.condIndep_general f p hhyper hread hsplit
    hXY hXZ hYZ hcover

end General

/-! ===========================================================================
  §2  父闭 ⟹ `Split`（缺口 A 的可证部分）
  =========================================================================== -/

/-- ⭐ **父闭**：`S` 对父集封闭。 -/
def parentClosed (G : DAG V) (S : Finset V) : Prop := ∀ v ∈ S, G.parents v ⊆ S

/-- ⭐ **父闭 ⟹ 局部域含于 `S`**：`v ∈ S` 且 `S` 父闭 ⟹ `readSetOf G v ⊆ S`。

`readSetOf G v = insert v (G.parents v)`，用 `Finset.insert_subset` 拆成
「`v ∈ S`」与「`G.parents v ⊆ S`」两条，分别由 `hv` 与 `hS` 给出。 -/
theorem readSetOf_subset_of_parentClosed {G : DAG V} {S : Finset V}
    (hS : parentClosed G S) {v : V} (hv : v ∈ S) :
    FactorizesToHyper.readSetOf G v ⊆ S := by
  unfold FactorizesToHyper.readSetOf
  exact Finset.insert_subset hv (hS v hv)

set_option linter.unusedSectionVars false in
/-- ⭐⭐⭐⭐ **父闭 ⟹ `Split`**（缺口 A 的可证部分）。

若 `X ∪ Z`、`Y ∪ Z` 都父闭且三块覆盖 `univ`，则每个读集
`readSetOf G v = {v} ∪ pa(v)` 整块落进 `X ∪ Z` 或 `Y ∪ Z` 之一。

**证明**：由 `hcover`，`v ∈ X ∪ Y ∪ Z`；用两层 `Finset.mem_union.mp` 分成三支：
`v ∈ X` / `v ∈ Y` / `v ∈ Z`。前两支给出 `v ∈ X ∪ Z` 或 `v ∈ Y ∪ Z`，
第三支 `v ∈ Z` 同时属于两边（择一起）。再用 `readSetOf_subset_of_parentClosed`。 -/
theorem split_of_parentClosed (G : DAG V) {X Y Z : Finset V}
    (hXZ : parentClosed G (X ∪ Z)) (hYZ : parentClosed G (Y ∪ Z))
    (hcover : X ∪ Y ∪ Z = Finset.univ) :
    FateV2.Predict.View19.Split (FactorizesToHyper.readSetOf G) X Y Z := by
  intro v
  have hv : v ∈ X ∪ Y ∪ Z := by rw [hcover]; exact Finset.mem_univ v
  rcases Finset.mem_union.mp hv with hv' | hvz
  · rcases Finset.mem_union.mp hv' with hvx | hvy
    · exact Or.inl (readSetOf_subset_of_parentClosed hXZ
        (Finset.mem_union.mpr (Or.inl hvx)))
    · exact Or.inr (readSetOf_subset_of_parentClosed hYZ
        (Finset.mem_union.mpr (Or.inl hvy)))
  · exact Or.inl (readSetOf_subset_of_parentClosed hXZ
      (Finset.mem_union.mpr (Or.inr hvz)))

/-! ===========================================================================
  §3  串联：`Factorizes` + 父闭 ⟹ `CondIndep`
  =========================================================================== -/

section Chain

variable [Nonempty α]

/-- ⭐⭐⭐⭐⭐ **最终串联**：DAG 因子分解 + 两块父闭 + 三对不交 + 覆盖 ⟹ 条件独立。

把 `split_of_parentClosed` 产出的 `Split` 直接喂给 `condIndep_of_factorizes_general`。 -/
theorem condIndep_of_factorizes_parentClosed
    (p : FateV2.Predict.FactorMarkov.Joint V α) (G : DAG V)
    (hfac : FateV2.Predict.FactorMarkov.Factorizes p G)
    (hXZc : parentClosed G (X ∪ Z)) (hYZc : parentClosed G (Y ∪ Z))
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hcover : X ∪ Y ∪ Z = Finset.univ) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y Z :=
  condIndep_of_factorizes_general p G hfac
    (split_of_parentClosed G hXZc hYZc hcover) hXY hXZ hYZ hcover

end Chain

end BridgeIntegrated

end FateV2.Predict