/-
# hTail 与 dSep 的关系：机检反例

## 结论（一句话）

> **`G.dSep X Y Z` 不能推出 `∀ v ∉ X∪Y∪Z, readSetOf G v ⊆ Z`。**
> 结论完全成立，且有 **`V = Fin 4` 上 `decide` 可判定的最小反例**。

## 反例

`V = Fin 4`，边集：`2 → 0`，`2 → 1`，`3 → 0`。

* 查询：`X = {0}`，`Y = {1}`，`Z = {2}`，故 `A = X ∪ Y ∪ Z = {0, 1, 2}`。
* 取 `v = 3 ∉ A`。`3` 在该图中**没有父**，故
  `readSetOf G 3 = {3} ∪ pa(3) = {3} ⊄ Z = {2}`（因为 `3 ∉ {2}`）。

`dSep {0} {1} {2}` **成立**：

* 三对集合两两不交；
* 唯一的无向 `X–Y` 路径是 `0 ← 2 → 1`，其中间点 `2` 是**非 collider**
  （两侧都是 `fromChild` 支），且 `2` 落在条件集 `Z` 内 ⟹ 被阻断；
* `3 → 0` 这条边只会让球从 `0` 沿「逆边」滚向 `3`，而 `bbStep` 的
  `fromChild` 支只在**中间点属于 `Z`** 时才沿 `parents` 前进；此处中间点为
  `0 ∉ Z`，故球停在 `0`，到不了 `1`；
* 因此 `bbReachableVertices {2} {0} ∩ {1} = ∅`。

以上由 `decide` 机检（`dSep` 有 `Decidable` 实例 `decDSep`，见 `forkDAG_dSep`）。

补充（同一张图上的第二处失败）：`3 → 0` 使得 `3 ∈ readSetOf G 0`
（`three_mem_readSet_zero`），即覆盖外的顶点还能污染 `X` 中顶点的读集。
两种失败都说明读集可以「横跨」到 `Z` 之外。

## 意义

「读集横跨」现象并不限于 `X∪Y∪Z` 内部（`Fate/SplitFromDAG.lean` §5 的 `v ∈ Z`
反例），而是**覆盖之外**的顶点同样可以自由横跨 —— 覆盖条件 `X ∪ Y ∪ Z = univ`
是 `dSep ⟹ Split` 的真正分界线，任何形如「`v ∉ X∪Y∪Z` ⟹ 读集 ⊆ Z」的
`hTail` 式假设**不能**从 `dSep` 得到，必须作为独立假设引入。

本文件不修改任何既有模块；不写 `Fate/` 目录；不改 `lean`。
零 `sorry` / `admit` / `axiom`。
-/

import FateWorld.FateV2.Predict.FactorizesToHyper
import FateWorld.FateV2.Modeling.CausSeparation
namespace FateV2.Predict

open FateV2.Modeling
namespace TailFromDSep

open Finset FateV2.Modeling.Graph

/-!
  # Predict · TailFromDSepFork

  ## 迁移登记
  - 来源：`FateWorld/Legacy/TailFromDSepFork.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorizesToHyper, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 反例图：`2 → 0`，`2 → 1`，`3 → 0`（`V = Fin 4`）
  =========================================================================== -/

/-- 边关系：`(2,0)`、`(2,1)`、`(3,0)`。 -/
def forkEdge : Fin 4 → Fin 4 → Prop :=
  fun u v => (u = 2 ∧ v = 0) ∨ (u = 2 ∧ v = 1) ∨ (u = 3 ∧ v = 0)

/-- 边关系的可判定性。 -/
@[instance_reducible]
def forkEdgeDec : DecidableRel forkEdge := by
  intro u v; unfold forkEdge; infer_instance

/-- 拓扑秩：`2,3 ↦ 0`；`0,1 ↦ 1`。用来说明无环。 -/
def forkRank (x : Fin 4) : ℕ := if x = 0 ∨ x = 1 then 1 else 0

theorem forkEdge_rank_lt {u v : Fin 4} (h : forkEdge u v) : forkRank u < forkRank v := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · unfold forkRank; decide
  · unfold forkRank; decide
  · unfold forkRank; decide

/-- ⭐ **反例图**：`V = Fin 4`，边 `2 → 0`、`2 → 1`、`3 → 0`。 -/
def forkDAG : FateV2.Modeling.Graph.DAG (Fin 4) where
  edge := forkEdge
  decEdge := forkEdgeDec
  acyclic := by
    intro v h
    have hmono : ∀ {a b : Fin 4},
        Relation.TransGen forkEdge a b → forkRank a < forkRank b := by
      intro a b hab
      induction hab with
      | single h => exact forkEdge_rank_lt h
      | tail _ hbc ih => exact lt_trans ih (forkEdge_rank_lt hbc)
    exact absurd (hmono h) (lt_irrefl _)

/-! ===========================================================================
  §2 两个机检事实
  =========================================================================== -/

/-- 反例中 `dSep {0} {1} {2}` **成立**（`decide` 判定）。 -/
theorem forkDAG_dSep : forkDAG.dSep {0} {1} ({2} : Finset (Fin 4)) := by
  decide

/-- 反例中 `3` 是 `0` 的父（边 `3 → 0`）。 -/
theorem three_mem_parents_zero : (3 : Fin 4) ∈ forkDAG.parents 0 :=
  (FateV2.Modeling.Graph.DAG.mem_parents forkDAG).mpr (by
    show forkEdge 3 0
    unfold forkEdge
    decide)

/-- 反例中 `3 ∈ readSetOf G 0`。 -/
theorem three_mem_readSet_zero :
    (3 : Fin 4) ∈ FateV2.Predict.FactorizesToHyper.readSetOf forkDAG 0 :=
  FateV2.Predict.FactorizesToHyper.mem_readSetOf.mpr (Or.inr three_mem_parents_zero)

/-- 反例中 `3 ∉ {0, 1, 2}`。 -/
theorem three_not_mem :
    (3 : Fin 4) ∉ ({0, 1, 2} : Finset (Fin 4)) := by
  decide

/-- 反例中 `3 ∈ readSetOf G 3`（自身）。 -/
theorem three_mem_readSet_three :
    (3 : Fin 4) ∈ FateV2.Predict.FactorizesToHyper.readSetOf forkDAG 3 :=
  FateV2.Predict.FactorizesToHyper.mem_readSetOf.mpr (Or.inl rfl)

/-- ⭐ **`hTail` 的结论在反例上失败**：`readSetOf G 3 ⊄ {2}`。

`readSetOf G 3 = {3} ∪ pa(3) = {3}`，而 `3 ∉ {2}`。 -/
theorem forkDAG_not_hTail :
    ¬ FateV2.Predict.FactorizesToHyper.readSetOf forkDAG (3 : Fin 4) ⊆ ({2} : Finset (Fin 4)) := by
  intro hsub
  exact absurd (hsub three_mem_readSet_three) (by decide)

/-! ===========================================================================
  §3 判决：`dSep` **不**蕴含 `hTail`
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **主定理**：不存在「`dSep` ⟹ 覆盖外顶点读集落进 `Z`」这样的定理。

存在一张 `Fin 4` 上的 DAG（`forkDAG`）与查询 `X = {0}`、`Y = {1}`、`Z = {2}`，
使得 `dSep X Y Z` 成立，但取 `v = 3 ∉ X ∪ Y ∪ Z` 时
`readSetOf G v ⊄ Z`。 -/
theorem hTail_from_dSep_false :
    ¬ (∀ (G : FateV2.Modeling.Graph.DAG (Fin 4)) (X Y Z : Finset (Fin 4)),
        G.dSep X Y Z → ∀ v : Fin 4, v ∉ X ∪ Y ∪ Z →
          FateV2.Predict.FactorizesToHyper.readSetOf G v ⊆ Z) := by
  intro h
  have hsub : FateV2.Predict.FactorizesToHyper.readSetOf forkDAG (3 : Fin 4)
      ⊆ ({2} : Finset (Fin 4)) := by
    refine h forkDAG {0} {1} {2} forkDAG_dSep 3 ?_
    rw [show ({0} : Finset (Fin 4)) ∪ {1} ∪ {2} = {0, 1, 2} by decide]
    exact three_not_mem
  exact forkDAG_not_hTail hsub

end TailFromDSep

end FateV2.Predict