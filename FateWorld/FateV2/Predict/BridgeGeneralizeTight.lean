/-
# ⑧ 因果结构补「紧」：`dSep ↔ Split` 的具体实例取等

## 0 问题与结论

`Fate/BridgeGeneralize.lean` 的 **B2.2** `dSep_forces_split` 给出**上界（正向）**：

> `G.dSep X Y Z` + 覆盖 `X ∪ Y ∪ Z = univ` ⟹ `Split (readSetOf G) X Y Z`。

`Fate/SplitFromDAG.lean` 的 `dSep_not_implies_split` 给出**下界（不可改进）**：

> 缺了覆盖条件，`dSep` 单独就**不**蕴含 `Split`（`V = Fin 3` 撞子反例）。

本文件补上**「紧」**：在 **最小具体 DAG** 上显式给出一个 `Split` 与 `dSep`
**同时成立**的查询，并且在这张图上对同一查询 **`Split` 也回推 `dSep`**
（即该查询处蕴含**取等**，不是单向的空洞蕴含）。

## 1 具体实例（`Fin 2` 上的单边 DAG）

* 顶点 `V = Fin 2`。
* 边：唯一一条 `0 → 1`（无环，按自然数秩 `0 < 1`）。
* 查询：`X = {0, 1}`、`Y = ∅`、`Z = ∅`。

此时：

* **覆盖** `{0,1} ∪ ∅ ∪ ∅ = univ` ✔
* `dSep X Y Z` 成立 ✔（`X` 与 `Y`、`Z` 两两不交；`Y = ∅` 使 Bayes-Ball 不相交条件平凡成立）
* `Split (readSetOf G) X Y Z` 成立 ✔（每个读集都 `⊆ X ∪ Z = univ`）

并且这张图上还有**否定侧**的取等证据：同一张图上 `X = {1}`、`Y = {0}`、`Z = ∅`
处 **`dSep` 与 `Split` 同时不成立** —— 说明在这种小图上两者的真值**同步**，
不是「一端恒真、一端恒假」的空洞关系。

## 2 定理一览

| # | 名称 | 陈述 | 状态 |
|---|---|---|---|
| T1 | `twoNodeDAG` | `Fin 2` 上单边 `0 → 1` 的 DAG | 定义 |
| T2 | `twoNode_dSep` | `twoNodeDAG.dSep {0,1} ∅ ∅` | ✅ |
| T3 | `twoNode_split` | `Split (readSetOf twoNodeDAG) {0,1} ∅ ∅` | ✅ |
| T4 | **`tight_example_two_node`** | ⭐ **「紧」主定理**：`∃ G X Y Z, 覆盖 ∧ dSep ∧ Split`（三者同真的具体实例） | ✅ |
| T5 | `twoNode_not_dSep` | 否定侧：`¬ twoNodeDAG.dSep {1} {0} ∅` | ✅ |
| T6 | `twoNode_not_split` | 否定侧：`¬ Split (readSetOf twoNodeDAG) {1} {0} ∅` | ✅ |
| T7 | **`tight_iff_on_example`** | ⭐⭐ **取等**：在上述具体 `(G, X, Y, Z)` 处 `dSep ↔ Split` | ✅ |

## 2.5 空实例警告（第 940 轮审计 F2）

**T4 `tight_example_two_node` 与 T7 `tight_iff_on_example` 的实例都取 `Y = empty`，
故 `dSep` 平凡为真，不构成「紧性」证据。见这两条定理的 docstring。**

## 3 纪律

**零 `sorry` / 零 `admit` / 零 `axiom`。不修改任何既有模块。**
所有结论均由 `decide` 机检（`dSep`、`Split` 在 `Fin 2` 上均可判定）。
-/

import FateWorld.FateV2.Predict.BridgeGeneralize
import FateWorld.FateV2.Modeling.CausDAG
import FateWorld.FateV2.Modeling.CausSeparation
set_option warn.classDefReducibility false

open FateV2.Modeling.Graph

namespace FateV2.Predict

open FateV2.Modeling
namespace BridgeGeneralizeTight

/-!
  # Predict · BridgeGeneralizeTight

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeGeneralizeTight.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BridgeGeneralize, _root.CausDAG, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 具体实例：`Fin 2` 上单边 `0 → 1`
  =========================================================================== -/

/-- 边关系：唯一一条 `0 → 1`。 -/
def twoNodeEdge : Fin 2 → Fin 2 → Prop := fun u v => u = 0 ∧ v = 1

/-- 上述边关系的可判定性。 -/
def twoNodeEdgeDec : DecidableRel twoNodeEdge := by
  intro u v; unfold twoNodeEdge; infer_instance

/-- 拓扑秩（自然数嵌入）`0 ↦ 0`、`1 ↦ 1`，用于证明无环。 -/
def twoNodeRank (x : Fin 2) : ℕ := (x : ℕ)

theorem twoNodeEdge_rank_lt {u v : Fin 2} (h : twoNodeEdge u v) :
    twoNodeRank u < twoNodeRank v := by
  rcases h with ⟨rfl, rfl⟩
  unfold twoNodeRank
  decide

/-- ⭐ **T1：`Fin 2` 上单边 `0 → 1` 的 DAG。** -/
def twoNodeDAG : FateV2.Modeling.Graph.DAG (Fin 2) where
  edge := twoNodeEdge
  decEdge := twoNodeEdgeDec
  acyclic := by
    intro v h
    have hmono : ∀ {a b : Fin 2},
        Relation.TransGen twoNodeEdge a b → twoNodeRank a < twoNodeRank b := by
      intro a b hab
      induction hab with
      | single h => exact twoNodeEdge_rank_lt h
      | tail _ hbc ih => exact lt_trans ih (twoNodeEdge_rank_lt hbc)
    exact absurd (hmono h) (lt_irrefl _)

/-! ===========================================================================
  §2 肯定侧：`dSep` 与 `Split` 同时成立
  =========================================================================== -/

/-- ⭐ **T2**：`twoNodeDAG.dSep {0,1} ∅ ∅` 成立。 -/
theorem twoNode_dSep : twoNodeDAG.dSep {0, 1} ∅ ∅ := by
  decide

/-- ⭐ **T3**：`Split (readSetOf twoNodeDAG) {0,1} ∅ ∅` 成立。

读集：`readSetOf G 0 = {0}`、`readSetOf G 1 = {0,1}`，两者都 `⊆ {0,1} ∪ ∅`。 -/
theorem twoNode_split :
    FateV2.Predict.View19.Split (FateV2.Predict.FactorizesToHyper.readSetOf twoNodeDAG) {0, 1} ∅ ∅ := by
  unfold FateV2.Predict.View19.Split FateV2.Predict.FactorizesToHyper.readSetOf
  decide

/-- T4: exists a concrete DAG and query with cover, dSep and Split all true.

WARNING -- EMPTY INSTANCE (audit round 940, F2):

This theorem's witness takes `Y = empty` (the term `empty` below stands for the
empty Finset), so `dSep X empty Z` is VACUOUSLY true: any `X`, `empty`, `Z`
satisfy the disjunctive premise.

=> This is NOT tightness, it is a vacuous instance. Counting it as tightness
evidence for item 8 makes the (correct) conclusion "item 8 lacks tightness"
indefensible.

Reason for keeping the theorem: it is still a legitimate Lean theorem (EXIT=0),
but it must NOT be cited as tightness evidence for item 8.

Genuine tightness requires `Y` nonempty and `dSep` nontrivial.
-/
theorem tight_example_two_node :
    ∃ (G : FateV2.Modeling.Graph.DAG (Fin 2)) (X Y Z : Finset (Fin 2)),
      X ∪ Y ∪ Z = Finset.univ ∧ G.dSep X Y Z ∧
      FateV2.Predict.View19.Split (FateV2.Predict.FactorizesToHyper.readSetOf G) X Y Z :=
  by
    exact ⟨twoNodeDAG, ({0, 1} : Finset (Fin 2)), ∅, ∅, by decide, twoNode_dSep, twoNode_split⟩
/-! ===========================================================================
  §3 否定侧：同一张图上另取查询，`dSep` 与 `Split` 同时**不**成立
  =========================================================================== -/

/-- ⭐ **T5**：`¬ twoNodeDAG.dSep {1} {0} ∅` —— 边 `0 → 1` 把 `{1}` 与 `{0}` 连通，
`X = {1}` 经反向边可达 `Y = {0}`，Bayes-Ball 被打开。 -/
theorem twoNode_not_dSep : ¬ twoNodeDAG.dSep {1} {0} ∅ := by
  decide

/-- ⭐ **T6**：`¬ Split (readSetOf twoNodeDAG) {1} {0} ∅` ——
`readSetOf G 1 = {0,1}` 既不是 `{1} ∪ ∅` 的子集，也不是 `{0} ∪ ∅` 的子集，横跨两侧。 -/
theorem twoNode_not_split :
    ¬ FateV2.Predict.View19.Split (FateV2.Predict.FactorizesToHyper.readSetOf twoNodeDAG) {1} {0} ∅ := by
  unfold FateV2.Predict.View19.Split FateV2.Predict.FactorizesToHyper.readSetOf
  decide

/-! ===========================================================================
  §4 取等主定理：在具体实例处 `dSep ↔ Split`
  =========================================================================== -/

/-- T7: at the concrete instance `(twoNodeDAG, {0,1}, empty, empty)`,

WARNING -- EMPTY INSTANCE (audit round 940, F2):

This theorem's instance also takes `Y = empty`, so `dSep X empty Z` is
VACUOUSLY true and hence so is the alleged `dSep <-> Split` coincidence; the
biconditional holds only because BOTH sides are trivially true.

=> This is NOT tightness, it is a vacuous instance. Counting it as tightness
evidence for item 8 makes the (correct) conclusion "item 8 lacks tightness"
indefensible.

Reason for keeping the theorem: it is still a legitimate Lean theorem (EXIT=0),
but it must NOT be cited as tightness evidence for item 8.

Genuine tightness requires `Y` nonempty and `dSep` nontrivial.

(Original note, superseded by the warning above:) at the concrete instance
`dSep` 与 `Split` **互为充要** —— 这是「`dSep_forces_split` 的蕴含在某实例上取等」
的机检证据。

**⚠ 这不是全局等价**（`SplitFromDAG.dSep_not_implies_split` 已证全局不等价）；
它只断言**一个具体实例**处两者的真值一致，从而蕴含在此处**不可再加强**。 -/
theorem tight_iff_on_example :
    twoNodeDAG.dSep ({0, 1} : Finset (Fin 2)) ∅ ∅ ↔
      FateV2.Predict.View19.Split (FateV2.Predict.FactorizesToHyper.readSetOf twoNodeDAG) {0, 1} ∅ ∅ :=
  ⟨fun _ => twoNode_split, fun _ => twoNode_dSep⟩

end BridgeGeneralizeTight
end FateV2.Predict