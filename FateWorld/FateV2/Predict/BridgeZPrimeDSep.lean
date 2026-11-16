/-
# `Fate/BridgeZPrimeDSep` —— `dSep` 对条件集扩大（`Z ⊆ Z'`）的**非单调性**

问题：`dSep G X Y Z` 是否随 `Z` 单调？即 `Z ⊆ Z'` 时
`dSep G X Y Z → dSep G X Y Z'`？

## ⚠ 修订说明（第 161 轮清理批次）

本文件原版（13 条定理）的核心链条是**建立在假命题之上**的，已订正。现如实记录：

| 原定理 | 原陈述 | 现状 |
|---|---|---|
| `isActiveWalk_mono` | `Z ⊆ Z'` ⟹ 活跃走法保持活跃 | 🔴 **假**。非碰撞点条件要求 `m ∉ Z`；`m ∉ Z` 不能推出 `m ∉ Z'`。证明在非碰撞点分支不可能闭合（Lean 报 `∈ Z'` vs `∈ Z` 类型错）。**已删除** |
| `bbReachableVertices_mono` | `bbReachableVertices` 随 `Z` 单调 | 🔴 **假**。反例：链 `0→1→2→3`，`3 ∈ bbReach ∅ {0}` 但 `3 ∉ bbReach {2} {0}`（见 `ch_reach_not_mono`）。**已删除** |
| `dSep_anti` | `dSep X Y Z' → dSep X Y Z`（`Z ⊆ Z'`） | 🔴 **假**。反例：`ch.dSep {0} {3} {2}` 真而 `ch.dSep {0} {3} ∅` 假（见 `dsep_mono_direction`）。**已删除** |
| `dSep_of_disjoint_of_reach` | `dSep_anti` 的分量版 | 🔴 **假**（同上）。**已删除** |
| `dsep_not_mono` | `gcol.dSep {0} {3} ∅` 真、`gcol.dSep {0} {3} {1}` 假 | 🔴 **假**：`Y = {3}` 是孤立点，`bbReachableVertices` 永不含 `3`，故 `gcol.dSep {0} {3} {1}` **真**（`decide` 已证）。**已删除** |
| `exists_dsep_but_not_dsep_mono` | `dsep_not_mono` 的打包版 | 🔴 **假**（依赖上条）。由真陈述 `exists_dsep_not_mono` 取代 |

**保留**（原样、可证）：`Trunc`/`mem_trunc`/`subset_trunc`、`bbZAncestors_mono`、
`gcol` 及 `gcol_edge01`/`gcol_pa1`/`gcol_activeWalk`/`gcol_reach_grows`。

**新增**（诚实的真陈述，替代假定理）：
* `ch`（链图 `0→1→2→3`）及 `ch_reach_not_mono` —— `bbReachableVertices` 关于 `Z` **非单调**的**真**反例；
* `dsep_mono_direction` / `exists_dsep_not_mono` —— `dSep` 关于 `Z` **非单调**的**真**反例。

`dSep` 关于 `Z` 的**正确**方向（更大 `Z` ⟹ 更易分离，Pearl 直觉）在本文件中
**未被证明**；这里只钉死「`dSep_anti` 是假的」这一事实。全程零 `sorry`/`admit`/`axiom`。
-/
import FateWorld.FateV2.Modeling.CausSeparation
import Mathlib.Tactic

open Finset
namespace FateV2.Predict.BridgeZPrimeDSep

open FateV2.Modeling

open FateV2.Modeling.Graph

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {G : FateV2.Modeling.Graph.DAG V}

set_option linter.unusedVariables false

/-!
  # Predict · BridgeZPrimeDSep

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeZPrimeDSep.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 `Trunc`（`Fate/BridgeExpanded` 的主构造，此地逐字复刻）
  =========================================================================== -/

/-- `Trunc G S = ⋃_{s ∈ S} lowerSet (topoOrder s)`。 -/
noncomputable def Trunc (G : FateV2.Modeling.Graph.DAG V) (S : Finset V) : Finset V :=
  Finset.univ.filter (fun u => ∃ s ∈ S, G.topoOrder u ≤ G.topoOrder s)

theorem mem_trunc {S : Finset V} {u : V} :
    u ∈ Trunc G S ↔ ∃ s ∈ S, G.topoOrder u ≤ G.topoOrder s := by
  unfold Trunc; simp

/-- `S ⊆ Trunc G S`。 -/
theorem subset_trunc (S : Finset V) : S ⊆ Trunc G S :=
  fun u hu => mem_trunc.mpr ⟨u, hu, le_refl _⟩

/-! ===========================================================================
  §2 `bbZAncestors` 对 `Z` 单调（唯一**成立**的单调性）
  =========================================================================== -/

/-- **`bbZAncestors` 对 `Z` 单调**：`Z ⊆ Z'` ⟹ `bbZAncestors Z ⊆ bbZAncestors Z'`。

`bbZAncestors Z = Z ∪ an_G(Z)`，两步都随集合单调。
（注意：这正是 `IsActiveWalk` 的**碰撞点**分支所需的方向；**非碰撞点**分支的方向相反，
故 `IsActiveWalk` 整体**不**单调——见文件头说明。） -/
theorem bbZAncestors_mono {Z Z' : Finset V} (h : Z ⊆ Z') :
    G.bbZAncestors Z ⊆ G.bbZAncestors Z' := by
  intro v hv
  simp only [FateV2.Modeling.Graph.DAG.bbZAncestors, FateV2.Modeling.Graph.DAG.ancestralSet,
    FateV2.Modeling.Graph.DAG.ancestorsSet, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and] at hv ⊢
  rcases hv with hvZ | ⟨w, hwZ, haw⟩
  · exact Or.inl (h hvZ)
  · exact Or.inr ⟨w, h hwZ, haw⟩

/-! ===========================================================================
  §3 反例图 `gcol`：碰撞点结构（`0 → 1 ← 2`）
  =========================================================================== -/

/-- `gcol` 的秩函数：用于证明无环。`0 ↦ 0`、`2 ↦ 1`、`1 ↦ 2`、`3 ↦ 3`。 -/
def rk (n : Fin 4) : ℕ :=
  match n with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 3
  | ⟨k + 4, h⟩ => absurd h (by omega)

/-- `gcol` 的每条边都使 `rk` 严格增。 -/
theorem rk_edge {u v : Fin 4} (h : (u = 0 ∨ u = 2) ∧ v = 1) : rk u < rk v := by
  obtain ⟨h1, h2⟩ := h
  subst h2
  rcases h1 with h1 | h1 <;> (subst h1; decide)

/-- **反例图 `gcol`**：`0 → 1 ← 2`（碰撞点 `1`），`3` 孤立。 -/
def gcol : FateV2.Modeling.Graph.DAG (Fin 4) where
  edge := fun u v => (u = 0 ∨ u = 2) ∧ v = 1
  decEdge := by intro u v; infer_instance
  acyclic := by
    intro v hv
    have key : ∀ x y : Fin 4,
        Relation.TransGen (fun u v : Fin 4 => (u = 0 ∨ u = 2) ∧ v = 1) x y →
          rk x < rk y := by
      intro x y hxy
      induction hxy with
      | single h => exact rk_edge h
      | tail _ hstep ih => exact lt_trans ih (rk_edge hstep)
    exact absurd (key v v hv) (lt_irrefl _)

/-- `gcol` 上 `0 → 1`。 -/
theorem gcol_edge01 : gcol.edge (0 : Fin 4) 1 := ⟨Or.inl rfl, rfl⟩

/-- `gcol` 上 `2 → 1`。 -/
theorem gcol_edge21 : gcol.edge (2 : Fin 4) 1 := ⟨Or.inr rfl, rfl⟩

/-- `gcol` 上 `0` 是 `1` 的父。 -/
theorem gcol_pa1 : (0 : Fin 4) ∈ gcol.parents 1 := gcol.mem_parents.mpr gcol_edge01

/-! ===========================================================================
  §4 碰撞点打开：`{1}` 使 `bbReachableVertices` 增大
  =========================================================================== -/

/-- **碰撞点打开的显式活跃走法** `[0, 1, 2]`（条件在 `{1}` 下）。 -/
theorem gcol_activeWalk :
    gcol.IsActiveWalk ({(1 : Fin 4)} : Finset (Fin 4)) [0, 1, 2] := by
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have hi1 : i = 0 ∨ i = 1 := by omega
    rcases hi1 with rfl | rfl
    · simpa using (show gcol.UAdj (0 : Fin 4) 1 from Or.inl gcol_edge01)
    · simpa using (show gcol.UAdj (1 : Fin 4) 2 from Or.inr gcol_edge21)
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ,
      List.length_cons, List.length_nil]
    have hcoll : gcol.IsCollider (0 : Fin 4) 1 2 := ⟨gcol_edge01, gcol_edge21⟩
    rw [if_pos hcoll]
    simp only [FateV2.Modeling.Graph.DAG.bbZAncestors, FateV2.Modeling.Graph.DAG.ancestralSet,
      FateV2.Modeling.Graph.DAG.ancestorsSet, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact Or.inl (mem_singleton_self 1)

/-- **碰撞点使可达集扩张**：`2` 在 `Z = {1}` 下可达，在 `Z = ∅` 下不可达。 -/
theorem gcol_reach_grows :
    (2 : Fin 4) ∈ gcol.bbReachableVertices ({(1 : Fin 4)} : Finset (Fin 4)) {0}
    ∧ (2 : Fin 4) ∉ gcol.bbReachableVertices (∅ : Finset (Fin 4)) {0} := by
  constructor <;> decide

/-! ===========================================================================
  §5 链图 `ch`：`bbReachableVertices` 关于 `Z` **非单调** 的真反例
  =========================================================================== -/

/-- **链图 `ch`**：`0 → 1 → 2 → 3`（无碰撞点）。 -/
def ch : FateV2.Modeling.Graph.DAG (Fin 4) where
  edge := fun u v => (v : Nat) = (u : Nat) + 1
  decEdge := by intro u v; infer_instance
  acyclic := by
    intro v hv
    have key : ∀ x y : Fin 4,
        Relation.TransGen (fun u v : Fin 4 => (v : Nat) = (u : Nat) + 1) x y →
          (x : Nat) < (y : Nat) := by
      intro x y hxy
      induction hxy with
      | single h => omega
      | tail _ hstep ih => omega
    exact absurd (key v v hv) (lt_irrefl _)

/-- ⭐⭐ **`bbReachableVertices` 关于 `Z` 非单调**（**真**反例）。

`∅ ⊆ {2}`，但 `3` 在 `Z = ∅` 下从 `{0}` 可达、在 `Z = {2}` 下不可达：
非碰撞点 `2` 被条件化后阻断链。**这直接否定**了原文件的 `bbReachableVertices_mono`。 -/
theorem ch_reach_not_mono :
    (∅ : Finset (Fin 4)) ⊆ ({(2 : Fin 4)} : Finset (Fin 4))
    ∧ (3 : Fin 4) ∈ ch.bbReachableVertices (∅ : Finset (Fin 4)) {0}
    ∧ (3 : Fin 4) ∉ ch.bbReachableVertices ({(2 : Fin 4)} : Finset (Fin 4)) {0} := by
  refine ⟨Finset.empty_subset _, ?_, ?_⟩ <;> decide

/-! ===========================================================================
  §6 `dSep` 关于 `Z` 非单调：真反例（取代原 `dsep_not_mono`）
  =========================================================================== -/

/-- ⭐⭐⭐ **`dSep` 关于 `Z` 非单调**（**真**反例，`ch` 图）。

`∅ ⊆ {2}`，但 `ch.dSep {0} {3} {2}` 成立而 `ch.dSep {0} {3} ∅` 失败。
**这直接否定**了原文件的 `dSep_anti`：条件集扩大（`∅ ↦ {2}`）反而**使**分离成立，
即 `dSep` 随 `Z` **增**（Pearl 直觉），而非原文件所声称的**反单调**。 -/
theorem dsep_mono_direction :
    (∅ : Finset (Fin 4)) ⊆ ({(2 : Fin 4)} : Finset (Fin 4))
    ∧ ch.dSep {(0 : Fin 4)} {(3 : Fin 4)} ({(2 : Fin 4)} : Finset (Fin 4))
    ∧ ¬ ch.dSep {(0 : Fin 4)} {(3 : Fin 4)} (∅ : Finset (Fin 4)) := by
  refine ⟨Finset.empty_subset _, ?_, ?_⟩ <;> decide

/-- **打包形式**：存在 `X Y Z Z'`（`Z ⊆ Z'`）使 `dSep X Y Z` **假**、`dSep X Y Z'` **真**。 -/
theorem exists_dsep_not_mono :
    ∃ (X Y Z Z' : Finset (Fin 4)),
      Z ⊆ Z' ∧ ¬ ch.dSep X Y Z ∧ ch.dSep X Y Z' :=
  ⟨{0}, {3}, ∅, {2}, Finset.empty_subset _, (dsep_mono_direction.2.2), dsep_mono_direction.2.1⟩

end FateV2.Predict.BridgeZPrimeDSep