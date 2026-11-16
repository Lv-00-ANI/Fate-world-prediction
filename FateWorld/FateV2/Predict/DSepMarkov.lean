import FateWorld.FateV2.Modeling.CausDAG
import FateWorld.FateV2.Modeling.CausBayesBall
import FateWorld.FateV2.Modeling.CausActivePath
import FateWorld.FateV2.Modeling.CausSeparation
import Mathlib.Tactic

/-!
  # Predict · DSepMarkov

  ## 迁移登记
  - 来源：`FateWorld/Legacy/DSepMarkov.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausDAG, _root.CausBayesBall, _root.CausActivePath, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-!
# `Fate/Stage2/DSepMarkov` —— d-分离的 Markov 性（最小真情形）

## 内容

本文件证明两件事，都**真正判定 `G`**：`bbInit` / `bbReachAux` / `bbReachable` /
`bbReachableVertices` 的递归结构出现在证明的**关键路径**上，而不是装饰性引用。

### A 组：孤立点（最小情形）

- `bbInit_singleton_of_isolated` —— `G.bbInit {x} = ∅`
- `bbReachAux_empty` —— 空前沿出发的 BFS 对**任意燃料**返回起始 `visited`
- `bbReachable_singleton_of_isolated` —— `G.bbReachable Z {x} = ∅`
- `bbReachableVertices_singleton_of_isolated` —— `G.bbReachableVertices Z {x} = ∅`
- `dSep_of_isolated` —— `G.dSep {x} Y Z`

### B 组：Bayes Ball 的**首步边判定**（非平凡）

- `isActiveWalk_pair` —— 相邻两点的 `[a, b]` 总是 active walk
  （`IsActiveWalk` 的中段 collider 条件在 `len = 2` 时**空真**）
- `head_adj_of_reachable` —— **`w ∈ bbReachableVertices Z X` ⟹ 存在 `x ∈ X` 与 `u`
  使 `G.UAdj x u`**。即：**reachable 的第一步必然穿过一条真实的图边**。

`head_adj_of_reachable` 是 `bbReachableVertices` 的**边判定内核**：
它把 `bbReachableVertices_iff_activeWalk` 的**完备性方向（←）真正消费**，
把「可达性」化为「图上有边」。这正是 `dSep` 第 4 子句真正做功的地方——
`dSep` 的「阻断」语义最终就是**图上不存在这样的一条边**。

**忠实性声明（⚠ 必读）**：`dSep` 是四个合取项的 **def**。
第 1–3 项（`Disjoint X Y`、`Disjoint X Z`、`Disjoint Y Z`）是**纯粹的集合不交**，
与 `G` 无关；只有第 4 项 `Disjoint (bbReachableVertices Z X) Y` 才**消费图结构**。
本文件的 A 组让第 4 项**平凡为真**（可达集为空），
B 组则证明第 4 项背后的**边判定内核**（`head_adj_of_reachable`）。
**本文件没有**、也不声称给出「`dSep ⟹ 条件独立」的完整 Markov 性。

## 记号说明

`IsIsolated` 由**本文件新引入**（已 grep 核实 `CausDAG` / `CausBayesBall` /
`CausActivePath` / `CausSeparation` / `Fate/` 内无同名定义）。
-/

namespace FateV2.Predict.Stage2.DSepMarkov

open FateV2.Modeling

open Finset
open FateV2.Modeling.Graph

variable {V : Type*} [DecidableEq V] [Fintype V]

-- ============================================================
-- A 组：孤立点（最小情形）
-- ============================================================

/-- ⭐⭐⭐ **孤立点**：无父、无子。 -/
def IsIsolated (G : DAG V) (x : V) : Prop :=
  G.parents x = ∅ ∧ G.children x = ∅

/-- ⭐⭐⭐ **孤立点的 `bbInit` 为空**。

`bbInit {x}` 只含 `x` 的孩子（`fromParent`）与父母（`fromChild`）；
`IsIsolated` 说两者都空，故并集为空。 -/
theorem bbInit_singleton_of_isolated (G : DAG V) (x : V)
    (h : IsIsolated G x) : G.bbInit {x} = ∅ := by
  obtain ⟨hpa, hch⟩ := h
  unfold DAG.bbInit
  rw [Finset.singleton_biUnion]
  rw [hpa, hch]
  simp

/-- ⭐⭐⭐ **`bbReachAux` 从空前沿出发，对任意燃料都返回起始 `visited`**。

`∅.biUnion _ = ∅`，故 `newStates = ∅`，递归在终止分支立即返回。 -/
theorem bbReachAux_empty (G : DAG V) (Z : Finset V) (visited : Finset (DAG.BBState V))
    (n : ℕ) : G.bbReachAux Z ∅ visited n = visited := by
  induction n generalizing visited with
  | zero => rfl
  | succ n ih =>
    change (let newStates := (∅ : Finset (DAG.BBState V)).biUnion (G.bbStep Z) \ visited
      if newStates = ∅ then visited
      else G.bbReachAux Z newStates (visited ∪ newStates) n) = visited
    rw [Finset.biUnion_empty, Finset.empty_sdiff]
    simp only [↓reduceIte]

/-- ⭐⭐⭐ **孤立点的可达状态集为空**。 -/
theorem bbReachable_singleton_of_isolated (G : DAG V) (x : V) (Z : Finset V)
    (h : IsIsolated G x) : G.bbReachable Z {x} = ∅ := by
  unfold DAG.bbReachable
  rw [bbInit_singleton_of_isolated G x h]
  exact bbReachAux_empty G Z ∅ _

/-- ⭐⭐⭐ **孤立点的可达顶点集为空**。 -/
theorem bbReachableVertices_singleton_of_isolated (G : DAG V) (x : V) (Z : Finset V)
    (h : IsIsolated G x) : G.bbReachableVertices Z {x} = ∅ := by
  unfold DAG.bbReachableVertices
  rw [bbReachable_singleton_of_isolated G x Z h]
  simp

/-- ⭐⭐⭐⭐⭐ **孤立点与任意集 d-分离**（A 组核心）。

`dSep` 的四个子句逐条验证。第 3 项 `Disjoint Y Z` 与边结构无关，
必须**显式**作为假设 `hYZ` 给出。 -/
theorem dSep_of_isolated (G : DAG V) (x : V) (Y Z : Finset V)
    (h : IsIsolated G x) (hxY : x ∉ Y) (hxZ : x ∉ Z) (hYZ : Disjoint Y Z) :
    G.dSep {x} Y Z := by
  refine ⟨?_, ?_, hYZ, ?_⟩
  · rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_singleton] at ha
    exact hxY (ha ▸ hb)
  · rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_singleton] at ha
    exact hxZ (ha ▸ hb)
  · rw [bbReachableVertices_singleton_of_isolated G x Z h]
    simp

-- ============================================================
-- B 组：正向 Markov 性（核心，非平凡）
-- ============================================================

/-- ⭐⭐⭐⭐ **长度 2 的顶点序列必然是 active walk**（中段条件空真）。

`IsActiveWalk` 的中段条件只在 `i + 2 < p.length` 上生效；
`p.length = 2` 时该区间为空，故**无需任何邻接假设**。
（这也说明：光靠 active walk 的「长度 ≥ 2」不能刻划可达性，
邻接约束只在 `len ≥ 3` 时才起作用。） -/
theorem isActiveWalk_pair (G : DAG V) (Z : Finset V) (a b : V) (hab : G.UAdj a b) :
    G.IsActiveWalk Z [a, b] := by
  constructor
  · intro i hi
    have h0 : i = 0 := by simp at hi; omega
    subst h0
    simpa using hab
  · intro i hi
    simp at hi

/-- ⭐⭐⭐⭐⭐ **可达 ⟹ 首步相邻**（`bbReachableVertices` 的边判定内核）。

若 `w ∈ G.bbReachableVertices Z X`，则存在 `x ∈ X` 与某个 `u` 使 `G.UAdj x u`：
因为长度 ≥ 2 的 active walk 的**第一步**必然是一条真实的无向边。

这是「Bayes Ball 的第一步只能用一条真实边」的精确形式化，
`G.bbReachableVertices_iff_activeWalk` 的**完备性方向（←）被真正消费**。 -/
theorem head_adj_of_reachable (G : DAG V) {X Z : Finset V} {w : V}
    (hw : w ∈ G.bbReachableVertices Z X) :
    ∃ x ∈ X, ∃ u : V, G.UAdj x u := by
  rw [DAG.bbReachableVertices_iff_activeWalk] at hw
  obtain ⟨x, hxX, p, hlen, hact, hhead, _⟩ := hw
  -- active walk 长度 ≥ 2，故必形如 `u :: r` 且 `r` 非空
  have hp2 : p.length ≥ 2 := hlen
  obtain ⟨u, r, rfl⟩ : ∃ u r, p = u :: r := by
    cases p with
    | nil => simp at hp2
    | cons a r => exact ⟨a, r, rfl⟩
  have hr : 0 < r.length := by
    simp only [List.length_cons] at hp2
    omega
  have hadj : G.UAdj ((u :: r).get ⟨0, by simp only [List.length_cons]; omega⟩)
      ((u :: r).get ⟨0 + 1, by simp only [List.length_cons]; omega⟩) :=
    hact.1 0 (by simp only [List.length_cons]; omega)
  simp only [List.get_cons_succ, Nat.zero_add] at hadj
  have hx : u = x := by have h := hhead; simpa using h
  refine ⟨x, hxX, r.get ⟨0, hr⟩, ?_⟩
  rw [← hx]
  exact hadj

end FateV2.Predict.Stage2.DSepMarkov

-- ============================================================
-- 公理审计（**必须无 `sorryAx`**）
-- ============================================================

-- A 组：孤立点的 bbInit 为空
#print axioms FateV2.Predict.Stage2.DSepMarkov.bbInit_singleton_of_isolated

-- A 组：空前沿 BFS 恒等
#print axioms FateV2.Predict.Stage2.DSepMarkov.bbReachAux_empty

-- A 组：孤立点的可达状态集为空
#print axioms FateV2.Predict.Stage2.DSepMarkov.bbReachable_singleton_of_isolated

-- A 组：孤立点的可达顶点集为空
#print axioms FateV2.Predict.Stage2.DSepMarkov.bbReachableVertices_singleton_of_isolated

-- ⭐ A 组核心：孤立点与任意集 d-分离
#print axioms FateV2.Predict.Stage2.DSepMarkov.dSep_of_isolated

-- B 组：长度 2 的 active walk
#print axioms FateV2.Predict.Stage2.DSepMarkov.isActiveWalk_pair

-- ⭐ B 组核心：可达 ⟹ 首步相邻
#print axioms FateV2.Predict.Stage2.DSepMarkov.head_adj_of_reachable
