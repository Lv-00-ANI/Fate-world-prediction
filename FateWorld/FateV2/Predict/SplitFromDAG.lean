/-
# 缺口 A：`dSep ⟹ Split` 的**确切形式**

本文件对「图侧 `dSep` 能否引出因子图分离谓词 `Split`」给出**判决性**回答，
全部机检（零 `sorry` / 零 `admit` / 零 `axiom`）。

## 0 一行结论

> **`dSep X Y Z` 本身不蕴含 `Split (readSetOf G) X Y Z`（见 §5 机检反例）；
> 但加上唯一一条额外前提 —— 覆盖 `X ∪ Y ∪ Z = univ` —— 就**蕴含**（§3.4）。
> 前提里**完全不需要任何父闭假设**。**

这与 `Fate/View19FactorGraphSplit.lean` 文档 §0.1 的表述需要**精确化**：
该文件说“`dSep ⟹ Split` 不一般成立”，这是对的；但它把“可证子类”归因于
**查询集父闭**，这只是一个**充分**条件，而**真正的分界线是覆盖条件**。
本文件把这条边界钉死：

| 假设 | `dSep ⟹ Split`？ | 机检 |
|---|---|---|
| `dSep X Y Z` 单独 | ✗ | `dSep_not_implies_split`（§5） |
| `dSep X Y Z` + `X ∪ Y ∪ Z = univ` | ✓ | `split_of_dSep`（§3.4） |
| 父闭 `X∪Z`、`Y∪Z` + 覆盖（**不需 `dSep`**） | ✓ | `split_of_parentClosed`（§2） |

注意上表第 3 行：父闭路线**根本不用 `dSep`**，所以它不是「`dSep ⟹ Split`」的
子类，而是一条**与 `dSep` 正交**的充分条件。真正消费 `dSep` 的是第 2 行。

## 1 为什么覆盖条件是本质的（数学直觉）

`Split (readSetOf G) X Y Z` 说的是：**每个读集 `R v = {v} ∪ pa(v)` 整块落在
`X ∪ Z` 或 `Y ∪ Z` 的一侧** —— 禁止「超边横跨 `X` 与 `Y`」。

* 取 `v ∈ X`。若某个父 `u ∈ Y`，则 `u → v` 是一条从 `Y` 进 `X` 的边，
  Bayes Ball 从 `X` 出发一步步就能滚到 `Y`，与 `dSep` 矛盾。
  **⟹ `pa(v) ∩ Y = ∅`**（`not_edge_of_dSep_right`）。
* 取 `v ∈ Y`。同理 `pa(v) ∩ X = ∅`（`not_edge_of_dSep_left`）。
* 取 `v ∈ Z`。若 `pa(v)` 同时碰到 `X`（经 `x`）和 `Y`（经 `y`），
  则 `x → v ← y` 是一个 **`Z` 内被打通的 collider**：球到 `v`（`v ∈ Z`）后
  会沿 `parents v` 继续滚到 `y`，与 `dSep` 矛盾。
  **⟹ `pa(v)` 最多碰到 `X`、`Y` 之一**（`no_collider_in_Z`）。

三条合起来：每个 `pa(v)` 都不会**横跨** `X` 与 `Y`。此时 `Split` 的唯一剩余
障碍是「`pa(v)` 含 `X∪Y∪Z` 之外的顶点」。**覆盖条件 `X ∪ Y ∪ Z = univ`
恰好排除它**，于是 `pa(v) ⊆ X∪Z` 或 `pa(v) ⊆ Y∪Z`。

反过来说，**没有覆盖条件时**第三条之外的两条（`v ∈ X` / `v ∈ Y`）仍然成立，
但 `v ∉ X∪Y∪Z` 的顶点可以拥有任意横跨的读集 —— 这正是 §5 反例的机制
（`V = Fin 3`，collider `0 → 2 ← 1`，`v = 2 ∉ X∪Y∪Z`）。

## 2 文件结构

* §1 `parentClosed`（定义）
* §2 `split_of_parentClosed` —— 父闭 + 覆盖 ⟹ `Split`（**不消费 `dSep`**）
* §3 `dSep` 的三条“禁边”引理 + `split_of_dSep` —— `dSep` + 覆盖 ⟹ `Split`
* §4 下游串联：`Factorizes` + `dSep` + 覆盖 ⟹ `CondIndep`（`Z = ∅`）
* §5 机检反例：`dSep` 单独**不**蕴含 `Split`（`V = Fin 3`，`decide` 可判定）
* §6 诚实边界

## 3 依赖

* `FateV2.Predict.FactorizesToHyper.readSetOf` / `condIndep_of_factorizes` —— `Fate/FactorizesToHyper.lean`
* `FateV2.Predict.View19.Split` —— `Fate/View19FactorGraphSplit.lean`
* `Causalean.Graph.DAG.dSep` / `dSep_symm` / `bbReachable_init_subset` /
  `bbReachable_bbStep_subset` / `bbStep` / `bbInit` —— `CausSeparation.lean`、
  `CausBayesBall.lean`
* `Causalean.Graph.DAG.parents` / `mem_parents` / `children` / `mem_children` —— `CausDAG.lean`

**本文件不修改任何既有模块；不写 `Fate/` 目录；不改 `Fate.lean`。**
-/

import FateWorld.FateV2.Predict.FactorizesToHyper
import FateWorld.FateV2.Modeling.CausSeparation
namespace FateV2.Predict

open FateV2.Modeling
namespace SplitFromDAG

open Finset FateV2.Modeling.Graph

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-!
  # Predict · SplitFromDAG

  ## 迁移登记
  - 来源：`FateWorld/Legacy/SplitFromDAG.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorizesToHyper, _root.CausSeparation
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §1 **`parentClosed`**：`S` 对父运算封闭
  =========================================================================== -/

/-- ⭐ **`S` 父闭**：`S` 中每个顶点的父集仍落在 `S` 内。 -/
def parentClosed (G : FateV2.Modeling.Graph.DAG V) (S : Finset V) : Prop :=
  ∀ v ∈ S, G.parents v ⊆ S

/-! ===========================================================================
  §2 父闭 ⟹ `Split`（**不消费 `dSep`**）

  ⚠ 这是「父闭路线」，与 `dSep` **正交**：它对任何 DAG 都成立，
  `dSep` 完全用不上。登记在此是为了**对比**：§3 的 `dSep` 路线
  **不需要**这两条父闭前提，只需要覆盖。
  =========================================================================== -/

/-- ⭐⭐⭐ **父闭 + 覆盖 ⟹ `Split`**。

若 `X ∪ Z` 与 `Y ∪ Z` 都父闭，且 `X ∪ Y ∪ Z = univ`，则每个 `v` 落在
`X∪Z` 或 `Y∪Z` 中，其读集 `{v} ∪ pa(v)` 被对应的父闭性整块收住。

**⚠ 本引理不使用 `dSep`。** -/
theorem split_of_parentClosed (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V)
    (hXZ : parentClosed G (X ∪ Z)) (hYZ : parentClosed G (Y ∪ Z))
    (hcover : X ∪ Y ∪ Z = univ) :
    FateV2.Predict.View19.Split (FateV2.Predict.FactorizesToHyper.readSetOf G) X Y Z := by
  intro v
  have hv : v ∈ X ∪ Y ∪ Z := by rw [hcover]; exact Finset.mem_univ v
  have hmem : v ∈ X ∪ Z ∨ v ∈ Y ∪ Z := by
    simp only [Finset.mem_union] at hv ⊢
    tauto
  rcases hmem with h | h
  · left
    rw [FateV2.Predict.FactorizesToHyper.readSetOf]
    exact Finset.insert_subset h (hXZ v h)
  · right
    rw [FateV2.Predict.FactorizesToHyper.readSetOf]
    exact Finset.insert_subset h (hYZ v h)

/-! ===========================================================================
  §3 **`dSep` 真正被消费**：`dSep` + 覆盖 ⟹ `Split`

  三条「禁边」引理把 `dSep` 的 Bayes Ball 语义翻译成对 `parents` 的纯组合约束，
  然后 §3.4 把它们拼成 `Split`。
  =========================================================================== -/

/-- 若 `x ∈ X` 且 `x → z`，则 Bayes Ball 状态 `(z, fromParent)` 从 `X` 可达。 -/
theorem bb_state_of_edge (G : FateV2.Modeling.Graph.DAG V) (Z X : Finset V) {x z : V}
    (hx : x ∈ X) (hxz : G.edge x z) :
    (z, FateV2.Modeling.Graph.DAG.BBDir.fromParent) ∈ G.bbReachable Z X :=
  G.bbReachable_init_subset Z X (by
    simp only [FateV2.Modeling.Graph.DAG.bbInit, Finset.mem_biUnion, Finset.mem_union,
      Finset.mem_map]
    exact ⟨x, hx, Or.inl ⟨z, (FateV2.Modeling.Graph.DAG.mem_children G).mpr hxz, rfl⟩⟩)

/-- ⭐ **禁边（右→左）**：`dSep X Y Z` 禁止从 `X` 直接指进 `Y` 的边。

否则球从 `x ∈ X` 一步滚到 `v ∈ Y`，与 `Disjoint (bbReachableVertices Z X) Y` 矛盾。 -/
theorem not_edge_of_dSep_left (G : FateV2.Modeling.Graph.DAG V) {X Y Z : Finset V}
    (h : G.dSep X Y Z) {u v : V} (hu : u ∈ X) (hv : v ∈ Y) : ¬ G.edge u v := by
  obtain ⟨hXY, hXZ, hYZ, hReach⟩ := h
  intro he
  have hmem : v ∈ G.bbReachableVertices Z X := by
    unfold FateV2.Modeling.Graph.DAG.bbReachableVertices
    exact Finset.mem_image.mpr ⟨_, bb_state_of_edge G Z X hu he, rfl⟩
  exact Finset.disjoint_left.mp hReach hmem hv

/-- ⭐ **禁边（左→右）**：`dSep X Y Z` 禁止从 `Y` 直接指进 `X` 的边（由 `dSep_symm`）。 -/
theorem not_edge_of_dSep_right (G : FateV2.Modeling.Graph.DAG V) {X Y Z : Finset V}
    (h : G.dSep X Y Z) {u v : V} (hu : u ∈ Y) (hv : v ∈ X) : ¬ G.edge u v :=
  not_edge_of_dSep_left G (FateV2.Modeling.Graph.DAG.dSep_symm G X Y Z h) hu hv

/-- ⭐⭐ **`Z` 内无横跨 collider**：`dSep X Y Z` 禁止 `x → z ← y`
（`x ∈ X`、`y ∈ Y`、`z ∈ Z`）。

此时 `z` 是**落在条件集内的 collider**，被激活：球从 `x` 到 `(z, fromParent)`
后，`bbStep`（`fromParent` 且 `z ∈ Z`）把球沿 `parents z` 送到 `y`，
与 `Disjoint (bbReachableVertices Z X) Y` 矛盾。 -/
theorem no_collider_in_Z (G : FateV2.Modeling.Graph.DAG V) {X Y Z : Finset V}
    (h : G.dSep X Y Z) {x y z : V} (hx : x ∈ X) (hy : y ∈ Y)
    (hxz : G.edge x z) (hyz : G.edge y z) (hzZ : z ∈ Z) : False := by
  obtain ⟨hXY, hXZ, hYZ, hReach⟩ := h
  have hstep : (y, FateV2.Modeling.Graph.DAG.BBDir.fromChild) ∈ G.bbReachable Z X := by
    refine G.bbReachable_bbStep_subset Z X (bb_state_of_edge G Z X hx hxz) ?_
    have hnz : ¬ (z ∉ Z) := fun hh => hh hzZ
    have hmem : (y, FateV2.Modeling.Graph.DAG.BBDir.fromChild)
        ∈ (G.parents z).map
            ⟨(·, FateV2.Modeling.Graph.DAG.BBDir.fromChild), fun a b hab => by simpa using hab⟩ :=
      Finset.mem_map.mpr ⟨y, (FateV2.Modeling.Graph.DAG.mem_parents G).mpr hyz, rfl⟩
    simpa [FateV2.Modeling.Graph.DAG.bbStep, hnz] using hmem
  have hmemv : y ∈ G.bbReachableVertices Z X := by
    unfold FateV2.Modeling.Graph.DAG.bbReachableVertices
    exact Finset.mem_image.mpr ⟨_, hstep, rfl⟩
  exact Finset.disjoint_left.mp hReach hmemv hy

/-- ⭐⭐⭐⭐ **`dSep` + 覆盖 ⟹ `Split`**（本文件的核心正定理）。

**只消费 `dSep` 与覆盖条件 `X ∪ Y ∪ Z = univ`；不需要任何父闭假设。**

证明按 `v` 的归属分三类（覆盖保证三类齐全）：
* `v ∈ X`：`pa(v) ∩ Y = ∅`（`not_edge_of_dSep_right`），故 `pa(v) ⊆ X∪Z`；
* `v ∈ Y`：`pa(v) ∩ X = ∅`（`not_edge_of_dSep_left`），故 `pa(v) ⊆ Y∪Z`；
* `v ∈ Z`：`pa(v)` 不能同时碰 `X` 与 `Y`（`no_collider_in_Z`），
  于是按「是否存在 `X`-父」二分，分别得到 `pa(v) ⊆ X∪Z` 或 `pa(v) ⊆ Y∪Z`。 -/
theorem split_of_dSep (G : FateV2.Modeling.Graph.DAG V) (X Y Z : Finset V)
    (hdsep : G.dSep X Y Z)
    (hcover : X ∪ Y ∪ Z = univ) :
    FateV2.Predict.View19.Split (FateV2.Predict.FactorizesToHyper.readSetOf G) X Y Z := by
  intro v
  have hv : v ∈ X ∪ Y ∪ Z := by rw [hcover]; exact Finset.mem_univ v
  simp only [Finset.mem_union] at hv
  have key : ∀ u ∈ G.parents v, u ∈ X ∪ Y ∪ Z := by
    intro u _; rw [hcover]; exact Finset.mem_univ u
  rcases hv with (hx | hy) | hz
  · -- v ∈ X
    left
    refine Finset.insert_subset (Finset.mem_union.mpr (Or.inl hx)) (fun u hu => ?_)
    have hu' := key u hu
    simp only [Finset.mem_union] at hu'
    have he : G.edge u v := (FateV2.Modeling.Graph.DAG.mem_parents G).mp hu
    rcases hu' with (hux | huy) | huz
    · exact Finset.mem_union.mpr (Or.inl hux)
    · exact absurd he (not_edge_of_dSep_right G hdsep huy hx)
    · exact Finset.mem_union.mpr (Or.inr huz)
  · -- v ∈ Y
    right
    refine Finset.insert_subset (Finset.mem_union.mpr (Or.inl hy)) (fun u hu => ?_)
    have hu' := key u hu
    simp only [Finset.mem_union] at hu'
    have he : G.edge u v := (FateV2.Modeling.Graph.DAG.mem_parents G).mp hu
    rcases hu' with (hux | huy) | huz
    · exact absurd he (not_edge_of_dSep_left G hdsep hux hy)
    · exact Finset.mem_union.mpr (Or.inl huy)
    · exact Finset.mem_union.mpr (Or.inr huz)
  · -- v ∈ Z
    by_cases hX : ∃ u ∈ G.parents v, u ∈ X
    · -- 存在 X-父 ⟹ pa(v) 不能碰 Y ⟹ pa(v) ⊆ X ∪ Z
      left
      refine Finset.insert_subset (Finset.mem_union.mpr (Or.inr hz)) (fun u hu => ?_)
      have hu' := key u hu
      simp only [Finset.mem_union] at hu'
      have he : G.edge u v := (FateV2.Modeling.Graph.DAG.mem_parents G).mp hu
      rcases hu' with (hux | huy) | huz
      · exact Finset.mem_union.mpr (Or.inl hux)
      · obtain ⟨x, hx, hxX⟩ := hX
        exact absurd (no_collider_in_Z G hdsep hxX huy
          ((FateV2.Modeling.Graph.DAG.mem_parents G).mp hx) he hz) id
      · exact Finset.mem_union.mpr (Or.inr huz)
    · -- 无 X-父 ⟹ 结合覆盖得 pa(v) ⊆ Y ∪ Z
      right
      refine Finset.insert_subset (Finset.mem_union.mpr (Or.inr hz)) (fun u hu => ?_)
      have hu' := key u hu
      simp only [Finset.mem_union] at hu'
      rcases hu' with (hux | huy) | huz
      · exact absurd ⟨u, hu, hux⟩ hX
      · exact Finset.mem_union.mpr (Or.inl huy)
      · exact Finset.mem_union.mpr (Or.inr huz)

/-! ===========================================================================
  §4 下游串联：`Factorizes` + `dSep` + 覆盖 ⟹ `CondIndep`（`Z = ∅`）

  `condIndep_of_factorizes`（`Fate/FactorizesToHyper.lean`）要求的正是
  `Split (readSetOf G) X Y ∅` 与 `X ∪ Y = univ` —— §3 的 `split_of_dSep`
  在 `Z = ∅` 时**恰好**补上了缺的那一环。
  =========================================================================== -/

/-- ⭐ 收窄形式：`Z = ∅` 时 `dSep X Y ∅` + `X ∪ Y = univ` 直接给 `Split`。 -/
theorem split_of_dSep_emptyZ (G : FateV2.Modeling.Graph.DAG V) (X Y : Finset V)
    (hdsep : G.dSep X Y ∅) (hcover : X ∪ Y = univ) :
    FateV2.Predict.View19.Split (FateV2.Predict.FactorizesToHyper.readSetOf G) X Y ∅ := by
  refine split_of_dSep G X Y ∅ hdsep ?_
  rw [Finset.union_empty]; exact hcover

section Chain

variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

/-- ⭐⭐⭐⭐ **全链**：`Factorizes p G` + `dSep X Y ∅` + `X ∪ Y = univ` ⟹
`CondIndep p X Y ∅`。

这是「图 ⟹ 概率」桥在 `Z = ∅` 情形的**完整闭合链条**：
$$p \text{ 因子分解于 } G \;\wedge\; X \perp_d Y \mid \emptyset \;\wedge\; X\cup Y = V
\;\Longrightarrow\; X \perp\!\!\!\perp_p Y \mid \emptyset.$$ -/
theorem condIndep_of_factorizes_dSep
    (p : FateV2.Predict.FactorMarkov.Joint V α) (G : FateV2.Modeling.Graph.DAG V)
    (hfac : FateV2.Predict.FactorMarkov.Factorizes p G) {X Y : Finset V}
    (hdsep : G.dSep X Y ∅) (hcover : X ∪ Y = univ) :
    FateV2.Predict.FactorMarkov.CondIndep p X Y ∅ := by
  have hd : Disjoint X Y := hdsep.1
  exact FateV2.Predict.FactorizesToHyper.condIndep_of_factorizes p G hfac
    (split_of_dSep_emptyZ G X Y hdsep hcover) hd hcover

end Chain

/-! ===========================================================================
  §5 **机检反例**：`dSep` 单独**不**蕴含 `Split`

  **最小反例**：`V = Fin 3`，collider 图 `0 → 2 ← 1`，查询 `X = {0}`、`Y = {1}`、
  `Z = ∅`。

  * `dSep {0} {1} ∅` **成立**：路径 `0 → 2 ← 1` 的唯一阻塞点是 collider `2`，
    而 `2 ∉ Z` 且 `2` 不是 `∅` 的祖先 ⟹ 该路径被阻塞；三对集合两两不交；
    Bayes Ball 从 `0` 出发到 `2` 时按 collider 规则停住，到不了 `1`。
  * `Split (readSetOf G) {0} {1} ∅` **不成立**：读集
    `readSetOf G 2 = {0, 1, 2}` 既不是 `{0}` 的子集，也不是 `{1}` 的子集
    —— 顶点 `2` **不在覆盖 `X∪Y∪Z = {0,1}` 之内**，它能自由地横跨两侧。

  这正好把“缺的是什么”指出来：**缺的是覆盖条件**，不是父闭。
  =========================================================================== -/

/-- Collider `0 → 2 ← 1` 的边关系。 -/
def colliderEdge : Fin 3 → Fin 3 → Prop :=
  fun u v => (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)

/-- 上述边关系的可判定性。 -/
def colliderEdgeDec : DecidableRel colliderEdge := by
  intro u v; unfold colliderEdge; infer_instance

/-- 拓扑秩：`0,1 ↦ 0`；`2 ↦ 1`。用来说明无环。 -/
def colliderRank (x : Fin 3) : ℕ := if x = 2 then 1 else 0

theorem colliderEdge_rank_lt {u v : Fin 3} (h : colliderEdge u v) :
    colliderRank u < colliderRank v := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · unfold colliderRank; decide
  · unfold colliderRank; decide

/-- ⭐ **反例图**：`V = Fin 3` 上的 collider `0 → 2 ← 1`。 -/
def colliderDAG : FateV2.Modeling.Graph.DAG (Fin 3) where
  edge := colliderEdge
  decEdge := colliderEdgeDec
  acyclic := by
    intro v h
    have hmono : ∀ {a b : Fin 3},
        Relation.TransGen colliderEdge a b → colliderRank a < colliderRank b := by
      intro a b hab
      induction hab with
      | single h => exact colliderEdge_rank_lt h
      | tail _ hbc ih => exact lt_trans ih (colliderEdge_rank_lt hbc)
    exact absurd (hmono h) (lt_irrefl _)

/-- 反例中 `dSep {0} {1} ∅` **成立**（`decide` 判定）。 -/
theorem colliderDAG_dSep : colliderDAG.dSep {0} {1} (∅ : Finset (Fin 3)) := by
  decide

/-- 反例中 `Split (readSetOf G) {0} {1} ∅` **不成立**（`decide` 判定）。 -/
theorem colliderDAG_not_split :
    ¬ FateV2.Predict.View19.Split (FateV2.Predict.FactorizesToHyper.readSetOf colliderDAG)
        {0} {1} (∅ : Finset (Fin 3)) := by
  unfold FateV2.Predict.View19.Split FateV2.Predict.FactorizesToHyper.readSetOf
  decide

/-- ⭐⭐⭐⭐⭐ **判决**：`dSep` **不**一般蕴含 `Split`。

存在一个 `V`（取 `V = Fin 3`）、一张 DAG（`colliderDAG`）与查询 `X, Y, Z`
使得 `dSep X Y Z` 成立而 `Split (readSetOf G) X Y Z` 不成立。 -/
theorem dSep_not_implies_split_fin3 :
    ¬ (∀ (G : FateV2.Modeling.Graph.DAG (Fin 3)) (X Y Z : Finset (Fin 3)),
        G.dSep X Y Z → FateV2.Predict.View19.Split (FateV2.Predict.FactorizesToHyper.readSetOf G) X Y Z) := by
  intro h
  exact colliderDAG_not_split
    (h colliderDAG {0} {1} ∅ colliderDAG_dSep)

end SplitFromDAG

end FateV2.Predict