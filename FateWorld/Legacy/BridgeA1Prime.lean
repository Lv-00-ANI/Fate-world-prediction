import FateWorld.Legacy.BridgeA1

/-! ===========================================================================
  `Fate/BridgeA1Prime` —— **A1 的正确替代：`pa G v ∩ de G v = ∅`**

  ## 0 背景与定位

  清单里的 **A1** 陈述为 `pa G v ∩ nd G v = ∅`。
  该陈述已被 **证伪**（`Fate/BridgeA1` 的 `a1_universally_false`）：
  真实关系是 `pa G v ⊆ nd G v`（`pa_subset_nonDescendants`），
  交集不但不空，反而**塌缩为整个 `pa G v`**。

  **A1 的正确不交陈述**是「父节点集与**后代集**不交」：

  $$\mathrm{pa}_G(v)\;\cap\;\mathrm{de}_G(v)\;=\;\varnothing,$$

  其中 `de G v` 记 `v` 的**（严格）后代集** `G.descendants v`。

  | 编号 | 内容 | 状态 |
  |---|---|---|
  | **A1'** | `pa G v ∩ de G v = ∅` | ✅ 零缺口，无条件定理 |
  | **A1'.mem** | `u ∈ pa v ⟹ u ∉ de v` | ✅ 零缺口 |
  | **A1'.symm** | `w ∈ de v ⟹ w ∉ pa v` | ✅ 零缺口 |
  | **A1'.card** | `#(pa v ∪ de v) = #(pa v) + #(de v)` | ✅ 零缺口 |
  | **A1'.false_of_nd** | 对照：`pa ∩ nd = pa`（即 A1 的塌缩）| ✅ 零缺口（重申）|

  ## 1 为什么这是「正确的」不交陈述

  每条边 `u → v`（即 `u ∈ pa v`）与「存在 `v → … → u` 的有向路径」（即 `u ∈ de v`）
  不能共存：若共存，则 `v` 沿路径回到自身，构成有向环，
  与 `DAG.acyclic` 及 `isAncestor_irrefl` 矛盾。

  因此「父」与「后代」在 DAG 中天然互斥 —— 这**正是** A3/A4 里
  「父节点因子 `φ_u` 不读 `v` 的取值」的图论根据：
  `v` 的取值不会改动指向 `v` 的边的因子里除了 `v` 以外的坐标关系，
  而 `u` 不是 `v` 的后代，故 `φ_u` 中的图结构一致性由 `de` 与 `pa` 的不交保证。

  ## 2 纪律确认

  * 单文件、`lake env lean Fate/BridgeA1Prime.lean` 验证；
  * 不改 `Fate.lean`，不改任何已有模块；
  * 零 `sorry` / `admit` / `axiom`；
  * 未使用 `mass` 塔性质；
  * 下面每条都是**无条件定理**，没有把结论写进前件。
  =========================================================================== -/

namespace Fate
namespace BridgeA1Prime

open Finset Fate.DAGFactorization

variable {V : Type u} [DecidableEq V] [Fintype V]

/-- **后代集别名** `de G v` := `v` 的（严格）后代集 `G.descendants v`。

清单以 `de` 记后代集；本文件把它显式定义为 `G.descendants v` 的缩写，
使陈述 `pa G v ∩ de G v = ∅` 与定义一一对应。 -/
abbrev de (G : Causalean.Graph.DAG V) (v : V) : Finset V := G.descendants v

/-- **`de` 的成员判据**：`u ∈ de G v ↔ isAncestor v u`。 -/
theorem mem_de {G : Causalean.Graph.DAG V} {u v : V} :
    u ∈ de G v ↔ G.isAncestor v u :=
  Causalean.Graph.DAG.mem_descendants G

/-! ## §1 主定理：`pa ∩ de = ∅` -/

/-- ⭐⭐⭐ **A1'（主定理）**：父节点集与后代集不交。

$$\mathrm{pa}_G(v)\;\cap\;\mathrm{de}_G(v)=\varnothing.$$

**证明**：设 `u ∈ pa v ∩ de v`。
* `u ∈ pa v` ⟹ `edge u v`（`mem_pa`）；
* `u ∈ de v` ⟹ `isAncestor v u`（`mem_de`）。

于是 `isAncestor v v`（`isAncestor_trans` 与 `isAncestor.edge`），
与 `isAncestor_irrefl` 矛盾。

**与 A1 的关键差别**：这里第二支用的是 `de v` 的成员判据 `isAncestor v u`，
而不是 `nd v` 的判据 `¬ isAncestor v u ∧ u ≠ v`。
后者对 `u ∈ pa v` **必然被满足**（故 A1 假），前者则**必然被违反**（故 A1' 真）。 -/
theorem pa_inter_de_eq_empty (G : Causalean.Graph.DAG V) (v : V) :
    pa G v ∩ de G v = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro u hu
  rw [Finset.mem_inter, mem_pa, mem_de] at hu
  exact Causalean.Graph.DAG.isAncestor_irrefl G v
    (Causalean.Graph.DAG.isAncestor_trans G hu.2
      (Causalean.Graph.DAG.isAncestor.edge hu.1))

/-- **A1'.mem**：父节点不是后代。 -/
theorem not_mem_de_of_mem_pa {G : Causalean.Graph.DAG V} {u v : V}
    (hu : u ∈ pa G v) : u ∉ de G v := by
  intro hd
  rw [mem_pa] at hu
  rw [mem_de] at hd
  exact Causalean.Graph.DAG.isAncestor_irrefl G v
    (Causalean.Graph.DAG.isAncestor_trans G hd
      (Causalean.Graph.DAG.isAncestor.edge hu))

/-- **A1'.symm**：后代不是父节点。 -/
theorem not_mem_pa_of_mem_de {G : Causalean.Graph.DAG V} {w v : V}
    (hw : w ∈ de G v) : w ∉ pa G v := by
  intro hu
  exact not_mem_de_of_mem_pa hu hw

/-- **A1'.disjoint**：`Disjoint` 形式（与 `Finset.disjoint_left` 互通的等价陈述）。 -/
theorem disjoint_pa_de (G : Causalean.Graph.DAG V) (v : V) :
    Disjoint (pa G v) (de G v) := by
  rw [Finset.disjoint_left]
  exact fun u hu hd => not_mem_de_of_mem_pa hu hd

/-- **A1'.card**：不交 ⟹ 基数可加。`#(pa v ∪ de v) = #(pa v) + #(de v)`。 -/
theorem card_pa_union_de (G : Causalean.Graph.DAG V) (v : V) :
    (pa G v ∪ de G v).card = (pa G v).card + (de G v).card :=
  Finset.card_union_of_disjoint (disjoint_pa_de G v)

/-! ## §2 对照：A1（`pa ∩ nd`）为何不是不交陈述（重申 + 自足化）

以下三条与 `Fate.BridgeA1` 的结论一致，重述以便本文件自足，
并**明确区分** A1 的「塌缩」与 A1' 的「不交」。
（证明直接调用 `Fate.BridgeA1.pa_inter_nonDescendants_eq` 等，
不重新发明。） -/

/-- **A1（原陈述）的真相**：`pa ∩ nd` 塌缩为 `pa`，与 `pa ∩ de = ∅` 形成对照。 -/
theorem pa_inter_nd_eq_pa (G : Causalean.Graph.DAG V) (v : V) :
    pa G v ∩ G.nonDescendants v = pa G v :=
  Fate.BridgeA1.pa_inter_nonDescendants_eq G v

/-- **A1' 与 A1 的分野**：`pa v` 中的任一元素都落在 `nd v` 里、且**不**落在 `de v` 里。 -/
theorem pa_mem_nd_and_not_de (G : Causalean.Graph.DAG V) {u : V} (hu : u ∈ pa G v) :
    u ∈ G.nonDescendants v ∧ u ∉ de G v :=
  ⟨Fate.BridgeA1.pa_subset_nonDescendants G v hu, not_mem_de_of_mem_pa hu⟩

/-- **A1' 的可证性对照**：`pa G v ∩ de G v = ∅` 对**所有** DAG、所有 `v` 成立，
无需任何附加条件（对比 `a1_universally_false` 中被否证的 A1）。 -/
theorem pa_inter_de_empty_universal :
    ∀ (W : Type) [DecidableEq W] [Fintype W]
      (G : Causalean.Graph.DAG W) (v : W), pa G v ∩ de G v = ∅ :=
  fun _ _ _ G v => pa_inter_de_eq_empty G v

end BridgeA1Prime
end Fate
