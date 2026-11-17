import FateWorld.FateV2.Predict.FactorRecursionRouteB
/-!
  # Predict · G1ParentNonDescendant

  ## 迁移登记
  - 来源：`FateWorld/Legacy/G1ParentNonDescendant.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FactorRecursionRouteB
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/G1ParentNonDescendant` —— **第 1 路的交付：G1 的裁决**

  ## 结论（重要）

  **任务书里给出的 G1 陈述「`pa G v ∩ nd(v) = ∅`」是 FALSE 的。**
  本文件给出：

  | # | 内容 | 状态 |
  |---|---|---|
  | **G1.refute** | `pa G v ⊆ G.nonDescendants v`（对**任意** DAG、任意 `v`）| ✅ **零缺口，已证** |
  | **G1.counter** | 具体反例：`Fin 2` 上的单边 DAG，`pa 1 ∩ nd 1 = {0} ≠ ∅` | ✅ **零缺口，已证** |
  | **G1′** | `pa G v ∩ descendants v = ∅`（**正确的**不交陈述）| ✅ **零缺口，已证** |
  | **G2** | `w ∈ nd(v) ⟹ v ∉ pa G w`（G4 真正需要的图论输入）| ✅ **零缺口，已证** |

  ## 为什么 G1 是错的（一句话）

  在 `CausDAG.lean` 里
  `nonDescendants v = univ.filter (fun w => ¬ isAncestor v w ∧ w ≠ v)`
  —— 即「`v` **到达不了**的、且不是 `v` 自身的点」。
  而父节点 `u ∈ pa v` 满足 `edge u v`，若还有 `isAncestor v u` 则
  `isAncestor v v`（传递性），与 `isAncestor_irrefl` 矛盾。
  **所以每个父节点都必然落在 `nd(v)` 里**：`pa G v ⊆ nd(v)`。

  故 `pa ∩ nd = pa`，只在 `v` 是**源点**（无父）时才为空。

  ⟹ 换言之：**`LMG` 定义里的 `nd ∪ pa` 就是 `nd`**（`pa ⊆ nd`），
  这不是 bug，而是 `nonDescendants` 这一口径的**必然结果**。
  `LMG` 的 `mass (nd ∪ pa')` **不需要**、也**不能**指靠 `pa ∩ nd = ∅`。

  ## 对 G4 的影响（给第 2/3 路的交接说明）

  G4「把 `v` 边缘化掉、剩下的因子仍分解」真正需要的图论事实**不是** G1，
  而是下面两条（本文件都已证、零缺口）：

  * **G1′** `pa G v ∩ descendants v = ∅`
    —— 父节点**不是** `v` 的后代（否则成环）。这才是「`v` 的取值不影响 `φ_u`，`u ∈ pa v`」。
  * **G2** `w ∈ nd(v) ⟹ v ∉ pa G w`
    —— 非后代 `w` 的因子 `φ_w` **不读** `v`（否则 `edge v w` ⇒ `w` 是后代）。
    这已在 `FactorRecursionRouteB.phi_eq_of_nondesc` 里用过。

  ⚠ **纪律确认**：本文件不含 `sorry`、不含 `axiom`，
  也没有把任何结论写进前件（这些是**无条件**定理）。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace FactorRecursionRouteB

open Finset Fate.DAGFactorization

variable {V : Type u} [DecidableEq V] [Fintype V]

/-! ## §1 G1 的否决：`pa ⊆ nd`（不是不交，而是包含！） -/

/-- ❌ **G1 反证（核心）**：**每个父节点都是非后代**。

$$\mathrm{pa}_G(v)\subseteq \mathrm{nd}_G(v).$$

**证明**：设 `u ∈ pa G v`，即 `edge u v`。
* `u ≠ v`：否则 `edge v v`，违反 `irrefl`；
* `¬ isAncestor v u`：否则 `isAncestor v u` 与 `edge u v` 经 `isAncestor_trans`
  给出 `isAncestor v v`，违反 `isAncestor_irrefl`。

⟹ `u ∈ univ.filter (fun w => ¬ isAncestor v w ∧ w ≠ v) = nonDescendants v`。 -/
theorem pa_subset_nonDescendants (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    pa G v ⊆ G.nonDescendants v := by
  intro u hu
  rw [mem_pa] at hu
  rw [FateV2.Modeling.Graph.DAG.nonDescendants, Finset.mem_filter]
  refine ⟨Finset.mem_univ u, ⟨?_, ?_⟩⟩
  · -- `¬ isAncestor v u`
    intro hanc
    exact FateV2.Modeling.Graph.DAG.isAncestor_irrefl G v
      (FateV2.Modeling.Graph.DAG.isAncestor_trans G hanc (FateV2.Modeling.Graph.DAG.isAncestor.edge hu))
  · -- `u ≠ v`
    intro huv
    rw [huv] at hu
    exact FateV2.Modeling.Graph.DAG.irrefl G v hu

/-- ❌ **G1（字面）被证伪**：`pa G v ∩ nd(v)` 等于 `pa G v`。

⟹ 只要 `v` 有父节点，交集就非空。**G1 不能作为任何证明的前件。** -/
theorem pa_inter_nonDescendants (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    pa G v ∩ G.nonDescendants v = pa G v :=
  Finset.inter_eq_left.mpr (pa_subset_nonDescendants G v)

/-- ❌ **G1（字面）的显式否定形态**：若 `v` 有父节点，则 `pa ∩ nd ≠ ∅`。 -/
theorem pa_inter_nonDescendants_nonempty (G : FateV2.Modeling.Graph.DAG V) {v : V}
    (hv : (pa G v).Nonempty) : (pa G v ∩ G.nonDescendants v).Nonempty := by
  rw [pa_inter_nonDescendants]
  exact hv

/-! ## §2 具体反例：`Fin 2` 上的单边 DAG -/

/-- 「箭头」DAG：`Fin 2` 上唯一一条边 `0 → 1`。 -/
def arrowDAG : FateV2.Modeling.Graph.DAG (Fin 2) where
  edge := fun u v => u = 0 ∧ v = 1
  decEdge := fun u v => inferInstanceAs (Decidable (u = 0 ∧ v = 1))
  acyclic := by
    intro v h
    have hstep : ∀ a b : Fin 2, (fun u v => u = 0 ∧ v = 1) a b → a.val < b.val := by
      intro a b hab; rw [hab.1, hab.2]; decide
    have key : ∀ (a : Fin 2)
        (_ : Relation.TransGen (fun u v => u = 0 ∧ v = 1) v a), v.val < a.val := by
      intro a ha
      induction ha with
      | single hab => exact hstep _ _ hab
      | tail _ hab ih => exact Nat.lt_trans ih (hstep _ _ hab)
    exact Nat.lt_irrefl v.val (key v h)

/-- ⭐ **具体反例，G1 为假**：`0 ∈ pa 1 ∩ nd 1`。 -/
theorem g1_counterexample : (pa arrowDAG 1 ∩ arrowDAG.nonDescendants 1).Nonempty := by
  refine ⟨0, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · rw [mem_pa]; exact ⟨rfl, rfl⟩
  · rw [FateV2.Modeling.Graph.DAG.nonDescendants, Finset.mem_filter]
    refine ⟨Finset.mem_univ 0, ⟨?_, ?_⟩⟩
    · intro hanc
      have hstep : ∀ a b : Fin 2, (fun u v => u = 0 ∧ v = 1) a b → a.val < b.val := by
        intro a b hab; rw [hab.1, hab.2]; decide
      have key : ∀ (a : Fin 2)
          (_ : Relation.TransGen (fun u v => u = 0 ∧ v = 1) (1 : Fin 2) a),
          (1 : Fin 2).val < a.val := by
        intro a ha
        induction ha with
        | single hab => exact hstep _ _ hab
        | tail _ hab ih => exact Nat.lt_trans ih (hstep _ _ hab)
      have := key 0 ((FateV2.Modeling.Graph.DAG.isAncestor_iff_transGen (G := arrowDAG)).mp hanc)
      exact absurd this (by decide)
    · decide

/-- ⭐ **`1` 确实有父节点 `0`**（反例非空，故 `pa ∩ nd ≠ ∅` 是实质的）。 -/
theorem arrowDAG_pa_one_nonempty : (pa arrowDAG 1).Nonempty :=
  ⟨0, by rw [mem_pa]; exact ⟨rfl, rfl⟩⟩

/-- ⭐ **与 G1 的直接矛盾**：该 DAG 上 `pa 1 ∩ nd 1` 非空。 -/
theorem g1_is_false : (pa arrowDAG 1 ∩ arrowDAG.nonDescendants 1).Nonempty :=
  pa_inter_nonDescendants_nonempty arrowDAG arrowDAG_pa_one_nonempty

/-! ## §3 正确的替代物：G1′ 与 G2（G4 真正需要的两条） -/

/-- ✅ **G1′（正确的「不交」陈述）**：父节点集与**后代集**不交。

$$\mathrm{pa}_G(v)\cap \mathrm{de}_G(v)=\varnothing.$$

**证明**：`u ∈ pa v` 给 `edge u v`；若同时 `isAncestor v u`，
则 `isAncestor v v`（传递性），与 `isAncestor_irrefl` 矛盾。 -/
theorem pa_disjoint_descendants (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    Disjoint (pa G v) (G.descendants v) := by
  rw [Finset.disjoint_left]
  intro u hu hd
  rw [mem_pa] at hu
  rw [FateV2.Modeling.Graph.DAG.mem_descendants] at hd
  exact FateV2.Modeling.Graph.DAG.isAncestor_irrefl G v
    (FateV2.Modeling.Graph.DAG.isAncestor_trans G hd (FateV2.Modeling.Graph.DAG.isAncestor.edge hu))

/-- ✅ **G2（G4 的直接输入）**：非后代 `w` 的父集**不含** `v`。

$$\bigl(w\in \mathrm{nd}_G(v)\bigr)\ \Longrightarrow\ v\notin \mathrm{pa}_G(w).$$

**证明**：若 `v ∈ pa G w` 则 `edge v w`，故 `isAncestor v w`，
与 `w ∈ nd(v)`（内含 `¬ isAncestor v w`）矛盾。

⟹ 沿 `v` 求和时 `φ_w`（`w ∈ nd`）**不随 `v` 变化**，这正是 G4 的第一支柱。
（`FactorRecursionRouteB.phi_eq_of_nondesc` 即以此为内核。） -/
theorem not_mem_pa_of_mem_nonDescendants {G : FateV2.Modeling.Graph.DAG V} {v w : V}
    (hw : w ∈ G.nonDescendants v) : v ∉ pa G w := by
  rw [mem_pa]
  intro hed
  rw [FateV2.Modeling.Graph.DAG.nonDescendants, Finset.mem_filter] at hw
  exact hw.2.1 (FateV2.Modeling.Graph.DAG.isAncestor.edge hed)

/-- ✅ G3（已有 `not_mem_pa_self`，此处引用确认，避免下游虚构名字）。 -/
theorem g3_reference (G : FateV2.Modeling.Graph.DAG V) (v : V) : v ∉ pa G v :=
  not_mem_pa_self G v

end FactorRecursionRouteB
end FateV2.Predict