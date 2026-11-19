import FateWorld.FateV2.Predict.G1ParentNonDescendant
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
  # Predict · BridgeA1

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeA1.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：G1ParentNonDescendant
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  `Fate/BridgeA1` —— **清单 A1（`pa(v) ∩ nd(v) = ∅`）的裁决**

  ## 0 结论（先看这个）

  **A1 的字面陈述是 FALSE 的，不可证，也不得作为任何下游证明的前件。**

  | 编号 | 陈述 | 状态 |
  |---|---|---|
  | **A1.refute** | `pa G v ⊆ G.nonDescendants v`（任意 DAG、任意 `v`）| ✅ **零缺口，无条件定理** |
  | **A1.collapse** | 故 `pa G v ∩ G.nonDescendants v = pa G v` | ✅ **零缺口，无条件定理** |
  | **A1.counter** | 具体反例 DAG：`pa 1 ∩ nd 1 = {0} ≠ ∅` | ✅ **零缺口，无条件定理** |
  | **A1'** | **正确的**不交陈述：`pa G v ∩ descendants G v = ∅` | ✅ **零缺口，无条件定理** |
  | **A1.needed** | A3/A4 真正需要的图论输入：`w ∈ nd(v) ⟹ v ∉ pa G w` | ✅ **零缺口，无条件定理** |

  ## 1 为什么 A1 是错的（一句话）

  `CausDAG.lean` 的定义（逐字）：

  ```
  nonDescendants v = Finset.univ.filter (fun w => ¬ G.isAncestor v w ∧ w ≠ v)
  ```

  即「**从 `v` 出发走不到**、且不等于 `v` 的点」。

  设 `u ∈ pa G v`，即 `G.edge u v`。

  * 若 `isAncestor v u`：由 `isAncestor_trans` 与 `isAncestor.edge hu`
    得 `isAncestor v v`，违反 `isAncestor_irrefl`。故 `¬ isAncestor v u`。
  * 若 `u = v`：则 `G.edge v v`，违反 `irrefl`。故 `u ≠ v`。

  两条正好是 `nonDescendants v` 的判据 ⟹ `u ∈ nd(v)`。

  **因此 `pa(v) ⊆ nd(v)`，交集塌缩为 `pa(v)`；只有当 `v` 是源点（无父）时交集才空。**

  ### 1.1 直觉错在哪里

  「父不是后代」是对的，但 `nd(v)` 的口径是「**不是 `v` 的后代**」，
  而非「**是 `v` 的祖先**」。父节点既是祖先、又不是后代，**正是 `nd(v)` 的成员**。
  把 `nd(v)` 误读成「祖先集」才会产生 A1。

  ## 2 项目内已有的三处同结论（交叉核对，非重复发明）

  * `Fate/G1ParentNonDescendant.lean`：`pa_subset_nonDescendants`、
    `pa_inter_nonDescendants`、`g1_counterexample`、`pa_disjoint_descendants`。
  * `Fate/LMGGlobalMarkovRoute5.lean`：R5.3 `¬ Disjoint (pa G v) (nd G v)`（链上 `v=1`）。
  * `Fate/ViewTenThreeBlock.lean`：`pa_subset_nonDesc_of_mem`、`not_mem_nonDesc_self`。

  **本文件按清单纪律「不重复发现、不重复交付」定位为：把 A1 的裁决
  收敛为一个自足的单文件**，同时给出**不依赖任何外部 A1 类结论的自足证明**
  （§3 的证明只使用 `CausDAG` 的原始定义与基本引理）。

  ## 3 给下游（A2/A3/A4）的交接

  * `A1`（`pa ∩ nd = ∅`）⟹ **丢弃**。任何用到它的推导必须重写。
  * `pa ∩ nd = pa` ⟹ `LMG` 定义里的 `nd ∪ pa` 等于 `nd`；
    不需要不交性，写 `nd` 即可（`Fate.G1ParentNonDescendant` §5 已说明）。
  * A3「乘性 `φ` 的边缘化分离」真正的图论输入是 `A1.needed`：
  非后代 `w` 的因子 `φ_w` 的读集 `pa(w)` **不含** `v`，
  故沿 `v` 求和时 `φ_w` 是常数。该事实已由 `A1.needed` 无条件给出。
  * A2（`v ∉ pa v`）由 `not_mem_pa_self` 无条件给出（见 `A1.self`）。

  **纪律确认**：无 `sorry` / `admit` / `axiom`；下面每条都是**无条件定理**，
  没有把结论写进前件。
  =========================================================================== -/

namespace FateV2.Predict

open FateV2.Modeling
namespace BridgeA1

open Finset FateV2.Predict.DAGFactorization

variable {V : Type u} [DecidableEq V] [Fintype V]

/-! ## §1 A1 的反证核心：`pa(v) ⊆ nd(v)` -/

/-- **A1.refute**：每个父节点都是非后代，故 `pa G v ⊆ nd G v`。

**证明**（只用 `CausDAG` 原始定义）：
`u ∈ pa G v` 给 `edge u v`。需证 `¬ isAncestor v u ∧ u ≠ v`。
* `¬ isAncestor v u`：否则 `isAncestor_trans` 加 `edge u v` 给 `isAncestor v v`，
  与 `isAncestor_irrefl` 矛盾；
* `u ≠ v`：否则 `edge v v`，与 `irrefl` 矛盾。 -/
theorem pa_subset_nonDescendants (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    pa G v ⊆ G.nonDescendants v := fun u hu => by
  rw [mem_pa] at hu
  rw [FateV2.Modeling.Graph.DAG.nonDescendants, Finset.mem_filter]
  exact ⟨Finset.mem_univ u, fun hanc => FateV2.Modeling.Graph.DAG.isAncestor_irrefl G v
      (FateV2.Modeling.Graph.DAG.isAncestor_trans G hanc (FateV2.Modeling.Graph.DAG.isAncestor.edge hu)),
    fun huv => FateV2.Modeling.Graph.DAG.irrefl G v (huv ▸ hu)⟩

/-- **A1.collapse**：交集不进反退，塌缩为 `pa G v` 本身。

$$\mathrm{pa}_G(v)\cap \mathrm{nd}_G(v)=\mathrm{pa}_G(v).$$ -/
theorem pa_inter_nonDescendants_eq (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    pa G v ∩ G.nonDescendants v = pa G v :=
  Finset.inter_eq_left.mpr (pa_subset_nonDescendants G v)

/-- **A1.refute'**：等价形式 —— `pa ∩ nd = ∅` 成立 **当且仅当** `v` 无父节点。
⟹ A1（对所有 `v` 断言 `= ∅`）只能是**空指称**，不能作前件。 -/
theorem pa_inter_nd_eq_empty_iff (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    pa G v ∩ G.nonDescendants v = ∅ ↔ pa G v = ∅ := by
  rw [pa_inter_nonDescendants_eq]

/-- **A1.refute''**：`v` 有父节点 ⟹ 交集**非空**（A1 的显式否定形态）。 -/
theorem pa_inter_nd_nonempty_of_nonempty (G : FateV2.Modeling.Graph.DAG V) {v : V}
    (hv : (pa G v).Nonempty) : (pa G v ∩ G.nonDescendants v).Nonempty := by
  rw [pa_inter_nonDescendants_eq]; exact hv

/-! ## §2 具体反例：`Fin 2` 上的单边 DAG

自足构造（不引用其它文件的 `arrowDAG`），以证明反例是**实质**的：
该 DAG 完全合法（`edge` 可判定、无环），而 `pa 1 ∩ nd 1 = {0}`。 -/

/-- 「箭头」DAG：`Fin 2` 上唯一一条边 `0 → 1`。 -/
def arrowDAG : FateV2.Modeling.Graph.DAG (Fin 2) where
  edge := fun u v => u = 0 ∧ v = 1
  decEdge := fun u v => inferInstanceAs (Decidable (u = 0 ∧ v = 1))
  acyclic := by
    have hstep : ∀ a b : Fin 2, (a = 0 ∧ b = 1) → a.val < b.val := by
      intro a b hab; rw [hab.1, hab.2]; decide
    intro v h
    have key : ∀ (a : Fin 2), Relation.TransGen (fun u v : Fin 2 => u = 0 ∧ v = 1) v a →
        v.val < a.val := by
      intro a ha
      induction ha with
      | single hab => exact hstep _ _ hab
      | tail _ hab ih => exact Nat.lt_trans ih (hstep _ _ hab)
    exact Nat.lt_irrefl v.val (key v h)

/-- 反例中的父节点：`0 ∈ pa arrowDAG 1`。 -/
theorem arrowDAG_pa_one : pa arrowDAG 1 = {0} := by
  ext u
  rw [mem_pa]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Finset.mem_singleton]
    have := h.1
    revert h
    revert this
    revert u
    decide
  · rw [Finset.mem_singleton] at h
    subst h
    exact ⟨rfl, rfl⟩

/-- 反例中的非后代集：`nd arrowDAG 1 = {0}`（`0` 是 `1` 的父，故不是 `1` 的后代）。 -/
theorem arrowDAG_nd_one : arrowDAG.nonDescendants 1 = {0} := by
  ext u
  rw [FateV2.Modeling.Graph.DAG.nonDescendants, Finset.mem_filter]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Finset.mem_singleton]
    revert h
    revert u
    decide
  · rw [Finset.mem_singleton] at h
    subst h
    refine ⟨Finset.mem_univ 0, ?_, ?_⟩
    · intro hanc
      -- `isAncestor 1 0` 需要一条 `1 → 0` 的路径，但唯一的边是 `0 → 1`
      have hkey : ∀ (a : Fin 2),
          Relation.TransGen (fun u v : Fin 2 => u = 0 ∧ v = 1) (1 : Fin 2) a →
          (1 : Fin 2).val < a.val := by
        intro a ha
        have hstep : ∀ a b : Fin 2, (a = 0 ∧ b = 1) → a.val < b.val := by
          intro a b hab; rw [hab.1, hab.2]; decide
        induction ha with
        | single hab => exact hstep _ _ hab
        | tail _ hab ih => exact Nat.lt_trans ih (hstep _ _ hab)
      exact absurd (hkey 0
        ((FateV2.Modeling.Graph.DAG.isAncestor_iff_transGen (G := arrowDAG)).mp hanc)) (by decide)
    · decide

/-- **A1.counter**：`pa 1 ∩ nd 1 = {0} ≠ ∅` —— 对合法 DAG 的显式反例。

⟹ A1 不是「尚未证明」，而是**假命题**。 -/
theorem a1_counterexample :
    pa arrowDAG 1 ∩ arrowDAG.nonDescendants 1 = ({0} : Finset (Fin 2)) := by
  rw [arrowDAG_pa_one, arrowDAG_nd_one, Finset.inter_self]

/-- **A1.counter_nonempty**：该交集非空。 -/
theorem a1_counterexample_nonempty :
    (pa arrowDAG 1 ∩ arrowDAG.nonDescendants 1).Nonempty := by
  rw [a1_counterexample]; exact ⟨0, Finset.mem_singleton_self 0⟩

/-- **A1.false**：A1 的**全称形式**被证伪。
不存在「对所有 DAG、所有 `v`，`pa v ∩ nd v = ∅`」这条定理。 -/
theorem a1_universally_false :
    ¬ (∀ (W : Type) [DecidableEq W] [Fintype W] (G : FateV2.Modeling.Graph.DAG W) (v : W),
        pa G v ∩ G.nonDescendants v = ∅) := by
  intro h
  have := h (Fin 2) arrowDAG 1
  rw [a1_counterexample] at this
  exact absurd this (by decide)

/-! ## §3 正确的替代物（下游 A3/A4 应改用这些） -/

/-- **A1'**：**正确的**不交陈述 —— 父节点集与**后代集**不交。

$$\mathrm{pa}_G(v)\cap \mathrm{de}_G(v)=\varnothing.$$

**证明**：`u ∈ pa v` 给 `edge u v`；若又 `isAncestor v u`，
则 `isAncestor_trans` 给 `isAncestor v v`，违反 `isAncestor_irrefl`。 -/
theorem pa_disjoint_descendants (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    Disjoint (pa G v) (G.descendants v) := by
  rw [Finset.disjoint_left]
  intro u hu hd
  rw [mem_pa] at hu
  rw [FateV2.Modeling.Graph.DAG.mem_descendants] at hd
  exact FateV2.Modeling.Graph.DAG.isAncestor_irrefl G v
    (FateV2.Modeling.Graph.DAG.isAncestor_trans G hd (FateV2.Modeling.Graph.DAG.isAncestor.edge hu))

/-- **A1.needed**（A3/A4 的真正输入）：非后代 `w` 的父集**不含** `v`。

$$w\in \mathrm{nd}_G(v)\ \Longrightarrow\ v\notin \mathrm{pa}_G(w).$$

**为什么这才是需要的**：`Factorizes` 中 `φ_w` 只读 `pa G w`。
沿 `v` 求和（边缘化）时，若 `v ∉ pa G w` 则 `φ_w` 在 `v` 方向上是常数、
可提出求和号 —— 这正是 A3 的「乘性 `φ` 的边缘化分离」第一支柱。
（`FactorRecursionRouteB.phi_eq_of_nondesc` 以此为核心。） -/
theorem not_mem_pa_of_mem_nonDescendants {G : FateV2.Modeling.Graph.DAG V} {v w : V}
    (hw : w ∈ G.nonDescendants v) : v ∉ pa G w := by
  rw [mem_pa]
  intro hed
  exact (Finset.mem_filter.mp hw).2.1 (FateV2.Modeling.Graph.DAG.isAncestor.edge hed)

/-- **A1.self**（清单 A2，同批交付以便下游对齐）：`v ∉ pa G v`。 -/
theorem not_mem_pa_self' (G : FateV2.Modeling.Graph.DAG V) (v : V) : v ∉ pa G v :=
  not_mem_pa_self G v

/-- **A1.closure**：非后代的前驱仍是非后代，因此 `nd(v)` 对「取父」封闭。
这保证沿 `nd(v)` 做乘法/边缘化时不逃出 `nd(v)`。 -/
theorem pa_subset_nonDescendants_of_mem {G : FateV2.Modeling.Graph.DAG V} {v w : V}
    (hw : w ∈ G.nonDescendants v) : pa G w ⊆ G.nonDescendants v := by
  intro u hu
  rw [mem_pa] at hu
  rw [FateV2.Modeling.Graph.DAG.nonDescendants, Finset.mem_filter]
  refine ⟨Finset.mem_univ u, ?_, ?_⟩
  · intro hanc
    exact (Finset.mem_filter.mp hw).2.1
      (FateV2.Modeling.Graph.DAG.isAncestor_trans G hanc (FateV2.Modeling.Graph.DAG.isAncestor.edge hu))
  · intro huv
    exact (Finset.mem_filter.mp hw).2.1 (huv ▸ FateV2.Modeling.Graph.DAG.isAncestor.edge hu)

/-- **A1.union**：故 `LMG` 定义里的 `nd ∪ pa` **就是** `nd` —— 不需要任何不交性。
这是「A1 在 `LMG` 定义中并不被需要」的精确陈述。 -/
theorem nonDescendants_union_pa (G : FateV2.Modeling.Graph.DAG V) (v : V) :
    G.nonDescendants v ∪ pa G v = G.nonDescendants v :=
  Finset.union_eq_left.mpr (pa_subset_nonDescendants G v)

end BridgeA1
end FateV2.Predict