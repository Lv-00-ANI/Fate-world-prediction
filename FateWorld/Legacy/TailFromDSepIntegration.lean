/-
  Fate/TailFromDSepIntegration.lean

  # 桥的最后整合：从 `dSep` 推出 `hTail`？

  ## 0 判决（全部机检，零 `sorry` / `admit` / `axiom`）

> **`dSep` 不蕴含 `hTail`，该命题为假；最小反例在 `V = Fin 3`（链 `0 → 2`）。**
> 更进一步：**在 `R = readSetOf G` 的口径下，`hTail` 逐字等价于覆盖条件
> `X ∪ Y ∪ Z = univ`** —— 它不是「尾块约束」而是「无尾块」的同义反复。

设 `A := X ∪ Y ∪ Z`。要证的命题是

```lean
G.dSep X Y Z → ∀ v, v ∉ A → readSetOf G v ⊆ Z
```

它有三层否决，每层都是机检定理：

### 第 1 层：反例（`dSep_not_implies_hTail_fin3`，§2）

`V = Fin 3`，图 `chainDAG : 0 → 2`（`1` 孤立），`X = {0}`、`Y = {1}`、`Z = ∅`。

* `dSep {0} {1} ∅` **成立**（`chainDAG_dSep`）：`0` 与 `1` 之间**没有路径**，
  Bayes Ball 无处可去。
* `2 ∉ A` 且 `pa(2) = {0} ⊆ X`，故 `readSetOf G 2 = {0, 2} ⊄ ∅ = Z`
  （`dSep_not_implies_hTail_fin3` 由 `Finset.notMem_empty` 收口）。

**机理**：`dSep` 只约束 `X`–`Y` 之间的路径（`bbReachableVertices Z X ∩ Y = ∅`），
对 `v ∉ A` 的**父集合**完全无视 —— 尾块顶点的父可以随意落在 `X`、`Y`
或另一尾块里。所以 `hTail` 的 `pa(v) ⊆ Z` 这一半**不可能**由 `dSep` 得到。

### 第 2 层：`hTail` 其实是覆盖条件的同义反复（`hTail_readSetOf_iff_cover`，§3）

```lean
(∀ v, v ∉ A → readSetOf G v ⊆ Z) ↔ A = univ          -- R = readSetOf G
```

* **⟸**（`hTail_of_cover`）：`A = univ` 时 `v ∉ A` 无解，`hTail` **空真**。
* **⟹**（`cover_of_hTail_readSetOf`）：`readSetOf G v` 总含 `v` 本身，
  故 `v ∉ A ⟹ v ∈ readSetOf G v ⊆ Z ⊆ A`，矛盾。于是每个 `v` 都在 `A` 里。

**⟹ 推论**：`condIndep_tail_block` 的 `hTail` 前提在 `R = readSetOf G` 时
**可满足当且仅当没有尾块**（`no_tail_of_hTail_readSetOf`）。

### 第 3 层：`hTail` 与 `dSep` 真正是什么关系（`hTail_iff_avoids`，§4）

对一般读集 `R`（配 `dSep` 已保证的 `Disjoint X Z`、`Disjoint Y Z`）：

```lean
(∀ v, v ∉ A → R v ⊆ Z)
  ↔ ∀ v, v ∉ A → (∀ u ∈ R v, u ∉ X ∪ Y) ∧ (∀ u ∈ R v, u ∈ Z)
```

即 `hTail` = **「尾块因子既不读 `X ∪ Y`，也不读任何尾块顶点」**（尾块自治）。
`dSep` 对此**一个字都不说**；而 `Split` + `hTail` 才给出全局
`∀ v, R v ⊆ A`（已入库的 `hAll_of_split_tail`）。

**⟹ 「`hTail` 与 `dSep` 之间没有任何（非平凡的）蕴含关系」**：
两者正交。唯一的方向性事实是「`hTail` 可满足 ⟹ 无尾块 ⟹ 覆盖」，
而这是 `hTail` 自身的退化，与 `dSep` 无关。

## 1 主定理 D 的正确前提（§5）

于是「`dSep ⟹ hTail`」整合路线的**正确形态**不是造出尾块约束，
而是 **`dSep` + 覆盖 ⟹ 无尾块 ⟹ `hTail` 空真**：

| 路线 | 覆盖 | `hTail` | 消费 `dSep` | 定理 |
|---|---|---|---|---|
| `dSep` 路线（无尾块） | `X∪Y∪Z = univ` | 空真（自动） | 是（造 `Split`） | `condIndep_tail_block_of_dSep_cover`（§5.2） |
| `hTail` 路线（有尾块） | 不需要 | 使用者提供 | **否** | 已入库 `TailBlockBridge.condIndep_tail_block` |

§5 把两条路线都机检地再接一次：`condIndep_tail_block_of_dSep_cover`
（消费 `dSep` + 覆盖 + 任意读集）与其 `R = readSetOf G` 特化
`..._readSetOf`；`cover_bridge_consistency` 再把它与已入库的
`BridgeDSepGeneral.condIndep_of_factorizes_dSep_general` 交叉核对。

## 2 诚实边界

* **不修改任何既有模块**；不写 `Fate/` 之外的内容；不改 `Fate.lean`。
* 本文件**不**声称 `condIndep_tail_block` 有缺陷 —— 它是真的；
  只是其 `hTail` 在 `readSetOf` 口径下只在**全覆盖**时可满足，
  此时主定理 D 与无尾块桥是同一件事。
* 若真要用「有尾块」的主定理 D（例如尾块顶点有非平凡父集），
  `hTail` 必须作为**独立假设**由调用方提供，且**不能**从任何 `dSep` 陈述推出。
* §2 用**链**反例，命中「`v ∉ A` 但 `pa(v) ⊆ X`」这一最直接机制；
  `Fate/SplitFromDAG.lean` §5 已有机检的 collider 反例
  （`V = Fin 3`，`0 → 2 ← 1`）覆盖「`pa(v)` 横跨 `X` 与 `Y`」；
  `Fate_agent_staging/SplitFromDSepComplete.lean` 另给深度 1 归约的独立证明。
-/

import FateWorld.Legacy.SplitFromDAG
import FateWorld.Legacy.BridgeDSepGeneral
import FateWorld.Legacy.TailBlockBridge

namespace Fate

namespace TailFromDSepIntegration

open Finset
open Causalean.Graph

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

/-! ===========================================================================
  §1  最小反例图：链 `0 → 2`（`1` 孤立），`V = Fin 3`
  =========================================================================== -/

/-- 链 `0 → 2`（`1` 孤立）的边关系。 -/
def chainEdge : Fin 3 → Fin 3 → Prop :=
  fun u v => u = 0 ∧ v = 2

/-- 上述边关系的可判定性。 -/
def chainEdgeDec : DecidableRel chainEdge := by
  intro u v; unfold chainEdge; infer_instance

/-- 拓扑秩：`0, 1 ↦ 0`；`2 ↦ 1`。用来说明无环。 -/
def chainRank (x : Fin 3) : ℕ := if x = 2 then 1 else 0

theorem chainEdge_rank_lt {u v : Fin 3} (h : chainEdge u v) :
    chainRank u < chainRank v := by
  obtain ⟨rfl, rfl⟩ := h
  unfold chainRank
  decide

/-- ⭐ **反例图**：`V = Fin 3` 上的单边链 `0 → 2`。 -/
def chainDAG : Causalean.Graph.DAG (Fin 3) where
  edge := chainEdge
  decEdge := chainEdgeDec
  acyclic := by
    intro v h
    have hmono : ∀ {a b : Fin 3},
        Relation.TransGen chainEdge a b → chainRank a < chainRank b := by
      intro a b hab
      induction hab with
      | single h => exact chainEdge_rank_lt h
      | tail _ hbc ih => exact lt_trans ih (chainEdge_rank_lt hbc)
    exact absurd (hmono h) (lt_irrefl _)

/-- 反例中 `dSep {0} {1} ∅` **成立**（`0` 与 `1` 之间无路径）。 -/
theorem chainDAG_dSep : chainDAG.dSep {0} {1} (∅ : Finset (Fin 3)) := by
  decide

/-- 反例中 `2 ∉ {0} ∪ {1} ∪ ∅`。 -/
theorem chainDAG_not_mem : (2 : Fin 3) ∉ ({0} ∪ {1} ∪ (∅ : Finset (Fin 3))) := by
  decide

/-- 反例中 `pa(2) = {0}`，故 `readSetOf G 2` 含 `0`。 -/
theorem chainDAG_mem_readSet :
    (0 : Fin 3) ∈ Fate.FactorizesToHyper.readSetOf chainDAG 2 := by
  rw [Fate.FactorizesToHyper.mem_readSetOf]
  refine Or.inr ?_
  rw [Causalean.Graph.DAG.mem_parents]
  show chainEdge 0 2
  unfold chainEdge
  decide

/-! ===========================================================================
  §2  判决 1：`dSep` **不**蕴含 `hTail`
  =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **主反例**（`V = Fin 3`）：`dSep {0} {1} ∅` 成立，但尾块顶点 `v = 2`
的读集 `{0, 2}` 不落在 `Z = ∅` 内，因为它的父 `0` 落在 `X` 里。 -/
theorem dSep_not_implies_hTail_fin3 :
    ¬ (∀ (G : Causalean.Graph.DAG (Fin 3)) (X Y Z : Finset (Fin 3)),
        G.dSep X Y Z →
        ∀ v, v ∉ X ∪ Y ∪ Z → Fate.FactorizesToHyper.readSetOf G v ⊆ Z) := by
  intro h
  have htail : Fate.FactorizesToHyper.readSetOf chainDAG 2 ⊆ (∅ : Finset (Fin 3)) :=
    h chainDAG {0} {1} ∅ chainDAG_dSep 2 chainDAG_not_mem
  exact Finset.notMem_empty 0 (htail chainDAG_mem_readSet)

/-- ⭐⭐⭐⭐⭐ **判决（全称形式）**：任意 `V` 上的命题亦为假。 -/
theorem hTail_from_dSep_false :
    ¬ (∀ (V : Type) [DecidableEq V] [Fintype V]
        (G : Causalean.Graph.DAG V) (X Y Z : Finset V),
        G.dSep X Y Z →
        ∀ v, v ∉ X ∪ Y ∪ Z → Fate.FactorizesToHyper.readSetOf G v ⊆ Z) := by
  intro h
  have h' : ∀ (G : Causalean.Graph.DAG (Fin 3)) (X Y Z : Finset (Fin 3)),
      G.dSep X Y Z →
      ∀ v, v ∉ X ∪ Y ∪ Z → Fate.FactorizesToHyper.readSetOf G v ⊆ Z :=
    h (Fin 3)
  exact dSep_not_implies_hTail_fin3 h'

/-! ===========================================================================
  §3  判决 2：`hTail`（`R = readSetOf G`）**等价于覆盖条件**
  =========================================================================== -/

/-- 覆盖 ⟹ `hTail`，对**任意**读集 `R`（`v ∉ univ` 无解，故空真）。 -/
theorem hTail_of_cover {R : V → Finset V} {X Y Z : Finset V}
    (hcover : X ∪ Y ∪ Z = Finset.univ) :
    ∀ v, v ∉ X ∪ Y ∪ Z → R v ⊆ Z := by
  intro v hv
  exact absurd (hcover ▸ Finset.mem_univ v) hv

/-- `hTail`（`R = readSetOf G`）⟹ 覆盖：`readSetOf G v ∋ v`，故
`v ∉ A ⟹ v ∈ Z ⊆ A`，矛盾。 -/
theorem cover_of_hTail_readSetOf (G : Causalean.Graph.DAG V) (X Y Z : Finset V)
    (hTail : ∀ v, v ∉ X ∪ Y ∪ Z → Fate.FactorizesToHyper.readSetOf G v ⊆ Z) :
    X ∪ Y ∪ Z = Finset.univ := by
  have hsub : Finset.univ ⊆ X ∪ Y ∪ Z := by
    intro v _
    by_contra hv
    have h1 : v ∈ Fate.FactorizesToHyper.readSetOf G v :=
      (Fate.FactorizesToHyper.mem_readSetOf).mpr (Or.inl rfl)
    have h2 : v ∈ Z := hTail v hv h1
    exact hv (Finset.mem_union.mpr (Or.inr h2))
  exact Finset.Subset.antisymm (Finset.subset_univ _) hsub

/-- ⭐⭐⭐⭐⭐ **核心判决**：`hTail` ⟺ 覆盖（`R = readSetOf G`）。

**`hTail` 不是尾块条件，而是「无尾块」的同义反复。** -/
theorem hTail_readSetOf_iff_cover (G : Causalean.Graph.DAG V) (X Y Z : Finset V) :
    (∀ v, v ∉ X ∪ Y ∪ Z → Fate.FactorizesToHyper.readSetOf G v ⊆ Z)
      ↔ X ∪ Y ∪ Z = Finset.univ :=
  ⟨cover_of_hTail_readSetOf G X Y Z, hTail_of_cover⟩

/-- 推论：`hTail` 一旦可满足，就**没有**尾块顶点。 -/
theorem no_tail_of_hTail_readSetOf (G : Causalean.Graph.DAG V) (X Y Z : Finset V)
    (hTail : ∀ v, v ∉ X ∪ Y ∪ Z → Fate.FactorizesToHyper.readSetOf G v ⊆ Z) :
    ∀ v : V, v ∈ X ∪ Y ∪ Z := by
  intro v
  rw [cover_of_hTail_readSetOf G X Y Z hTail]
  exact Finset.mem_univ v

/-! ===========================================================================
  §4  判决 3：`hTail` 的真实语义 = 尾块因子与 `X ∪ Y` 及尾块内部解耦
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **`hTail` 的语义分解**（需 `dSep` 已保证的 `Disjoint X Z`、`Disjoint Y Z`）：

`hTail` ⟺ 每个尾块因子的读集**既不碰 `X ∪ Y`，也整体落在 `Z` 内**。

⟹ `hTail` 的内容是**尾块自治**（尾块因子与 `A` 解耦），
与 `dSep`（只谈 `X`–`Y` 路径）**正交**。 -/
theorem hTail_iff_avoids (R : V → Finset V) (X Y Z : Finset V)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    (∀ v, v ∉ X ∪ Y ∪ Z → R v ⊆ Z) ↔
      ∀ v, v ∉ X ∪ Y ∪ Z → (∀ u ∈ R v, u ∉ X ∪ Y) ∧ (∀ u ∈ R v, u ∈ Z) := by
  constructor
  · intro h v hv
    refine ⟨fun u hu => ?_, fun u hu => h v hv hu⟩
    have hZ : u ∈ Z := h v hv hu
    intro huv
    rcases Finset.mem_union.mp huv with h1 | h1
    · exact Finset.disjoint_left.mp hXZ h1 hZ
    · exact Finset.disjoint_left.mp hYZ h1 hZ
  · intro h v hv u hu
    exact (h v hv).2 u hu

/-- 尾块因子与 `X ∪ Y` 无关（`hTail` 的一半，单独消费）。 -/
theorem hTail_avoids_XY (R : V → Finset V) (X Y Z : Finset V)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hTail : ∀ v, v ∉ X ∪ Y ∪ Z → R v ⊆ Z) :
    ∀ v, v ∉ X ∪ Y ∪ Z → ∀ u ∈ R v, u ∉ X ∪ Y :=
  fun v hv => ((hTail_iff_avoids R X Y Z hXZ hYZ).mp hTail v hv).1

/-! ===========================================================================
  §5  正确的整合：`dSep` + 覆盖 ⟹ 无尾块 ⟹ 主定理 D
  =========================================================================== -/

section Integration

variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

/-- ⭐⭐⭐⭐⭐ **整合后的主定理 D（`dSep` 路线）**。

`hTail` **不由 `dSep` 推出，而由覆盖推出**（`hTail_of_cover`，空真）。
这是「从 `dSep` 推出 `hTail`」这条整合路线的正确形态：
**不是造出尾块约束，而是 `dSep` + 覆盖消灭尾块**。

参数与已入库的 `TailBlockBridge.condIndep_tail_block` 逐字对齐，
只是 `hTail` 被 `hTail_of_cover hcover` 自动补上。 -/
theorem condIndep_tail_block_of_dSep_cover
    {X Y Z : Finset V} {G : Causalean.Graph.DAG V}
    {ψ : V → (V → α) → ℝ} {R : V → Finset V} {p : (V → α) → ℝ}
    (hfac : ∀ w, p w = ∏ v : V, ψ v w)
    (hread : Fate.View19.ReadSet ψ R)
    (hsplit : Fate.View19.Split R X Y Z)
    (hdsep : G.dSep X Y Z)
    (hcover : X ∪ Y ∪ Z = Finset.univ) :
    Fate.FactorMarkov.CondIndep p X Y Z := by
  have hXY : Disjoint X Y := hdsep.1
  have hXZ : Disjoint X Z := hdsep.2.1
  have hYZ : Disjoint Y Z := hdsep.2.2.1
  exact Fate.GraphToProbView7.condIndep_tail_block hfac hread
    (hTail_of_cover hcover) hsplit hXY hXZ hYZ

end Integration

/-! ### §5.2 与已入库的无尾块桥交叉核对 -/

/-- ⭐⭐⭐⭐ **一致性**：在 `Factorizes p G` 口径下，
「`dSep` + 覆盖」既给出 `Split (readSetOf G) X Y Z`（`split_of_dSep`，
主定理 D 的 `hsplit` 前提），又直接给出 `CondIndep`（无尾块桥）。
两个结论必须同时成立 —— 机检确认。 -/
theorem cover_bridge_consistency
    {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    (p : Fate.FactorMarkov.Joint V α) (G : Causalean.Graph.DAG V) {X Y Z : Finset V}
    (hfac : Fate.FactorMarkov.Factorizes p G)
    (hdsep : G.dSep X Y Z) (hcover : X ∪ Y ∪ Z = Finset.univ) :
    Fate.FactorMarkov.CondIndep p X Y Z ∧
      Fate.View19.Split (Fate.FactorizesToHyper.readSetOf G) X Y Z :=
  ⟨Fate.BridgeDSepGeneral.condIndep_of_factorizes_dSep_general p G hfac hdsep hcover,
    Fate.SplitFromDAG.split_of_dSep G X Y Z hdsep hcover⟩

end TailFromDSepIntegration

end Fate
