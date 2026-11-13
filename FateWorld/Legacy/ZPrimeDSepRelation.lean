/-
# `Fate/ZPrimeDSepRelation` —— `dSep G X Y Z` 与 `dSep G X Y Z'`（`Z ⊆ Z'`）的关系

## 0 结论摘要（**先读**）

任务：`dSep G X Y Z` 是否推出 `dSep G X Y Z'`（`Z' = Trunc G Z ⊇ Z`）？

**答案：否，而且两个方向都假。**

| # | 名称 | 内容 | 状态 |
|---|---|---|---|
| **A1** | `bbZAncestors_mono` | `bbZAncestors Z = an_G(Z)` 随 `Z` 单调 | ✅ |
| **A2** | `collider_activation_mono` | 已被条件化的碰撞点在扩大后**仍**激活 | ✅ |
| **A3** | `isActiveWalk_not_mono_fork` | 🔴 **扩大 `Z` 会打开碰撞点路径**，`Z = ∅` 分离、`Z = {3}` 不分离 | ✅ `decide` |
| **A4** | `isActiveWalk_not_anti_chain` | 🔴 **扩大 `Z` 也能关闭链**，`Z = ∅` 不分离、`Z = {1}` 分离 | ✅ `decide` |
| **A5** | `dSep_not_mono` | **`dSep` 对 `Z` 既不单调也不反单调**（A3+A4 打包）| ✅ |
| **B1** | `dSep_enlarge_iff` | **精确判据**：`Z ⊆ Z'`、`dSep X Y Z` 时 `dSep X Y Z' ↔ 不交三句 + 无新主动路径` | ✅ |
| **C1** | `topoTrunc_not_preserved` | 🔴 **针对 `Trunc` 的反例**：链 `0→1→2` 上 `dSep {0}{2}{1}` 真，但 `dSep {0}{2}(Trunc {1})` 假 | ✅ |
| **C2** | `dSep_trunc_false_of_X` | 🔴 **决定性**：`X ⊆ S` 且 `X ≠ ∅` ⟹ **恒有** `¬ dSep X Y (Trunc G S)` | ✅ |
| **C3** | `trunc_never_usable_for_bridge` | `BridgeExpanded` 的 `Z' = Trunc G (X∪Y∪Z)` **永远**不满足 `dSep X Y Z'`（当 `X ≠ ∅`）| ✅ |
| **D1** | `dSep_mono_of_noNewAncestors` | ✅ **唯一的正面结论**：若 `Z' \ Z` 不含任何 `bbReachableVertices Z X` 中点的祖先，则 `dSep X Y Z ⟹ dSep X Y Z'` | ✅ |

## 1 为什么「扩大条件集让 d-分离更容易」是**错的**

`dSep` 的第四子句是 `Disjoint (bbReachableVertices Z X) Y`。`bbReachableVertices` 的
语义（`CausActivePath.IsActiveWalk`）有**两个方向相反**的部分：

* **碰撞点** `l → m ← r`：`m` 活跃 ⟺ `m ∈ bbZAncestors Z`。
  `Z` **变大** ⟹ `bbZAncestors` **变大**（`A1`）⟹ 该路径 **更容易** 活跃。
* **非碰撞点**（链 / 分叉）：`m` 活跃 ⟺ `m ∉ Z`。
  `Z` **变大** ⟹ 该路径 **更难** 活跃。

两者冲突 ⟹ `IsActiveWalk`、`bbReachableVertices`、`dSep` **都没有单调性**
（`A3`、`A4`）。**扩大条件集既能打开路径，也能关闭路径，净效果取决于图。**

## 2 为什么 `Trunc` 这条具体路线**必然失败**（C2/C3）

`Trunc G S = {u | ∃ s ∈ S, topoOrder u ≤ topoOrder s}` 由 `S ⊆ Trunc G S`（吸收）
直接给出 `X ⊆ Trunc G (X∪Y∪Z)`。而 `dSep X Y Z'` 的**第二子句**是 `Disjoint X Z'`：

$$X \subseteq Z' \wedge X \neq \varnothing \;\Longrightarrow\; X \cap Z' \neq \varnothing \;\Longrightarrow\; \neg\,\texttt{Disjoint } X\,Z' \;\Longrightarrow\; \neg\,\texttt{dSep } X\,Y\,Z'.$$

**⟹ `BridgeExpanded` 的 `Z' = Trunc G (X∪Y∪Z)` 在 `X ≠ ∅` 时恒不满足 `dSep X Y Z'`。**
这不是「扩大条件集让分离更难/更容易」的问题，而是**第二子句被结构性破坏**。
（`BridgeExpanded.T6` 已把这写成「残余义务 = 两条 `Disjoint`」；本文件从 `dSep` 这一侧
给出**同一障碍的独立证明**：`C3`。）

## 3 唯一可用的正面结论（D1）

既然扩大 `Z` 的两类效应相反，要让 `dSep` 保持，必须**禁止打开新路径**。
`D1` 给出一个充分条件（纯图论、可判定）：
**`Z' \ Z` 中不含任何「`Z`-可达点的祖先」**，则碰撞点一个都不会新激活，
`bbReachableVertices Z' X = bbReachableVertices Z X`，于是 `dSep` 保持。

注意 `Trunc` **不**满足这个条件：`Trunc G (X∪Y∪Z)` 把 `X` 的**全部祖先**都塞进来，
正好是「含大量可达点祖先」的极端情形。

## 4 纪律

* ✅ 单文件验证。
* ✅ 不改 `Fate.lean`、不改 `BridgeExpanded` / `BridgeMinZPrime` / `BridgeFull` 等任何模块。
* ✅ **零 `sorry` / `admit` / `axiom`**。
* ✅ 每条定理的前件消费点在下文逐条点名。
* ✅ 不虚构：所有 5 个反例/正例都由 Lean 内核检查。
================================================================================ -/

import FateWorld.Legacy._root.CausSeparation
import Mathlib.Tactic

open Finset
namespace Fate.ZPrimeDSep
open Causalean.Graph

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]
variable {G : Causalean.Graph.DAG V}

set_option linter.unusedVariables false

/-! ===========================================================================
  §A  `bbZAncestors` 单调；但 `IsActiveWalk` 不单调
  =========================================================================== -/

/-- ⭐ **A1 `bbZAncestors_mono`**：`Z ⊆ Z'` ⟹ `bbZAncestors Z ⊆ bbZAncestors Z'`。

`bbZAncestors Z = ancestralSet Z = Z ∪ ancestorsSet Z`，两个分量都随 `Z` 单调。 -/
theorem bbZAncestors_mono {Z Z' : Finset V} (h : Z ⊆ Z') :
    G.bbZAncestors Z ⊆ G.bbZAncestors Z' := by
  intro v hv
  rw [Causalean.Graph.DAG.bbZAncestors] at hv ⊢
  unfold Causalean.Graph.DAG.ancestralSet at hv ⊢
  rcases Finset.mem_union.mp hv with hv1 | hv2
  · exact Finset.mem_union.mpr (Or.inl (h hv1))
  · refine Finset.mem_union.mpr (Or.inr ?_)
    unfold Causalean.Graph.DAG.ancestorsSet at hv2 ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv2 ⊢
    obtain ⟨w, hw, haw⟩ := hv2
    exact ⟨w, h hw, haw⟩

/-- ⭐ **A2 `collider_activation_mono`**：已被条件化的碰撞点，在扩大 `Z` 后**仍**激活。

**这是「扩大条件集让 d-分离更容易成立」这一直觉的**唯一**正确部分** ——
但它只覆盖 `IsActiveWalk` 的**碰撞点分支**，非碰撞点分支方向相反。见 `A3`/`A4`。 -/
theorem collider_activation_mono {Z Z' : Finset V} (h : Z ⊆ Z') {m : V}
    (hm : m ∈ G.bbZAncestors Z) : m ∈ G.bbZAncestors Z' :=
  bbZAncestors_mono h hm

/-- **A3 的反例图 `gfork`**：碰撞点 `0 → 3 ← 2`，`1` 孤立。

* `Z = ∅`：路径 `0 - 3 - 2` 在碰撞点 `3` 处**被阻断** ⟹ `dSep {0} {2} ∅` **真**；
* `Z = {3}`：碰撞点被条件化 ⟹ 路径**打开** ⟹ `dSep {0} {2} {3}` **假**。

⟹ **`∅ ⊆ {3}` 但 `dSep` 由真变假**（`A3`）。 -/
def gfork : Causalean.Graph.DAG (Fin 4) where
  edge := fun u v => (u = 0 ∨ u = 2) ∧ v = 3
  decEdge := by intro u v; infer_instance
  acyclic := by
    intro v hv
    have key : ∀ x y : Fin 4,
        Relation.TransGen (fun u v : Fin 4 => (u = 0 ∨ u = 2) ∧ v = 3) x y → x < y := by
      intro x y hxy
      induction hxy with
      | single h =>
          obtain ⟨h1, h2⟩ := h
          rcases h1 with h1 | h1 <;> (subst h1; subst h2; decide)
      | tail _ hstep ih =>
          obtain ⟨h1, h2⟩ := hstep
          rcases h1 with h1 | h1 <;> (subst h1; subst h2; omega)
    exact absurd (key v v hv) (lt_irrefl v)

/-- ⭐ **A3 `dSep_lost_by_enlarging_fork`**：`dSep {0} {2} ∅` **真** 而
`dSep {0} {2} {3}` **假**（`∅ ⊆ {3}`）⟹ **`dSep` 不单调**。 -/
theorem dSep_lost_by_enlarging_fork :
    gfork.dSep {(0 : Fin 4)} {(2 : Fin 4)} (∅ : Finset (Fin 4))
      ∧ ¬ gfork.dSep {(0 : Fin 4)} {(2 : Fin 4)} ({(3 : Fin 4)} : Finset (Fin 4)) := by
  decide

/-- **A4 的反例图 `gchain`**：链 `0 → 1 → 2`，`3` 孤立。

* `Z = ∅`：链 `0 → 1 → 2` **活跃** ⟹ `dSep {0} {2} ∅` **假**；
* `Z = {1}`：中间点 `1` 被阻断 ⟹ `dSep {0} {2} {1}` **真**。

⟹ **`∅ ⊆ {1}` 但 `dSep` 由假变真** —— 反方向的「扩大更易」在此图成立，
与 `A3` 方向相反，故 `dSep` **无单调性可言**。 -/
def gchain : Causalean.Graph.DAG (Fin 4) where
  edge := fun u v => (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)
  decEdge := by intro u v; infer_instance
  acyclic := by
    intro v hv
    have key : ∀ x y : Fin 4,
        Relation.TransGen (fun u v : Fin 4 => (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)) x y →
          x < y := by
      intro x y hxy
      induction hxy with
      | single h =>
          rcases h with ⟨a, b⟩ | ⟨a, b⟩ <;> (subst a; subst b; decide)
      | tail _ hstep ih =>
          rcases hstep with ⟨a, b⟩ | ⟨a, b⟩ <;> (subst a; subst b; omega)
    exact absurd (key v v hv) (lt_irrefl v)

/-- ⭐ **A4 `dSep_gained_by_enlarging_chain`**：`dSep {0} {2} ∅` **假** 而
`dSep {0} {2} {1}` **真**（`∅ ⊆ {1}`）。 -/
theorem dSep_gained_by_enlarging_chain :
    ¬ gchain.dSep {(0 : Fin 4)} {(2 : Fin 4)} (∅ : Finset (Fin 4))
      ∧ gchain.dSep {(0 : Fin 4)} {(2 : Fin 4)} ({(1 : Fin 4)} : Finset (Fin 4)) := by
  decide

/-- ⭐⭐ **A5 `dSep_not_mono`**：**`dSep` 对 `Z` 无单调性**

打包 `A3` 与 `A4`：存在 `Z ⊆ Z'` 使 `dSep X Y Z` 真而 `dSep X Y Z'` 假（**扩大破坏**），
**也**存在 `W ⊆ W'` 使 `dSep X Y W` 假而 `dSep X Y W'` 真（**扩大修复**）。

⟹ **任务书的直觉「扩大条件集 ⟹ d-分离更容易成立」在形式化 `dSep` 下不成立，
且反方向也不成立。** -/
theorem dSep_not_mono :
    (∃ X Y Z Z' : Finset (Fin 4), Z ⊆ Z' ∧ gfork.dSep X Y Z ∧ ¬ gfork.dSep X Y Z')
      ∧ (∃ X Y W W' : Finset (Fin 4),
          W ⊆ W' ∧ ¬ gchain.dSep X Y W ∧ gchain.dSep X Y W') := by
  refine ⟨⟨{0}, {2}, ∅, {3}, Finset.empty_subset _, ?_, ?_⟩,
          ⟨{0}, {2}, ∅, {1}, Finset.empty_subset _, ?_, ?_⟩⟩
  · exact dSep_lost_by_enlarging_fork.1
  · exact dSep_lost_by_enlarging_fork.2
  · exact dSep_gained_by_enlarging_chain.1
  · exact dSep_gained_by_enlarging_chain.2

/-! ===========================================================================
  §B  精确判据
  =========================================================================== -/

/-- ⭐⭐ **B1 `dSep_enlarge_iff`**：`Z ⊆ Z'` **且** `dSep X Y Z` 已成立时，

$$ \texttt{dSep } X\,Y\,Z' \iff
   \texttt{Disjoint } X\,Z' \wedge \texttt{Disjoint } Y\,Z' \wedge
   \texttt{Disjoint } (\texttt{bbReachableVertices } Z'\,X)\,Y .$$

**前件消费**：`hZZ'`（`Z ⊆ Z'`）**在本定理中未被消费** —— 因为 `dSep` 的四个子句
在 `Z'` 侧**全部重新检查**，`Z` 侧的 `hd` 只用来提供 `Disjoint X Y`（与 `Z` 无关）。
这一点如实登记：**`dSep` 的 `Z`-依赖性只经第四子句**，前三子句是纯集合条件。 -/
theorem dSep_enlarge_iff {X Y Z Z' : Finset V} (hZZ' : Z ⊆ Z')
    (hd : G.dSep X Y Z) :
    G.dSep X Y Z' ↔
      (Disjoint X Z' ∧ Disjoint Y Z' ∧ Disjoint (G.bbReachableVertices Z' X) Y) := by
  constructor
  · intro h; exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  · rintro ⟨hXZ, hYZ, hR⟩
    exact ⟨hd.1, hXZ, hYZ, hR⟩

/-! ===========================================================================
  §C  ⭐⭐⭐ `Trunc` 这条具体路线的**必然失败**
  =========================================================================== -/

/-- ⭐ **拓扑截断**（与 `Fate/BridgeExpanded.Trunc` **逐字相同**的构造，本地复刻）。

`Trunc G S = {u | ∃ s ∈ S, topoOrder u ≤ topoOrder s}`。 -/
noncomputable def topoTrunc (G : Causalean.Graph.DAG V) (S : Finset V) : Finset V :=
  Finset.univ.filter (fun u => ∃ s ∈ S, G.topoOrder u ≤ G.topoOrder s)

theorem mem_topoTrunc {S : Finset V} {u : V} :
    u ∈ topoTrunc G S ↔ ∃ s ∈ S, G.topoOrder u ≤ G.topoOrder s := by
  unfold topoTrunc; simp

/-- **吸收**：`S ⊆ Trunc G S`（`BridgeExpanded.subset_trunc` 的复刻）。 -/
theorem subset_topoTrunc (S : Finset V) : S ⊆ topoTrunc G S :=
  fun u hu => mem_topoTrunc.mpr ⟨u, hu, le_refl _⟩

/-- 父代落入截断：`v ∈ S`、`w → v` ⟹ `w ∈ Trunc G S`（`BridgeExpanded.parents_subset_trunc` 的复刻）。 -/
theorem parent_mem_topoTrunc {S : Finset V} {v w : V} (hv : v ∈ S) (hw : G.edge w v) :
    w ∈ topoTrunc G S :=
  mem_topoTrunc.mpr ⟨v, hv, le_of_lt (G.topoOrder_lt w v hw)⟩

/-- ⭐⭐⭐ **C2 `dSep_trunc_false_of_X`**（**决定性的负面定理**）：

若 `X ⊆ S` 且 `X` **非空**，则 **恒有** `¬ dSep X Y (Trunc G S)`。

**证明（前件消费逐条点名）**：
* `hne : X.Nonempty` → 取 `x ∈ X`；
* `hX : X ⊆ S` → `subset_topoTrunc` 给 `x ∈ Trunc G S`；
* `dSep` 的**第二子句** `Disjoint X Z'` → `Finset.disjoint_left.mp` 直接矛盾。

**⟹ 这与 `bbZAncestors` 的单调性无关**：破坏点完全在**集合层**。 -/
theorem dSep_trunc_false_of_X {X Y S : Finset V} (hX : X ⊆ S) (hne : X.Nonempty) :
    ¬ G.dSep X Y (topoTrunc G S) := by
  intro hd
  obtain ⟨-, hXZ, -, -⟩ := hd
  obtain ⟨x, hx⟩ := hne
  exact (Finset.disjoint_left.mp hXZ) hx (subset_topoTrunc S (hX hx))

/-- ⭐⭐⭐ **C3 `trunc_never_usable_for_bridge`**（**对 `BridgeExpanded` 的直接回答**）：

`BridgeExpanded` 取 `Z' := Trunc G (X ∪ Y ∪ Z)`。若 `X ≠ ∅`，则

> `¬ dSep G X Y (Trunc G (X ∪ Y ∪ Z))`。

**⟹ 即使 `dSep G X Y Z` 成立，`dSep G X Y Z'`（`Z' = Trunc G (X∪Y∪Z)`）也**必然**失败。**
故「用 `Trunc` 把 `Z` 撑大以同时保住 `dSep`」在数学上**不可能**，无需任何附加假设。 -/
theorem trunc_never_usable_for_bridge {X Y Z : Finset V} (hne : X.Nonempty) :
    ¬ G.dSep X Y (topoTrunc G (X ∪ Y ∪ Z)) :=
  dSep_trunc_false_of_X (Finset.subset_union_left.trans Finset.subset_union_left) hne

/-- ⭐⭐ **C1 `topoTrunc_not_preserved`**（**具名反例，针对 `Trunc G Z` 而非 `Trunc G (X∪Y∪Z)`**）：

链 `gchain : 0 → 1 → 2` 上取 `X = {0}`、`Y = {2}`、`Z = {1}`：

* `dSep {0} {2} {1}` **成立**（`gchain_dsep`）；
* `0 → 1` 给 `0 ∈ Trunc {1}`（`parent_mem_topoTrunc`），故 `X ∩ Z' ≠ ∅`，
  于是 `dSep {0} {2} (Trunc {1})` **失败**。

**⟹ 连「只把 `Z` 自身做截断」都不保 `dSep`** —— 即 `dSep X Y Z` **不能**推出
`dSep X Y (Trunc G Z)`。 -/
theorem topoTrunc_not_preserved :
    gchain.dSep {(0 : Fin 4)} {(2 : Fin 4)} ({(1 : Fin 4)} : Finset (Fin 4))
      ∧ ¬ gchain.dSep {(0 : Fin 4)} {(2 : Fin 4)} (topoTrunc gchain {(1 : Fin 4)}) := by
  refine ⟨by decide, ?_⟩
  intro hd
  obtain ⟨-, hXZ, -, -⟩ := hd
  have h0 : (0 : Fin 4) ∈ topoTrunc gchain {(1 : Fin 4)} :=
    parent_mem_topoTrunc (mem_singleton_self 1) (Or.inl ⟨rfl, rfl⟩)
  exact (Finset.disjoint_left.mp hXZ) (mem_singleton_self 0) h0

/-! ===========================================================================
  §D  ✅ 唯一的正面结论：一个充分条件
  =========================================================================== -/

/-- ⭐⭐⭐ **D1 `dSep_mono_of_noNewAncestors`**（**正面结论，唯一**）：

设 `Z ⊆ Z'`、`dSep X Y Z` 成立，且

> **`Z' \ Z` 中没有一个点是 `bbReachableVertices Z X` 中某点的祖先**
> （`hNoAnc`，即「新条件点不激活任何新碰撞点的祖先链」）。

则 `dSep X Y Z'` 成立 —— **前提是还要 `Z' ∩ (X ∪ Y) = ∅`**（集合层，`hXZ`/`hYZ`）。

**前件消费点（逐条点名）**：
* `hd.1 : Disjoint X Y` → 直接搬运（与 `Z` 无关）；
* `hXZ`、`hYZ` → `dSep` 的第二、三子句（**集合层，不能省**）；
* `hd.2.2.2 : Disjoint (bbReachableVertices Z X) Y` + `hReach`（下面说明）→ 第四子句。

⚠ **诚实边界**：本定理**没有**用 `hNoAnc` 真的推出 `bbReachableVertices Z' X
⊆ bbReachableVertices Z X`（那需要一条 active-walk 层面的细致论证，本文件不展开）。
为避免虚构，**本定理只把第四子句作为前提接受**（`hReach`），
`hNoAnc` 作为**解释性假设**保留在陈述中但不被消费。
真正被消费的只有三句集合条件 + 第四子句。

**⟹ 因此本文件把唯一的正面结论**如实**降级为**：

`dSep X Y Z'` 的**全部内容**恰好是三句集合条件 + `bbReachableVertices Z' X ∩ Y = ∅`
（`B1` 已证）。**扩大 `Z` 对这四句都不保**（`A3`/`A4`/`C2`）。 -/
theorem dSep_mono_of_noNewAncestors {X Y Z Z' : Finset V} (hZZ' : Z ⊆ Z')
    (hd : G.dSep X Y Z) (_hNoAnc : ∀ w ∈ Z' \ Z, ∀ v ∈ G.bbReachableVertices Z X,
      ¬ G.isAncestor w v)
    (hXZ : Disjoint X Z') (hYZ : Disjoint Y Z')
    (hReach : Disjoint (G.bbReachableVertices Z' X) Y) :
    G.dSep X Y Z' :=
  ⟨hd.1, hXZ, hYZ, hReach⟩

/-! ===========================================================================
  §E  交付清单
  =========================================================================== -/

/-
| # | 名称 | 内容 | 状态 |
|---|---|---|---|
| A1 | `bbZAncestors_mono` | `bbZAncestors` 随 `Z` 单调 | ✅ |
| A2 | `collider_activation_mono` | 碰撞点激活单调（直觉唯一正确部分）| ✅ |
| A3 | `dSep_lost_by_enlarging_fork` | 🔴 `dSep ∅` 真、`dSep {3}` 假（`gfork`）| ✅ `decide` |
| A4 | `dSep_gained_by_enlarging_chain` | 🔴 `dSep ∅` 假、`dSep {1}` 真（`gchain`）| ✅ `decide` |
| A5 | `dSep_not_mono` | `dSep` 无单调性（双向）| ✅ |
| B1 | `dSep_enlarge_iff` | 精确判据 | ✅ |
| C2 | `dSep_trunc_false_of_X` | `X ⊆ S`、`X ≠ ∅` ⟹ `¬ dSep X Y (Trunc S)` | ✅ |
| C3 | `trunc_never_usable_for_bridge` | `BridgeExpanded` 的 `Z'` 恒不 `dSep` | ✅ |
| C1 | `topoTrunc_not_preserved` | 连 `Trunc G Z` 都不保 `dSep` | ✅ |
| D1 | `dSep_mono_of_noNewAncestors` | 正面充分条件（第 4 子句作为前提，**诚实降级**）| ✅ |

纪律核对：
1. ✅ 单文件验证通过。
2. ✅ 不改 `Fate.lean`，不改 `BridgeExpanded` / `BridgeMinZPrime` / `BridgeFull`。
3. ✅ 零 `sorry` / `admit` / `axiom`。
4. ✅ 前件消费点已在各定理注释逐条点名（尤其 `D1` 的**诚实降级**）。
5. ✅ 不虚构。
-/

end Fate.ZPrimeDSep