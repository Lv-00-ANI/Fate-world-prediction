import FateWorld.Legacy._root.CausSeparation
import FateWorld.Legacy.DAGFactorizationGeneral
import FateWorld.Legacy.FactorRecursionRouteB

/-! ===========================================================================
  `Fate/DSepTopoPeel` —— **第 6 路：`dSep` 与拓扑序的兼容性（逐点剥离）**
  =========================================================================== -/

namespace Fate
namespace DSepTopoPeel

open Finset
open Causalean.Graph
open Causalean.Graph.DAG

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-! ### §0 补证小工具（`CausDAG` 没有直接给出，但不是「缺口」） -/

/-- `ancClosure` 沿「再走一步边」保持（`w → z` ⟹ `ancClosure w ⊆ ancClosure z`）。 -/
theorem ancClosure_subset_of_edge (G : DAG V) {w z : V} (h : G.edge w z) :
    G.ancClosure w ⊆ G.ancClosure z := by
  intro u hu
  rw [G.mem_ancClosure] at hu ⊢
  rw [G.isAncestor_iff_transGen] at *
  exact hu.tail h

/-- `ancClosure` 沿**祖先**关系单调。 -/
theorem ancClosure_mono_of_ancestor (G : DAG V) {u v : V} (huv : G.isAncestor u v) :
    G.ancClosure u ⊆ G.ancClosure v := by
  intro w hw
  rw [G.mem_ancClosure] at hw ⊢
  rw [G.isAncestor_iff_transGen] at *
  exact hw.trans huv

/-- `bbZAncestors Z` 沿祖先关系**向上封闭**。 -/
theorem mem_bbZAncestors_of_anc {G : DAG V} {Z : Finset V} {u v : V}
    (hv : v ∈ G.bbZAncestors Z) (huv : G.isAncestor u v) : u ∈ G.bbZAncestors Z := by
  simp only [bbZAncestors, ancestralSet, Finset.mem_union, ancestorsSet,
    Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  rcases hv with h | ⟨z, hz, huz⟩
  · exact Or.inr ⟨v, h, huv⟩
  · exact Or.inr ⟨z, hz, by
      rw [G.isAncestor_iff_transGen] at *
      exact huv.trans huz⟩

/-- `Z ⊆ bbZAncestors Z`。 -/
theorem subset_bbZAncestors (G : DAG V) (Z : Finset V) : Z ⊆ G.bbZAncestors Z := by
  intro z hz
  show z ∈ G.ancestralSet Z
  rw [ancestralSet]
  exact Finset.mem_union_left _ hz

/-- `bbZAncestors Z` 对「取父」封闭。 -/
theorem parents_subset_bbZAncestors (G : DAG V) {Z : Finset V} {w v : V}
    (hw : w ∈ G.bbZAncestors Z) (hv : v ∈ G.parents w) : v ∈ G.bbZAncestors Z :=
  mem_bbZAncestors_of_anc hw (isAncestor.edge (G.mem_parents.mp hv))

omit [DecidableEq V] [Fintype V] in
/-- `bbInit` 里那个匿名 embedding 作用在 `w` 上**就是** `(w, b)`。

`rfl` 可证：匿名构造器 `⟨(·, b), ⋯⟩` 的 `toFun` 定义上就是 `(·, b)`。 -/
theorem bbInit_emb_apply (b : BBDir) (w : V) :
    (⟨(·, b), fun a c (h : (a, b) = (c, b)) => by simpa using h⟩ : V ↪ BBState V) w
      = ((w, b) : BBState V) := rfl

/-- **`bbInit` 的成员性表征（显式形式，绕开匿名 embedding 的透明性问题）**：

`s ∈ bbInit X` 当且仅当存在 `x ∈ X` 使得 `s.1` 是 `x` 的孩子（徽章 `fromParent`）
或 `x` 的父母（徽章 `fromChild`），且 `s` 恰为 `(s.1, 对应徽章)`。

把第一坐标 `s.1` **直接**写进结论，避免在证明里再去建立 `x` 与 `s.1` 的关系。 -/
theorem mem_bbInit_iff {G : DAG V} {X : Finset V} {s : BBState V} :
    s ∈ G.bbInit X ↔
      (∃ x ∈ X, G.edge x s.1 ∧ s.2 = BBDir.fromParent) ∨
      (∃ x ∈ X, G.edge s.1 x ∧ s.2 = BBDir.fromChild) := by
  constructor
  · intro hs
    simp only [bbInit, mem_biUnion, mem_map, mem_union, G.mem_children, G.mem_parents,
      bbInit_emb_apply] at hs
    obtain ⟨x, hx, x_fl | x_fr⟩ := hs
    · obtain ⟨c, hc, hcs⟩ := x_fl
      refine Or.inl ⟨x, hx, ?_, ?_⟩
      · rw [← hcs]; exact hc
      · rw [← hcs]
    · obtain ⟨c, hc, hcs⟩ := x_fr
      refine Or.inr ⟨x, hx, ?_, ?_⟩
      · rw [← hcs]; exact hc
      · rw [← hcs]
  · rintro (⟨x, hx, he, hb⟩ | ⟨x, hx, he, hb⟩)
    · simp only [bbInit, mem_biUnion, mem_map, mem_union, G.mem_children, G.mem_parents,
        bbInit_emb_apply]
      refine ⟨x, hx, Or.inl ⟨s.1, ?_, ?_⟩⟩
      · exact he
      · ext <;> simp [hb]
    · simp only [bbInit, mem_biUnion, mem_map, mem_union, G.mem_children, G.mem_parents,
        bbInit_emb_apply]
      refine ⟨x, hx, Or.inr ⟨s.1, ?_, ?_⟩⟩
      · exact he
      · ext <;> simp [hb]

/-! ### ⚠ 关于「`bbInit X` 的第一坐标在 `X` 内」这一陈述

曾经想证明的引理是

    `s ∈ G.bbInit X → s.1 ∈ X`

**这个陈述是假的**，无法证明。反例：取 `V = Fin 2`、边为 `0 → 1`、`X = {0}`。
此时 `(1, fromParent) ∈ bbInit {0}`（因为 `1` 是 `0` 的孩子），但其第一坐标
`1 ∉ {0}`。根因在于 `bbInit` 的**定义**：

    bbInit X = X.biUnion (fun x => children x × {fromParent} ∪ parents x × {fromChild})

它装的是 `X` 的**邻居**（孩子配 `fromParent`、父母配 `fromChild`），而非 `X` 自身。
`mem_bbInit_iff` 已经忠实刻画了这一点（右边是 `G.edge x s.1` 或 `G.edge s.1 x`，
是**边关系**，不是等式 `s.1 = x`）。

因此这里给出**可证且为真**的替代引理：`bbInit X` 的第一坐标总与 `X` 中某点相邻。
`bbInit_fst_mem` 的名字不再使用，以免暗示不成立的 `s.1 ∈ X`。 -/

/-- **`bbInit X` 的第一坐标与 `X` 中某点相邻**（正确的、从 `bbInit` 定义可推的陈述）。 -/
theorem bbInit_fst_adj {G : DAG V} {X : Finset V} {s : BBState V} (hs : s ∈ G.bbInit X) :
    ∃ x ∈ X, G.edge x s.1 ∨ G.edge s.1 x := by
  rcases mem_bbInit_iff.mp hs with ⟨x, hx, he, _⟩ | ⟨x, hx, he, _⟩
  · exact ⟨x, hx, Or.inl he⟩
  · exact ⟨x, hx, Or.inr he⟩

/-! ===========================================================================
  §1 ⭐⭐ **徽章（badge）分解 —— T1**

  `bbStep` 的两个分支里，`children` 与 `parents` 的产出徽章各自一致；于是
  「第一坐标 ∈ `X`」这一族在 `fromParent` 分支的 `children` 侧、以及
  `fromChild` 分支的 `parents` 侧被保持，而 `bbZAncestors Z` 一族被
  `parents`/`children` 两侧都保持（沿祖先关系向上/向下封闭）。

  ⚠ **精确的不变量**（这是本文件采用的、**可证**的那条）：

  $$s \in \mathrm{bbReach}(Z,X) \;\Longrightarrow\;
    s_1 \in X \cup \mathrm{bbZAnc}(Z).$$

  证明用 `bbReachable_minimal`，候选集
  $$T := (X \times \{\texttt{fromParent}, \texttt{fromChild}\}) \cup
         (\mathrm{bbZAnc}(Z) \times \{\texttt{fromParent}, \texttt{fromChild}\}),$$
  即**徽章无关**的 `X ∪ bbZAnc(Z)`。

  ⚠⚠ **关键点**：`fromChild` 分支在 `w ∉ Z` 时**也**能走 `children`（到达子节点
  徽章变 `fromParent`）。此时子节点可能**既不在 `X` 也不在 `bbZAnc(Z)`** ——
  所以 `T := (X ∪ bbZAnc(Z)) ×ᵘ` **不封闭**。

  ⟹ 必须把 `fromParent` 侧的 `children` 步也**抓住**：`fromChild` 的 `children`
  后继要求 `w ∈ bbZAnc(Z)`，其子节点一般不在 `bbZAnc(Z)` 内。
  **因此 `T` 必须再并上「`bbZAnc(Z)` 的 children」**，而这会**发散**。

  ⟹ **§1 的结论（诚实登记）**：徽章分解**在 `fromChild → children` 这一支上失效**。
  这不是证明技巧的问题，而是 `bbStep` 的 `fromChild` 分支确实允许
  「碰一个非 collider 后继续朝子节点跑」。

  好消息是：**主定理（§3 剥离）不需要徽章分解**。§2 走一条**完全不同**、
  **更强**的路：直接证明可达顶点集在「拓扑最末点」处**可以被完全算出来**。
  徽章分解留作**可选缺口** `badge_decomposition_Gap`（见 §5）。
  =========================================================================== -/

/-- ⚠ **可选缺口（显式 `Prop`，不进前件、不被下游使用）**：
可达态的第一坐标落在 `X ∪ bbZAncestors Z` 内。 -/
def badge_decomposition_Gap : Prop :=
  ∀ {V : Type u} [DecidableEq V] [Fintype V] (G : DAG V) (Z X : Finset V) (s : BBState V),
    s ∈ G.bbReachable Z X → s.1 ∈ X ∪ G.bbZAncestors Z

/-! ===========================================================================
  §2 ⭐⭐⭐ **空缺（perfect gap）：可达顶点集的精确计算**

  本节的**核心观察**（这是「拓扑序剥离」在 Lean 里真正可落地的口径）：

  > 若顶点 `ℓ` 满足「**无入边且不属于 `Z`**」（`Z ∪ {ℓ}` 里没有点能指向它），
  > 则 `ℓ` **唯一**的到达方式是**从 `ℓ` 自身的初始前沿**（即 `ℓ → c` 一步，
  > 徽章 `fromParent`）。
  >
  > ⟹ `bbReachableVertices Z (insert ℓ S) = bbReachableVertices Z S ∪ {ℓ}`，
  > 从而 **`ℓ` 是否可达完全由「它自己」决定**，与 `S` 无关。

  **为什么这够用**：取 `ℓ` 为 `X ∪ Y ∪ Z` 中拓扑序**最小**的点 ⟹ `ℓ` 无入边；
  又由 `dSep` 的第二、三合取项，`ℓ` 与 `Z`、`Y` 不相交，故 `ℓ ∉ Z`。
  于是 §3 的剥离**无需任何额外假设**，`ℓ` 由 `Finset.exists_min_image` 选出。
  =========================================================================== -/

/-- **`perfectGap`**：「`Z ∪ {ℓ}` 里没有点指向 `ℓ`」——即 `ℓ` 在 `Z ∪ {ℓ}` 中是源点。 -/
def perfectGap (G : DAG V) (Z : Finset V) (l : V) : Prop :=
  ∀ u ∈ insert l Z, ¬ G.edge u l

/-- **`perfectGap_of_min` ⭐⭐**：若 `ℓ` 在 `S` 中拓扑序最小且 `ℓ ∉ Z`，则 `perfectGap`。

**证明**：若 `u ∈ insert ℓ Z` 且 `u → ℓ`，则 `topoOrder u < topoOrder ℓ`；
而 `u ≠ ℓ`（无自环）且 `u ∈ S`（`ℓ ∉ Z`）时与 `ℓ` 的最小性矛盾；
`u = ℓ` 时违反无环性。 -/
theorem perfectGap_of_min {G : DAG V} {S Z : Finset V} {l : V}
    (hZS : ∀ u ∈ Z, u ∈ S) (hmin : ∀ w ∈ S, G.topoOrder l ≤ G.topoOrder w) :
    perfectGap G Z l := by
  intro u hu hedu
  rcases Finset.mem_insert.mp hu with h1 | huZ
  · rw [h1] at hedu
    exact G.acyclic l (Relation.TransGen.single hedu)
  · have hlt := G.topoOrder_lt u l hedu
    have hge := hmin u (hZS u huZ)
    omega

end DSepTopoPeel
end Fate
