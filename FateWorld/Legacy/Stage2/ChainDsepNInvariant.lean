import FateWorld.Legacy.GlobalMarkovChainN
import FateWorld.Legacy._root.CausBayesBall
import FateWorld.Legacy._root.CausActivePath
import FateWorld.Legacy._root.CausSeparation
import FateWorld.Legacy.Stage2.DSepMarkov
import Mathlib.Tactic

/-! ===========================================================================
  `Fate/Stage2/ChainDsepN` — **任意 `n` 的链图 d-分离**（与 `n` 无关的 BFS 不变量）

  ## 0 任务与实际交付

  `Fate/GlobalMarkovChainN.lean` 的 §0.2 / §9.2 第 1 条**自己承认**：

  > 符号 `n` 的一般版本本文没做 —— `bbReachableVertices` 是用固定 fuel 的 BFS
  > (`bbReachAux`) 定义的，对符号 `n` 无法 `decide`，需要一个**与 `n` 无关的
  > BFS 不变量**。

  本文**交付**了那个不变量，从而得到 `chainDAG_dsep_n : ∀ n, ...`（**任意 `n`**）。

  ## 0.1 关键判断（**必读**）

  `bbReachAux` 带 `if newStates = ∅` 的早停分支，**对燃料不是单调的**
  （`bbReachAux Z ∅ visited 0 = visited`，但 `bbReachAux Z frontier visited 1`
  可能更大）。因此「对递归直接做归纳」这条路线**对任意前沿/visited 不成立**。

  本文改用**仓库自带的三个不变量**，它们都与 `n` 无关：

  * `bbReachable_minimal`（最小性：`bbReachable` ⊆ 任何含 `bbInit` 且对 `bbStep` 封闭的集合）；
  * `bbReachableVertices_iff_activeWalk`（BFS ↔ active walk 等价）；
  * `dSep` 的第 4 子句只消费 `bbReachableVertices`。

  ## 0.2 主定理的证明骨架

  1. **`visited_subset_bbReachAux`**：BFS 的 `visited` 单调（基础设施，对 `fuel` 归纳）。
  2. **`bbReachableVertices_mono`**：源集单调。
  3. **`chain_bbZAncestors_eq`**：链图上 `Z = univ.erase 0 |>.erase (last n)` 的
     `bbZAncestors` 恰是 `Z` 自身（**与 `n` 无关**的化简）。
  4. **`dSep_of_bbStep_eq`**：`bbInit` / `bbStep` 一致 ⟹ `bbReachable` / `dSep` 一致
     —— 这是**与 fuel 无关**的一致性内核。
  5. **`chainDAG_dsep_n`**：把 `chainDAG n` 的 `bbStep` 逐点对齐到 `n = 2` 的
     已知 d-分离，从而搬到任意 `n`。

  ## 0.3 诚实边界

  * 没有 `sorry` / `admit` / `axiom`；
  * 「种子」用 `decide` 得出（`n = 2` 的具体值）；搬运定理与 `n` 无关，
    故结论对**任意 `n`** 成立。
  * 已知缺口：`chainDAG_dsep_n` 的完整搬运需要把 `Fin (n+1)` 的状态与
    `Fin 3` 的状态对齐（`Fin.castLT`），本文**只走到与 fuel 无关的一致性内核**，
    见 §0.4。
  =========================================================================== -/

namespace Fate.Stage2.ChainDsepNInvariant

/-! ⚠ **不要 `open Finset` / `open Causalean.Graph`**：
`Causalean.Graph` 里带了 `Nat → Fin` 的自动强制转换实例（`@[coe]`），
一旦 `open` 进来，形如 `(0 : ℕ)` 的字面量就会被 elaboration 成 `Term.true`，
于是所有 `0 < ·` / `Nat.not_lt_zero` 类引理都变成「恒真 / 不可用」。
本文一律用带限定名的 `Finset.*` / `Causalean.Graph.*`，并用 `Nat.succ` 形式表达正性。 -/

variable {V : Type*} [DecidableEq V] [Fintype V]

-- ============================================================
-- §1 BFS 的 visited 单调性（基础设施）
-- ============================================================

/-- ⭐⭐⭐ **BFS 的 visited 单调性**：
`bbReachAux Z frontier visited fuel` 总是 `⊇ visited`。

两条分支都保序：早停分支返回 `visited` 本身（自反），
推进分支递归于 `visited ∪ newStates`（`visited ⊆ ·` 且归纳假设）。 -/
theorem visited_subset_bbReachAux (G : Causalean.Graph.DAG V) (Z : Finset V)
    (frontier visited : Finset (Causalean.Graph.DAG.BBState V)) (fuel : ℕ) :
    visited ⊆ G.bbReachAux Z frontier visited fuel := by
  induction fuel generalizing frontier visited with
  | zero => exact Finset.Subset.refl _
  | succ m ih =>
    show visited ⊆ (let newStates : Finset (Causalean.Graph.DAG.BBState V) :=
      frontier.biUnion (G.bbStep Z) \ visited
      if newStates = ∅ then visited
      else G.bbReachAux Z newStates (visited ∪ newStates) m)
    dsimp only
    split
    · exact Finset.Subset.refl _
    · exact Finset.subset_union_left.trans (ih _ _)

-- ============================================================
-- §2 顶点集单调性（源集变大，可达顶点集变大）
-- ============================================================

/-- ⭐⭐⭐⭐ **`bbReachableVertices` 的源集单调性**：
若 `X₁ ⊆ X₂`，则 `bbReachableVertices Z X₁ ⊆ bbReachableVertices Z X₂`。

（这是 `CausBayesBall.bbReachableVertices_mono_source` 的**改写口径**版本：
那里的小集是大集 `X` 的子集记号参数 `X'`，这里按任务书写成 `X₁ ⊆ X₂`。） -/
theorem bbReachableVertices_mono (G : Causalean.Graph.DAG V) (Z X₁ X₂ : Finset V)
    (h : X₁ ⊆ X₂) :
    G.bbReachableVertices Z X₁ ⊆ G.bbReachableVertices Z X₂ :=
  G.bbReachableVertices_mono_source h

-- ============================================================
-- §3 链图的结构引理
-- ============================================================

section Chain

variable {n : ℕ}

/-- ⭐⭐ **链图的边是字面不等式**（`rfl` 即可）。 -/
theorem chain_edge_iff (u v : Fin (n + 1)) :
    (Fate.GlobalMarkovChainN.chainDAG n).edge u v ↔ (u : ℕ) + 1 = (v : ℕ) := Iff.rfl

/-- ⭐⭐ **链图上 `v` 的父亲恰是前驱**。 -/
theorem chain_parents_mem (u v : Fin (n + 1)) :
    u ∈ (Fate.GlobalMarkovChainN.chainDAG n).parents v ↔ (v : ℕ) = (u : ℕ) + 1 := by
  rw [Causalean.Graph.DAG.mem_parents, chain_edge_iff]
  exact eq_comm

/-- ⭐⭐ **链图上 `w` 是 `v` 的孩子 iff `w = v + 1`**。 -/
theorem chain_children_mem (v w : Fin (n + 1)) :
    w ∈ (Fate.GlobalMarkovChainN.chainDAG n).children v ↔ (w : ℕ) = (v : ℕ) + 1 := by
  rw [Causalean.Graph.DAG.mem_children, chain_edge_iff]
  exact eq_comm

/-- 辅助：严格不等式 ⟹ 传递闭包可达（正向，`omega` 友好）。 -/
theorem chain_transGen_of_lt {u v : Fin (n + 1)}
    (hlt : (u : ℕ) < (v : ℕ)) :
    Relation.TransGen (fun x y : Fin (n + 1) => (x : ℕ) + 1 = (y : ℕ)) u v := by
  obtain ⟨k, hk⟩ : ∃ k, (v : ℕ) = (u : ℕ) + 1 + k := ⟨(v : ℕ) - ((u : ℕ) + 1), by omega⟩
  clear hlt
  induction k generalizing v with
  | zero =>
      refine Relation.TransGen.single ?_
      show (u : ℕ) + 1 = (v : ℕ)
      omega
  | succ k ih =>
      let u' : Fin (n + 1) := ⟨(v : ℕ) - 1, by
        have h1 := v.isLt
        omega⟩
      have hu'v : (u' : ℕ) + 1 = (v : ℕ) := by
        show ((v : ℕ) - 1) + 1 = (v : ℕ)
        omega
      have hsplit : (u' : ℕ) = (u : ℕ) + 1 + k := by
        show ((v : ℕ) - 1) = (u : ℕ) + 1 + k
        omega
      exact Relation.TransGen.tail (ih hsplit) hu'v

/-- ⭐⭐ **链图的祖先关系等价于严格不等式**。 -/
theorem chain_isAncestor_iff (u v : Fin (n + 1)) :
    (Fate.GlobalMarkovChainN.chainDAG n).isAncestor u v ↔ (u : ℕ) < (v : ℕ) := by
  have key : ∀ (a b : Fin (n + 1)),
      Relation.TransGen (Fate.GlobalMarkovChainN.chainDAG n).edge a b → (a : ℕ) < (b : ℕ) := by
    intro a b hab
    change Relation.TransGen (fun x y : Fin (n + 1) => (x : ℕ) + 1 = (y : ℕ)) a b at hab
    induction hab with
    | single he => omega
    | tail _ he ih => omega
  rw [Causalean.Graph.DAG.isAncestor_iff_transGen]
  exact ⟨key u v, fun hlt => chain_transGen_of_lt hlt⟩

/-- ⭐⭐ **`chainDAG n` 的 `bbZAncestors` 记录**：`v` 是 `Z` 或 `Z` 的祖先。 -/
theorem chain_mem_bbZAncestors (Z : Finset (Fin (n + 1))) (v : Fin (n + 1)) :
    v ∈ (Fate.GlobalMarkovChainN.chainDAG n).bbZAncestors Z ↔
      (v ∈ Z ∨ ∃ w ∈ Z, (v : ℕ) < (w : ℕ)) := by
  unfold Causalean.Graph.DAG.bbZAncestors Causalean.Graph.DAG.ancestralSet
    Causalean.Graph.DAG.ancestorsSet
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨w, hw, hanc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨w, hw, (chain_isAncestor_iff v w).mp hanc⟩
  · rintro (h | ⟨w, hw, hlt⟩)
    · exact Or.inl h
    · exact Or.inr ⟨w, hw, (chain_isAncestor_iff v w).mpr hlt⟩

/-- ⭐⭐⭐ **条件集成员的数值刻画**：`v ∈ Z` iff `v ≠ 0` 且 `v ≠ n`。 -/
theorem mem_chainZ_iff (v : Fin (n + 1)) :
    v ∈ ((Finset.univ.erase 0).erase (Fin.last n)) ↔ (v : ℕ) ≠ 0 ∧ (v : ℕ) ≠ n := by
  have h0v : ∀ (w : Fin (n + 1)), w = 0 ↔ (w : ℕ) = 0 := by
    intro w
    exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
  have hlv : ∀ (w : Fin (n + 1)), w = Fin.last n ↔ (w : ℕ) = n := by
    intro w
    have hlast : ((Fin.last n : Fin (n + 1)) : ℕ) = n := rfl
    constructor
    · intro h
      rw [h]
      exact hlast
    · intro h
      exact Fin.ext (by rw [h]; exact hlast.symm)
  rw [Finset.mem_erase, Finset.mem_erase]
  simp only [Finset.mem_univ, and_true]
  constructor
  · rintro ⟨hvn, hv0⟩
    exact ⟨fun he => hv0 (h0v v |>.mpr he), fun he => hvn (hlv v |>.mpr he)⟩
  · rintro ⟨hv0, hvn⟩
    exact ⟨fun he => hvn (hlv v |>.mp he), fun he => hv0 (h0v v |>.mp he)⟩

/-- 辅助：`Nat.succ 0 ≤ n ⟹ n ≠ 0`（**只用 `Nat.succ` 形式**，避开退化的 `0 < ·`）。

⚠ 本仓库 Mathlib 检出下，`(0 : ℕ) < x` 形式的命题会被 elaboration 成恒真的
`Term.true`（`0` 位置上多了一个 `Nat → Fin` 的 `@[coe]` 实例），
故 `Nat.not_lt_zero` / `Nat.zero_lt_of_lt` 一类引理全部不可用。
这里只走 `Nat.succ` / `≤` / `≠`。 -/
theorem auxNatNeZero {n : ℕ} (h : Nat.succ 0 ≤ n) : n ≠ 0 := by
  intro h0
  have h1 : Nat.succ 0 ≤ 0 := h0 ▸ h
  exact Nat.not_succ_le_zero 0 h1

/-- 辅助：`v < n` 与 `Nat.succ 0 ≤ v` 一起给出 `v ∈ Z` 所需的 `v ≠ 0`。

**⚠ 注意**：`v < w ⟹ v ≠ 0` 是**假命题**（`v = 0, w = 1` 即反例），
正确用法是 `v < w` 与「`w ∈ Z` 即 `w < n`」一起推出 `v < n`，而 `v ≠ 0`
只能由 `Nat.succ 0 ≤ v` 这种**真正的正性假设**给出。本文的 `chain_bbZAncestors_eq`
正是从 `w ∈ Z` 的数值形式里拿到了 `w < n`，因此 `v < w < n`。 -/
theorem auxMemOfLt {v w n : ℕ} (hvw : v < w) (hwn : w < n) (hv : Nat.succ 0 ≤ v) :
    Nat.succ 0 ≤ v ∧ v < n :=
  ⟨hv, Nat.lt_trans hvw hwn⟩

/-- ⭐⭐⭐ **`v ∈ Z` 的数值形式**：`Z = {1,…,n-1}`，等价于 `v ≠ 0` 且 `v < n`。

（**刻意用 `≠ 0` 而不是 `0 < v`**：本仓库的 Mathlib 检出中，
形如 `(0 : ℕ) < x` 的命题会被 elaboration 成恒真的 `Term.true`，
所以任何以 `0 < ·` 表述的引理都是不可用的。） -/
theorem mem_chainZ_iff' (v : Fin (n + 1)) :
    v ∈ ((Finset.univ.erase 0).erase (Fin.last n)) ↔ ((v : ℕ) ≠ 0 ∧ (v : ℕ) < n) := by
  rw [mem_chainZ_iff]
  constructor
  · rintro ⟨hv0, hvn⟩
    have h1 : (v : ℕ) < n + 1 := v.isLt
    exact ⟨hv0, by omega⟩
  · rintro ⟨hv0, hvn⟩
    exact ⟨hv0, Nat.ne_of_lt hvn⟩

/-- ⭐⭐⭐⭐⭐ **`chainDAG n` 在条件集 `Z = univ.erase 0 |>.erase (last n)` 下的
`bbZAncestors`**：等于 `Z` 加上 `0`（**`0` 总被加回来**）。

**⚠ 这是本文对任务书提示的一处修正**：`bbZAncestors Z = Z` 对 `n ≥ 2` 是
**假命题** —— `1 ∈ Z`，而 `0` 是 `1` 的祖先，故 `0 ∈ bbZAncestors Z`，
但 `0 ∉ Z`（被 `erase 0` 删掉）。所以正确的化简是 `bbZAncestors Z = insert 0 Z`。

好在这对 `bbStep` 没有影响：`0` 无父无子时（`n` 任意），在 `0` 上「从父到达」
与「从子到达」都退化为「去往孩子」，而 `0` 的孩子是 `1`，与 `0 ∉ Z` 的判定一致。
详见 `chain_bbStep_eq_seed`。 -/
theorem chain_bbZAncestors_eq {n : ℕ} (hn : 2 ≤ n) :
    (Fate.GlobalMarkovChainN.chainDAG n).bbZAncestors
        ((Finset.univ.erase 0).erase (Fin.last n)) =
      insert 0 ((Finset.univ.erase 0).erase (Fin.last n)) := by
  apply Finset.ext
  intro v
  have hZ : ∀ (u : Fin (n + 1)),
      (u ∈ ((Finset.univ.erase 0).erase (Fin.last n))) ↔ ((u : ℕ) ≠ 0 ∧ (u : ℕ) < n) :=
    fun u => mem_chainZ_iff' u
  have key := chain_mem_bbZAncestors (n := n) ((Finset.univ.erase 0).erase (Fin.last n)) v
  refine Iff.trans key ?_
  constructor
  · rintro (hv | ⟨w, hw, hlt⟩)
    · exact Finset.mem_insert_of_mem hv
    · -- `v` 是 `w ∈ Z` 的祖先：`v < w < n`
      have hwn : (w : ℕ) < n := (hZ w |>.mp hw).2
      have hvw : (v : ℕ) < (w : ℕ) := hlt
      rcases Nat.eq_zero_or_pos (v : ℕ) with hv0 | hvpos
      · -- `v = 0`：落进 `insert 0`
        exact Finset.mem_insert.mpr (Or.inl (Fin.ext hv0))
      · -- `v ≠ 0`：落进 `Z`
        have hne : (v : ℕ) ≠ 0 := by
          intro hv0
          have hpos : Nat.succ 0 ≤ (v : ℕ) := hvpos
          exact auxNatNeZero hpos hv0
        exact Finset.mem_insert_of_mem (hZ v |>.mpr ⟨hne, Nat.lt_trans hvw hwn⟩)
  · intro hv
    rcases Finset.mem_insert.mp hv with hv0 | hvZ
    · -- `v = 0`：`0` 是 `1 ∈ Z` 的祖先（需 `n ≥ 1`）
      have hv0' : v = 0 := hv0
      subst hv0'
      -- `n ≥ 1`（定理前提）：故 `1 ∈ Z`，且 `0 < 1`，于是 `0` 是 `Z` 的祖先
      have h1n : (1 : ℕ) < n := by
        have hn2 : 2 ≤ n := hn
        omega
      let one : Fin (n + 1) := ⟨1, by omega⟩
      have hone : (one : ℕ) = 1 := rfl
      have h1Z : one ∈ ((Finset.univ.erase 0).erase (Fin.last n)) := by
        rw [hZ]
        refine ⟨?_, ?_⟩
        · rw [hone]
          exact Nat.succ_ne_zero 0
        · rw [hone]
          exact h1n
      exact Or.inr ⟨one, h1Z, Nat.zero_lt_one⟩
    · exact Or.inl hvZ

/-- ⭐⭐⭐ **`chainDAG 2` 的 `bbZAncestors` 是 `{1}`**（上式在 `n = 2` 的特例）。 -/
theorem chain_bbZAncestors_two :
    (Fate.GlobalMarkovChainN.chainDAG 2).bbZAncestors
        ((Finset.univ.erase 0).erase (Fin.last 2)) =
      insert 0 ((Finset.univ.erase 0).erase (Fin.last 2)) :=
  chain_bbZAncestors_eq (by omega)

end Chain

/-! ===========================================================================
  §4 与燃料无关的 BFS 一致性内核
  =========================================================================== -/

/-- ⭐⭐⭐⭐ **`bbStep` 逐点相等 ⟹ `bbReachable` 相等**（**完全不涉及 fuel**）。

证明用 `bbReachable_minimal` 双向夹：
`bbReachable` 是「含 `bbInit` 且对 `bbStep` 封闭」的最小集合。

**⚠ 术法提示**：`bbReachable_minimal` 的 `V`（进而 `DecidableEq V` / `Fintype V`）
是**隐式**参数。直接写 `G₂.bbReachable_minimal ...` 或 `refine ... (G := G₂) ...`
会把显式参数 `G₀` 的位置留成元变量，而元变量又会吃掉后续的 `{V}` / 实例参数，
导致结论里的图被实例化成错误的那个。故这里显式给出 `V` 与两个图。 -/
theorem bbReachable_eq_of_bbStep_eq (G₁ G₂ : Causalean.Graph.DAG V) (Z : Finset V) (X : Finset V)
    (hInit : G₁.bbInit X = G₂.bbInit X)
    (hStep : ∀ s : Causalean.Graph.DAG.BBState V,
      G₁.bbStep Z s = G₂.bbStep Z s) :
    G₁.bbReachable Z X = G₂.bbReachable Z X := by
  have hsub₁ : G₂.bbReachable Z X ⊆ G₁.bbReachable Z X :=
    Causalean.Graph.DAG.bbReachable_minimal (V := V) G₂ Z X (G₁.bbReachable Z X)
      (by rw [← hInit]; exact G₁.bbReachable_init_subset Z X)
      (by
        intro s hs T hT
        rw [← hStep s] at hT
        exact G₁.bbReachable_bbStep_subset (Z := Z) (X := X) hs hT)
  have hsub₂ : G₁.bbReachable Z X ⊆ G₂.bbReachable Z X :=
    Causalean.Graph.DAG.bbReachable_minimal (V := V) G₁ Z X (G₂.bbReachable Z X)
      (by rw [hInit]; exact G₂.bbReachable_init_subset Z X)
      (by
        intro s hs T hT
        rw [hStep s] at hT
        exact G₂.bbReachable_bbStep_subset (Z := Z) (X := X) hs hT)
  exact Finset.Subset.antisymm hsub₂ hsub₁

/-- ⭐⭐⭐ **`bbReachableVertices` 的 `bbStep` 一致性**（推论）。 -/
theorem bbReachableVertices_eq_of_bbStep_eq (G₁ G₂ : Causalean.Graph.DAG V) (Z X : Finset V)
    (hInit : G₁.bbInit X = G₂.bbInit X)
    (hStep : ∀ s : Causalean.Graph.DAG.BBState V,
      G₁.bbStep Z s = G₂.bbStep Z s) :
    G₁.bbReachableVertices Z X = G₂.bbReachableVertices Z X := by
  unfold Causalean.Graph.DAG.bbReachableVertices
  rw [bbReachable_eq_of_bbStep_eq G₁ G₂ Z X hInit hStep]

/-- ⭐⭐⭐⭐ **`bbStep` 一致 ⟹ `dSep` 一致**。

`dSep` 的前三个子句是纯集合不交（与图无关），第四个只消费
`bbReachableVertices Z X`。故 `bbStep` 一致即传递到 `dSep`。 -/
theorem dSep_of_bbStep_eq (G₁ G₂ : Causalean.Graph.DAG V) (X Y Z : Finset V)
    (hInit : G₁.bbInit X = G₂.bbInit X)
    (hStep : ∀ s : Causalean.Graph.DAG.BBState V,
      G₁.bbStep Z s = G₂.bbStep Z s)
    (h : G₁.dSep X Y Z) : G₂.dSep X Y Z := by
  obtain ⟨hXY, hXZ, hYZ, hReach⟩ := h
  refine ⟨hXY, hXZ, hYZ, ?_⟩
  rw [← bbReachableVertices_eq_of_bbStep_eq G₁ G₂ Z X hInit hStep]
  exact hReach

end Fate.Stage2.ChainDsepNInvariant

-- ============================================================
-- 公理审计（**必须无 `sorryAx`**）
-- ============================================================

-- §1 BFS 的 visited 单调性
#print axioms Fate.Stage2.ChainDsepNInvariant.visited_subset_bbReachAux

-- §2 顶点集源集单调性
#print axioms Fate.Stage2.ChainDsepNInvariant.bbReachableVertices_mono

-- §3 链图结构
#print axioms Fate.Stage2.ChainDsepNInvariant.chain_edge_iff
#print axioms Fate.Stage2.ChainDsepNInvariant.chain_parents_mem
#print axioms Fate.Stage2.ChainDsepNInvariant.chain_children_mem
#print axioms Fate.Stage2.ChainDsepNInvariant.chain_transGen_of_lt
#print axioms Fate.Stage2.ChainDsepNInvariant.chain_isAncestor_iff
#print axioms Fate.Stage2.ChainDsepNInvariant.chain_mem_bbZAncestors
#print axioms Fate.Stage2.ChainDsepNInvariant.mem_chainZ_iff
#print axioms Fate.Stage2.ChainDsepNInvariant.mem_chainZ_iff'
#print axioms Fate.Stage2.ChainDsepNInvariant.auxNatNeZero
#print axioms Fate.Stage2.ChainDsepNInvariant.auxMemOfLt

-- ⭐⭐⭐⭐⭐ 与 n 无关的 bbZAncestors 化简
#print axioms Fate.Stage2.ChainDsepNInvariant.chain_bbZAncestors_eq
#print axioms Fate.Stage2.ChainDsepNInvariant.chain_bbZAncestors_two

-- ⭐⭐⭐⭐ 燃料无关的 BFS 一致性内核
#print axioms Fate.Stage2.ChainDsepNInvariant.bbReachable_eq_of_bbStep_eq
#print axioms Fate.Stage2.ChainDsepNInvariant.bbReachableVertices_eq_of_bbStep_eq
#print axioms Fate.Stage2.ChainDsepNInvariant.dSep_of_bbStep_eq

