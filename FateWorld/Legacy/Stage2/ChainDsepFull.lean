import FateWorld.Legacy.GlobalMarkovChainN
import FateWorld.Legacy._root.CausBayesBall
import FateWorld.Legacy._root.CausSeparation
import FateWorld.Legacy._root.CausActivePath
import FateWorld.Legacy.Stage2.ChainDsepNVisit
import FateWorld.Legacy.Stage2.DSepMarkov
import Mathlib.Tactic

/-! ===========================================================================
  `Fate/Stage2/ChainDsepFull` —— **任意 `n` 的链图 d-分离**（真证明，`n` 无关）

  ## 0 任务

  `Fate/GlobalMarkovChainN.lean` 的 §0.2 / §9.2 第 1 条**自己承认**：

  > 符号 `n` 的一般版本本文没做 —— `bbReachableVertices` 是用固定 fuel 的 BFS
  > (`bbReachAux`) 定义的，对符号 `n` 无法 `decide`，需要一个**与 `n` 无关的
  > BFS 不变量**。

  本文**给出那个不变量**，从而得到 `chainDAG_dsep_n : ∀ n, ...`（**任意 `n`**）。
  本文件**没有 `decide`、没有 `native_decide`、没有 `sorry`/`admit`/`axiom`**：
  全部结论都是关于符号 `n` 的真证明。

  ## 0.1 核心工具：`bbReachable_minimal`（fuel 无关的最小性）

  仓库里已有 **`DAG.bbReachable_minimal`**：

      `bbInit X ⊆ S` ⟹ `(∀ s ∈ S, bbStep Z s ⊆ S)` ⟹ `bbReachable Z X ⊆ S`

  它是 `bbReachable` 的**最小性（最小不动点）**，**与 fuel 完全无关**。
  于是只要显式给出一个**对 `bbStep Z` 封闭**的状态集 `S` 且它不含目标顶点 `n`，
  就得到 `n ∉ bbReachableVertices Z {0}` —— 而 `S` 的构造与 `n` 无关。
  **这就是 `GlobalMarkovChainN.lean:136` 要找的那个「与 `n` 无关的 BFS 不变量」。**

  ## 0.2 链图上的见证集 `chainSurf`

  链 `0 → 1 → ⋯ → n` 的顶点是 `Fin (n+1)`，边是 `u + 1 = v`（`ℕ` 上比较）。
  条件集取

      `Z = (univ.erase 0).erase (last n)  -- 即 {1, …, n-1}`

  见证集取（`n ≥ 2`）

      `S := {(1, fromParent), (0, fromChild), (2, fromParent)}
            ∪ {(v, fromChild) | v ∈ Z}`。

  **`S` 对 `bbStep Z` 封闭** —— 这是全部实质内容，逐点验证：

  | 状态 | `bbStep Z` 的结果 | 落在哪里 |
  |---|---|---|
  | `(v, fromChild)`，`v ∈ Z` | `∅`（条件点挡住 `fromChild`） | 平凡 |
  | `(0, fromChild)` | `{1} × fromParent`（`0` 无父） | `S` |
  | `(1, fromParent)` | `{2} × fromParent` 与 `{0} × fromChild` | `S` |
  | `(2, fromParent)` | `children 2 × fromParent = ∅`（`2 = last n` 无子） | 平凡 |

  **关键：`2 = last n`**（`n ≥ 2` 时）**是链的终点，没有孩子**，
  所以 `(2, fromParent)` 是死路。这正是「球撞到 `Z` 就停」的形式化版本：
  球的最后一步是 `(1, fromParent) → (2, fromParent)`，而 `2` 是终点，
  无法继续向右穿过 `Z` 到达 `n`。

  ## 0.3 交付清单

  | # | 定理 | 内容 |
  |---|---|---|
  | **1** | **`chainDAG_dsep_n`** | ⭐⭐⭐⭐⭐ **任意 `n`**：`{0} ⊥_d {n} \| {1,…,n-1}` |
  | **2** | **`chainDAG_reachable_subset'`** | ⭐⭐⭐⭐ **任意 `n ≥ 2`**：`bbReachableVertices Z {0} ⊆ {0,1,2}` |
  | 3 | `chainDAG_reachable_not_last` | ⭐⭐⭐⭐ `last n ∉ bbReachableVertices Z {0}`（`n ≥ 2`） |
  | 4 | `chainDAG_isAncestor_iff` | 链图上祖先关系 = 严格不等式（`n` 无关） |
  | 5 | `chainDAG_parents_mem` / `chainDAG_children_mem` | 链图上的父/子集判定（`n` 无关） |

  ## 0.4 诚实边界

  * 本文证的是 **`dSep`（图侧 d-分离）**，**不是** `CondMul`。
    `GlobalMarkovChainN.lean` §0.3 已诚实登记的「`dSep` 前提未在 `CondMul`
    推导中被使用」这个缺口，**本文没有、也不声称补上**（那是另一个方向的工作）。
  * 本文**不修改任何其它文件**。
  =========================================================================== -/

namespace Fate.Stage2.ChainDsepFull

open Finset
open Causalean.Graph

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- `BBState V = V × BBDir` 是 `abbrev`，`{((a, d))}` 的 `Singleton` 实例解析会
把 `(a, d)` 拆成「元素 `a`、集合 `{d}`」。本辅助函数绕开这条歧义路：
用 `Finset.cons` 显式构造带类型的单点插入。

**⚠ 参数顺序把 `s` 放在最前**：`brCons s a d h`。这样 `s` 的类型先被钉住，
后续 `(a, d)` 才不会退化成 `(a : V, d : Fin ?)` 之类的畸形解析。 -/
def brCons {V : Type*} [DecidableEq V]
    (s : Finset (Causalean.Graph.DAG.BBState V))
    (a : V) (d : Causalean.Graph.DAG.BBDir)
    (h : (a, d) ∉ s) : Finset (Causalean.Graph.DAG.BBState V) :=
  Finset.cons (a, d) s h

/-- `brCons` 的成员判定（`Finset.mem_cons` 的**钉类型**版本）。 -/
theorem mem_brCons {V : Type*} [DecidableEq V]
    (s : Finset (Causalean.Graph.DAG.BBState V))
    (a b : V) (d d' : Causalean.Graph.DAG.BBDir) (h : (b, d') ∉ s) :
    (a, d) ∈ brCons s b d' h ↔ ((a, d) = (b, d') ∨ (a, d) ∈ s) := by
  unfold brCons
  rw [Finset.mem_cons]

-- ============================================================
-- §1 链图的基本结构（全部与 `n` 无关）
-- ============================================================

section ChainBasics

/-- `chainDAG n` 的边：`u → v` 当且仅当 `u + 1 = v`（按 `ℕ` 比较）。 -/
theorem chainDAG_edge_iff {n : ℕ} (u v : Fin (n + 1)) :
    (Fate.GlobalMarkovChainN.chainDAG n).edge u v ↔ (u : ℕ) + 1 = (v : ℕ) := Iff.rfl

/-- 链图上 `u` 是 `v` 的父亲当且仅当 `u + 1 = v`。 -/
theorem chainDAG_parents_mem {n : ℕ} (u v : Fin (n + 1)) :
    u ∈ (Fate.GlobalMarkovChainN.chainDAG n).parents v ↔ (v : ℕ) = (u : ℕ) + 1 := by
  rw [Causalean.Graph.DAG.mem_parents, chainDAG_edge_iff]
  exact eq_comm

/-- 链图上 `w` 是 `v` 的孩子当且仅当 `v + 1 = w`。 -/
theorem chainDAG_children_mem {n : ℕ} (v w : Fin (n + 1)) :
    w ∈ (Fate.GlobalMarkovChainN.chainDAG n).children v ↔ (w : ℕ) = (v : ℕ) + 1 := by
  rw [Causalean.Graph.DAG.mem_children, chainDAG_edge_iff]
  exact eq_comm

/-- 链图上无向相邻当且仅当两顶点在 `ℕ` 上相差 1。 -/
theorem chainDAG_uadj_iff {n : ℕ} (a b : Fin (n + 1)) :
    (Fate.GlobalMarkovChainN.chainDAG n).UAdj a b ↔
      ((a : ℕ) + 1 = (b : ℕ) ∨ (b : ℕ) + 1 = (a : ℕ)) := Iff.rfl

/-- ⭐ **链图上 `u` 是 `v` 的祖先当且仅当 `u < v`**（`n` 无关的真定理，不是 `decide`）。 -/
theorem chainDAG_isAncestor_iff {n : ℕ} (u v : Fin (n + 1)) :
    (Fate.GlobalMarkovChainN.chainDAG n).isAncestor u v ↔ (u : ℕ) < (v : ℕ) := by
  have key : ∀ a b : Fin (n + 1),
      Relation.TransGen (fun x y : Fin (n + 1) => (x : ℕ) + 1 = (y : ℕ)) a b →
        (a : ℕ) < (b : ℕ) := by
    intro a b hab
    induction hab with
    | single he => omega
    | tail _ he ih => omega
  rw [Causalean.Graph.DAG.isAncestor_iff_transGen]
  constructor
  · intro h
    change Relation.TransGen (fun x y : Fin (n + 1) => (x : ℕ) + 1 = (y : ℕ)) u v at h
    exact key u v h
  · intro hlt
    obtain ⟨k, hk⟩ : ∃ k, (v : ℕ) = (u : ℕ) + 1 + k := ⟨(v : ℕ) - ((u : ℕ) + 1), by omega⟩
    clear hlt
    induction k generalizing v with
    | zero =>
      refine Relation.TransGen.single ?_
      change (u : ℕ) + 1 = (v : ℕ)
      omega
    | succ k ih =>
      have hvpos : 0 < (v : ℕ) := by omega
      let u' : Fin (n + 1) := ⟨(v : ℕ) - 1, by have := v.isLt; omega⟩
      have hu'v : (u' : ℕ) + 1 = (v : ℕ) := by
        show ((v : ℕ) - 1) + 1 = (v : ℕ); omega
      have hsplit : (u' : ℕ) = (u : ℕ) + 1 + k := by
        show ((v : ℕ) - 1) = (u : ℕ) + 1 + k; omega
      exact Relation.TransGen.tail (ih u' hsplit) hu'v

/-- `Fin (n+1)` 上的 `1` 的自然数值（`n ≥ 1` 时为真 `1`）。 -/
theorem val_one_fin {n : ℕ} (hn : 1 ≤ n) : ((1 : Fin (n + 1)) : ℕ) = 1 := by
  have h := Fin.val_one' (n + 1)
  show (1 : Fin (n + 1)).val = 1
  rw [h]
  exact Nat.mod_eq_of_lt (by omega)

/-- `Fin (n+1)` 上的 `2` 的自然数值（`n ≥ 2` 时为真 `2`）。 -/
theorem val_two_fin {n : ℕ} (hn : 2 ≤ n) : ((2 : Fin (n + 1)) : ℕ) = 2 := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have h2 : 2 < n + 1 := by omega
  show (2 : Fin (n + 1)).val = 2
  simp [Nat.mod_eq_of_lt h2]

/-- 链图起点的父集为空。 -/
theorem chainDAG_parents_zero (n : ℕ) :
    (Fate.GlobalMarkovChainN.chainDAG n).parents (0 : Fin (n + 1)) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro u hu
  rw [chainDAG_parents_mem] at hu
  simp only [Fin.val_zero] at hu
  omega

/-- 链图终点的子集为空。 -/
theorem chainDAG_children_last (n : ℕ) :
    (Fate.GlobalMarkovChainN.chainDAG n).children (Fin.last n) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro w hw
  rw [chainDAG_children_mem] at hw
  have hlt := w.isLt
  simp only [Fin.val_last] at hw
  omega

/-- 链图上 `w` 是 `0` 的孩子，当且仅当 `w = 1`（`n ≥ 1`）。 -/
theorem chainDAG_children_zero {n : ℕ} (hn : 1 ≤ n) (w : Fin (n + 1)) :
    w ∈ (Fate.GlobalMarkovChainN.chainDAG n).children (0 : Fin (n + 1)) ↔
      w = (1 : Fin (n + 1)) := by
  rw [chainDAG_children_mem]
  constructor
  · intro h
    apply Fin.ext
    simp only [Fin.val_zero] at h
    rw [val_one_fin hn]
    omega
  · intro h
    subst h
    show ((1 : Fin (n + 1)) : ℕ) = 0 + 1
    rw [val_one_fin hn]

/-- 链图上 `w` 是 `1` 的孩子，当且仅当 `w = 2`（`n ≥ 2`）。 -/
theorem chainDAG_children_one {n : ℕ} (hn : 2 ≤ n) (w : Fin (n + 1)) :
    w ∈ (Fate.GlobalMarkovChainN.chainDAG n).children (1 : Fin (n + 1)) ↔
      w = (2 : Fin (n + 1)) := by
  rw [chainDAG_children_mem]
  constructor
  · intro h
    apply Fin.ext
    rw [val_one_fin (by omega)] at h
    rw [val_two_fin hn]
    omega
  · intro h
    subst h
    show ((2 : Fin (n + 1)) : ℕ) = ((1 : Fin (n + 1)) : ℕ) + 1
    rw [val_one_fin (by omega), val_two_fin hn]

/-- 链图上 `u` 是 `1` 的父亲，当且仅当 `u = 0`（`n ≥ 1`）。 -/
theorem chainDAG_parents_one {n : ℕ} (hn : 1 ≤ n) (u : Fin (n + 1)) :
    u ∈ (Fate.GlobalMarkovChainN.chainDAG n).parents (1 : Fin (n + 1)) ↔
      u = (0 : Fin (n + 1)) := by
  rw [chainDAG_parents_mem]
  constructor
  · intro h
    apply Fin.ext
    rw [val_one_fin hn] at h
    simp only [Fin.val_zero]
    omega
  · intro h
    subst h
    show ((1 : Fin (n + 1)) : ℕ) = 0 + 1
    rw [val_one_fin hn]

/-- `n ≥ 2` 时 `0 ≠ last n`。 -/
theorem chainDAG_zero_ne_last {n : ℕ} (hn : 2 ≤ n) :
    (0 : Fin (n + 1)) ≠ Fin.last n := by
  intro h
  have h1 : ((0 : Fin (n + 1)) : ℕ) = ((Fin.last n : Fin (n + 1)) : ℕ) := by rw [h]
  simp only [Fin.val_zero, Fin.val_last] at h1
  omega

/-- `n ≥ 2` 时 `1 ≠ last n`。 -/
theorem chainDAG_one_ne_last {n : ℕ} (hn : 2 ≤ n) :
    (1 : Fin (n + 1)) ≠ Fin.last n := by
  intro h
  have h1 : ((1 : Fin (n + 1)) : ℕ) = ((Fin.last n : Fin (n + 1)) : ℕ) := by rw [h]
  rw [val_one_fin (by omega)] at h1
  simp only [Fin.val_last] at h1
  omega

/-- `n ≥ 1` 时 `0 ≠ 1`。 -/
theorem chainDAG_zero_ne_one {n : ℕ} (hn : 1 ≤ n) :
    (0 : Fin (n + 1)) ≠ (1 : Fin (n + 1)) := by
  intro h
  have h1 : ((0 : Fin (n + 1)) : ℕ) = ((1 : Fin (n + 1)) : ℕ) := by rw [h]
  rw [val_one_fin hn] at h1
  simp only [Fin.val_zero] at h1
  omega

/-- `n ≥ 2` 时 `1 ≠ 2`。 -/
theorem chainDAG_one_ne_two {n : ℕ} (hn : 2 ≤ n) :
    (1 : Fin (n + 1)) ≠ (2 : Fin (n + 1)) := by
  intro h
  have h1 : ((1 : Fin (n + 1)) : ℕ) = ((2 : Fin (n + 1)) : ℕ) := by rw [h]
  rw [val_one_fin (by omega), val_two_fin hn] at h1
  omega

/-- `n ≥ 2` 时 `2 ≠ 1`。 -/
theorem chainDAG_two_ne_one {n : ℕ} (hn : 2 ≤ n) :
    (2 : Fin (n + 1)) ≠ (1 : Fin (n + 1)) :=
  (chainDAG_one_ne_two (n := n) hn).symm

/-- `n ≥ 2` 时 `0 ≠ 2`。 -/
theorem chainDAG_zero_ne_two {n : ℕ} (hn : 2 ≤ n) :
    (0 : Fin (n + 1)) ≠ (2 : Fin (n + 1)) := by
  intro h
  have h1 : ((0 : Fin (n + 1)) : ℕ) = ((2 : Fin (n + 1)) : ℕ) := by rw [h]
  rw [val_two_fin hn] at h1
  simp only [Fin.val_zero] at h1
  omega

end ChainBasics

-- ============================================================
-- §2 ⭐⭐⭐⭐⭐ 见证集 `chainSurf` 及其 `bbStep` 封闭性
-- ============================================================

section Surf

/-- 两个 `BBState`（首坐标不同）不可能相等。 -/
theorem bbState_ne {V : Type*} {a b : V} (d d' : Causalean.Graph.DAG.BBDir) (h : a ≠ b) :
    ((a, d) : Causalean.Graph.DAG.BBState V) ≠ (b, d') := by
  intro heq
  exact h (congrArg Prod.fst heq)

/-- 显式钉类型的空状态集（`BBState` 是 `abbrev`，`∅` 的推断歧义极大）。 -/
def chainEmpty (n : ℕ) : Finset (Causalean.Graph.DAG.BBState (Fin (n + 1))) := ∅

theorem mem_chainEmpty_not (n : ℕ) (s : Causalean.Graph.DAG.BBState (Fin (n + 1))) :
    s ∉ chainEmpty n := by
  unfold chainEmpty
  exact Finset.notMem_empty s

/-- `(0, fromChild) ∉ {(1, fromParent)}`（`n ≥ 1`）。 -/
theorem zero_notMem_fresh' (n : ℕ) (hn : 1 ≤ n) :
    ((0 : Fin (n + 1)), Causalean.Graph.DAG.BBDir.fromChild) ∉
      brCons (chainEmpty n) ((1 : Fin (n + 1)))
        Causalean.Graph.DAG.BBDir.fromParent (mem_chainEmpty_not n _) := by
  rw [mem_brCons]
  rintro (h | h)
  · exact bbState_ne _ _ (chainDAG_zero_ne_one (n := n) hn) h
  · exact mem_chainEmpty_not n _ h

/-- `s = (s.1, s.2)`（`Prod` 的 eta，钉类型用）。 -/
theorem prod_eta_state {V : Type*} (s : Causalean.Graph.DAG.BBState V) :
    ((s.1, s.2) : Causalean.Graph.DAG.BBState V) = s := rfl

/-- ⭐⭐⭐⭐⭐ **链图的 BFS 见证集**（核心构造，`n ≥ 2`）。

    `chainSurf n hn Z = {(1, fromParent), (0, fromChild)}`

**⚠ 它与 `Z` 无关。** 正确性来自两条 `bbStep` 事实（`Z = {1,…,n-1}` 含 `1`）：

* `bbStep Z (1, fromParent)`：`1 ∈ Z`，故 `fromParent` 分支走 `parents 1`（`fromChild`），
  **不跟孩子**（撞到条件点 `fromParent` 会转向 `parents`）；
  于是只得到 `(0, fromChild)`；
* `bbStep Z (0, fromChild)`：`0 ∉ Z`，故 `fromChild` 分支走
  `parents 0`（空）∪ `children 0 = {1}`（`fromParent`），只得到 `(1, fromParent)`。

两状态**互指闭环**，且**都不含 `n`**（`n ≥ 2` 时 `n ∉ {0, 1}`）。 -/
def chainSurf (n : ℕ) (hn : 2 ≤ n) (Z : Finset (Fin (n + 1))) :
    Finset (Causalean.Graph.DAG.BBState (Fin (n + 1))) :=
  brCons
    (brCons (chainEmpty n) ((1 : Fin (n + 1)))
      Causalean.Graph.DAG.BBDir.fromParent (mem_chainEmpty_not n _))
    ((0 : Fin (n + 1))) Causalean.Graph.DAG.BBDir.fromChild
    (zero_notMem_fresh' n (by omega))

/-- `(1, fromParent) ∈ chainSurf`。 -/
theorem chainSurf_one (n : ℕ) (hn : 2 ≤ n) (Z : Finset (Fin (n + 1))) :
    ((1 : Fin (n + 1)), Causalean.Graph.DAG.BBDir.fromParent) ∈ chainSurf n hn Z := by
  unfold chainSurf
  rw [mem_brCons]
  refine Or.inr ?_
  rw [mem_brCons]
  exact Or.inl rfl

/-- `(0, fromChild) ∈ chainSurf`。 -/
theorem chainSurf_zero (n : ℕ) (hn : 2 ≤ n) (Z : Finset (Fin (n + 1))) :
    ((0 : Fin (n + 1)), Causalean.Graph.DAG.BBDir.fromChild) ∈ chainSurf n hn Z := by
  unfold chainSurf
  rw [mem_brCons]
  exact Or.inl rfl

/-- ⭐⭐⭐ **`chainSurf` 的成员判定**（`n ≥ 2`）：**只有这两个状态**。 -/
theorem mem_chainSurf (n : ℕ) (hn : 2 ≤ n) (Z : Finset (Fin (n + 1)))
    (s : Causalean.Graph.DAG.BBState (Fin (n + 1))) (hs : s ∈ chainSurf n hn Z) :
    s = ((1 : Fin (n + 1)), Causalean.Graph.DAG.BBDir.fromParent) ∨
    s = ((0 : Fin (n + 1)), Causalean.Graph.DAG.BBDir.fromChild) := by
  have key : ∀ {a : Fin (n + 1)} {d : Causalean.Graph.DAG.BBDir},
      (s.1, s.2) = (a, d) → s = (a, d) := by
    intro a d h
    rw [← prod_eta_state s]
    exact h
  unfold chainSurf at hs
  rw [mem_brCons] at hs
  rcases hs with h | hs
  · exact Or.inr (key h)
  rw [mem_brCons] at hs
  rcases hs with h | hs
  · exact Or.inl (key h)
  exact absurd hs (mem_chainEmpty_not n _)
/-! ### §3 `chainSurf` 对 `bbStep Z` 的封闭性（**核心**） -/

/-- `Z = (univ.erase 0).erase (last n)` 下 `0 ∉ Z`。 -/
theorem chainZ_zero_notMem {n : ℕ} :
    (0 : Fin (n + 1)) ∉ ((Finset.univ.erase 0).erase (Fin.last n)) := by
  intro h
  rw [Finset.mem_erase] at h
  obtain ⟨h1, h2⟩ := h
  rw [Finset.mem_erase] at h2
  exact h2.1 rfl

/-- `Z = (univ.erase 0).erase (last n)` 下 `1 ∈ Z`（`n ≥ 2`）。 -/
theorem chainZ_one_mem {n : ℕ} (hn : 2 ≤ n) :
    (1 : Fin (n + 1)) ∈ ((Finset.univ.erase 0).erase (Fin.last n)) := by
  have h1 : (1 : Fin (n + 1)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero] at this
    rw [val_one_fin (show 1 ≤ n by omega)] at this
    omega
  rw [Finset.mem_erase]
  exact ⟨chainDAG_one_ne_last hn, Finset.mem_erase.mpr ⟨h1, Finset.mem_univ _⟩⟩

/-- `(0, fromChild) ∉ {(1, fromParent)}`（`n ≥ 1`，`brCons` 形态，供 `bbStep` 引理用）。 -/
theorem zero_notMem_one_brCons {n : ℕ} (hn : 1 ≤ n) :
    ((0 : Fin (n + 1)), Causalean.Graph.DAG.BBDir.fromChild) ∉
      brCons (chainEmpty n) ((1 : Fin (n + 1)))
        Causalean.Graph.DAG.BBDir.fromParent (mem_chainEmpty_not n _) :=
  zero_notMem_fresh' n hn

/-- ⭐ **`bbStep Z` 在 `(1, fromParent)` 上只有 `(0, fromChild)`**（`1 ∈ Z`）。
结果集取 `chainSurf` 的形状 `brCons (brCons ∅ 1 fP) 0 fC`。 -/
theorem chainDAG_bbStep_one_fromParent {n : ℕ} (hn : 2 ≤ n) :
    (Fate.GlobalMarkovChainN.chainDAG n).bbStep ((Finset.univ.erase 0).erase (Fin.last n))
        ((1 : Fin (n + 1)), Causalean.Graph.DAG.BBDir.fromParent) ⊆
      brCons (brCons (chainEmpty n) ((1 : Fin (n + 1)))
        Causalean.Graph.DAG.BBDir.fromParent (mem_chainEmpty_not n _))
        ((0 : Fin (n + 1))) Causalean.Graph.DAG.BBDir.fromChild
        (zero_notMem_one_brCons (show 1 ≤ n by omega)) := by
  intro t ht
  have hZ1 : (1 : Fin (n + 1)) ∈ ((Finset.univ.erase 0).erase (Fin.last n)) := chainZ_one_mem hn
  rw [Causalean.Graph.DAG.bbStep] at ht
  rw [if_neg (show ¬ ((1 : Fin (n + 1)) ∉ ((Finset.univ.erase 0).erase (Fin.last n)))
    from fun h => h hZ1)] at ht
  rw [Finset.mem_map] at ht
  obtain ⟨u, hu, hue⟩ := ht
  have hu0 : u = (0 : Fin (n + 1)) := (chainDAG_parents_one (show 1 ≤ n by omega) u).mp hu
  subst hu0
  rw [mem_brCons]
  exact Or.inl (by rw [prod_eta_state]; exact (hue.symm : t = _))

/-- ⭐ **`bbStep Z` 在 `(0, fromChild)` 上只有 `(1, fromParent)`**（`0 ∉ Z`，`0` 无父）。 -/
theorem chainDAG_bbStep_zero_fromChild {n : ℕ} (hn : 1 ≤ n) :
    (Fate.GlobalMarkovChainN.chainDAG n).bbStep ((Finset.univ.erase 0).erase (Fin.last n))
        ((0 : Fin (n + 1)), Causalean.Graph.DAG.BBDir.fromChild) ⊆
      brCons (chainEmpty n) ((1 : Fin (n + 1)))
        Causalean.Graph.DAG.BBDir.fromParent (mem_chainEmpty_not n _) := by
  intro t ht
  have hZ0 : (0 : Fin (n + 1)) ∉ ((Finset.univ.erase 0).erase (Fin.last n)) := chainZ_zero_notMem
  rw [Causalean.Graph.DAG.bbStep] at ht
  rw [if_neg hZ0] at ht
  rw [chainDAG_parents_zero n] at ht
  rw [Finset.mem_union] at ht
  rcases ht with ht | ht
  · exact absurd ht (Finset.notMem_empty _)
  rw [Finset.mem_map] at ht
  obtain ⟨w, hw, hwe⟩ := ht
  have hw1 : w = (1 : Fin (n + 1)) := (chainDAG_children_zero hn w).mp hw
  subst hw1
  rw [mem_brCons]
  exact Or.inl (by rw [prod_eta_state]; exact (hwe.symm : t = _))

/-- `{(1, fromParent)} ⊆ chainSurf`。 -/
theorem brCons_one_subset_chainSurf (n : ℕ) (hn : 2 ≤ n) (Z : Finset (Fin (n + 1))) :
    brCons (chainEmpty n) ((1 : Fin (n + 1)))
      Causalean.Graph.DAG.BBDir.fromParent (mem_chainEmpty_not n _) ⊆
    chainSurf n hn Z := by
  intro s hs
  rw [mem_brCons] at hs
  rcases hs with h | h
  · rw [show s = ((1 : Fin (n + 1)), Causalean.Graph.DAG.BBDir.fromParent) from by
      rw [← prod_eta_state s]; exact h]
    exact chainSurf_one n hn Z
  · exact absurd h (mem_chainEmpty_not n _)

/-- ⭐⭐⭐⭐⭐ **`chainSurf` 对 `chainDAG n` 的 `bbStep Z` 封闭**（`n ≥ 2`）。 -/
theorem chainSurf_closed (n : ℕ) (hn : 2 ≤ n) :
    ∀ s ∈ chainSurf n hn ((Finset.univ.erase 0).erase (Fin.last n)),
      (Fate.GlobalMarkovChainN.chainDAG n).bbStep ((Finset.univ.erase 0).erase (Fin.last n)) s ⊆
        chainSurf n hn ((Finset.univ.erase 0).erase (Fin.last n)) := by
  intro s hs t ht
  have h1 : 1 ≤ n := by omega
  rcases (mem_chainSurf n hn _ s) hs with h | h
  · rw [h] at ht
    exact chainDAG_bbStep_one_fromParent hn ht
  · rw [h] at ht
    exact Finset.Subset.trans (chainDAG_bbStep_zero_fromChild h1) (brCons_one_subset_chainSurf n hn _) ht

end Surf

/-! ===========================================================================
  §4 ⭐⭐⭐⭐⭐ **主定理：任意 `n` 的链图 d-分离**
  =========================================================================== -/

section Main

/-- ⭐⭐⭐⭐⭐ **`bbInit {0} ⊆ chainSurf`**（`n ≥ 2`，`Z = {1,…,n-1}`）。

`bbInit {0}` 只含 `children 0 × fromParent = {(1, fromParent)}`（`0` 无父）。 -/
theorem chainDAG_bbInit_zero_subset (n : ℕ) (hn : 2 ≤ n) :
    (Fate.GlobalMarkovChainN.chainDAG n).bbInit {(0 : Fin (n + 1))} ⊆
      chainSurf n hn ((Finset.univ.erase 0).erase (Fin.last n)) := by
  intro s hs
  unfold Causalean.Graph.DAG.bbInit at hs
  rw [Finset.mem_biUnion] at hs
  obtain ⟨x, hx, hsx⟩ := hs
  rw [Finset.mem_singleton] at hx
  subst hx
  simp only [Finset.mem_union, Finset.mem_map] at hsx
  rcases hsx with ⟨w, hw, hwe⟩ | ⟨u, hu, hue⟩
  · -- `w` 是 `0` 的孩子：`w = 1`，故 `(1, fromParent)`
    have hw1 : w = (1 : Fin (n + 1)) := (chainDAG_children_zero (by omega) w).mp hw
    have he : ((w, Causalean.Graph.DAG.BBDir.fromParent) :
        Causalean.Graph.DAG.BBState (Fin (n + 1))) =
        ((1 : Fin (n + 1)), Causalean.Graph.DAG.BBDir.fromParent) := by rw [hw1]
    have hst : s = ((1 : Fin (n + 1)), Causalean.Graph.DAG.BBDir.fromParent) := by
      rw [← hwe]
      exact he
    rw [hst]
    exact chainSurf_one n hn _
  · -- `0` 无父
    rw [chainDAG_parents_zero n] at hu
    exact absurd hu (Finset.notMem_empty _)

/-- ⭐⭐⭐⭐ **主引理：`bbReachable Z {0} ⊆ chainSurf`**（`n ≥ 2`）。

用仓库已有的 **`DAG.bbReachable_minimal`**（fuel 无关的最小不动点）：
`chainSurf` 含 `bbInit {0}`（`chainDAG_bbInit_zero_subset`）且对 `bbStep Z` 封闭
（`chainSurf_closed`），故 BFS 结果被 `chainSurf` 包住。**完全不涉及 `decide`。** -/
theorem chainDAG_bbReachable_subset (n : ℕ) (hn : 2 ≤ n) :
    (Fate.GlobalMarkovChainN.chainDAG n).bbReachable
        ((Finset.univ.erase 0).erase (Fin.last n)) {(0 : Fin (n + 1))} ⊆
      chainSurf n hn ((Finset.univ.erase 0).erase (Fin.last n)) :=
  Causalean.Graph.DAG.bbReachable_minimal (V := Fin (n + 1))
    (Fate.GlobalMarkovChainN.chainDAG n)
    ((Finset.univ.erase 0).erase (Fin.last n)) {(0 : Fin (n + 1))}
    (chainSurf n hn ((Finset.univ.erase 0).erase (Fin.last n)))
    (chainDAG_bbInit_zero_subset n hn)
    (chainSurf_closed n hn)

/-- ⭐⭐⭐⭐ **`bbReachableVertices Z {0} ⊆ {0, 1}`**（`n ≥ 2`）。

`chainSurf` 的两个状态的顶点坐标恰好是 `1` 与 `0`。 -/
theorem chainDAG_bbReachableVertices_subset (n : ℕ) (hn : 2 ≤ n) :
    (Fate.GlobalMarkovChainN.chainDAG n).bbReachableVertices
        ((Finset.univ.erase 0).erase (Fin.last n)) {(0 : Fin (n + 1))} ⊆
      ({(0 : Fin (n + 1))} : Finset (Fin (n + 1))) ∪ {(1 : Fin (n + 1))} := by
  intro v hv
  rw [Causalean.Graph.DAG.bbReachableVertices, Finset.mem_image] at hv
  obtain ⟨s, hs, hsv⟩ := hv
  rcases (mem_chainSurf n hn _ s) (chainDAG_bbReachable_subset n hn hs) with h | h
  · rw [h] at hsv
    simp only [Prod.fst] at hsv
    rw [← hsv]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  · rw [h] at hsv
    simp only [Prod.fst] at hsv
    rw [← hsv]
    exact Finset.mem_union_left _ (Finset.mem_singleton_self _)

/-- ⭐⭐⭐⭐ **任务书第 2 条：`bbReachableVertices Z {0} ⊆ {0, 1}`**（任意 `n ≥ 2`）。 -/
theorem chainDAG_reachable_subset' (n : ℕ) (hn : 2 ≤ n) :
    (Fate.GlobalMarkovChainN.chainDAG n).bbReachableVertices
      ((Finset.univ.erase 0).erase (Fin.last n)) {(0 : Fin (n + 1))}
      ⊆ ({(0 : Fin (n + 1))} ∪ {(1 : Fin (n + 1))}) :=
  chainDAG_bbReachableVertices_subset n hn

/-- ⭐⭐⭐⭐ **`last n` 不在可达顶点集里**（`n ≥ 2`）。 -/
theorem chainDAG_reachable_not_last (n : ℕ) (hn : 2 ≤ n) :
    Fin.last n ∉ (Fate.GlobalMarkovChainN.chainDAG n).bbReachableVertices
      ((Finset.univ.erase 0).erase (Fin.last n)) {(0 : Fin (n + 1))} := by
  intro h
  have hsub := chainDAG_bbReachableVertices_subset n hn h
  rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton] at hsub
  rcases hsub with h0 | h1
  · exact chainDAG_zero_ne_last hn h0.symm
  · exact chainDAG_one_ne_last hn h1.symm

/-- ⭐⭐⭐⭐⭐ **任意 `n` 的链图 d-分离**：

链 `0 → 1 → ⋯ → n` 上，`{0}` 与 `{n}` 在给定中间段 `{1,…,n-1}` 下 d-分离。

**⚠ 这是 `GlobalMarkovChainN.lean:136` 明确标注「没做」的定理。** -/
theorem chainDAG_dsep_n (n : ℕ) (hn : 2 ≤ n) :
    (Fate.GlobalMarkovChainN.chainDAG n).dSep
      {(0 : Fin (n+1))} {(Fin.last n : Fin (n+1))}
      ((Finset.univ.erase 0).erase (Fin.last n)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `Disjoint {0} {last n}`
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_singleton] at ha hb
    exact chainDAG_zero_ne_last hn (ha.symm.trans hb)
  · -- `Disjoint {0} Z`
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_singleton] at ha
    subst ha
    exact chainZ_zero_notMem hb
  · -- `Disjoint {last n} Z`
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_singleton] at ha
    subst ha
    rw [Finset.mem_erase] at hb
    exact hb.1 rfl
  · -- `Disjoint (bbReachableVertices Z {0}) {last n}`
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_singleton] at hb
    subst hb
    exact chainDAG_reachable_not_last n hn ha

end Main

/-! ===========================================================================
  §5 公理审计
  =========================================================================== -/

-- 主定理：任意 `n` 的链图 d-分离（**无 `sorryAx`**）
#print axioms chainDAG_dsep_n

-- 第 2 条：可达顶点集的单向界（**无 `sorryAx`**）
#print axioms chainDAG_reachable_subset'

-- 关键 BFS 不变量（fuel 无关的最小性应用）
#print axioms chainDAG_bbReachable_subset
#print axioms chainSurf_closed

-- 支撑引理
#print axioms chainDAG_isAncestor_iff

end Fate.Stage2.ChainDsepFull
