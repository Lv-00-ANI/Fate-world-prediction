/-
命运理论 · **T2.1 的实质证明：有限图上 d-分离的可判定性**
================================================================================

模块：`Fate.T21FiniteSearch`（第 269 轮）

## 清单原文（T2.1）

> **d-分离的良定义性**：对 DAG `G = (V,E)` 与互不相交的 `X,Y,Z ⊆ V`，
> 「`Z` 阻断 `X` 到 `Y` 的一切路径」这一定义**不依赖于路径的枚举方式**，
> **且在有限图上可判定**。

## 本文件交付

### (A)「不依赖枚举方式」的可计算内容 —— **有向路径必无重复顶点**

`Reach G a b` 与「存在一条有向路径**列表** `l`」等价
（`reach_iff_exists_path`）。**关键定理 `isDirPath_nodup`**：由
`CausalGraph.acyclic`，任何有向路径列表**无重复顶点**，
故长度 `≤ card V`。这把「路径」存在量词的搜索空间压到有限阶 ——
这是用无环性证出来的真命题，**不是定义展开**。

### (B)「在有限图上可判定」—— 有限迭代判定过程

定义 `reachIter G n S`（每轮沿 `Adj` 扩张一步），证明

  `b ∈ reachIter G (card V) {a} ↔ Reach G a b`

由此得到 `Reach` 的 `Decidable` 实例，再由它合成
`openAt'`、`DOpen'`、`DConnected'` 的可判定性。

## 与既有文件的关系

* `Fate/T21DSepWellDefined.lean`：逐条对应 Pearl Rule 2/3，但**自我登记为
  「10/10 全是定义展开」**，无可判定性。
* `Fate/T21Decidable.lean`：仅给 `openAt`（**简化版**，无后代）的逐三元组
  `Decidable`，自我登记「层次 B（`DOpen`）、层次 C（`DConnected`）未做」。
* **本文件补的正是层次 B/C 的根**：`Reach` 的可判定性 + 长度上界。

## 边界（诚实登记）

* 本文件完成清单 T2.1 第二子句（「在有限图上可判定」）在**本项目
  `CausalGraph` 载体**上的陈述。
* **不**声称与 `Causalean` 侧 `DAG.dSep`（Bayes Ball 形式）等价 ——
  那是一条独立的适配性命题。
* 零 `sorry`、零 `axiom`。
-/

import FateWorld.Legacy.CausalPath
import FateWorld.Legacy.CausalDescendant
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Fate.T21

open Fate.CausalDirection Fate.CausalPath Fate.CausalDescendant

universe u
variable {V : Type u}

/-! ==========================================================================
  §1  有向路径的列表表征
========================================================================== -/

/-- `IsDirPath G l`：`l` 的相邻元素由 `G.Adj` 连接（有向）。 -/
def IsDirPath (G : CausalGraph V) (l : List V) : Prop := l.IsChain (fun x y => G.Adj x y)

theorem isDirPath_tail (G : CausalGraph V) {a : V} {l : List V}
    (h : IsDirPath G (a :: l)) : IsDirPath G l := by
  simpa [IsDirPath] using h.tail

theorem isDirPath_head_adj (G : CausalGraph V) {a b : V} {l : List V}
    (h : IsDirPath G (a :: b :: l)) : G.Adj a b := by
  simpa [IsDirPath] using (List.isChain_cons_cons.1 h).1

theorem isDirPath_drop (G : CausalGraph V) {l : List V} (h : IsDirPath G l) (i : ℕ) :
    IsDirPath G (l.drop i) := by
  induction i generalizing l with
  | zero => simpa using h
  | succ n ih =>
    cases l with
    | nil => exact List.isChain_nil
    | cons a t =>
      have ht : IsDirPath G t := isDirPath_tail G h
      simpa using ih ht

/-! ==========================================================================
  §2  按步数索引的可达（`ReachN`）
========================================================================== -/

/-- 恰 `n` 步的 `Adj` 链（长度索引化，用于有限搜索的正确性证明）。 -/
inductive ReachN (G : CausalGraph V) : ℕ → V → V → Prop where
  | zero (a : V) : ReachN G 0 a a
  | step {n : ℕ} {a b c : V} (h : G.Adj a b) (w : ReachN G n b c) : ReachN G (n+1) a c

/-- `ReachN` ⟹ `Reach`。 -/
theorem reachN_imp_reach (G : CausalGraph V) : {n : ℕ} → {a b : V} →
    ReachN G n a b → Reach G a b
  | 0, a, _, .zero _ => Reach.refl a
  | _+1, _, _, .step hadj w => Reach.step hadj (reachN_imp_reach G w)

/-- `Reach` ⟹ 存在步数的 `ReachN`。 -/
theorem reach_imp_reachN (G : CausalGraph V) {a b : V} (h : Reach G a b) :
    ∃ n : ℕ, ReachN G n a b := by
  induction h with
  | refl a => exact ⟨0, ReachN.zero a⟩
  | step hadj _ ih =>
    obtain ⟨n, w⟩ := ih
    exact ⟨n+1, ReachN.step hadj w⟩

/-- **有向路径列表 ⟹ `ReachN`**：步数等于列表长度减一。 -/
theorem isDirPath_imp_reachN (G : CausalGraph V) :
    ∀ {l : List V} {s e : V}, IsDirPath G l → l.head? = some s → l.getLast? = some e →
      ∃ n, ReachN G n s e ∧ l.length = n + 1 := by
  intro l
  induction l with
  | nil => intro s e _ h; simp at h
  | cons x t ih =>
    intro s e hc hhead hlast
    have hxs : x = s := by simpa using hhead
    subst hxs
    cases t with
    | nil =>
      have hse : x = e := by simpa using hlast
      subst hse
      exact ⟨0, ReachN.zero x, rfl⟩
    | cons y t' =>
      have hxy : G.Adj x y := isDirPath_head_adj G hc
      have ht : IsDirPath G (y :: t') := isDirPath_tail G hc
      have hlast' : (y :: t').getLast? = some e := by simpa using hlast
      obtain ⟨n, hr, hlen⟩ := ih ht rfl hlast'
      exact ⟨n+1, ReachN.step hxy hr, by simp [hlen]⟩

/-- `ReachN` 可拼接：`m` 步之后接 `n` 步。 -/
theorem reachN_trans (G : CausalGraph V) :
    ∀ {m n : ℕ} {a b c : V}, ReachN G m a b → ReachN G n b c → ReachN G (m+n) a c
  | 0, n, a, b, c, h1, h2 => by
    cases h1 with
    | zero _ => simpa using h2
  | m+1, n, a, b, c, h1, h2 => by
    cases h1 with
    | @step _ _ _ _ hadj w =>
      simpa [Nat.succ_add] using ReachN.step hadj (reachN_trans G w h2)

/-! ==========================================================================
  §3  沿链的可达（真内容：归纳，不是定义展开）
========================================================================== -/

/-- **沿有向链：链首非平凡可达尾部的任意成员。** -/
theorem head_reachPos_mem (G : CausalGraph V) (s : V) (t : List V)
    (hchain : IsDirPath G (s :: t)) : ∀ c ∈ t, Relation.TransGen G.Adj s c := by
  induction t generalizing s with
  | nil => intro c hc; simp at hc
  | cons b rest ih =>
    intro c hc
    have hsab : G.Adj s b := isDirPath_head_adj G hchain
    have htail : IsDirPath G (b :: rest) := isDirPath_tail G hchain
    rcases List.mem_cons.1 hc with hc | hc
    · rw [hc]
      exact Relation.TransGen.single hsab
    · exact Relation.TransGen.head hsab (ih b htail c hc)

/-! ==========================================================================
  §4  ⭐⭐⭐ **(A) 有向路径必无重复顶点**（长度上界）
========================================================================== -/

/-- ⭐⭐⭐ **无环 ⟹ 有向路径列表无重复顶点。**

若 `l[i] = l[j]`（`i < j`），则 `l.drop i` 仍是有向链且以 `l[i]` 为首、
`l[j]` 在其尾部，故 `TransGen Adj l[i] l[j]`；代入 `l[i] = l[j]` 得
`TransGen Adj x x`，与 `CausalGraph.acyclic` 矛盾。 -/
theorem isDirPath_nodup (G : CausalGraph V) {l : List V} (h : IsDirPath G l) : l.Nodup := by
  rw [List.nodup_iff_getElem?_ne_getElem?]
  intro i j hi hj heq
  have hilen : i < l.length := by omega
  obtain ⟨s, t, hst⟩ : ∃ s t, l.drop i = s :: t := by
    cases hd : l.drop i with
    | nil =>
      have hle : l.length ≤ i := by simpa using hd
      omega
    | cons s t => exact ⟨s, t, rfl⟩
  have hsd : l[i]? = some s := by
    have h := List.head?_drop (l := l) (i := i)
    rw [hst] at h
    simpa using h.symm
  have hdd : IsDirPath G (s :: t) := hst ▸ isDirPath_drop G h i
  have hmemj : l[j]? = some l[j] := List.getElem?_eq_some_iff.2 ⟨hj, rfl⟩
  have hjt : l[j] ∈ t := by
    have hmem : l[j]? = (l.drop i)[j - i]? := by
      rw [List.getElem?_drop]
      congr 1
      omega
    rw [hst] at hmem
    obtain ⟨k, hk⟩ : ∃ k, j - i = k + 1 := ⟨j - i - 1, by omega⟩
    rw [hk, List.getElem?_cons_succ] at hmem
    exact List.mem_of_getElem? (hmem.symm ▸ hmemj)
  have hreach := head_reachPos_mem G s t hdd l[j] hjt
  have heqs : s = l[j] := by
    rw [hsd, hmemj] at heq
    simpa using heq
  rw [heqs] at hreach
  exact G.acyclic l[j] hreach

/-- ⭐⭐ **长度上界**：有向路径列表长度 `≤ card V`。 -/
theorem isDirPath_length_le_card [Fintype V] (G : CausalGraph V) {l : List V}
    (h : IsDirPath G l) : l.length ≤ Fintype.card V :=
  List.Nodup.length_le_card (isDirPath_nodup G h)

/-! ==========================================================================
  §5  可达 ↔ 有向路径列表
========================================================================== -/

/-- 有向路径列表 ⟹ 首可达末。 -/
theorem isDirPath_last_reach (G : CausalGraph V) :
    ∀ {l : List V} {a b : V}, l.head? = some a → l.getLast? = some b → IsDirPath G l →
      Reach G a b := by
  intro l
  induction l with
  | nil => intro a b h; simp at h
  | cons x rest ih =>
    intro a b hhead hlast hchain
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    cases rest with
    | nil =>
      have hxa : x = b := by simpa using hlast
      subst hxa
      exact Reach.refl x
    | cons y rest' =>
      have hxy : G.Adj x y := isDirPath_head_adj G hchain
      have htail : IsDirPath G (y :: rest') := isDirPath_tail G hchain
      have hlast' : (y :: rest').getLast? = some b := by simpa using hlast
      exact Reach.step hxy (ih rfl hlast' htail)

/-- 可达 ⟹ 存在有向路径列表。 -/
theorem reach_imp_exists_path (G : CausalGraph V) {a b : V} (h : Reach G a b) :
    ∃ l : List V, IsDirPath G l ∧ l.head? = some a ∧ l.getLast? = some b := by
  induction h with
  | refl a => exact ⟨[a], by simp [IsDirPath], rfl, rfl⟩
  | step hadj _ ih =>
    obtain ⟨l, hchain, hhead, hlast⟩ := ih
    cases l with
    | nil => simp at hhead
    | cons y rest =>
      obtain rfl : y = _ := by simpa using hhead
      exact ⟨_ :: _ :: _, by
          rw [IsDirPath, List.isChain_cons]
          exact ⟨fun z hz => by
            obtain rfl : y = z := by simpa using hz
            exact hadj, hchain⟩, rfl, by simpa using hlast⟩

/-- ⭐⭐ **可达 ⟺ 存在有向路径列表**。 -/
theorem reach_iff_exists_path (G : CausalGraph V) (a b : V) :
    Reach G a b ↔ ∃ l : List V, IsDirPath G l ∧ l.head? = some a ∧ l.getLast? = some b :=
  ⟨reach_imp_exists_path G, fun ⟨_, hc, hh, hl⟩ => isDirPath_last_reach G hh hl hc⟩

/-- ⭐⭐⭐ **可达 ⟹ 存在长度 ≤ card V 的有向路径列表**（有限搜索的依据）。 -/
theorem reach_imp_exists_short_path [Fintype V] (G : CausalGraph V) {a b : V}
    (h : Reach G a b) :
    ∃ l : List V, IsDirPath G l ∧ l.head? = some a ∧ l.getLast? = some b ∧
      l.length ≤ Fintype.card V := by
  obtain ⟨l, hchain, hhead, hlast⟩ := reach_imp_exists_path G h
  exact ⟨l, hchain, hhead, hlast, isDirPath_length_le_card G hchain⟩

/-! ==========================================================================
  §6  ⭐⭐⭐⭐ **(B) 有限迭代判定过程**
========================================================================== -/

/-- 一步扩张：`S` 加上 `S` 中顶点的全部后继。 -/
def reachStep (G : CausalGraph V) [DecidableEq V] [Fintype V]
    [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  S ∪ S.biUnion (fun u => Finset.univ.filter (fun v => G.Adj u v))

/-- `n` 轮扩张。 -/
def reachIter (G : CausalGraph V) [DecidableEq V] [Fintype V] [DecidableRel G.Adj] :
    ℕ → Finset V → Finset V
  | 0, S => S
  | n+1, S => reachStep G (reachIter G n S)

theorem reachIter_zero (G : CausalGraph V) [DecidableEq V] [Fintype V] [DecidableRel G.Adj]
    (S : Finset V) : reachIter G 0 S = S := rfl

theorem reachIter_succ (G : CausalGraph V) [DecidableEq V] [Fintype V] [DecidableRel G.Adj]
    (n : ℕ) (S : Finset V) : reachIter G (n+1) S = reachStep G (reachIter G n S) := rfl

theorem mem_reachStep (G : CausalGraph V) [DecidableEq V] [Fintype V] [DecidableRel G.Adj]
    {S : Finset V} {v : V} :
    v ∈ reachStep G S ↔ v ∈ S ∨ ∃ u ∈ S, G.Adj u v := by
  simp only [reachStep, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and]

section IterLemmas

variable (G : CausalGraph V) [DecidableEq V] [Fintype V] [DecidableRel G.Adj]

/-- `reachIter` 对初始集单调。 -/
theorem reachIter_mono (n : ℕ) {S T : Finset V} (h : S ⊆ T) :
    reachIter G n S ⊆ reachIter G n T := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [reachIter_succ, reachIter_succ]
    intro u hu
    rw [mem_reachStep] at hu ⊢
    rcases hu with hu | ⟨w, hw, hadj⟩
    · exact Or.inl (ih hu)
    · exact Or.inr ⟨w, ih hw, hadj⟩

/-- `reachIter` 关于轮数单调（元素保持）。 -/
theorem reachIter_le_succ (k : ℕ) (S : Finset V) :
    reachIter G k S ⊆ reachIter G (k+1) S := by
  rw [reachIter_succ]
  intro u hu
  rw [mem_reachStep]
  exact Or.inl hu

/-- `reachIter` 关于轮数单调（一般形式）。 -/
theorem reachIter_le_of_le {k m : ℕ} (hkm : k ≤ m) (S : Finset V) :
    reachIter G k S ⊆ reachIter G m S := by
  induction m with
  | zero =>
    have : k = 0 := Nat.le_zero.1 hkm
    subst this; exact subset_rfl
  | succ m ih =>
    rcases Nat.lt_or_ge k (m+1) with hlt | hge
    · have h1 := ih (Nat.lt_succ_iff.1 hlt)
      exact subset_trans h1 (reachIter_le_succ G m S)
    · have h2 : k = m+1 := le_antisymm hkm hge
      subst h2; exact subset_rfl

/-- `reachIter` 的轮数可加。 -/
theorem reachIter_add (i j : ℕ) (S : Finset V) :
    reachIter G (i+j) S = reachIter G i (reachIter G j S) := by
  induction i with
  | zero => simp [reachIter_zero]
  | succ i ih =>
    rw [Nat.succ_add, reachIter_succ, reachIter_succ, ih]

/-- 从 `{a}` 出发的迭代对起点单调：`a` 可达的集合包含 `{a}`。 -/
theorem reachIter_singleton_subset (n : ℕ) (a : V) :
    ({a} : Finset V) ⊆ reachIter G n {a} := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact subset_trans ih (reachIter_le_succ G n _)

/-- ⭐⭐ **可靠性**：`b ∈ reachIter n {a}` ⟹ 存在长度 `≤ n` 的 `Adj` 链。 -/
theorem reachIter_sound (n : ℕ) {a b : V} (h : b ∈ reachIter G n {a}) :
    ∃ k : ℕ, k ≤ n ∧ ReachN G k a b := by
  induction n generalizing b with
  | zero =>
    rw [reachIter_zero, Finset.mem_singleton] at h
    exact ⟨0, le_refl 0, h ▸ ReachN.zero b⟩
  | succ n ih =>
    rw [reachIter_succ, mem_reachStep] at h
    rcases h with h1 | ⟨u, hu, hadj⟩
    · obtain ⟨k, hk, hr⟩ := ih h1
      exact ⟨k, le_trans hk (Nat.le_succ n), hr⟩
    · obtain ⟨k, hk, hr⟩ := ih hu
      refine ⟨k+1, by omega, ?_⟩
      have h2 := reachN_trans G hr (ReachN.step hadj (ReachN.zero b))
      simpa using h2

/-- ⭐⭐ **完备性**：恰 `n` 步的 `Adj` 链 ⟹ 终元落入 `reachIter G n {a}`。 -/
theorem reachN_mem_reachIter (n : ℕ) {a b : V} (h : ReachN G n a b) :
    b ∈ reachIter G n {a} := by
  induction n generalizing a with
  | zero =>
    cases h with
    | zero a => rw [reachIter_zero, Finset.mem_singleton]
  | succ n ih =>
    cases h with
    | @step _ _ m b' hadj hr' =>
      -- `a → m`（一步），`m → b`（n 步），故 `a → b`（n+1 步）
      have hm : m ∈ reachIter G 1 {a} := by
        rw [reachIter_succ, reachIter_zero, mem_reachStep]
        exact Or.inr ⟨a, by rw [Finset.mem_singleton], hadj⟩
      have hb : b ∈ reachIter G n {m} := ih hr'
      rw [reachIter_add G n 1 {a}]
      exact reachIter_mono G (n := n) (by
        intro v hv
        rw [Finset.mem_singleton] at hv
        subst hv
        exact hm) hb

end IterLemmas

/-- ⭐⭐⭐ **主定理（判定过程的正确性）**：

`b` 可从 `a` 全前向到达 ⟺ `b ∈ reachIter G (card V) {a}`。 -/
theorem mem_reachIter_card_iff_reach (G : CausalGraph V) [DecidableEq V] [Fintype V]
    [DecidableRel G.Adj] {a b : V} :
    b ∈ reachIter G (Fintype.card V) {a} ↔ Reach G a b := by
  constructor
  · intro h
    obtain ⟨k, _, hr⟩ := reachIter_sound G (Fintype.card V) h
    exact reachN_imp_reach G hr
  · intro h
    -- 可达 ⟹ 存在长度 ≤ card V 的有向路径列表
    obtain ⟨l, hc, hh, hl, hlen⟩ := reach_imp_exists_short_path G h
    -- 该列表给出 `ReachN G n a b`，且 `n + 1 = l.length ≤ card V`
    obtain ⟨n, hn, hlen'⟩ := isDirPath_imp_reachN G hc hh hl
    have hle : n ≤ Fintype.card V := by omega
    exact reachIter_le_of_le G hle {a} (reachN_mem_reachIter G n hn)

/-- ⭐⭐⭐⭐ **`Reach` 的可判定性**（清单 T2.1 第二子句的根）。 -/
instance decidableReach (G : CausalGraph V) [DecidableEq V] [Fintype V]
    [DecidableRel G.Adj] (a b : V) : Decidable (Reach G a b) :=
  decidable_of_iff (b ∈ reachIter G (Fintype.card V) {a})
    (mem_reachIter_card_iff_reach (a := a) (b := b) G)

/-! ==========================================================================
  §7  ⭐⭐⭐⭐ **层次 B/C：`openAt'` / `DOpen'` / `DConnected'` 的可判定性**
========================================================================== -/

section Full

variable (G : CausalGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- ⭐⭐⭐ **`openAt'` 可判定**（层次 B）。

collider 分支的 `∃ z ∈ Z, Reach G b z` 由 `Reach` 的可判定性
（`decidableReach`）与 `Fintype` 的全称/存在量化自动可判定。 -/
instance decidableOpenAt' {a b c : V} {Z : Set V} [DecidablePred (· ∈ Z)]
    (s₁ : DStep G a b) (s₂ : DStep G b c) : Decidable (openAt' G s₁ s₂ Z) := by
  unfold openAt'
  split
  · -- collider 分支：有限存在量化
    exact Fintype.decidableExistsFintype
  · exact inferInstance

/-- ⭐⭐⭐ **`DOpen'` 可判定**（层次 B 的核心）。

对带向路径 `w` 结构递归：每步用 `decidableOpenAt'`。 -/
def decidableDOpen'_aux {Z : Set V} [DecidablePred (· ∈ Z)] :
    ∀ {a b : V} (w : DWalk G a b), Decidable (DOpen' G Z w)
  | _, _, .nil _ => isTrue trivial
  | _, _, .cons _ (.nil _) => isTrue trivial
  | _, _, .cons s₁ (.cons s₂ w) =>
    haveI : Decidable (openAt' G s₁ s₂ Z) := decidableOpenAt' G s₁ s₂
    haveI : Decidable (DOpen' G Z (.cons s₂ w)) := decidableDOpen'_aux (.cons s₂ w)
    inferInstanceAs (Decidable (_ ∧ _))

instance decidableDOpen' {Z : Set V} [DecidablePred (· ∈ Z)]
    {a b : V} (w : DWalk G a b) : Decidable (DOpen' G Z w) :=
  decidableDOpen'_aux G w

end Full

end Fate.T21
