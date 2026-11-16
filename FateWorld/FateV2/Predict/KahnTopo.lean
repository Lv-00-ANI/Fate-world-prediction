/-
-/

module
public import FateWorld.FateV2.Modeling.CausDAG
public import Mathlib.Data.Fintype.Pigeonhole

/-!
  # Predict · KahnTopo

  ## 迁移登记
  - 来源：`FateWorld/Legacy/KahnTopo.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausDAG
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! # Kahn's algorithm: a constructive topological order of a finite DAG

`Fate/DAGFactorizationGeneral.lean` provides a topological *numbering* `topoEnum : V ≃ Fin (card V)`
built from `DAG.topoOrder v = ancestorRank v * |V| + enum v`, where the tie-breaking `enum`
is a bare `Classical.choose`-style enumeration of an arbitrary finite type.  That order is used
purely for its ordering properties; nothing about it reflects the *structure* of the algorithm
that would actually build a topological order.

This file replaces that with **Kahn's algorithm** in its textbook form: repeatedly pick a vertex
with no incoming edge among the vertices not yet output, append it, and delete it.  The engine of
the whole file is the finite-DAG **local source lemma** (`local_source`): every nonempty vertex
subset of a DAG has an element with no in-edge from within the subset.  This is the `Finset` /
`Fintype` version of `exists_min` that the COMPLEX-1 §5 item 11 asks for — it extracts a
**source**, not a global linear order.

## What is proved

Given `G : DAG V` with `[Fintype V] [DecidableEq V]`:

* `topoList_nodup`      — the Kahn order has no repeats;
* `topoList_complete`   — its underlying `Finset` is `univ` (all vertices appear);
* `topoList_length`     — its length is `card V`; with the previous two, `topoList G` is a
                          **permutation** of the vertex set;
* `topoList_topo`       — **topological property**: along every edge `u → w` the tail `u`
                          occurs strictly before the head `w` (`idxOf u < idxOf w`);
* `topoList_ancestor`   — the same for *paths*: any strict ancestor occurs strictly earlier.

## Honest scope / limitations

* `pickMin` is still `noncomputable`: choosing *which* local source to remove needs
  `Classical.choose` on an arbitrary `Fintype` (there is no computable enumeration of a bare
  finite type, exactly as for `CausDAG.topoOrder`).  What changes is the **object being chosen**:
  it is a genuine in-degree-zero vertex of the remaining set (a Kahn step), not an arbitrary
  tie-break in a linear order.  The *loop structure* (delete-one-source-per-round, `card V`
  rounds) is fully explicit and finite.
* This file is self-contained over `CausDAG`; it does not modify any existing module.

## References

* A. B. Kahn, *Topological sorting of large networks*, CACM 5(11), 1962.
-/

@[expose] public section

namespace FateV2.Predict.Causalean.Graph

open FateV2.Modeling
variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ### The local-source lemma -/

/-- A "parent picker" that stays inside `S` while any in-edge comes from `S`.  Used only
internally to turn a hypothetical counterexample into an infinite descent. -/
noncomputable def stepOf (G : DAG V) (S : Finset V) (_hS : ∀ v ∈ S, ∃ u, G.edge u v ∧ u ∈ S)
    (v : V) : V :=
  if h : ∃ u, G.edge u v ∧ u ∈ S then Classical.choose h else v

theorem stepOf_mem (G : DAG V) (S : Finset V) (hS : ∀ v ∈ S, ∃ u, G.edge u v ∧ u ∈ S)
    {v : V} (hv : v ∈ S) : stepOf G S hS v ∈ S := by
  unfold stepOf; rw [dif_pos (hS v hv)]
  exact (Classical.choose_spec (hS v hv)).2

theorem stepOf_edge (G : DAG V) (S : Finset V) (hS : ∀ v ∈ S, ∃ u, G.edge u v ∧ u ∈ S)
    {v : V} (hv : v ∈ S) : G.edge (stepOf G S hS v) v := by
  unfold stepOf; rw [dif_pos (hS v hv)]
  exact (Classical.choose_spec (hS v hv)).1

theorem iterate_mem (G : DAG V) (S : Finset V) (hS : ∀ v ∈ S, ∃ u, G.edge u v ∧ u ∈ S)
    {v : V} (hv : v ∈ S) (k : ℕ) : (stepOf G S hS)^[k] v ∈ S := by
  induction k with
  | zero => simpa using hv
  | succ k ih => rw [Function.iterate_succ_apply']; exact stepOf_mem G S hS ih

/-- A positive iterate of the parent picker is a strict ancestor (via `TransGen`). -/
theorem transGen_iterate (G : DAG V) (S : Finset V)
    (hS : ∀ v ∈ S, ∃ u, G.edge u v ∧ u ∈ S) {v : V} (hv : v ∈ S) :
    ∀ k, 0 < k → Relation.TransGen G.edge ((stepOf G S hS)^[k] v) v := by
  intro k
  induction k with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ k ih =>
    intro _
    rw [Function.iterate_succ_apply']
    cases k with
    | zero =>
      simp only [Function.iterate_zero, id]
      exact Relation.TransGen.single (stepOf_edge G S hS hv)
    | succ k =>
      have h1 : (stepOf G S hS)^[k+1] v ∈ S := iterate_mem G S hS hv (k+1)
      exact Relation.TransGen.head (stepOf_edge G S hS h1) (ih (Nat.succ_pos k))

/-- **Local source lemma.** Every nonempty vertex subset of a DAG has an element with no
incoming edge from within the subset.  This is the graph-theoretic `exists_min`; the proof is
a pigeonhole argument: if every vertex of `S` had a parent in `S`, iterating a parent picker
yields a repeat, hence a directed cycle, contradicting acyclicity. -/
theorem local_source (G : DAG V) (S : Finset V) (hS : S.Nonempty) :
    ∃ v ∈ S, ∀ u, G.edge u v → u ∉ S := by
  by_contra h
  push Not at h
  obtain ⟨v0, hv0⟩ := hS
  have hS' : ∀ v ∈ S, ∃ u, G.edge u v ∧ u ∈ S := by
    intro v hv; obtain ⟨u, he, hu⟩ := h v hv; exact ⟨u, he, hu⟩
  set f := stepOf G S hS' with hfdef
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun n : Fin (Fintype.card V + 1) => f^[n.val] v0) (by simp)
  have key : ∀ a b : ℕ, a < b → f^[b] v0 = f^[a] v0 → False := by
    intro a b hab heqab
    have hmem_i : f^[a] v0 ∈ S := iterate_mem G S hS' hv0 a
    have htg : Relation.TransGen G.edge (f^[b-a] (f^[a] v0)) (f^[a] v0) :=
      transGen_iterate G S hS' hmem_i (b-a) (Nat.sub_pos_of_lt hab)
    have hsplit : f^[b-a] (f^[a] v0) = f^[b] v0 := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt hab)]
    rw [hsplit, heqab] at htg
    exact G.acyclic (f^[a] v0) htg
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i.val j.val hlt heq.symm
  · exact key j.val i.val hlt heq

/-! ### Kahn's algorithm -/

/-- Pick a local source of `S` (a vertex with no in-edge from `S`).  This is the Kahn step;
`Classical.choose` selects one such source, guaranteed to exist by `local_source`. -/
noncomputable def pickMin (G : DAG V) (S : Finset V) (hS : S.Nonempty) : V :=
  Classical.choose (local_source G S hS)

theorem pickMin_mem (G : DAG V) (S : Finset V) (hS : S.Nonempty) : pickMin G S hS ∈ S :=
  (Classical.choose_spec (local_source G S hS)).1

theorem pickMin_src (G : DAG V) (S : Finset V) (hS : S.Nonempty) :
    ∀ u, G.edge u (pickMin G S hS) → u ∉ S :=
  (Classical.choose_spec (local_source G S hS)).2

/-- **Kahn's algorithm, auxiliary loop.** Each round, if vertices remain, take a local source
of the remaining set, append it to the output, and delete it.  `n` is a fuel bound. -/
noncomputable def kahnAux (G : DAG V) : ℕ → Finset V → List V → List V
  | 0, _, acc => acc
  | n+1, S, acc =>
    if h : S.Nonempty then
      kahnAux G n (S.erase (pickMin G S h)) (acc ++ [pickMin G S h])
    else acc

/-- **Cover invariant.** Running `n` rounds from `(S, acc)` (with `acc` disjoint from `S` and
`n ≥ card S`) leaves every vertex accounted for: the output's `Finset` is `acc ∪ S`. -/
theorem kahnAux_cover (G : DAG V) (n : ℕ) :
    ∀ (S : Finset V) (acc : List V),
      (∀ x ∈ acc, x ∉ S) → S.card ≤ n →
      (kahnAux G n S acc).toFinset = acc.toFinset ∪ S := by
  induction n with
  | zero =>
    intro S acc _ hcard
    have hSe : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hSe
    simp [kahnAux]
  | succ n ih =>
    intro S acc hdisj hcard
    rw [kahnAux]
    by_cases h : S.Nonempty
    · rw [dif_pos h]
      set v := pickMin G S h with hv
      have hvS : v ∈ S := pickMin_mem G S h
      have hcard' : (S.erase v).card ≤ n := by
        rw [Finset.card_erase_of_mem hvS]; omega
      have hdisj' : ∀ x ∈ acc ++ [v], x ∉ S.erase v := by
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact fun hh => hdisj x hx (Finset.mem_of_mem_erase hh)
        · exact Finset.notMem_erase v S
      have hmain := ih (S.erase v) (acc ++ [v]) hdisj' hcard'
      rw [hmain]
      have hvv : ([v] : List V).toFinset = ({v} : Finset V) := by simp
      have hins : ({v} : Finset V) ∪ S.erase v = S := by
        rw [Finset.singleton_union, Finset.insert_erase hvS]
      rw [List.toFinset_append, hvv, Finset.union_assoc, hins]
    · rw [dif_neg h]
      rw [Finset.not_nonempty_iff_eq_empty] at h
      subst h
      simp

/-- **Full invariant.** Alongside coverage, the accumulated list stays `Nodup` and, crucially,
is a *topological prefix*: every in-edge into an output vertex has its tail also output and
strictly earlier.  This is what makes the final list a topological order. -/
theorem kahnAux_spec (G : DAG V) (n : ℕ) :
    ∀ (S : Finset V) (acc : List V), acc.Nodup →
      (∀ x ∈ acc, x ∉ S) → acc.toFinset ∪ S = Finset.univ →
      (∀ w ∈ acc, ∀ u, G.edge u w → u ∈ acc ∧ acc.idxOf u < acc.idxOf w) →
      S.card ≤ n →
      (kahnAux G n S acc).Nodup ∧
      (kahnAux G n S acc).toFinset = Finset.univ ∧
      (∀ w ∈ kahnAux G n S acc, ∀ u, G.edge u w →
        u ∈ kahnAux G n S acc ∧
          (kahnAux G n S acc).idxOf u < (kahnAux G n S acc).idxOf w) := by
  induction n with
  | zero =>
    intro S acc hN hdisj hcov hP hcard
    have hSe : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hSe
    refine ⟨hN, ?_, hP⟩
    simpa [kahnAux] using hcov
  | succ n ih =>
    intro S acc hN hdisj hcov hP hcard
    rw [kahnAux]
    by_cases h : S.Nonempty
    · rw [dif_pos h]
      set v := pickMin G S h with hv
      have hvS : v ∈ S := pickMin_mem G S h
      have hvsrc : ∀ u, G.edge u v → u ∉ S := pickMin_src G S h
      have hvacc : v ∉ acc := fun hva => hdisj v hva hvS
      have hcard' : (S.erase v).card ≤ n := by
        rw [Finset.card_erase_of_mem hvS]; omega
      have hdisj' : ∀ x ∈ acc ++ [v], x ∉ S.erase v := by
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact fun hh => hdisj x hx (Finset.mem_of_mem_erase hh)
        · exact Finset.notMem_erase v S
      have hcov' : (acc ++ [v]).toFinset ∪ S.erase v = Finset.univ := by
        have hvv : ([v] : List V).toFinset = ({v} : Finset V) := by simp
        have hins : ({v} : Finset V) ∪ S.erase v = S := by
          rw [Finset.singleton_union, Finset.insert_erase hvS]
        rw [List.toFinset_append, hvv]
        change (acc.toFinset ∪ {v}) ∪ S.erase v = Finset.univ
        rw [Finset.union_assoc, hins, hcov]
      have hN' : (acc ++ [v]).Nodup := by
        rw [List.nodup_append']
        refine ⟨hN, List.nodup_singleton v, ?_⟩
        simp only [List.Disjoint, List.mem_singleton]
        exact fun a ha e => hvacc (e ▸ ha)
      have hidx_v : (acc ++ [v]).idxOf v = acc.length := by
        rw [List.idxOf_append_of_notMem hvacc]
        simp
      have hlen : ∀ u ∈ acc, (acc ++ [v]).idxOf u = acc.idxOf u := by
        intro u hu; exact List.idxOf_append_of_mem hu
      have hP' : ∀ w ∈ acc ++ [v], ∀ u, G.edge u w →
          u ∈ acc ++ [v] ∧ (acc ++ [v]).idxOf u < (acc ++ [v]).idxOf w := by
        intro w hw u huw
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · obtain ⟨hu, hlt⟩ := hP w hw u huw
          exact ⟨List.mem_append_left _ hu, by rw [hlen u hu, hlen w hw]; exact hlt⟩
        · -- w = v: every parent of v is already output (it is not in S), and lies earlier.
          have hunotS : u ∉ S := hvsrc u huw
          have huacc : u ∈ acc.toFinset := by
            have : u ∈ acc.toFinset ∪ S := by rw [hcov]; exact Finset.mem_univ u
            rcases Finset.mem_union.mp this with h | h
            · exact h
            · exact absurd h hunotS
          have huacc' : u ∈ acc := by simpa using huacc
          refine ⟨List.mem_append_left _ huacc', ?_⟩
          rw [hlen u huacc', hidx_v]
          exact List.idxOf_lt_length_of_mem huacc'
      have hspec := ih (S.erase v) (acc ++ [v]) hN' hdisj' hcov' hP' hcard'
      exact hspec
    · rw [dif_neg h]
      rw [Finset.not_nonempty_iff_eq_empty] at h
      subst h
      refine ⟨hN, ?_, hP⟩
      simpa using hcov

/-! ### The topological order -/

/-- **Kahn topological order** of a finite DAG: run `card V` rounds from the full vertex set.
Each nonempty round deletes one source, so `card V` rounds consume every vertex. -/
noncomputable def topoList (G : DAG V) : List V :=
  kahnAux G (Fintype.card V) (Finset.univ : Finset V) []

/-- The Kahn order lists no vertex twice. -/
theorem topoList_nodup (G : DAG V) : (topoList G).Nodup := by
  unfold topoList
  exact (kahnAux_spec G (Fintype.card V) Finset.univ []
    List.nodup_nil (by intro x hx; simp at hx)
    (by rw [List.toFinset_nil, Finset.empty_union])
    (by intro w hw; simp at hw) (by simp)).1

/-- **Completeness**: the Kahn order contains every vertex. -/
theorem topoList_complete (G : DAG V) :
    (topoList G).toFinset = (Finset.univ : Finset V) := by
  unfold topoList
  exact (kahnAux_spec G (Fintype.card V) Finset.univ []
    List.nodup_nil (by intro x hx; simp at hx)
    (by rw [List.toFinset_nil, Finset.empty_union])
    (by intro w hw; simp at hw) (by simp)).2.1

/-- The Kahn order has length `card V`; with `topoList_nodup` and `topoList_complete` this makes
`topoList G` a **permutation** of the vertex set. -/
theorem topoList_length (G : DAG V) : (topoList G).length = Fintype.card V := by
  have h := List.toFinset_card_of_nodup (topoList_nodup G)
  rw [topoList_complete, Finset.card_univ] at h
  omega

/-- **Topological property**: along every edge `u → w` the tail occurs strictly before the head
in the Kahn order. -/
theorem topoList_topo (G : DAG V) {u w : V} (h : G.edge u w) :
    (topoList G).idxOf u < (topoList G).idxOf w := by
  have hspec := kahnAux_spec G (Fintype.card V) Finset.univ []
    List.nodup_nil (by intro x hx; simp at hx)
    (by rw [List.toFinset_nil, Finset.empty_union])
    (by intro y hy; simp at hy) (by simp)
  have hcov := hspec.2.1
  have htopo := hspec.2.2
  have hwmem : w ∈ kahnAux G (Fintype.card V) Finset.univ [] := by
    rw [← List.mem_toFinset, hcov]; exact Finset.mem_univ w
  exact (htopo w hwmem u h).2

/-- **Ancestor-consistency**: any strict ancestor occurs strictly earlier in the Kahn order.
This strengthens `topoList_topo` from single edges to directed paths. -/
theorem topoList_ancestor (G : DAG V) {u w : V} (h : Relation.TransGen G.edge u w) :
    (topoList G).idxOf u < (topoList G).idxOf w := by
  induction h with
  | single hab => exact topoList_topo G hab
  | tail _ hbc ih => exact lt_trans ih (topoList_topo G hbc)

end FateV2.Predict.Causalean.Graph