/-
-/

module
public import FateWorld.Legacy._root.CausSeparation
public import Mathlib.Tactic.FinCases

/-! # d-Separation is not monotone in the conditioning set

`DAG.dSep X Y Z` (d-separation of `X` from `Y` given `Z`) is **monotone in the
source and target sets** (`DAG.dSep_subset_left`, `DAG.dSep_subset_right` in
`CausSeparation`) but is famously **not monotone in the conditioning set**: adding
a vertex to `Z` can *open* a previously blocked path by activating a collider.

This file produces an explicit, fully verified witness of that failure — a
three-vertex chain `X → M ← Y` in which `M` is a collider:

* conditioning on nothing, the only path `X → M ← Y` is blocked at the collider
  `M`, so `X` and `Y` **are** d-separated;
* conditioning on `{M}` activates the collider, opening the path, so `X` and `Y`
  are **not** d-separated.

The main result `dSep_not_monotone_cond` states exactly this; it is a genuine
non-implication (the hypothesis and the conclusion concern different conditioning
sets), not a restatement of its own hypothesis.

## Main results

* `colliderDAG` — the three-vertex collider `X → M ← Y`.
* `colliderDAG_bbReachable_nil` — the Ball reachable set of `X` given `∅` is `{M}`.
* `colliderDAG_bbReachable_M` — the Ball reachable set of `X` given `{M}` is all
  three vertices.
* `colliderDAG_dSep_nil` — `X` and `Y` are d-separated given `∅`.
* `colliderDAG_not_dSep_M` — `X` and `Y` are **not** d-separated given `{M}`.
* `dSep_not_monotone_cond` — conditioning-set monotonicity fails.

## References

* Pearl, *Causality* (2nd ed.), §1.2.3 (colliders and path blocking).
-/

@[expose] public section

namespace Causalean.Graph

namespace DAG

open Finset

/-- The edge relation of the three-vertex collider `X → M ← Y`, with
`X = 0`, `M = 1`, `Y = 2`. -/
def colliderEdge (u v : Fin 3) : Prop := (u = 0 ∧ v = 1) ∨ (u = 2 ∧ v = 1)

instance colliderEdgeDecidable : DecidableRel colliderEdge :=
  fun u v => by unfold colliderEdge; infer_instance

/-- A topological ranking for `colliderEdge`: both sources sit below the collider. -/
def colliderRank (u : Fin 3) : ℕ := if u = 1 then 1 else 0

/-- **The three-vertex collider** `X → M ← Y` on `Fin 3`, where `X = 0`, `M = 1`,
`Y = 2`. -/
def colliderDAG : DAG (Fin 3) where
  edge := colliderEdge
  decEdge := colliderEdgeDecidable
  acyclic := DAG.acyclic_of_topoOrder (W := ℕ) (r := (· < ·)) (e := colliderEdge)
    (τ := colliderRank) (fun u v h => by
      unfold colliderEdge at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> unfold colliderRank <;> decide)

/-- Given no conditioning, the Bayes-Ball reachable set from `X = 0` consists of the
collider `M = 1` alone: the ball travels `X → M` and stops there, because `M` is an
unconditioned collider. -/
theorem colliderDAG_bbReachable_nil :
    colliderDAG.bbReachableVertices (∅ : Finset (Fin 3)) {0} = {1} := by
  ext i
  fin_cases i <;> decide

/-- Given the conditioning set `{M}`, the Bayes-Ball reachable set from `X = 0` is all
three vertices: conditioning on the collider `M = 1` lets the ball pass through it. -/
theorem colliderDAG_bbReachable_M :
    colliderDAG.bbReachableVertices ({1} : Finset (Fin 3)) {0} = {0, 1, 2} := by
  ext i
  fin_cases i <;> decide

/-- With no conditioning, `X = 0` and `Y = 2` **are** d-separated: the query sets are
pairwise disjoint and the reachable set `{M}` misses `Y`. -/
theorem colliderDAG_dSep_nil : colliderDAG.dSep {0} {2} (∅ : Finset (Fin 3)) := by
  unfold DAG.dSep
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- With `{M}` conditioned on, `X = 0` and `Y = 2` are **not** d-separated: the collider
is activated, so `Y` lies in the reachable set. -/
theorem colliderDAG_not_dSep_M : ¬ colliderDAG.dSep {0} {2} ({1} : Finset (Fin 3)) := by
  unfold DAG.dSep
  intro h
  obtain ⟨_, _, _, hReach⟩ := h
  have hM : (2 : Fin 3) ∈ colliderDAG.bbReachableVertices ({1} : Finset (Fin 3)) {0} := by
    rw [colliderDAG_bbReachable_M]
    decide
  exact (Finset.disjoint_left.mp hReach) hM (by decide)

/-- **d-Separation is not monotone in the conditioning set.**

There is a finite DAG `G` and vertex sets `X`, `Y`, `Z`, `m` such that `X` and `Y` are
d-separated given `Z` but **not** given `Z ∪ {m}`. The witness is the three-vertex
collider `X → M ← Y` with `Z = ∅` and `m = M`. -/
theorem dSep_not_monotone_cond :
    ∃ (V : Type) (_ : DecidableEq V) (_ : Fintype V) (G : DAG V)
      (X Y Z : Finset V) (m : V),
      G.dSep X Y Z ∧ ¬ G.dSep X Y (insert m Z) :=
  ⟨Fin 3, inferInstance, inferInstance, colliderDAG, {0}, {2}, ∅, 1,
    colliderDAG_dSep_nil, by simpa using colliderDAG_not_dSep_M⟩

end DAG

end Causalean.Graph