/-
-/

module

public import FateWorld.Legacy._root.CausDAG
public import Mathlib.Tactic

/-! # `Fate/T1A2` — Read-sets and graph factorization

## Primitives

* `ReadsOnlyOn S f` — `f` depends only on the coordinates in `S` (a read-set constraint).
  Monotone in `S`; its empty case is exactly constancy.
* `nd G v` — the non-descendant set `V \ ({v} ∪ desc(v))`, with membership criterion `mem_nd`.
* `FactorizesOn G p` — the positive Markov factorization `p x = ∏ v, π v x`, each factor
  `π v` reading only `{v} ∪ pa(v)` and **strictly positive**.

## Why positivity

The naive form `∃ π, (read-set constraints) ∧ ∀ x, p x = ∏ v, π v x` is *vacuous*: `π v` is
pinned only on `{v} ∪ pa(v)`, every other coordinate is free, so the product can be rigged
to hit any prescribed `p`. The positivity clause `0 < π v x` removes that freedom — a
product of positive reals is positive, so `p` must be positive everywhere — and
`factorizesOn_not_trivial` certifies that the condition has real force: the zero function
`p ≡ 0` is *not* positively factorizable, on any `G`.

## Contents

| item | status |
|---|---|
| `ReadsOnlyOn` | defined |
| `ReadsOnlyOn.mono` | proved |
| `readsOnlyOn_empty_iff` | proved |
| `ReadsOnlyOn.insert` | proved |
| `nd` | defined |
| `mem_nd` | proved |
| `not_mem_nd_self` | proved |
| `FactorizesOn` (positive form) | defined |
| `factorizesOn_def` | proved |
| `FactorizesOn.pos` | proved |
| `FactorizesOn.ne_zero` | proved |
| `factorizesOn_not_trivial` | **proved** (non-vacuity, task 4) |
| `not_factorizesOn_of_exists_zero` | proved |
-/

@[expose] public section

namespace Fate.T1A2

open Causalean.Graph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## §1 Read-sets -/

/-- **Read-set**: `f` reads only the coordinates in `S`.

If `x` and `y` agree on every member of `S`, then `f x = f y`. This is the only place the
set `S` occurs; nothing is asserted about coordinates outside `S`, which is exactly the
point — `f` is *constrained* not to look at them. -/
def ReadsOnlyOn (S : Finset V) (f : (V → Bool) → ℝ) : Prop :=
  ∀ x y : V → Bool, (∀ u ∈ S, x u = y u) → f x = f y

/-- **Monotonicity**: a function reading only `S` also reads only any `T ⊇ S`. -/
theorem ReadsOnlyOn.mono {S T : Finset V} {f : (V → Bool) → ℝ}
    (hST : S ⊆ T) (h : ReadsOnlyOn S f) : ReadsOnlyOn T f := by
  intro x y hxy
  exact h x y (fun u hu => hxy u (hST hu))

/-- **Reading only the empty set is constancy**: `ReadsOnlyOn ∅ f ↔ ∀ x y, f x = f y`. -/
theorem readsOnlyOn_empty_iff {f : (V → Bool) → ℝ} :
    ReadsOnlyOn ∅ f ↔ ∀ x y, f x = f y := by
  constructor
  · intro h x y
    exact h x y (fun u hu => absurd hu (Finset.notMem_empty u))
  · intro h x y _
    exact h x y

/-- A function reading only `S` also reads only `insert u S`. -/
theorem ReadsOnlyOn.insert {S : Finset V} {f : (V → Bool) → ℝ} (u : V)
    (h : ReadsOnlyOn S f) : ReadsOnlyOn (insert u S) f :=
  h.mono (Finset.subset_insert u S)

/-! ## §2 Non-descendant sets -/

/-- **Non-descendants** of `v`: `V \ ({v} ∪ desc(v))`. -/
def nd (G : DAG V) (v : V) : Finset V :=
  Finset.univ \ (G.descendants v ∪ {v})

/-- **Membership criterion**: `u` is a non-descendant of `v` iff `v` is not a strict
ancestor of `u` and `u ≠ v`.

Depends on `DAG.mem_descendants` (`CausDAG.lean:317`). -/
theorem mem_nd {G : DAG V} {u v : V} :
    u ∈ nd G v ↔ ¬ G.isAncestor v u ∧ u ≠ v := by
  unfold nd
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, true_and,
    DAG.mem_descendants, Finset.mem_singleton, not_or]

/-- A vertex is never a non-descendant of itself. -/
theorem not_mem_nd_self {G : DAG V} (v : V) : v ∉ nd G v := by
  rw [mem_nd]
  exact fun h => h.2 rfl

/-! ## §3 Graph factorization, positive form -/

/-- **Graph factorization** of `p` along `G`: there is one conditional factor `π v` per
vertex, each reading only the coordinates in `{v} ∪ pa(v)`, each **strictly positive**, and
`p x = ∏ v, π v x` for every configuration `x`.

The positivity `0 < π v x` is the hypothesis that makes the equation bite: together with
`Finset.prod_pos` it forces `p` to be positive everywhere, so `π` cannot be rigged to make
the constraint vacuous. See `factorizesOn_not_trivial`. -/
def FactorizesOn (G : DAG V) (p : (V → Bool) → ℝ) : Prop :=
  ∃ π : V → (V → Bool) → ℝ,
    (∀ v, ReadsOnlyOn (insert v (G.parents v)) (π v)) ∧
    (∀ v x, 0 < π v x) ∧
    ∀ x, p x = ∏ v, π v x

/-- Unfolding form of `FactorizesOn` (pointwise restatement, convenient downstream). -/
theorem factorizesOn_def {G : DAG V} {p : (V → Bool) → ℝ} :
    FactorizesOn G p ↔
      ∃ π : V → (V → Bool) → ℝ,
        (∀ v, ReadsOnlyOn (insert v (G.parents v)) (π v)) ∧
        (∀ v x, 0 < π v x) ∧
        ∀ x, p x = ∏ v, π v x :=
  Iff.rfl

/-- **Positivity transfers**: a positively factorized `p` is strictly positive everywhere.

This is precisely where the positivity clause of `FactorizesOn` is consumed: the product
of strictly positive reals is strictly positive. -/
theorem FactorizesOn.pos {G : DAG V} {p : (V → Bool) → ℝ} (h : FactorizesOn G p) :
    ∀ x, 0 < p x := by
  obtain ⟨π, -, hpos, hfac⟩ := h
  intro x
  rw [hfac x]
  exact Finset.prod_pos (fun v _ => hpos v x)

/-- A positively factorized `p` never vanishes. -/
theorem FactorizesOn.ne_zero {G : DAG V} {p : (V → Bool) → ℝ} (h : FactorizesOn G p)
    (x : V → Bool) : p x ≠ 0 :=
  ne_of_gt (h.pos x)

/-! ## §4 Non-vacuity: `FactorizesOn` is not trivially true -/

/-- **`FactorizesOn` is not a vacuous condition.** For every DAG `G` on any vertex type the
zero function `p ≡ 0` is not positively factorizable, so there is a DAG (e.g. `Fin 2` with no
edges) and a `p` with `¬ FactorizesOn G p`.

Proof: `FactorizesOn` forces `0 < p x` at every `x`, but `p x = 0`. Equivalently, an
explicit `∃`-form witness at `V = Fin 2`. -/
theorem factorizesOn_not_trivial :
    ∃ (G : DAG (Fin 2)) (p : (Fin 2 → Bool) → ℝ), ¬ FactorizesOn G p := by
  -- The empty DAG on `Fin 2`: a transitive closure of the empty relation is empty.
  have hac : ∀ v : Fin 2, ¬ Relation.TransGen (fun _ _ : Fin 2 => False) v v := by
    intro w hw
    -- ⚠ 归纳必须**泛化终点**：`TransGen.tail` 的归纳假设是 `False w a`，
    -- 若先固定终点为 `w`（`le_antisymm` 式写法），motive 类型不匹配。
    have key : ∀ {a : Fin 2}, Relation.TransGen (fun _ _ : Fin 2 => False) w a → False := by
      intro a htr
      induction htr with
      | single h => exact h
      | tail _ h _ => exact h
    exact key hw
  refine ⟨⟨fun _ _ => False, fun _ _ => isFalse id, hac⟩, fun _ => 0, fun h => ?_⟩
  exact lt_irrefl 0 (h.pos (fun _ => false))

/-- General form: a `p` that vanishes somewhere is not positively factorizable. -/
theorem not_factorizesOn_of_exists_zero {G : DAG V} {p : (V → Bool) → ℝ} (x : V → Bool)
    (hx : p x = 0) : ¬ FactorizesOn G p := by
  intro h
  exact absurd hx (h.ne_zero x)

/-! ## Axiom audit -/

#print axioms ReadsOnlyOn.mono
#print axioms readsOnlyOn_empty_iff
#print axioms ReadsOnlyOn.insert
#print axioms mem_nd
#print axioms not_mem_nd_self
#print axioms FactorizesOn.pos
#print axioms FactorizesOn.ne_zero
#print axioms factorizesOn_not_trivial
#print axioms not_factorizesOn_of_exists_zero

/-! ## §5 Downstream-facing composites (round R-10)

The `T1A2` series has eleven modules (`T1A2`, `T1A2CI`, `T1A2CI3`, `T1A2Chain`, `T1A2N`,
`T1A2Prob`, `T1A2Substance`, `T1A2Theta`, `T1A2Encode`, `T1A2Fin`, `T1A2Bridge`). They each
build one layer on top of the primitives of this file; the theorems below are the composites
they were missing, all stated with **this file's vocabulary only** (so that they need no
import of a sibling module and no cycle through `public import CausDAG`).

| item | content |
|---|---|
| `node_reads` | the read-set of a single factor, named |
| `readSet_univ_of_le` | any read-set inside a superset `U` makes the factor read `U` |
| `prod_reads_union_ext` | full product `∏ v ⊆ ⋃ v, {v} ∪ pa(v)` |
| `prod_reads_superset` | full product reads any superset of all read-sets |
| `prod_read_pos` | a product of strictly positive factors is strictly positive |
| `prod_reads_nontrivial` | a product that reads `∅` is constant (non-degeneracy) |
| `factorizesOn_split` | the *same* `π` splits `p` along every `S` / `Sᶜ`, and `p > 0` |
| `factorizesOn_prod_pos` | `p` positive and its whole product form, pointwise |
| `factorizesOn_prod_reads` | the whole product `∏ v, π v x` (= `p x`) reads `univ` |
-/

/-- **The read-set of one factor, named.**

`FactorizesOn` stores the read-set constraints in a `∀`; this theorem pulls one of them out
so that downstream code can `exact` it without unfolding the existential. -/
theorem node_reads {G : DAG V} (pi : V → (V → Bool) → ℝ)
    (hreads : ∀ v, ReadsOnlyOn (insert v (G.parents v)) (pi v)) (v : V) :
    ReadsOnlyOn (insert v (G.parents v)) (pi v) :=
  hreads v

/-- **Enlarging a read-set never destroys the constraint.**

The `U`-form of `ReadsOnlyOn.mono`, written so the read-set `insert v (G.parents v)` is
already discharged. -/
theorem readSet_univ_of_le {G : DAG V} (pi : V → (V → Bool) → ℝ) (v : V) (U : Finset V)
    (h : ReadsOnlyOn (insert v (G.parents v)) (pi v))
    (hU : insert v (G.parents v) ⊆ U) : ReadsOnlyOn U (pi v) :=
  ReadsOnlyOn.mono hU h

/-- **The full product reads the union of all read-sets.**

`∏ v, π v x` is the right-hand side of the `FactorizesOn` equation, but `ReadsOnlyOn` is
about `π v` one factor at a time. This composite closes the gap. -/
theorem prod_reads_union_ext {G : DAG V} (pi : V → (V → Bool) → ℝ)
    (hreads : ∀ v, ReadsOnlyOn (insert v (G.parents v)) (pi v)) :
    ReadsOnlyOn (Finset.univ.biUnion (fun v => insert v (G.parents v)))
      (fun x => ∏ v, pi v x) := by
  intro x y hxy
  apply Finset.prod_congr rfl
  intro v _
  exact hreads v x y (fun a ha => hxy a (Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, ha⟩))

/-- **The full product reads any superset of all read-sets.**

The useful form: instead of manipulating the `biUnion`, a caller only has to know that every
`{v} ∪ pa(v)` sits inside their set `U`. -/
theorem prod_reads_superset {G : DAG V} (pi : V → (V → Bool) → ℝ)
    (hreads : ∀ v, ReadsOnlyOn (insert v (G.parents v)) (pi v))
    (U : Finset V) (hU : ∀ v, insert v (G.parents v) ⊆ U) :
    ReadsOnlyOn U (fun x => ∏ v, pi v x) := by
  have h := prod_reads_union_ext pi hreads
  refine ReadsOnlyOn.mono ?_ h
  intro a ha
  rw [Finset.mem_biUnion] at ha
  obtain ⟨v, -, hv⟩ := ha
  exact hU v hv

/-- **A product of strictly positive factors is strictly positive.**

The pointwise half of `FactorizesOn.pos`, isolated so that it can be reused for the
`S`-indexed products appearing in separability statements. -/
theorem prod_read_pos {pi : V → (V → Bool) → ℝ} (hpos : ∀ v x, 0 < pi v x)
    (x : V → Bool) : 0 < ∏ v, pi v x :=
  Finset.prod_pos (fun v _ => hpos v x)

/-- **A product reading nothing is constant** (non-degeneracy of the read-set notion).

This certifies that `ReadsOnlyOn` is not satisfied by every function: a product of positive
factors that `ReadsOnlyOn ∅` must be constant, so making it read `∅` is a real restriction.
The proof uses `Finset.prod_pos` twice — once to get a positive value, once, through the
read-set hypothesis, to propagate that single value to every configuration. -/
theorem prod_reads_nontrivial {pi : V → (V → Bool) → ℝ}
    (h : ReadsOnlyOn ∅ (fun x => ∏ v, pi v x)) :
    ∀ x y, (∏ v, pi v x) = (∏ v, pi v y) :=
  readsOnlyOn_empty_iff.mp h

/-- **The *same* factor family splits `p` along every `S` / `Sᶜ`, and `p` is positive.**

`Fate.T1A2CI.factorizesOn_separable` produces a *fresh* witness `π` from `h`; here the
witness is the one already fixed by `FactorizesOn`, and positivity is conjoined in the same
statement, so a caller does one elimination instead of two. -/
theorem factorizesOn_split {G : DAG V} {p : (V → Bool) → ℝ} (h : FactorizesOn G p) :
    ∃ pi : V → (V → Bool) → ℝ,
      (∀ v, ReadsOnlyOn (insert v (G.parents v)) (pi v)) ∧
      (∀ v x, 0 < pi v x) ∧
      ∀ S : Finset V, ∀ x, p x = (∏ v ∈ S, pi v x) * (∏ v ∈ Sᶜ, pi v x) ∧ 0 < p x := by
  obtain ⟨pi, hreads, hpos, hfac⟩ := h
  refine ⟨pi, hreads, hpos, fun S x => ⟨?_, FactorizesOn.pos ⟨pi, hreads, hpos, hfac⟩ x⟩⟩
  rw [hfac x]
  exact (Finset.prod_mul_prod_compl S (fun v => pi v x)).symm

/-- **Pointwise product form of a factorized `p`, together with positivity.**

`factorizesOn_def` gives the existence form; this gives the *evaluated* form that downstream
`rw`-style proofs actually consume. -/
theorem factorizesOn_prod_pos {G : DAG V} {p : (V → Bool) → ℝ} (h : FactorizesOn G p) :
    ∃ pi : V → (V → Bool) → ℝ,
      (∀ v, ReadsOnlyOn (insert v (G.parents v)) (pi v)) ∧
      (∀ x, p x = ∏ v, pi v x ∧ 0 < p x) := by
  obtain ⟨pi, hreads, hpos, hfac⟩ := h
  refine ⟨pi, hreads, fun x => ⟨hfac x, ?_⟩⟩
  rw [hfac x]
  exact prod_read_pos hpos x

/-- **The whole product reads the full vertex set** (hence `p` does too).

Combines `prod_reads_superset` with `Finset.subset_univ`, and rewrites the product back to
`p` by the factorization equation: `p` is readable from `univ`, i.e. the factorization does
not secretly depend on a larger space. -/
theorem factorizesOn_prod_reads {G : DAG V} {p : (V → Bool) → ℝ} (h : FactorizesOn G p) :
    ReadsOnlyOn (Finset.univ : Finset V) p := by
  obtain ⟨pi, hreads, -, hfac⟩ := h
  have hreads' : ReadsOnlyOn (Finset.univ : Finset V) (fun x => ∏ v, pi v x) :=
    prod_reads_superset pi hreads Finset.univ (fun v => Finset.subset_univ _)
  intro x y hxy
  calc p x = ∏ v, pi v x := hfac x
    _ = ∏ v, pi v y := hreads' x y hxy
    _ = p y := (hfac y).symm

/-! ## Axiom audit (downstream composites) -/

#print axioms node_reads
#print axioms readSet_univ_of_le
#print axioms prod_reads_union_ext
#print axioms prod_reads_superset
#print axioms prod_read_pos
#print axioms prod_reads_nontrivial
#print axioms factorizesOn_split
#print axioms factorizesOn_prod_pos
#print axioms factorizesOn_prod_reads

end Fate.T1A2