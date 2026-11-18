module
public import FateWorld.FateV2.Modeling.CausSeparation
public import FateWorld.FateV2.Modeling.CausActivePath
public import Mathlib.Data.Finset.Basic

/-!
  # Predict · CausBayesBallEquiv

  ## 迁移登记
  - 来源：`FateWorld/Legacy/CausBayesBallEquiv.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：_root.CausSeparation, _root.CausActivePath
  - 补充 open 域：FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-
# Bayes Ball vs. d-Separation: the equivalence

`CausSeparation.dSep` defines d-separation *as* "the Bayes ball cannot reach `Y` from
`X` given `Z`". That is an operational statement. The classical, textbook definition of
d-separation is *topological*: no walk (path) from `X` to `Y` is active given `Z`, where
a walk is active when every collider on it lies in the ancestral closure of `Z` and every
non-collider lies outside `Z`.

This file makes the two definitions independent:

* `dSepWalk` — the topological definition. It does **not** mention the Bayes ball.
* `DAG.dSep` (from `CausSeparation`) — the operational Bayes-ball definition.

and then proves they agree:

* `bayesBall_iff_dSepWalk` — `Disjoint (bbReachableVertices Z X) Y ↔ dSepWalk X Y Z`.

The proof rests on the already-proved correctness theorem
`bbReachableVertices_iff_activeWalk` (`CausActivePath.lean`), which says the Bayes-ball
BFS reaches exactly the endpoints of active walks. Since `dSepWalk` is purely
topological, this is a genuine equivalence with the textbook notion rather than an
unfolding of a definition.

## Main results

* `dSepWalk` — topological d-separation (no active walk)
* `bayesBall_iff_dSepWalk` — Bayes-ball blocking ⇔ no active walk
* `dSep_iff_dSepWalk` — the bundled `dSep` agrees with topological d-separation
* `dSepWalk_decidable` — d-separation is decidable via the Bayes ball
* `dSepWalk_iff_not_dSepWalk_of_swap` — symmetry of the topological notion

## References

* Pearl (1988), *Probabilistic Reasoning in Intelligent Systems*, Def. 2.27
* Shachter (1998), Bayes Ball
* Basic Concepts.tex, Definition (d-separation)
-/


@[expose] public section

namespace FateV2.Predict.Causalean.Graph

open FateV2.Modeling
variable {V : Type*} [DecidableEq V] [Fintype V]

namespace DAG

variable (G : DAG V)

/-- **Topological d-separation.** For [a directed acyclic graph](hyp:G) and [source,
target and conditioning sets](hyp:X,Y,Z), the [`dSepWalk` relation](goal) holds exactly
when [no walk from a vertex of `X` to a vertex of `Y` is active given `Z`](step:1).

    This is the textbook definition: it quantifies over *walks* (lists of pairwise
    adjacent vertices, orientation-free) and tests them with the collider/non-collider
    activity condition `IsActiveWalk`. It never mentions Bayes-ball reachability, so
    relating it to `dSep` is a real theorem.

    It imposes no disjointness requirement; `dSep` adds the pairwise-disjointness
    side conditions on top (see `dSep_iff_dSepWalk`). -/
def dSepWalk (X Y Z : Finset V) : Prop :=
  ¬ G.HasActiveWalk X Y Z

/-- For [a directed acyclic graph](hyp:G) and [source, target and conditioning
sets](hyp:X,Y,Z), the [query-set disjointness condition](goal) bundles
[the three pairwise-disjointness requirements](step:1) carried by the operational `dSep`. -/
def dSepQueryDisjoint (X Y Z : Finset V) : Prop :=
  Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z

/-- **Bayes ball decides d-separation.** For [a directed acyclic graph](hyp:G) and
[source, target and conditioning sets](hyp:X,Y,Z), [the Bayes ball fails to reach `Y`
from `X` given `Z`](hyp) if and only if [every walk from `X` to `Y` is inactive given
`Z`](goal).

    Both directions are immediate from the correctness theorem
    `bbReachableVertices_iff_activeWalk`, which identifies the Bayes-ball reachable
    vertices with the endpoints of active walks:

    * reaching `y ∈ Y` exhibits an active walk to `y`, killing `dSepWalk`;
    * an active walk to `y ∈ Y` makes `y` reachable, killing the disjointness. -/
theorem bayesBall_iff_dSepWalk (X Y Z : Finset V) :
    Disjoint (G.bbReachableVertices Z X) Y ↔ G.dSepWalk X Y Z := by
  constructor
  · -- Ball cannot reach `Y`  ⟹  no active walk ends in `Y`.
    rintro hdisj ⟨p, hlen, hact, hhead, hlast⟩
    obtain ⟨x, hxX, hx⟩ : ∃ x ∈ X, p.head? = some x := by
      obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hhead
      exact ⟨x, hx, hxeq.symm⟩
    obtain ⟨y, hyY, hy⟩ : ∃ y ∈ Y, p.getLast? = some y := by
      obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hlast
      exact ⟨y, hy, hyeq.symm⟩
    have hreach : y ∈ G.bbReachableVertices Z X :=
      (G.bbReachableVertices_iff_activeWalk X Z y).mpr
        ⟨x, hxX, p, hlen, hact, hx, hy⟩
    exact Finset.disjoint_left.mp hdisj hreach hyY
  · -- No active walk ends in `Y`  ⟹  the ball cannot reach `Y`.
    -- Destruct `Disjoint` via an explicit common element.
    rw [Finset.disjoint_left]
    rintro hwalk y hyReach hyY
    obtain ⟨x, hxX, p, hlen, hact, hx, hy⟩ :=
      (G.bbReachableVertices_iff_activeWalk X Z y).mp hyReach
    exact hwalk ⟨p, hlen, hact,
      Finset.mem_image.mpr ⟨x, hxX, hx.symm⟩,
      Finset.mem_image.mpr ⟨y, hyY, hy.symm⟩⟩

/-- **Bayes ball ⇔ d-separation, bundled form.** For [a directed acyclic graph](hyp:G) and
[source, target and conditioning sets](hyp:X,Y,Z), the operational [`dSep`](hyp) holds
exactly when [the query sets are pairwise disjoint and every walk from `X` to `Y` is
inactive given `Z`](goal).

    The second conjunct is the topological definition `dSepWalk`; this theorem is what
    licenses reading `dSep` as the textbook notion of d-separation. -/
theorem dSep_iff_dSepWalk (X Y Z : Finset V) :
    G.dSep X Y Z ↔ dSepQueryDisjoint X Y Z ∧ G.dSepWalk X Y Z := by
  unfold dSep dSepQueryDisjoint
  rw [G.bayesBall_iff_dSepWalk]
  tauto

/-- **d-separation is symmetric.** For [a directed acyclic graph](hyp:G) and [source,
target and conditioning sets](hyp:X,Y,Z), [`X` is d-separated from `Y` given
`Z`](hyp) [if and only if `Y` is d-separated from `X` given `Z`](goal).

    Read through `dSepWalk`, this is a statement about active walks: reversing a walk
    swaps its endpoints and preserves activity (`isActiveWalk_reverse`), so the
    topological condition is symmetric. -/
theorem dSepWalk_symm (X Y Z : Finset V) :
    G.dSepWalk X Y Z ↔ G.dSepWalk Y X Z := by
  constructor
  · rintro hwalk ⟨p, hlen, hact, hhead, hlast⟩
    -- Reverse the walk; `isActiveWalk_reverse` preserves activity and swaps endpoints.
    refine hwalk ⟨p.reverse, ?_, G.isActiveWalk_reverse hact, ?_, ?_⟩
    · simpa using hlen
    · rwa [List.head?_reverse]
    · rwa [List.getLast?_reverse]
  · rintro hwalk ⟨p, hlen, hact, hhead, hlast⟩
    refine hwalk ⟨p.reverse, ?_, G.isActiveWalk_reverse hact, ?_, ?_⟩
    · simpa using hlen
    · rwa [List.head?_reverse]
    · rwa [List.getLast?_reverse]

/-- **Bayes ball gives a decision procedure for d-separation.** For [a directed acyclic
graph](hyp:G) and [source, target and conditioning sets](hyp:X,Y,Z), [the topological
relation `dSepWalk`](goal) is decidable.

    This is the algorithmic content of the theorem: `bayesBall_iff_dSepWalk` transports
    decidability of "the Bayes ball cannot reach `Y`" — computed from the finite BFS
    `bbReachable` — to the topological notion. No separate path enumeration is needed. -/
instance dSepWalk_decidable (X Y Z : Finset V) : Decidable (G.dSepWalk X Y Z) :=
  decidable_of_iff (Disjoint (G.bbReachableVertices Z X) Y)
    (G.bayesBall_iff_dSepWalk X Y Z)

end DAG

end FateV2.Predict.Causalean.Graph
