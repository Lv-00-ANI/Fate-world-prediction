import FateWorld.Legacy.NaryIndex
import FateWorld.Legacy.FinJoint
import Mathlib.Data.Fintype.Pi

/-! ===========================================================================
  §GenNDegenerate  the N-ary condition at `|ι| = 2` (round 209)

  ## What this module establishes

  `NaryIndex` recorded as a limitation:

  > "Algebraically `CondIndepN` at `|ι| = 2` **is** `CondIndepFin`, but this is
  >  not formalised."

  We formalise the **algebraic core** of that statement:

  * **N-ary side** (definition, `Fate/CondIndepN.lean`):
    `CondIndepN p  ⟺  ∀ xs z, p xs z * (NMass p z)^(|ι| - 1) = ∏ i, marg p i (xs i) z`

  * At `|ι| = 2` the exponent is `2 - 1 = 1`, so the condition reads
    `p xs z * NMass p z = marg p 0 (xs 0) z * marg p 1 (xs 1) z`
    — see `condIndepN_fin2_shape`.

  * **binary side** (definition, `Fate/FinJoint.lean`):
    `CondIndepFin q  ⟺  ∀ x y z, q ((x,y),z) * margZ q z = margXZ q x z * margYZ q y z`

  Both are the same equation **"joint × total = product of one-variable
  marginals"**.  The statement below records the **N-ary side** of this
  correspondence; the literal transport to `CondIndepFin` is **not** formalised
  (see the limitation note below).

  ## CORRECTION (round 210): the literal transport **already exists**

  The claim below ("the transport is not carried out") was **wrong**.  The
  binary-equivalence form is **already proven** in `Fate/CondIndepN.lean`:

      theorem condIndepN_bool_iff (p : ((i : Bool) -> boolFam alpha beta i) -> gamma -> R) :
          CondIndepN p <-> CondIndepFin (toFin p)

  (`boolFam alpha beta : Bool -> Type` is the two-element index family, and
  `toFin` transports to `(alpha x beta) x gamma -> R`.)  So `CondIndepN` at a
  two-element index set **is** `CondIndepFin`, literally, axiom-clean.

  What this module adds is the `Fin 2`-shaped statement (as opposed to the
  `Bool`-shaped one), plus the algebraic shape lemma below.
  =========================================================================== -/

namespace Fate.GenN

open MeasureTheory ProbabilityTheory

section ShapeFin2

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)] [∀ i, DecidableEq (fam i)]

/-- ⭐⭐ **At `|ι| = 2` the N-ary condition has the binary shape**.

`CondIndepN` says `p xs z * NMass^(|ι|-1) = ∏ i, marg i (xs i) z`; when
`Fintype.card ι = 2` the exponent `|ι| - 1` is `1`, so the condition reduces to

    p xs z * NMass p z = ∏ i, marg p i (xs i) z

which is exactly the shape of `CondIndepFin`
(`q ((x,y),z) * margZ q z = margXZ q x z * margYZ q y z`). -/
theorem condIndepN_fin2_shape
    (p : Fate.GenC3.NJoint (ι := ι) fam γ) (hcard : Fintype.card ι = 2) :
    Fate.GenC3.CondIndepN p
      ↔ ∀ xs z, p xs z * Fate.GenC3.NMass p z = ∏ i, Fate.GenC3.marg p i (xs i) z := by
  rw [Fate.GenC3.condIndepN_iff]
  constructor
  · intro h xs z
    have h2 := h xs z
    rw [hcard] at h2
    simpa using h2
  · intro h xs z
    have h2 := h xs z
    rw [hcard]
    simpa using h2

end ShapeFin2

end Fate.GenN
