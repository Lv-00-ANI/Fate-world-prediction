import FateWorld.FateV2.Modeling.NaryBridgeDone
import Mathlib.Data.Fintype.Pi

/-!
  # Modeling · NaryPointwise

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NaryPointwise.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NaryBridgeDone
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenNPointwise  GLOBAL (∀ a) form of the N-ary bridge final theorem (round 206)

  ## Why this module exists (semantic audit R0, round 206)

  The final theorem `nary_bridge_final_one_line` is stated for a **single anchor
  point** `a`.  Agent R0's semantic audit observed:

  > "it is only stated at one anchor `a`, and does not declare `forall a`.
  >  Taken as the global statement 'the kernel factorizes', pointwise
  >  multiplicativity is **not sufficient** to give a kernel factorization."

  Correct: the algebraic chain delivers **pointwise** multiplicativity.  This
  module quantifies it **universally over all anchors of nonzero mass**, which
  is the strongest statement the assembly supports, and states it as
  `∀ a` rather than for a fixed `a`.

  ## What remains (honest)

  * The events are the **cylinder events** `coordSet i (Sf i)`.  Every `fam i`
    is a `Fintype`, so these generate the whole product σ-algebra and a
    monotone-class upgrade is available — **not carried out here**.
  * `μ{a} ≠ 0` and `μ.real(fiberN a.2) ≠ 0` exclude null fibers — the usual
    "conditioning on a null event" restriction, not an artefact.
  =========================================================================== -/

namespace FateV2.Modeling.GenN

open MeasureTheory ProbabilityTheory

section Pointwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)] [∀ i, DecidableEq (fam i)]
variable {γ : Type*} [Fintype γ] [DecidableEq γ] [MeasurableSpace γ]
  [MeasurableSingletonClass γ]
variable [∀ i, MeasurableSpace (fam i)] [∀ i, MeasurableSingletonClass (fam i)]
variable [MeasurableSpace ((∀ j, fam j) × γ)]
variable [MeasurableSingletonClass ((∀ j, fam j) × γ)]
variable [StandardBorelSpace ((∀ j, fam j) × γ)]

/-- ⭐⭐⭐⭐⭐ **GLOBAL form: `∀ a`, the conditional kernel is multiplicative**.

For **every** anchor point `a` with nonzero mass and nonzero fiber mass,

    kappa_a(iInter i, t_i) = prod i, kappa_a(t_i)

with `t_i = coordSet i (Sf i)`. -/
theorem nary_bridge_pointwise_all
    (p : ((∀ j, fam j) × γ) → ℝ) (hp : ∀ w, 0 ≤ p w)
    (pN : FateV2.Modeling.GenC3.NJoint (ι := ι) fam γ)
    (hpN : ∀ xs z, pN xs z = p (xs, z))
    (hcond : FateV2.Modeling.GenC3.CondIndepN pN)
    (hproj : ∀ i, Measurable (fun w : (∀ j, fam j) × γ => w.1 i))
    (hsnd : Measurable (fun w : (∀ j, fam j) × γ => w.2))
    (Sf : ∀ i, Finset (fam i)) :
    letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
    ∀ a : (∀ j, fam j) × γ,
      (weightedCountN p) {a} ≠ 0 →
      (weightedCountN p).real (fiberN a.2) ≠ 0 →
      ((condExpKernel (Ω := (∀ j, fam j) × γ) (weightedCountN p)
        (MeasurableSpace.comap (fun w : (∀ j, fam j) × γ => w.2) inferInstance)) a).real
          (⋂ i, coordSet (fam := fam) (γ := γ) i ((Sf i : Set (fam i))))
        = ∏ i, ((condExpKernel (Ω := (∀ j, fam j) × γ) (weightedCountN p)
        (MeasurableSpace.comap (fun w : (∀ j, fam j) × γ => w.2) inferInstance)) a).real
          (coordSet (fam := fam) (γ := γ) i ((Sf i : Set (fam i)))) := by
  letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
  intro a hμa hM
  exact nary_bridge_final_one_line p hp pN hpN hcond hproj hsnd Sf a hμa hM

end Pointwise

end FateV2.Modeling.GenN
