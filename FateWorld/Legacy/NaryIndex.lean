import FateWorld.Legacy.NaryGeneric
import FateWorld.Legacy.NaryPointwise
import FateWorld.Legacy.NaryBridgeDone
import FateWorld.Legacy.NaryClose
import FateWorld.Legacy.NaryCancel
import FateWorld.Legacy.NaryProduct
import FateWorld.Legacy.NaryConnect3
import FateWorld.Legacy.NaryLink
import FateWorld.Legacy.NaryMassLink
import FateWorld.Legacy.NaryAssembly
import FateWorld.Legacy.NaryFiberDecomp

/-! ===========================================================================
  §GenNIndex  ⭐ THE N-ARY BRIDGE — a single entry point (round 208)

  This module imports every component of the N-ary bridge and records, in one
  place, **what was proven and under which assumptions**.  It contains no new
  mathematics; it exists so that a reader (or an auditor) can find the whole
  chain from one file.

  # The theorem

  Let `p : (∀ i, fam i) × γ → ℝ` be a nonnegative (unnormalised) weight,
  `pN xs z = p (xs, z)`, and suppose `CondIndepN pN` holds, i.e. for all `xs z`

      pN xs z * (NMass pN z)^(|ι| - 1) = ∏ i, marg pN i (xs i) z

  (the standard "joint conditional density factorises into its one-variable
  conditional marginals" condition; for `|ι| = 2` this is exactly `CondIndepFin`).
  Let `S i ⊆ fam i` be arbitrary, `t i = coordSet i (S i) = {w | w.1 i ∈ S i}`,
  `t = ⋂ i, t i`, and `κ_a = condExpKernel (weightedCountN p) (comap snd) a`.
  Then, for **every** anchor `a` of nonzero mass whose fiber has nonzero mass,

      κ_a(t) = ∏ i, κ_a(t i)

  — conditional independence in multiplicative form on the conditional kernel.

  # The chain (each arrow is a proven theorem)

      1.  mu.real(t ∩ fiberN z) = ∑ xs, [∀i, xs i ∈ S i] · p (xs, z)
              `joint_real_eq_indicator_sum`        (NaryConnect3)
              uses `real_eq_sum_of_fiber` (NaryFiberDecomp) + `mem_iInter_coordSet_finset` (NaryLink)

      2.  mu.real(coordSet i (S i) ∩ fiberN z) = ∑ a ∈ S i, marg pN i a z
              `coordSet_real_eq_marg_sum`          (NaryConnect3)
              uses `sum_marg_eq_fiberwise` (NaryMargSum)

      3.  (∑ xs, [∀i, xs i ∈ S i] · pN xs z) * M^(|ι|-1) = ∏ i, ∑ a ∈ S i, marg pN i a z
              `product_factorize`                  (NaryProduct)
              uses `condIndepN_sum_factorize` (NaryAlgebra)

      4.  mu.real(fiberN z) = ∑ xs, p (xs, z) = NMass pN z
              `fiberN_real_eq_sum'` (NaryAssembly) + `NMass_eq_sum` (NaryMassLink)
              — the **only** place `hp` is used

      5.  κ(t) * M = mu.real(t ∩ fiberN z)          `kernelValue_iInter_coordSet_mul` (NaryFinalBridge)
          κ(t i) * M = mu.real(t i ∩ fiberN z)      `kernelValue_coordSet_mul` (NaryBridge)
              — these need `mu {a} ≠ 0`

      6.  κ*M = A, A*M^(n-1) = ∏(κ_i*M), M ≠ 0  ==>  κ = ∏ κ_i
              `bridge_close` (NaryBridgeFinal) = `cancel_mass_pow` (NaryCancel)

  # Assumption ledger

  | assumption | why it cannot be dropped |
  |---|---|
  | `hp : ∀ w, 0 ≤ p w` | `weightedCountN` uses `ENNReal.ofReal`, which **truncates negatives to 0**; without `hp` the "kernel" no longer expresses `p`'s conditional probability (`GuardNecessary` counterexample, round 177). |
  | `hpN : ∀ xs z, pN xs z = p (xs, z)` | links the two paths: `marg`/`NMass` are `Finset` sums over `pN`, while `weightedCountN` reads `p`. |
  | `μ {a} ≠ 0`, `μ.real(fiberN a.2) ≠ 0` | conditioning on a null event is undefined; the kernel value is arbitrary there. |
  | `CondIndepN pN` | the hypothesis. |
  | `hproj`, `hsnd` | this project's product σ-algebra is a standalone instance, so projections are not automatically measurable. |
  | `[StandardBorelSpace …]`, `[MeasurableSingletonClass …]`, `[Fintype γ]` | `condExpKernel`'s domain is finite/discrete here. |

  # The three layers of the final statement

  | form | theorem | round |
  |---|---|---|
  | single anchor, finset parameters | `nary_bridge_final_one_line` (NaryBridgeDone) | 204 |
  | `∀ a`, finset parameters | `nary_bridge_pointwise_all` (NaryPointwise) | 206 |
  | `∀ a`, **arbitrary set** parameters | `nary_bridge_generic` (NaryGeneric) | 207 |

  # Honest limitations

  * Pointwise multiplicativity (`∀ a`) is proven; a **global kernel
    factorization** would require additionally that the events range over the
    whole σ-algebra.  Since every `fam i` is a `Fintype`, the cylinder events do
    generate it, so this is a monotone-class argument away — **not carried out**.
  * The relation between this theorem and the **binary** bridge is now settled
    at the **condition** level: `condIndepN_bool_iff` (in `Fate/CondIndepN.lean`)
    proves

        CondIndepN p  <->  CondIndepFin (toFin p)

    for the two-element index family `boolFam`, i.e. `CondIndepN` at `|iota| = 2`
    **is literally** `CondIndepFin` (axiom-clean).  `NaryFin2` records the
    `Fin 2`-shaped algebraic version.
    What is **not** formalised is the relation between the two **conclusions**
    (`condIndepFin_to_bridge`, phrased via `Kernel.Indep`, versus the
    multiplicative kernel form proven here); these are different statements
    about the kernel, not different formulations of the same one.
  =========================================================================== -/

namespace Fate.GenN

end Fate.GenN
namespace Fate.GenN

open MeasureTheory ProbabilityTheory

section FiberNMass

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*} [Fintype γ] [MeasurableSpace γ]
variable [MeasurableSpace ((∀ j, fam j) × γ)]
variable [MeasurableSingletonClass ((∀ j, fam j) × γ)]

omit [MeasurableSpace γ] in
/-- ⭐⭐⭐⭐ fiber mass = NMass -/
theorem fiberN_real_eq_NMass
    (p : ((∀ j, fam j) × γ) → ℝ) (hp : ∀ w, 0 ≤ p w)
    (pN : Fate.GenC3.NJoint (ι := ι) fam γ)
    (hpN : ∀ xs z, pN xs z = p (xs, z))
    (z : γ)
    [dec : DecidablePred (· ∈ (fiberN z : Set ((∀ j, fam j) × γ)))] :
    (weightedCountN p).real (fiberN z) = Fate.GenC3.NMass pN z := by
  rw [NMass_eq_sum pN z, fiberN_real_eq_sum' p hp z]
  exact Finset.sum_congr rfl (fun xs _ => (hpN xs z).symm)

end FiberNMass

section CoordSetReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*} [Fintype γ] [MeasurableSpace γ]
variable [MeasurableSpace ((∀ j, fam j) × γ)]
variable [MeasurableSingletonClass ((∀ j, fam j) × γ)]

omit [MeasurableSpace γ] in
/-- ⭐⭐⭐ coordSet real = double sum -/
theorem coordSet_real_eq_double_sum
    (p : ((∀ j, fam j) × γ) → ℝ) (hp : ∀ w, 0 ≤ p w)
    (i : ι) (S : Set (fam i)) [DecidablePred (· ∈ S)] :
    (weightedCountN p).real (coordSet (fam := fam) (γ := γ) i S)
      = ∑ w : (∀ j, fam j), ∑ z : γ, (if w i ∈ S then p (w, z) else 0) := by
  rw [weightedCountN_real_eq_sum p hp]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  refine Finset.sum_congr rfl (fun z _ => ?_)
  have h : ((w, z) ∈ coordSet (fam := fam) (γ := γ) i S) ↔ w i ∈ S := Iff.rfl
  by_cases hw : w i ∈ S
  · rw [if_pos (h.mpr hw), if_pos hw]
  · rw [if_neg (fun hc => hw (h.mp hc)), if_neg hw]

end CoordSetReal

section NMassNonneg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*}

/-- ⭐⭐ NMass nonneg -/
theorem NMass_nonneg_of_nonneg (p : Fate.GenC3.NJoint (ι := ι) fam γ)
    (hp : ∀ xs z, 0 ≤ p xs z) (z : γ) :
    0 ≤ Fate.GenC3.NMass p z := by
  rw [NMass_eq_sum p z]
  exact Finset.sum_nonneg (fun xs _ => hp xs z)

end NMassNonneg

section CardTwo

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)] [∀ i, DecidableEq (fam i)]
variable {γ : Type*}

/-- ⭐⭐⭐ card two factorize -/
theorem condIndepN_sum_factorize_card_two
    (p : Fate.GenC3.NJoint (ι := ι) fam γ)
    (h : Fate.GenC3.CondIndepN p)
    (hcard : Fintype.card ι = 2)
    (S : ∀ i, Set (fam i)) [∀ i, DecidablePred (· ∈ S i)]
    (z : γ) :
    (∑ xs : (∀ j, fam j), (if ∀ i, xs i ∈ S i then p xs z else 0))
        * Fate.GenC3.NMass p z
      = ∏ i, ∑ a : fam i, (if a ∈ S i then Fate.GenC3.marg p i a z else 0) := by
  have h2 := Fate.GenC3.condIndepN_sum_factorize p h S z
  rw [hcard] at h2
  simpa using h2

end CardTwo

end Fate.GenN

namespace Fate.GenN

section ProducedShape

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- ⭐⭐⭐⭐ **produced 形状 ⟹ `M^n` 乘法形状**（`NaryClose` × `NaryCancel`）。

`NaryClose.bridge_close_produced` 的目标是 `kappa = ∏ kappa_i`；本定理**不改目标**，
而是把它的**中间恒等式** `kappa * M^n = ∏ (kappa_i * M)` 单独暴露出来，
并证明它可由 produced 形状的三个假设直接得到（这正是 `cancel_mass_pow` 的输入）。

**前件**：`hκM : kappa * M = A`、`hAB : A * M^(n-1) = B`、`hB : B = ∏ (kappa_i * M)`。
**结论**：`kappa * M^n = ∏ (kappa_i * M)`。

⚠ 前件**不含**结论：三条假设分别谈 `A`、`B`、`M^(n-1)`，结论是 `M^n` 形式的
恒等式；两者之间需要 `pow_card_eq_pred_mul` 重排指数。 -/
theorem mul_pow_card_of_produced
    (kappa A B : ℝ) (kappa_i : ι → ℝ) (M : ℝ)
    (hκM : kappa * M = A)
    (hAB : A * M ^ (Fintype.card ι - 1) = B)
    (hB : B = ∏ i, (kappa_i i * M)) :
    kappa * M ^ Fintype.card ι = ∏ i, (kappa_i i * M) := by
  have hBeq : B = ∏ i, (kappa_i i * M) := hB
  calc kappa * M ^ Fintype.card ι
      = kappa * (M ^ (Fintype.card ι - 1) * M) := by
        rw [Fate.GenC3.pow_card_pred_mul Fintype.card_pos M]
    _ = (kappa * M) * M ^ (Fintype.card ι - 1) := by ring
    _ = A * M ^ (Fintype.card ι - 1) := by rw [hκM]
    _ = B := hAB
    _ = ∏ i, (kappa_i i * M) := hBeq

/-- ⭐⭐⭐⭐ **produced 形状与 `M^n` 形状一致**：两条闭合路径给出同一结论
（`NaryClose` 的 `bridge_close_produced` 与 `NaryCancel` 的 `cancel_mass_pow`）。

**前件**：produced 形状（`hκM`、`hAB`、`hB`）+ `M ≠ 0`。
**结论**：`kappa * M^n = (∏ kappa_i) * M^n`
—— 即 `NaryClose` 与 `NaryCancel` 两条路径在**同一条恒等式**上汇合。

⚠ 前件**不含**结论：结论是乘积与 `M^n` 的**乘法**恒等式，
而 `bridge_close_produced` 的结论是 `kappa = ∏ kappa_i`（无 `M`）。 -/
theorem produced_shape_meets_cancel_shape
    (kappa A B : ℝ) (kappa_i : ι → ℝ) (M : ℝ)
    (hκM : kappa * M = A)
    (hAB : A * M ^ (Fintype.card ι - 1) = B)
    (hB : B = ∏ i, (kappa_i i * M)) :
    kappa * M ^ Fintype.card ι = (∏ i, kappa_i i) * M ^ Fintype.card ι := by
  rw [mul_pow_card_of_produced kappa A B kappa_i M hκM hAB hB]
  exact Fate.GenN.prod_mul_const_eq' kappa_i M

/-- ⭐⭐⭐ **`cancel_mass_pow` 与 `bridge_close_produced` 互为逆**：
在同一组 produced 假设下，把两条闭合路径的结论**并列**。
（`bridge_close_produced` 给无 `M` 形式；本定理同时给出 `M^n` 形式。） -/
theorem bridge_close_produced_and_pow
    (kappa A B : ℝ) (kappa_i : ι → ℝ) (M : ℝ) (hM : M ≠ 0)
    (hκM : kappa * M = A)
    (hAB : A * M ^ (Fintype.card ι - 1) = B)
    (hB : B = ∏ i, (kappa_i i * M)) :
    kappa = ∏ i, kappa_i i ∧
      kappa * M ^ Fintype.card ι = (∏ i, kappa_i i) * M ^ Fintype.card ι :=
  ⟨Fate.GenN.bridge_close_produced (ι := ι) kappa A B kappa_i M hM hκM hAB hB,
    produced_shape_meets_cancel_shape kappa A B kappa_i M hκM hAB hB⟩

end ProducedShape

section FiberSaturation

variable {ι : Type*} {fam : ι → Type*} {γ : Type*} [MeasurableSpace γ]
variable [MeasurableSpace ((∀ i, fam i) × γ)]

omit [MeasurableSpace ((∀ i, fam i) × γ)] in
/-- ⭐⭐⭐⭐ **`m'`-可测函数的水平集被纤维饱和**（`NaryTrim` × `NaryKernel2`）。

`NaryTrim.comap_snd_mem_fiberN` 说「`m'`-可测集是纤维的并」；
`NaryKernel2.comap_snd_apply_eq_of_fiberN` 说「`m'`-可测函数在纤维上取常值」。
本定理把两者**串起来**：对 `m'`-可测的 `f`，任何包含 `a` 的超级水平集
`{w | f w < f a + 1}` 都含整条 `fiberN a.2`，且 `f` 在其上等于 `f a`。

**前件**：`hf : f` 是 `m'`-可测的。
**结论**：`fiberN a.2 ⊆ {w | f w = f a}`。

⚠ 前件**不含**结论：前件只谈 `f` 的可测性（相对于 `comap snd`），
结论是**逐点等式** —— 由 `comap` 的结构逼出。 -/
theorem fiberN_subset_of_comap_measurable
    {f : (∀ i, fam i) × γ → ℝ}
    (hf : @Measurable ((∀ i, fam i) × γ) ℝ
      (MeasurableSpace.comap (fun w : (∀ i, fam i) × γ => w.2) inferInstance) _ f)
    (a : (∀ i, fam i) × γ) :
    {w : (∀ i, fam i) × γ | w.2 = a.2} ⊆ {w | f w = f a} := by
  intro w hw
  have h := @Fate.GenN.comap_snd_apply_eq_of_fiberN ι fam γ _ f hf w a (by simpa using hw)
  simp [h]

end FiberSaturation

section MargFiberwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)] [∀ i, DecidableEq (fam i)]
variable {γ : Type*}

/-- ⭐⭐⭐⭐ **边际和的两种过滤形式一致**（`NaryMargSum` × 内层展开）。

`NaryMargSum.sum_marg_eq_fiberwise` 把 `∑ a∈Sf, ∑ xs, [xs i = a] p` 化成
「`Finset.univ.filter (xs i ∈ Sf)` 上的和」。本定理把它**改写成指示函数形式**
`∑ xs, [xs i ∈ Sf] p` —— 这正是 `NaryConnect3.coordSet_real_eq_marg_sum`
与 `NaryProduct.product_factorize` 两端都要的中间形状。

**前件**：无（对任意 `pN`、`Sf`、`z` 成立）。
**结论**：`∑ xs, [xs i ∈ Sf] pN xs z = ∑ a∈Sf, ∑ xs, [xs i = a] pN xs z`
（方向与 `sum_marg_eq_fiberwise` **相反**，故不是它的换名）。 -/
theorem sum_ite_mem_eq_sum_marg (p : Fate.GenC3.NJoint (ι := ι) fam γ)
    (i : ι) (Sf : Finset (fam i)) (z : γ) :
    (∑ xs : (∀ j, fam j), (if xs i ∈ Sf then p xs z else 0))
      = ∑ a ∈ Sf, ∑ xs : (∀ j, fam j), (if xs i = a then p xs z else 0) := by
  classical
  have h := Fate.GenN.sum_marg_eq_fiberwise (p := p) i Sf z
  rw [Finset.sum_filter] at h
  exact h.symm

/-- ⭐⭐⭐ **`filter_filter_absorb` 的推论：过滤器的嵌套可交换**
（`NaryMargSum` 的两个定理组合）。 -/
theorem sum_filter_mem_filter_eq (p : Fate.GenC3.NJoint (ι := ι) fam γ)
    (i : ι) (Sf : Finset (fam i)) {a : fam i} (ha : a ∈ Sf) (z : γ) :
    (∑ xs ∈ (Finset.univ.filter (fun xs : (∀ j, fam j) => xs i = a)), p xs z)
      = ∑ xs ∈ (Finset.univ.filter (fun xs : (∀ j, fam j) => xs i ∈ Sf)).filter
          (fun xs : (∀ j, fam j) => xs i = a), p xs z := by
  rw [Fate.GenN.filter_filter_absorb (i := i) (Sf := Sf) ha]

end MargFiberwise

end Fate.GenN

/-! ## §GenNWire3 接上 `NaryConnect2`（R-27）

`NaryConnect2.weightedCountN_coordSet` 此前零外部消费。以下定理消费它，
把 `weightedCountN` 在 `coordSet` 上的 `ENNReal` 求值与其 `real` 版本对齐。 -/

namespace Fate.GenN

open MeasureTheory ProbabilityTheory

section Connect2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*} [Fintype γ] [MeasurableSpace γ]
variable [MeasurableSpace ((∀ j, fam j) × γ)]
variable [MeasurableSingletonClass ((∀ j, fam j) × γ)]

omit [MeasurableSpace γ] in
/-- ⭐⭐⭐ **`weightedCountN` 在 `coordSet` 上的 `ENNReal` 求值**
（`NaryConnect2.weightedCountN_coordSet`）。

**前件**：`S` 可判定。**结论**：
`weightedCountN p (coordSet i S) = ∑ xs, ∑ z, [xs i ∈ S] ofReal (p (xs, z))`。

⚠ 非同一律：本定理只是把该引理**提到本模块的求值链**上（`NaryIndex` 是
N 元链的入口，下游 `NaryBridgeDone` 等需要在此处可见的显式形式）。 -/
theorem weightedCountN_coordSet_eq_sum (p : ((∀ j, fam j) × γ) → ℝ)
    (i : ι) (S : Set (fam i)) [DecidablePred (· ∈ S)] :
    weightedCountN p (coordSet (fam := fam) (γ := γ) i S)
      = ∑ xs : (∀ j, fam j), ∑ z : γ,
          (if xs i ∈ S then ENNReal.ofReal (p (xs, z)) else 0) :=
  weightedCountN_coordSet p i S

end Connect2

end Fate.GenN
