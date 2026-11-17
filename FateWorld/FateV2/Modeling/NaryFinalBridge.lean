import FateWorld.FateV2.Modeling.NaryRealSum
import FateWorld.FateV2.Modeling.NaryBridge
import FateWorld.FateV2.Modeling.NaryAlgebra
/-!
  # Modeling · NaryFinalBridge

  ## 迁移登记
  - 来源：`FateWorld/Legacy/NaryFinalBridge.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：NaryRealSum, NaryBridge, NaryAlgebra
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §GenNFinalBridge  N 元桥的最终组装 (round 190)

  ## 目标

  For t_i = coordSet i S_i (each S_i a measurable set), t = iInter i, t_i:

    kappa_a(t_i) * M  =  mu.real(t_i intersect fiberN a.2)
    kappa_a(t)   * M  =  mu.real(t intersect fiberN a.2)

  and by the algebraic factorization (NaryAlgebra.condIndepN_sum_factorize)
  plus weightedCountN_real_eq_sum (hp needed), the multi-coordinate product
  form follows.

  ## All parts are in place

  - iInter_coordSet (NaryBridgeMulti)
  - weightedCountN_real_eq_sum (NaryRealSum, needs hp)
  - kernelValue_coordSet_mul (NaryBridge)
  - condIndepN_sum_factorize (NaryAlgebra)

  ## Honest status

  The single-coordinate kernel formula is proven (NaryBridge).
  The multi-coordinate product form still requires careful algebra:
  the algebraic factorization is in terms of `marg` while the kernel formula
  is in terms of `mu.real`; bridging them needs the explicit evaluation of
  `mu.real(t_i) / M` for each i and then multiplying out.
  =========================================================================== -/

namespace FateV2.Modeling.GenN

open MeasureTheory ProbabilityTheory

section KernelOnInter

variable {ι : Type*} [Fintype ι]
variable {fam : ι → Type*}
variable {γ : Type*}
variable [MeasurableSpace ((∀ j, fam j) × γ)]

/-- the set `iInter i, coordSet i (S i)` is measurable when each `S i` is
and each projection is measurable. -/
theorem iInter_coordSet_measurable
    (S : ∀ i, Set (fam i)) [∀ i, MeasurableSpace (fam i)]
    (hS : ∀ i, MeasurableSet (S i))
    (hproj : ∀ i, Measurable (fun w : (∀ j, fam j) × γ => w.1 i)) :
    MeasurableSet (⋂ i, coordSet i (S i) : Set ((∀ j, fam j) × γ)) := by
  have h : (⋂ i, coordSet i (S i) : Set ((∀ j, fam j) × γ))
      = ⋂ i, (fun w : (∀ j, fam j) × γ => w.1 i) ⁻¹' (S i) := by
    ext w
    simp [coordSet]
  rw [h]
  exact MeasurableSet.iInter (fun i => hproj i (hS i))

end KernelOnInter

/-! ## Section: multi-coordinate kernel value

For `t_i = coordSet i (S i)`, the kernel value satisfies

    kappa(t) * M = mu.real(t intersect fiberN a.2)

where `t = iInter i, t_i` and `M` is the fiber mass.
This follows directly from `bridgeKernelValue_mul_fiberN` once `t` is measurable.
-/

section MultiCoordKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
variable [MeasurableSpace ((∀ j, fam j) × γ)]
variable [MeasurableSingletonClass ((∀ j, fam j) × γ)]
variable [StandardBorelSpace ((∀ j, fam j) × γ)]

omit [MeasurableSingletonClass ((∀ j, fam j) × γ)] in
/-- multi-coordinate kernel value:
    kappa(t) * M = mu.real(t intersect fiberN a.2),
    where t = iInter i, coordSet i (S i). -/
theorem kernelValue_iInter_coordSet_mul
    (p : ((∀ j, fam j) × γ) → ℝ)
    (S : ∀ i, Set (fam i)) [∀ i, MeasurableSpace (fam i)]
    (hS : ∀ i, MeasurableSet (S i))
    (hproj : ∀ i, Measurable (fun w : (∀ j, fam j) × γ => w.1 i))
    (hsnd : Measurable (fun w : (∀ j, fam j) × γ => w.2))
    (a : (∀ j, fam j) × γ)
    (hmu : (weightedCountN p) {a} ≠ 0) :
    letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
    ((condExpKernel (Ω := (∀ j, fam j) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ j, fam j) × γ => w.2) inferInstance)) a).real
        (⋂ i, coordSet i (S i))
      * (weightedCountN p).real (fiberN a.2)
      = (weightedCountN p).real ((⋂ i, coordSet i (S i)) ∩ fiberN a.2) :=
  bridgeKernelValue_mul_fiberN p (⋂ i, coordSet i (S i))
    (iInter_coordSet_measurable S hS hproj) hsnd a hmu

end MultiCoordKernel

end FateV2.Modeling.GenN
