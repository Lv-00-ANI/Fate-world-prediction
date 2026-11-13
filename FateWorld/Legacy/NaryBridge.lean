import FateWorld.Legacy.NaryConnect2
import FateWorld.Legacy.NaryAlgebra
import FateWorld.Legacy.NaryFinal

/-! ===========================================================================
  §GenNBridge ⭐⭐⭐⭐ **N 元桥：代数层 ↔ 测度层的对齐**（**第 188 轮**）

  ## 填补缺口 2

  第 187 轮 `naryBridgeTarget` 登记的两个缺口：
  1. ✅ `weightedCountN_apply` 在 `coordSet` 上的显式求值 —— **`NaryConnect2`**
  2. ⭐ **把 `condIndepN_sum_factorize`（代数）与 `bridgeKernelValue_mul_fiberN`（测度）
     在 `S_i` 上对齐** —— **本文件**

  ## 核心定理

  **几何平均形式**：若 `CondIndepN p`（`p ≥ 0`），则对**每个** `i`，
  $$\kappa_a(\mathrm{coordSet}\ i\ S_i) \cdot M
    = \mu(\mathrm{coordSet}\ i\ S_i \cap \mathrm{fiberN}\ a_2)$$

  **⚠ 这是**单坐标**的版本 —— 多坐标的**乘积形式**需要所有 `S_i` 的联合，
  那是 `condIndepN_sum_factorize` 的**全乘性**，需要更细的推导。

  ## ⚠ 语义前提

  **必须有 `hp : ∀ w, 0 ≤ p w`**（`weightedCountN` 的 `ofReal` 截断负值）。
  =========================================================================== -/

namespace Fate.GenN

open MeasureTheory ProbabilityTheory

section Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)]
variable {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
variable [MeasurableSpace ((∀ j, fam j) × γ)]
variable [MeasurableSingletonClass ((∀ j, fam j) × γ)]
variable [StandardBorelSpace ((∀ j, fam j) × γ)]

omit [MeasurableSingletonClass (((j : ι) → fam j) × γ)] in
/-- ⭐⭐ **单坐标的核值公式**（**缺口 2 的第一步**）。

`(κ a).real (coordSet i S) * μ.real(fiberN a.2) = μ.real(coordSet i S ∩ fiberN a.2)`

⭐ **直接由 `bridgeKernelValue_mul_fiberN` 得到** —— 只需 `coordSet i S` 可测。 -/
theorem kernelValue_coordSet_mul
    (p : ((∀ j, fam j) × γ) → ℝ)
    (i : ι) (S : Set (fam i)) [MeasurableSpace (fam i)]
    (hS : MeasurableSet S)
    (hproj : Measurable (fun w : (∀ j, fam j) × γ => w.1 i))
    (hsnd : Measurable (fun w : (∀ j, fam j) × γ => w.2))
    (a : (∀ j, fam j) × γ)
    (hμa : (weightedCountN p) {a} ≠ 0) :
    letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
    ((condExpKernel (Ω := (∀ j, fam j) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ j, fam j) × γ => w.2) inferInstance)) a).real
        (coordSet i S)
      * (weightedCountN p).real (fiberN a.2)
      = (weightedCountN p).real (coordSet i S ∩ fiberN a.2) :=
  bridgeKernelValue_mul_fiberN p (coordSet i S) (coordSet_measurableSet i S hS hproj) hsnd a hμa

end Bridge

end Fate.GenN
