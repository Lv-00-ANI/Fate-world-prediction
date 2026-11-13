import FateWorld.Legacy.NaryBridgeFinal
import FateWorld.Legacy.NaryConnect3
import FateWorld.Legacy.NaryAssembly
import FateWorld.Legacy.NaryMassLink
import FateWorld.Legacy.NaryProduct
import FateWorld.Legacy.NaryCancel
import Mathlib.Data.Fintype.Pi
/-! ===========================================================================
  §fin_Q0   ⭐⭐⭐⭐⭐ **N 元桥的最终定理（一句话）**

  ## 最终陈述

  令 `p` 为 `(∀ i, fam i) × γ` 上的非负权（**未归一**），`pN xs z = p (xs, z)`
  且 `CondIndepN pN`（`{X_i}_{i ∈ ι}` 在给定 `Z` 下条件独立），
  `Sf i ⊆ fam i` 有限，`a : (∀ i, fam i) × γ` 且 `μ {a} ≠ 0`。
  记

  * `κ_a := condExpKernel (weightedCountN p) (comap snd) a`（条件核）
  * `t_i := coordSet i ↑(Sf i)`，`t := ⋂ i, t_i`
  * `M  := μ.real (fiberN a.2)`（纤维质量 = `NMass pN a.2`）

  则
  ```
  κ_a(t) = ∏ i, κ_a(t_i)
  ```
  即 **「复合坐标事件的信息 = 各坐标事件信息之积」**
  —— 条件独立在**条件核**上的乘性形式。

  ## 组装（全部来自既有部件，本文件只做接线）

  | 步 | 内容 | 引理 |
  |---|---|---|
  | `hi` | `κ_a(t_i) * M = ∑ a ∈ Sf i, marg pN i a a.2` | `kernelValue_coordSet_mul` + `coordSet_real_eq_marg_sum` |
  | `hj` | `κ_a(t) * M^n = ∏ i, ∑ a ∈ Sf i, marg pN i a a.2` | `kernelValue_iInter_coordSet_mul` + `joint_real_eq_indicator_sum` + `product_factorize` + `fiberN_real_eq_sum'` + `NMass_eq_sum` |
  | 收尾 | `A * M^n = ∏ i, (B i * M) ⟹ A = ∏ i, B i` | `bridge_close`（= `cancel_mass_pow`） |

  ## 假设账（诚实清单）

  * `hp : ∀ w, 0 ≤ p w` —— **不可去**：`weightedCountN` 用 `ENNReal.ofReal`，
    负值被截断为 0（`GuardNecessary` 的反例）。
  * `hpN : ∀ xs z, pN xs z = p (xs, z)` —— 两条路径（`marg`/`NMass` 走 `pN`，
    `weightedCountN` 走 `p`）的连接。
  * `hμa : μ {a} ≠ 0` —— 核值公式的守卫（等价于 `M ≠ 0`，见 `bridge_close` 的 `hM`）。
  * `hproj` / `hsnd` —— 可测性（本项目的乘积 σ-代数是独立实例，无法自动得到）。
  * `[StandardBorelSpace …]`、`[MeasurableSingletonClass …]`、`[Fintype γ]`、
    `[∀ i, MeasurableSingletonClass (fam i)]` —— 只因 `condExpKernel` 的定义域是有限/离散。

  **无 `sorry` / `admit` / `axiom`。**
  =========================================================================== -/

namespace Fate.GenN

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {fam : ι → Type*} [∀ i, Fintype (fam i)] [∀ i, DecidableEq (fam i)]
variable {γ : Type*} [Fintype γ] [DecidableEq γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
variable [∀ i, MeasurableSpace (fam i)] [∀ i, MeasurableSingletonClass (fam i)]
variable [MeasurableSpace ((∀ j, fam j) × γ)]
variable [MeasurableSingletonClass ((∀ j, fam j) × γ)]
variable [StandardBorelSpace ((∀ j, fam j) × γ)]

/-! ## §1 可判定性胶水（`fiberN` 是 `def`，tc 搜索不展开它） -/

/-- `(⋂ i, coordSet i ↑(Sf i)) ∩ fiberN z` 上的可判定性。 -/
@[instance_reducible]
def jointCoordFiberDec (Sf : ∀ i, Finset (fam i)) (z : γ) :
    DecidablePred (· ∈ ((⋂ i, coordSet (fam := fam) (γ := γ) i ((Sf i : Set (fam i))))
      ∩ fiberN z : Set ((∀ j, fam j) × γ))) := by
  have hiff : ∀ w : (∀ j, fam j) × γ,
      (w ∈ ((⋂ i, coordSet (fam := fam) (γ := γ) i ((Sf i : Set (fam i)))) ∩ fiberN z
        : Set ((∀ j, fam j) × γ))) ↔ (∀ i, w.1 i ∈ Sf i) ∧ w.2 = z := by
    intro w
    simp [coordSet, fiberN, Set.mem_iInter]
  intro w
  exact decidable_of_iff ((∀ i, w.1 i ∈ Sf i) ∧ w.2 = z) (hiff w).symm

/-- `fiberN z` 上的可判定性。 -/
@[instance_reducible]
def fiberNDecPred (z : γ) :
    DecidablePred (· ∈ (fiberN z : Set ((∀ j, fam j) × γ))) := by
  intro w; unfold fiberN; infer_instance

/-! ## §2 ⭐ `hi`：单坐标的核值恒等式 -/

omit [Nonempty ι] in
/-- ⭐⭐⭐ **`hi`**：对 **每个** `i`，
`κ_a(coordSet i ↑(Sf i)) * M = ∑ a ∈ Sf i, marg pN i a a.2`。

由 `kernelValue_coordSet_mul`（测度层）与 `coordSet_real_eq_marg_sum`
（测度层 → 代数层）串联而得。 -/
theorem kernel_coord_mul_eq_marg_sum
    (p : ((∀ j, fam j) × γ) → ℝ) (hp : ∀ w, 0 ≤ p w)
    (pN : Fate.GenC3.NJoint (ι := ι) fam γ)
    (hlink : ∀ xs z, pN xs z = p (xs, z))
    (hproj : ∀ i, Measurable (fun w : (∀ j, fam j) × γ => w.1 i))
    (hsnd : Measurable (fun w : (∀ j, fam j) × γ => w.2))
    (Sf : ∀ i, Finset (fam i))
    (a : (∀ j, fam j) × γ)
    (hμa : (weightedCountN p) {a} ≠ 0) :
    letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
    ∀ i : ι,
      ((condExpKernel (Ω := (∀ j, fam j) × γ) (weightedCountN p)
        (MeasurableSpace.comap (fun w : (∀ j, fam j) × γ => w.2) inferInstance)) a).real
          (coordSet (fam := fam) (γ := γ) i ((Sf i : Set (fam i))))
        * ((weightedCountN p).real (fiberN a.2))
      = ∑ x ∈ Sf i, Fate.GenC3.marg pN i x a.2 := by
  letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
  intro i
  have h1 := kernelValue_coordSet_mul (fam := fam) (γ := γ) p i ((Sf i : Set (fam i)))
    (Finset.measurableSet (Sf i)) (hproj i) hsnd a hμa
  haveI : DecidablePred (· ∈ (coordSet (fam := fam) (γ := γ) i ((Sf i : Set (fam i)))
      : Set ((∀ j, fam j) × γ))) := by
    intro w; unfold coordSet; infer_instance
  haveI : DecidablePred (· ∈ (coordSet (fam := fam) (γ := γ) i ((Sf i : Set (fam i)))
      ∩ fiberN a.2 : Set ((∀ j, fam j) × γ))) := by
    intro w; unfold coordSet fiberN; infer_instance
  have h2 := coordSet_real_eq_marg_sum (fam := fam) (γ := γ) pN p hp hlink i (Sf i) a.2
  rw [h1, h2]

/-! ## §3 ⭐ `hj`：联合的核值恒等式 -/

/-- ⭐⭐⭐⭐ **`hj`**：`κ_a(⋂ i, t_i) * M^n = ∏ i, ∑ a ∈ Sf i, marg pN i a a.2`。

由 `kernelValue_iInter_coordSet_mul`（测度层）、`joint_real_eq_indicator_sum`
（测度层 → 指示和）、`product_factorize`（代数因子化）、
`fiberN_real_eq_sum'` + `NMass_eq_sum`（`M = NMass pN a.2`）串联而得。 -/
theorem kernel_iInter_mul_eq_prod_marg_sum
    (p : ((∀ j, fam j) × γ) → ℝ) (hp : ∀ w, 0 ≤ p w)
    (pN : Fate.GenC3.NJoint (ι := ι) fam γ)
    (hpN : ∀ xs z, pN xs z = p (xs, z))
    (hcond : Fate.GenC3.CondIndepN pN)
    (hproj : ∀ i, Measurable (fun w : (∀ j, fam j) × γ => w.1 i))
    (hsnd : Measurable (fun w : (∀ j, fam j) × γ => w.2))
    (Sf : ∀ i, Finset (fam i))
    (a : (∀ j, fam j) × γ)
    (hμa : (weightedCountN p) {a} ≠ 0) :
    letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
    ((condExpKernel (Ω := (∀ j, fam j) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ j, fam j) × γ => w.2) inferInstance)) a).real
        (⋂ i, coordSet (fam := fam) (γ := γ) i ((Sf i : Set (fam i))))
      * ((weightedCountN p).real (fiberN a.2)) ^ Fintype.card ι
      = ∏ i, ∑ x ∈ Sf i, Fate.GenC3.marg pN i x a.2 := by
  letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
  set M : ℝ := (weightedCountN p).real (fiberN a.2) with hMdef
  set A : ℝ := ∑ xs : (∀ j, fam j),
      (if ∀ i, xs i ∈ Sf i then p (xs, a.2) else 0) with hAdef
  set B : ℝ := ∏ i, ∑ x ∈ Sf i, Fate.GenC3.marg pN i x a.2 with hBdef
  -- (1) 核值 × `M` = `μ(t ∩ fiberN)`
  have h1 := kernelValue_iInter_coordSet_mul (fam := fam) (γ := γ) p
    (fun i => (Sf i : Set (fam i))) (fun i => Finset.measurableSet (Sf i)) hproj hsnd a hμa
  -- (2) `μ(t ∩ fiberN a.2) = ∑ xs, [∀ i, xs i ∈ Sf i] p (xs, a.2)`
  have h2 : (weightedCountN p).real
      ((⋂ i, coordSet (fam := fam) (γ := γ) i ((Sf i : Set (fam i)))) ∩ fiberN a.2) = A := by
    haveI : DecidablePred (· ∈ ((⋂ i, coordSet (fam := fam) (γ := γ) i
        ((Sf i : Set (fam i)))) ∩ fiberN a.2 : Set ((∀ j, fam j) × γ))) :=
      jointCoordFiberDec Sf a.2
    have hbase := joint_real_eq_indicator_sum (fam := fam) (γ := γ) p hp Sf a.2
    rw [hbase, hAdef]
  -- (3) `M = NMass pN a.2`
  haveI : DecidablePred (· ∈ (fiberN a.2 : Set ((∀ j, fam j) × γ))) := fiberNDecPred a.2
  have h3 : M = Fate.GenC3.NMass pN a.2 := by
    rw [hMdef, fiberN_real_eq_sum' p hp a.2, Fate.GenN.NMass_eq_sum]
    exact Finset.sum_congr rfl (fun xs _ => (hpN xs a.2).symm)
  -- (4) 代数因子化 `A * M^(n-1) = B`
  have h4 : A * M ^ (Fintype.card ι - 1) = B := by
    rw [hAdef, hBdef]
    have hbase := product_factorize pN hcond Sf a.2
    rw [← h3] at hbase
    have hsum : (∑ xs : (∀ j, fam j), (if ∀ i, xs i ∈ Sf i then p (xs, a.2) else 0))
        = ∑ xs : (∀ j, fam j), (if ∀ i, xs i ∈ Sf i then pN xs a.2 else 0) := by
      refine Finset.sum_congr rfl (fun xs _ => ?_)
      rw [hpN xs a.2]
    rw [hsum]
    exact hbase
  -- 组合：`κ(t) * M = A`，再升到 `M^n`
  have hκM : ((condExpKernel (Ω := (∀ j, fam j) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ j, fam j) × γ => w.2) inferInstance)) a).real
        (⋂ i, coordSet (fam := fam) (γ := γ) i ((Sf i : Set (fam i)))) * M = A := by
    rw [h1, h2]
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos
  set κ : ℝ := ((condExpKernel (Ω := (∀ j, fam j) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ j, fam j) × γ => w.2) inferInstance)) a).real
        (⋂ i, coordSet (fam := fam) (γ := γ) i ((Sf i : Set (fam i)))) with hκdef
  have hκM' : κ * M = A := hκM
  calc κ * M ^ Fintype.card ι
      = κ * (M ^ (Fintype.card ι - 1) * M) := by
        rw [Fate.GenC3.pow_card_pred_mul hcard M]
    _ = (κ * M) * M ^ (Fintype.card ι - 1) := by ring
    _ = A * M ^ (Fintype.card ι - 1) := by rw [hκM']
    _ = B := h4

/-! ## §4 ⭐⭐⭐⭐⭐ 最终定理（一句话） -/

/-- ⭐⭐⭐⭐⭐ **N 元桥最终定理**。

在 `p ≥ 0`、`pN xs z = p (xs, z)`、`CondIndepN pN` 下，
条件核 `κ = condExpKernel μ (comap snd)` 在**复合坐标事件**
`t = ⋂ i, coordSet i ↑(Sf i)` 上的值是**各坐标值之积**：

```
κ_a(⋂ i, coordSet i ↑(Sf i)) = ∏ i, κ_a(coordSet i ↑(Sf i))
```

**这是 `hi` / `hj` 经 `bridge_close` 的一行收尾**：
取 `kappa := κ_a(t)`、`kappa_i := fun i => κ_a(t_i)`、
`b i := ∑ a ∈ Sf i, marg pN i a a.2`、`M := μ.real (fiberN a.2)`。 -/
theorem nary_bridge_final_one_line
    (p : ((∀ j, fam j) × γ) → ℝ) (hp : ∀ w, 0 ≤ p w)
    (pN : Fate.GenC3.NJoint (ι := ι) fam γ)
    (hpN : ∀ xs z, pN xs z = p (xs, z))
    (hcond : Fate.GenC3.CondIndepN pN)
    (hproj : ∀ i, Measurable (fun w : (∀ j, fam j) × γ => w.1 i))
    (hsnd : Measurable (fun w : (∀ j, fam j) × γ => w.2))
    (Sf : ∀ i, Finset (fam i))
    (a : (∀ j, fam j) × γ)
    (hμa : (weightedCountN p) {a} ≠ 0)
    (hM : (weightedCountN p).real (fiberN a.2) ≠ 0) :
    letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
    ((condExpKernel (Ω := (∀ j, fam j) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ j, fam j) × γ => w.2) inferInstance)) a).real
        (⋂ i, coordSet (fam := fam) (γ := γ) i ((Sf i : Set (fam i))))
      = ∏ i, ((condExpKernel (Ω := (∀ j, fam j) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ j, fam j) × γ => w.2) inferInstance)) a).real
        (coordSet (fam := fam) (γ := γ) i ((Sf i : Set (fam i)))) := by
  letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
  exact bridge_close
    (((condExpKernel (Ω := (∀ j, fam j) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ j, fam j) × γ => w.2) inferInstance)) a).real
        (⋂ i, coordSet (fam := fam) (γ := γ) i ((Sf i : Set (fam i)))))
    (fun i => ((condExpKernel (Ω := (∀ j, fam j) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ j, fam j) × γ => w.2) inferInstance)) a).real
        (coordSet (fam := fam) (γ := γ) i ((Sf i : Set (fam i)))))
    (fun i => ∑ x ∈ Sf i, Fate.GenC3.marg pN i x a.2)
    ((weightedCountN p).real (fiberN a.2))
    hM
    (fun i => kernel_coord_mul_eq_marg_sum p hp pN hpN hproj hsnd Sf a hμa i)
    (kernel_iInter_mul_eq_prod_marg_sum p hp pN hpN hcond hproj hsnd Sf a hμa)

/-- ⭐⭐⭐⭐ **最终定理（除法律形式）**：右端写成
`(∏ i, ∑ a ∈ Sf i, marg pN i a a.2) / M^n`。

与 `nary_bridge_final_one_line` 等价（`M ≠ 0` 时），
但把「各坐标条件边缘和」显式化 —— 这就是桥的**可计算**形式。 -/
theorem nary_bridge_final_div
    (p : ((∀ j, fam j) × γ) → ℝ) (hp : ∀ w, 0 ≤ p w)
    (pN : Fate.GenC3.NJoint (ι := ι) fam γ)
    (hpN : ∀ xs z, pN xs z = p (xs, z))
    (hcond : Fate.GenC3.CondIndepN pN)
    (hproj : ∀ i, Measurable (fun w : (∀ j, fam j) × γ => w.1 i))
    (hsnd : Measurable (fun w : (∀ j, fam j) × γ => w.2))
    (Sf : ∀ i, Finset (fam i))
    (a : (∀ j, fam j) × γ)
    (hμa : (weightedCountN p) {a} ≠ 0)
    (hM : (weightedCountN p).real (fiberN a.2) ≠ 0) :
    letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
    ((condExpKernel (Ω := (∀ j, fam j) × γ) (weightedCountN p)
      (MeasurableSpace.comap (fun w : (∀ j, fam j) × γ => w.2) inferInstance)) a).real
        (⋂ i, coordSet (fam := fam) (γ := γ) i ((Sf i : Set (fam i))))
      = (∏ i, ∑ x ∈ Sf i, Fate.GenC3.marg pN i x a.2)
          / ((weightedCountN p).real (fiberN a.2)) ^ Fintype.card ι := by
  letI : IsFiniteMeasure (weightedCountN p) := weightedCountN_isFiniteMeasure p
  have hkey := kernel_iInter_mul_eq_prod_marg_sum p hp pN hpN hcond hproj hsnd Sf a hμa
  rw [eq_div_iff (pow_ne_zero _ hM)]
  exact hkey

end Fate.GenN
