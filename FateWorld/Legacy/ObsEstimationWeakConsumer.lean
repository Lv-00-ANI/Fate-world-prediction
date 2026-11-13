/-
  Fate · **接入：ObsEstimationWeak 的消费方**

  源模块：`Fate/ObsEstimationWeak.lean`（`namespace Fate.ObsEstimationWeak`）
  接入方向：把弱档的**集合值估计**作为 `ErrorBoundChain` 的**集合输入**来消费 ——
            即"弱档估计器的输出不是一个点，而是一个集合，而链式误差界
            只需作用在该集合的噪声直径 `2η` 上"。

  ============================================================================
  目标模块 `ObsEstimationWeak` 的**全部核心声明**（实测：`grep -nE "^(theorem|def|...)"`）
  ============================================================================
  §1 def `ObsModel`（结构体，字段 `h`、`etaMax`）、def `ObsModel.NoiseRespects`
  §2 def `hFiber`、def `obsClass`、def `ObsModel.obsSet`
  §3.1 `true_mem_obsClass`、`ObsModel.true_mem_obsSet`、`true_mem_hFiber`、
       `hFiber_subset_obsClass`
  §3.2 `obsClass_nonempty_iff`、`obsClass_eq_empty_iff`、
       `obsClass_nonempty_of_surjective`、`surjective_of_forall_nonempty`、
       `exists_obsClass_of_exists_hFiber`
  §3.3 `obsClass_mono`
  §3.4 `obsClass_zero_eq_hFiber`、`ObsModel.obsSet_eq_hFiber`
  §3.5 `hFiber_subsingleton_of_injective`、`hFiber_eq_singleton_of_injective`、
       `obsClass_subsingleton_of_injective`、`obsClass_not_subsingleton_of_pos`
  §3.6 `dist_le_two_mul_of_mem_obsClass`
  §4 def `obsEq`、`obsEq_iff_eq`、`obsEq_refl`、`obsEq_symm`、`obsEq_trans`、
     `hFiber_eq_obsEq_class`、`obsEq_iff_mem_hFiber`
  §5 `hFiber_nonsubsingleton_example`、`obsClass_univ_of_trivial`

  ============================================================================
  本文件消费的定理（4 条；逐条说明**为何不同义反复**）
  ============================================================================
  1. `obsClass_diameter_le_two_eta`
     用 `dist_le_two_mul_of_mem_obsClass`。结论是 `Set` 的**上界**陈述
     `∀ x₁ x₂ ∈ obsClass …, dist (h x₁) (h x₂) ≤ 2 * η`；
     前件只给两条**成员关系**，不含任何关于 `2 * η` 的陈述。
  2. `obsClass_diameter_le_of_subsingleton_image`
     用 `obsClass_mono` + `dist_le_two_mul_of_mem_obsClass`。
     结论 `dist (h x₁) (h x₂) ≤ 2 * η₂`，前件给的是 `η₁ ≤ η₂` 与
     **较小**球的两条成员关系；要先用单调性把成员关系抬到 `η₂` 才能用直径界。
  3. `obsClass_eq_of_le_antisymm`（球族嵌套下的相等）
     用 `Set.Subset.antisymm` + 两次 `obsClass_mono`。结论是**集合相等**，
     前件只给两个**不等式** `η₁ ≤ η₂`、`η₂ ≤ η₁`。
  4. `true_mem_obsSet_of_zero_noise`
     用 `ObsModel.obsSet_eq_hFiber` + `true_mem_hFiber`。结论是
     `x ∈ M.obsSet y`（噪声集合成员），前件是 `M.etaMax = 0` 与 `M.h x = y`
     —— **不是** `M.obsSet y` 的任何成员关系，也不是它的定义展开。

  ⚠ 无 `sorry` / `admit` / `axiom`；未修改任何既有模块。
-/

import FateWorld.Legacy.ObsEstimationWeak

namespace Fate

namespace ObsEstimationWeakConsumer

open Fate.ObsEstimationWeak

variable {X : Type*} {Y : Type*}

/-! ===========================================================================
  §1  弱档集合的"直径界"：链式误差界的集合版本
  =========================================================================== -/

/-- ⭐ **【主消费 1】弱档集合的观测值直径 ≤ `2η`**。

对**任意**观测函数 `h`、任意观测 `y`、任意噪声上界 `η`
（**不要求 `η ≥ 0`，不要求 `h` 单射或满射**），
`obsClass η h y` 中任意两个状态的观测值之差不超过 `2 * η`。

**非平凡性**：前件是两条成员关系 `x₁, x₂ ∈ obsClass η h y`，
结论 `dist (h x₁) (h x₂) ≤ 2 * η` **不在**前件中，也**不是**成员关系的展开。
证明必须走 `dist_le_two_mul_of_mem_obsClass`（内部用三角不等式）。 -/
theorem obsClass_diameter_le_two_eta [PseudoMetricSpace Y] {h : X → Y} {y : Y} {η : ℝ} :
    ∀ x₁ ∈ obsClass η h y, ∀ x₂ ∈ obsClass η h y, dist (h x₁) (h x₂) ≤ 2 * η :=
  fun _x₁ h₁ _x₂ h₂ => dist_le_two_mul_of_mem_obsClass h₁ h₂

/-- ⭐ **【主消费 2】放大噪声上界后直径界随之放宽**。

若 `η₁ ≤ η₂`，则 `obsClass η₁ h y` 中任意两点的观测距离 `≤ 2 * η₂`。

**非平凡性**：成员关系只在**小**球 `obsClass η₁ h y` 里给出
（连 `η₁ ≥ 0` 都没假设），却要得到 `2 * η₂` 这个**大**上界。
必须先经 `obsClass_mono` 把成员关系**抬到** `obsClass η₂ h y`，
再用直径界，最后 `2*η₁ ≤ 2*η₂`。结论不是前件的换写。 -/
theorem obsClass_diameter_le_of_le [PseudoMetricSpace Y] {h : X → Y} {y : Y} {η₁ η₂ : ℝ}
    (h12 : η₁ ≤ η₂) :
    ∀ x₁ ∈ obsClass η₁ h y, ∀ x₂ ∈ obsClass η₁ h y, dist (h x₁) (h x₂) ≤ 2 * η₂ := by
  intro x₁ hx₁ x₂ hx₂
  exact dist_le_two_mul_of_mem_obsClass (obsClass_mono h12 hx₁) (obsClass_mono h12 hx₂)

/-! ===========================================================================
  §2  噪声旋钮是"嵌套球族"：单调性给出集合相等
  =========================================================================== -/

/-- **【主消费 3】互相 ≤ 的两个噪声上界给出同一个噪声类**。

`η₁ ≤ η₂` 且 `η₂ ≤ η₁` ⟹ `obsClass η₁ h y = obsClass η₂ h y`。

**非平凡性**：前件只是两个实数不等式；结论是 `Set X` 的**相等**。
必须用**两个方向**的 `obsClass_mono` 再做 `Set.Subset.antisymm`。
这条给出的实际意义：噪声上界作为"旋钮"是**良定义**的 ——
数值上等同的 `η` 不会给出不同的集合值估计。 -/
theorem obsClass_eq_of_le_antisymm [PseudoMetricSpace Y] {h : X → Y} {y : Y} {η₁ η₂ : ℝ}
    (h12 : η₁ ≤ η₂) (h21 : η₂ ≤ η₁) : obsClass η₁ h y = obsClass η₂ h y :=
  Set.Subset.antisymm (obsClass_mono h12) (obsClass_mono h21)

/-- **【主消费 3'】** 上一条的**模型版**：两个 `ObsModel` 只差 `etaMax` 且数值相等时，
它们的噪声集合相同。

**非平凡性**：结论是 `M₁.obsSet y = M₂.obsSet y`，涉及两个**不同**结构体的字段；
前件给的是 `M₁.h = M₂.h` 与 `M₁.etaMax ≤ M₂.etaMax ≤ M₁.etaMax`，
**没有**任何关于 `obsSet` 的陈述。需消去 `h` 的相等再套用上一条。 -/
theorem obsSet_eq_of_eta_le_antisymm [PseudoMetricSpace Y] (M₁ M₂ : ObsModel X Y)
    (hh : M₁.h = M₂.h) (h12 : M₁.etaMax ≤ M₂.etaMax) (h21 : M₂.etaMax ≤ M₁.etaMax)
    (y : Y) : M₁.obsSet y = M₂.obsSet y := by
  obtain ⟨h1, e1⟩ := M₁
  obtain ⟨h2, e2⟩ := M₂
  simp only at hh
  subst hh
  simp only [ObsModel.obsSet]
  exact obsClass_eq_of_le_antisymm h12 h21

/-! ===========================================================================
  §3  零噪声退化：精确纤维版的"正确性"
  =========================================================================== -/

/-- **【主消费 4】零噪声下真实状态必在噪声集合中**。

若 `M.etaMax = 0` 且 `M.h x = y`（无损观测），则 `x ∈ M.obsSet y`。

**非平凡性**：前件是 `M.etaMax = 0` 和一个**函数等式** `M.h x = y`；
结论 `x ∈ M.obsSet y` 是关于**集合成员**的陈述，且 `M.obsSet` 的定义里
含 `dist (·) y ≤ M.etaMax` —— 从等式得到距离陈述必须经
`ObsModel.obsSet_eq_hFiber`（把噪声集合识别为精确纤维）**和**
`true_mem_hFiber` 两步。**结论不在前件中。** -/
theorem true_mem_obsSet_of_zero_noise [MetricSpace Y] (M : ObsModel X Y)
    (h0 : M.etaMax = 0) {x : X} {y : Y} (hx : M.h x = y) : x ∈ M.obsSet y := by
  rw [ObsModel.obsSet_eq_hFiber M h0]
  exact true_mem_hFiber hx

end ObsEstimationWeakConsumer

end Fate
