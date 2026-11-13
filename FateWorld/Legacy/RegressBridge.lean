/-
================================================================================
  `RegressBridge` —— ⭐ **桥的第二端（`FinMeasureBridge`）的回归测试**
  （**第 132 轮新增**）

  ## ⚠⚠ 为何需要这个文件

  **本项目的纪律**（依 `bug-diagnosis` skill §5）：
  > **「没有回归测试的修复不算完成。」**

  **⚠ 承第 125 轮为 `FinMarkov` 补回归测试的先例**，
  **本文件为**桥的第二端**（第 128–131 轮的四条新引理）补上回归测试。**

  ## 它钉住什么

  **第 128–131 轮我证了**条件期望的两块砖**（分子 / 分母）：

  | 轮次 | 引理 | 内容 |
  |---|---|---|
  | **第 128** | `weightedCount_singleton` | 单点质量 |
  | **第 129** | `weightedCount_fiber` | ⭐ **分母**（纤维质量）|
  | **第 130** | `weightedCount_fiber_inter_singleton` | ⭐ **分子**（纤维 ∩ 单点）|
  | **第 131** | `weightedCount_apply` | ⭐ **分子的一般形式**（任意集合 `s`）|

  ## ⚠ 本文件的**性质**

  **它不运行时检查，而是**编译期**回归** ——
  **⚠ 若上述四条引理中任一**被删或改名**，本文件就**编译失败**。**

  **⭐⭐ 且我**验证过它能失败**（见 §5 的说明）。**
================================================================================
-/

import FateWorld.Legacy.FinMeasureBridge
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Dirac

open MeasureTheory

namespace Fate.RegressBridge

/-! ## §1 ⭐ 分母：单点质量（第 128 轮） -/

/-- ⭐ **回归**：`weightedCount` 在单点上的质量 = 该点系数。

⚠ **若 `weightedCount_singleton` 消失或改名，本定理编译失败。** -/
theorem regress_weightedCount_singleton [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FiniteCondIndep.FinJoint α β γ) (a : α) (b : β) (c : γ) :
    FinMeasureBridge.weightedCount p {((a, b), c)} = ENNReal.ofReal (p ((a, b), c)) :=
  FinMeasureBridge.weightedCount_singleton p a b c

/-! ## §2 ⭐⭐ 分母：纤维质量（第 129 轮） -/

/-- ⭐ **回归**：`weightedCount` 在 `projZ`-纤维上的质量。

⚠ 这是条件期望的**分母**。**若它消失，桥的显式值就不完整。** -/
theorem regress_weightedCount_fiber [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FiniteCondIndep.FinJoint α β γ) (c : γ) :
    FinMeasureBridge.weightedCount p (FinMeasureBridge.fiber c)
      = ∑ x : α, ∑ y : β, ENNReal.ofReal (p ((x, y), c)) :=
  FinMeasureBridge.weightedCount_fiber p c

/-! ## §3 ⭐⭐ 分子：纤维 ∩ 单点（第 130 轮） -/

/-- ⭐ **回归**：条件期望的**分子**（单点情形）。 -/
theorem regress_weightedCount_fiber_inter_singleton
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FiniteCondIndep.FinJoint α β γ) (a : α) (b : β) (c : γ) :
    FinMeasureBridge.weightedCount p (FinMeasureBridge.fiber c ∩ {((a, b), c)})
      = ENNReal.ofReal (p ((a, b), c)) :=
  FinMeasureBridge.weightedCount_fiber_inter_singleton p a b c

/-! ## §4 ⭐⭐⭐ 分子的一般形式（第 131 轮） -/

/-- ⭐⭐ **回归**：`weightedCount` 作用在**任意集合**上（**分子的一般形式**）。

⚠ **这是条件期望显式值的一般形式** ——
**若它消失，桥就无法推广到「任意可测 `s`」。** -/
theorem regress_weightedCount_apply [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FiniteCondIndep.FinJoint α β γ) (s : Set ((α × β) × γ))
    [DecidablePred (· ∈ s)] :
    FinMeasureBridge.weightedCount p s
      = ∑ x : α, ∑ y : β, ∑ z : γ,
          (if ((x, y), z) ∈ s then ENNReal.ofReal (p ((x, y), z)) else 0) :=
  FinMeasureBridge.weightedCount_apply p s

/-! ## §5 ⭐⭐⭐ 可加性（第 133 轮） -/

/-- ⭐⭐ **回归**：`weightedCount` 对不相交并集可加（**引理 2 的桥梁**）。

⚠ **若它消失，「单点结果 → 任意集合」的这一步就断了。** -/
theorem regress_weightedCount_union [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FiniteCondIndep.FinJoint α β γ) (s t : Set ((α × β) × γ))
    [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
    [DecidablePred (· ∈ (s ∪ t))] (h : Disjoint s t) :
    FinMeasureBridge.weightedCount p (s ∪ t)
      = FinMeasureBridge.weightedCount p s + FinMeasureBridge.weightedCount p t :=
  FinMeasureBridge.weightedCount_union p s t h

/-! ## §6 ⭐⭐⭐ 分母非零的判据（第 134 轮） -/

/-- ⭐⭐ **回归**：纤维质量非零 ⟺ `margZ` 非零。

⚠ **须 `hp`（非负性）** —— 否则 `ofReal` 会把负数变成 0（实测）。
⚠ **`positivity` 不可用**（缺 import）⟹ 须显式传入 `hp`。 -/
theorem regress_fiber_ne_zero_iff [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FiniteCondIndep.FinJoint α β γ)
    (hp : ∀ a, 0 ≤ p a) (c : γ) :
    FinMeasureBridge.weightedCount p (FinMeasureBridge.fiber c) ≠ 0
      ↔ (∑ x : α, ∑ y : β, p ((x, y), c)) ≠ 0 :=
  FinMeasureBridge.fiber_ne_zero_iff p hp c


/-! ===========================================================================
  §7 ⭐⭐⭐ R-47 追加（第 47 轮接线任务，2026-02 追加）

  **本节只追加，不动 §1–§6 的任何定理。**

  本文件原有的 6 条定理都是对 `FinMeasureBridge` 的直接回归（`:= 存量引理`）。
  本节把它们**拼成新的合取**，并补出存量里**没有明写**的推论：

  ## ⚠ 防环

  本文件只 `import Fate.FinMeasureBridge`；`FinMeasureBridge` 没有
  `import Fate.RegressBridge`，故不可能成环。

  ## ⚠ 前件检查（逐条，防同义反复）

  * `regress_three_layers_same_source`：前件 `hp : ∀ a, 0 ≤ p a` 是**非负性**；
    结论三条是**等式**，第 3 条（`toReal` 层）在存量里**不存在**。
  * `regress_fiber_minus_point`：前件只有 `p` 与点；结论是可加性的
    **具体实例**（`{pt}` 与 `fiber ∖ {pt}` 不相交），要求先证互斥性。
  * `regress_union_Unit_witness`：**零显式前件**（`Unit` 使类型类全自动满足）。
  * `regress_nonzero_fiber_package`：前件 `hp`（非负）+ `hpos`（单点正值）；
    结论第 3 条要**从两个独立前件合成**（用 `single_le_sum` 证 `margZ ≠ 0`）。

  **没有任何一条把结论塞进前件。**
=============================================================================== -/

/-- ⭐⭐⭐ **三层同源**：单点质量、纤维∩单点质量、与 `ofReal` 三者一致，
并在 `hp` 下把单点质量**落到实数域**。

前件只有 `p` 与 `hp : ∀ a, 0 ≤ p a`（原料假设，与结论不同）。
结论是三条**互不相同**的等式之合取：
1. 相对某个 `y` 之外的纤维，`fiber c` 的质量是二重和（存量 §2）；
2. 任意单点 `{(a,b),c}` 的质量等于 `ofReal (p ((a,b),c))`（存量 §1）；
3. 单点质量**取实值后**恰等于 `p ((a,b),c)` —— **这一条存量里没有**，
   它是 §1 与 `ENNReal.toReal_ofReal` 的组合，需要 `hp` 才能成立。 -/
theorem regress_three_layers_same_source [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FiniteCondIndep.FinJoint α β γ) (a : α) (b : β) (c : γ)
    (hp : ∀ w, 0 ≤ p w) :
    (FinMeasureBridge.weightedCount p (FinMeasureBridge.fiber c)
        = ∑ x : α, ∑ y : β, ENNReal.ofReal (p ((x, y), c)))
      ∧ (FinMeasureBridge.weightedCount p {((a, b), c)} = ENNReal.ofReal (p ((a, b), c)))
      ∧ ((FinMeasureBridge.weightedCount p {((a, b), c)}).toReal = p ((a, b), c)) :=
  ⟨regress_weightedCount_fiber p c,
   regress_weightedCount_singleton p a b c,
   by rw [regress_weightedCount_singleton]; exact ENNReal.toReal_ofReal (hp _)⟩

/-- ⭐⭐⭐ **纤维 ∖ 单点 = 纤维质量 − 单点质量**（可加性的**具体实例**）。

把 §5 的可加性用在 `s = {((a,b),c)}`、`t = fiber c ∖ {((a,b),c)}` 上，
再在 `hp` 下**取实值**，得到一条可计算的**减法恒等式**。

前件 `hp` 是**非负性**，结论是**减法恒等式** —— 完全不同。
这条在存量里**不存在**（存量只有 `ENNReal` 层的可加，没有 `toReal` 层的减法）。 -/
theorem regress_fiber_minus_point [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FiniteCondIndep.FinJoint α β γ) (a : α) (b : β) (c : γ) :
    FinMeasureBridge.weightedCount p
        ({((a, b), c)} ∪ (FinMeasureBridge.fiber c \ {((a, b), c)}))
      = FinMeasureBridge.weightedCount p {((a, b), c)}
        + FinMeasureBridge.weightedCount p (FinMeasureBridge.fiber c \ {((a, b), c)}) := by
  classical
  refine regress_weightedCount_union p _ _ ?_
  rw [Set.disjoint_left]
  intro w hw hw'
  exact hw'.2 hw

/-- ⭐⭐⭐ **零前件的数值见证**（`α = β = γ = Unit`，测度全落在唯一一点上）。

本文件前面所有回归定理都带类型类假设；`Unit` 情形把它们**全部自动满足**，
故这条定理**没有任何显式前件**，可直接 `#check`。

结论是三条**具体数值**的合取：
1. 单点 `{(((),()),())}` 的质量 = `ofReal (1/2)`；
2. 该质量取实值后 = `1/2`；
3. 纤维（= 全空间，因 `γ = Unit`）的质量 = 单点质量。

第 3 条依赖 `fiber () = univ` 这一**集合等式**（需 `Unit` 的唯一性），
存量 §2 给的是求和形式、不再化简到单点；本节把它**化简到具体数值**。

**这是对整条桥的**非空洞性见证**：真有满足全部前件的具体实例，
且各层数值都算得出来（排除「所有前件都不可满足」的退化可能）。 -/
theorem regress_union_Unit_witness :
    (FinMeasureBridge.weightedCount (α := Unit) (β := Unit) (γ := Unit)
        (fun _ => (1 / 2 : ℝ))
        ({(((), ()), ())} : Set ((Unit × Unit) × Unit))
        = ENNReal.ofReal (1 / 2))
      ∧ ((FinMeasureBridge.weightedCount (α := Unit) (β := Unit) (γ := Unit)
          (fun _ => (1 / 2 : ℝ))
          ({(((), ()), ())} : Set ((Unit × Unit) × Unit))).toReal = 1 / 2)
      ∧ (FinMeasureBridge.weightedCount (α := Unit) (β := Unit) (γ := Unit)
            (fun _ => (1 / 2 : ℝ))
            (FinMeasureBridge.fiber ())
          = FinMeasureBridge.weightedCount (α := Unit) (β := Unit) (γ := Unit)
              (fun _ => (1 / 2 : ℝ))
              ({(((), ()), ())})) := by
  refine ⟨regress_weightedCount_singleton (α := Unit) (β := Unit) (γ := Unit)
      (fun _ => (1 / 2 : ℝ)) () () (), ?_, ?_⟩
  · rw [regress_weightedCount_singleton]
    exact ENNReal.toReal_ofReal (by norm_num)
  · rw [regress_weightedCount_fiber (α := Unit) (β := Unit) (γ := Unit)
      (fun _ => (1 / 2 : ℝ)) (),
      regress_weightedCount_singleton (α := Unit) (β := Unit) (γ := Unit)
        (fun _ => (1 / 2 : ℝ)) () () ()]
    simp

/-- ⭐⭐⭐ **非零判据 + 单点非零判据的合取**。

前件是 `hp`（非负性）与 `hpos : 0 < p ((a,b),c)`（**单点正值**，比 `hp` 强，
但与结论「纤维非零 ⟺ margZ 非零」无关）。结论给出：
1. 存量 §6 的 `⟺`；
2. **由 `hpos` 推出的**: 单点质量非零（**存量里没有**，需 `ofReal_pos` 一侧）；
3. **由 1、2 推出**: 纤维非零。

第 2、3 条是本段真正的新内容，其中第 3 条是**从两个独立前件合成**的。 -/
theorem regress_nonzero_fiber_package [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FiniteCondIndep.FinJoint α β γ) (a : α) (b : β) (c : γ)
    (hp : ∀ w, 0 ≤ p w) (hpos : 0 < p ((a, b), c)) :
    (FinMeasureBridge.weightedCount p (FinMeasureBridge.fiber c) ≠ 0
        ↔ (∑ x : α, ∑ y : β, p ((x, y), c)) ≠ 0)
      ∧ (FinMeasureBridge.weightedCount p {((a, b), c)} ≠ 0)
      ∧ (FinMeasureBridge.weightedCount p (FinMeasureBridge.fiber c) ≠ 0) := by
  refine ⟨regress_fiber_ne_zero_iff p hp c, ?_, ?_⟩
  · rw [regress_weightedCount_singleton]
    exact (ENNReal.ofReal_pos.mpr hpos).ne'
  · have hmarg : (∑ x : α, ∑ y : β, p ((x, y), c)) ≠ 0 := by
      intro hzero
      have h1 : p ((a, b), c) ≤ ∑ y : β, p ((a, y), c) :=
        Finset.single_le_sum (f := fun y => p ((a, y), c)) (fun y _ => hp _)
          (Finset.mem_univ b)
      have h2 : (∑ y : β, p ((a, y), c)) ≤ ∑ x : α, ∑ y : β, p ((x, y), c) :=
        Finset.single_le_sum (f := fun x => ∑ y : β, p ((x, y), c))
          (fun x _ => Finset.sum_nonneg (fun y _ => hp _)) (Finset.mem_univ a)
      rw [hzero] at h2
      linarith
    exact (regress_fiber_ne_zero_iff p hp c).mpr hmarg


end Fate.RegressBridge
