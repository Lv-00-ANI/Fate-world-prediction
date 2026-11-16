import FateWorld.FateV2.Modeling.FinCondIndepMeasure
import FateWorld.FateV2.Modeling.BridgeProofStep3
open MeasureTheory ProbabilityTheory

namespace FateV2.Modeling.BridgeKernel

theorem bridgeKernelStep1 [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (s : Set ((α × β) × γ)) (hs : MeasurableSet s) :
    letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
      Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
    (fun ω => (((condExpKernel (Ω := (α × β) × γ) (Fate.FinMeasureBridge.weightedCount p)
      (MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) ω).real s))
      =ᵐ[Fate.FinMeasureBridge.weightedCount p]
      (Fate.FinMeasureBridge.weightedCount p)[s.indicator fun _ => 1
        | MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance] := by
  letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
    Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
  exact Fate.BridgeProofStep3.condExpKernel_real_apply
    (inferInstance : MeasurableSpace ((α × β) × γ))
    (Fate.FinMeasureBridge.weightedCount p)
    (MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)
    (MeasurableSpace.comap_le_iff_le_map.mpr Fate.FinCondIndepMeasure.measurable_projZ) hs

/-- ⭐⭐⭐ **`comap projZ`-可测函数在**每个纤维上是常数****（**桥的第 2 步核心**）。

**⚠ 证明思路**：若 `f w₁ ≠ f w₂`，则存在一个**水平集**把它们分开 ——
**而该水平集是 `projZ` 的原像**（由 `MeasurableSpace.measurableSet_comap`）
**⟹ `projZ w₁ = projZ w₂` 时不可能分开。**

**⭐⭐ 用途**：桥里 `μ[1_s | comap projZ]` 是 `comap projZ`-可测的
**⟹ 它在每个**纤维**上是常数** —— 这是「核值 = 纤维上的条件概率」的关键一步。** -/
theorem comap_projZ_apply_eq_of_fiber {α β γ : Type*}
    [MeasurableSpace ((α × β) × γ)] [MeasurableSpace γ]
    {f : (α × β) × γ → ℝ}
    (hf : Measurable[MeasurableSpace.comap (fun w : (α × β) × γ => w.2) inferInstance] f)
    (w₁ w₂ : (α × β) × γ) (h : w₁.2 = w₂.2) : f w₁ = f w₂ := by
  by_contra hne
  have hlt : f w₁ < f w₂ ∨ f w₂ < f w₁ := lt_or_gt_of_ne hne
  rcases hlt with hlt | hlt
  · have hset : MeasurableSet[MeasurableSpace.comap (fun w : (α × β) × γ => w.2) inferInstance]
        {w | f w < f w₂} := hf measurableSet_Iio
    rw [MeasurableSpace.measurableSet_comap] at hset
    obtain ⟨S, _, hS⟩ := hset
    have hm1 : w₁ ∈ {w : (α × β) × γ | f w < f w₂} := hlt
    rw [← hS] at hm1
    have hm2 : w₂ ∉ {w : (α × β) × γ | f w < f w₂} := lt_irrefl (f w₂)
    rw [← hS] at hm2
    exact hm2 (by simpa [h] using hm1)
  · have hset : MeasurableSet[MeasurableSpace.comap (fun w : (α × β) × γ => w.2) inferInstance]
        {w | f w < f w₁} := hf measurableSet_Iio
    rw [MeasurableSpace.measurableSet_comap] at hset
    obtain ⟨S, _, hS⟩ := hset
    have hm1 : w₂ ∈ {w : (α × β) × γ | f w < f w₁} := hlt
    rw [← hS] at hm1
    have hm2 : w₁ ∉ {w : (α × β) × γ | f w < f w₁} := lt_irrefl (f w₁)
    rw [← hS] at hm2
    exact hm2 (by simpa [h] using hm1)

/-- ⭐⭐ **常数函数在可测集上的积分**（**桥第 3 步的工具**）。

**⚠ 用途**：第 148 轮证了「`μ[1_s | comap projZ]` 在纤维上是**常数**」
**⟹ 故它在纤维上的积分 = `μ.real (fiber c) * c₀`** ——
**⭐ 本定理是这一步的直接工具。** -/
theorem integral_const_over_set {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
    (μ : Measure ((α × β) × γ)) (T : Set ((α × β) × γ)) (c : ℝ) :
    ∫ _w in T, c ∂μ = μ.real T * c := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul]

/-- ⭐⭐ **`μ[1_s | m']` 是 `m'`-可测的**（**桥第 4 步的前提**）。

**⚠ 用途**：配合第 148 轮的 `comap_projZ_apply_eq_of_fiber`，
**⟹ 条件期望在**每个纤维上是常数**。** -/
theorem condExp_indicator_measurable [MeasurableSpace ((α × β) × γ)] [MeasurableSpace γ]
    (μ : Measure ((α × β) × γ)) (s : Set ((α × β) × γ)) :
    Measurable[MeasurableSpace.comap (fun w : (α × β) × γ => w.2) inferInstance]
      (μ[s.indicator fun _ => (1:ℝ) | MeasurableSpace.comap (fun w : (α × β) × γ => w.2) inferInstance]) :=
  stronglyMeasurable_condExp.measurable

/-- ⭐⭐⭐⭐ **桥的核值在**每个纤维上是常数**（**逐点版**）**（**第 151 轮**）。

**⚠⚠ 这是桥的**第 3 步的完成** —— 它把三环接通**：

| 环 | 内容 | 出处 |
|---|---|---|
| **1** | `(κ ω).real s =ᵐ μ[1_s \| m']` | 第 147 轮 `bridgeKernelStep1` |
| **2** | `μ[1_s \| m']` 是 `m'`-可测 | 第 150 轮 `condExp_indicator_measurable` |
| **3** | `m'`-可测函数在纤维上常数 | 第 148 轮 `comap_projZ_apply_eq_of_fiber` |

**⭐⭐ 桥接环 1 与环 3**（**`=ᵐ` → 逐点**）：用第 137 轮的 `ae_iff_forall_or_zero` ——
**⚠ 它把零质量点吸收（`∨ μ{ω} = 0`），故只需在**正质量点**上逐点验证。**

**⚠ 前提 `h1` / `h2`**（两点的单点质量非零）**是必需的** ——
**第 134 轮的 `fiber_ne_zero_iff` 给出它们的可判定判据。** -/
theorem bridgeKernelValue_depends_on_fiber [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (s : Set ((α × β) × γ)) (hs : MeasurableSet s)
    (ω₁ ω₂ : (α × β) × γ) (h : ω₁.2 = ω₂.2)
    (h1 : (Fate.FinMeasureBridge.weightedCount p) {ω₁} ≠ 0)
    (h2 : (Fate.FinMeasureBridge.weightedCount p) {ω₂} ≠ 0) :
    letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
      Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
    ((condExpKernel (Fate.FinMeasureBridge.weightedCount p)
      (MeasurableSpace.comap (fun w : (α × β) × γ => w.2) inferInstance)) ω₁).real s
      = ((condExpKernel (Fate.FinMeasureBridge.weightedCount p)
      (MeasurableSpace.comap (fun w : (α × β) × γ => w.2) inferInstance)) ω₂).real s := by
  letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
    Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
  have hk := bridgeKernelStep1 p s hs
  have hmeas := condExp_indicator_measurable (Fate.FinMeasureBridge.weightedCount p) s
  have hconst := comap_projZ_apply_eq_of_fiber hmeas ω₁ ω₂ h
  have key : ∀ w, (Fate.FinMeasureBridge.weightedCount p) {w} ≠ 0 →
      ((condExpKernel (Fate.FinMeasureBridge.weightedCount p)
        (MeasurableSpace.comap (fun w : (α × β) × γ => w.2) inferInstance)) w).real s
        = (Fate.FinMeasureBridge.weightedCount p)[s.indicator fun _ => (1:ℝ)
          | MeasurableSpace.comap (fun w : (α × β) × γ => w.2) inferInstance] w := by
    intro w hw
    have h' : ∀ᵐ x ∂(Fate.FinMeasureBridge.weightedCount p),
        ((condExpKernel (Fate.FinMeasureBridge.weightedCount p)
          (MeasurableSpace.comap (fun w : (α × β) × γ => w.2) inferInstance)) x).real s
          = (Fate.FinMeasureBridge.weightedCount p)[s.indicator fun _ => (1:ℝ)
            | MeasurableSpace.comap (fun w : (α × β) × γ => w.2) inferInstance] x := hk
    have := Fate.FinMeasureBridge.ae_iff_forall_or_zero (Fate.FinMeasureBridge.weightedCount p)
      (fun x => ((condExpKernel (Fate.FinMeasureBridge.weightedCount p)
        (MeasurableSpace.comap (fun w : (α × β) × γ => w.2) inferInstance)) x).real s
        = (Fate.FinMeasureBridge.weightedCount p)[s.indicator fun _ => (1:ℝ)
          | MeasurableSpace.comap (fun w : (α × β) × γ => w.2) inferInstance] x)
    rw [this] at h'
    rcases h' w with h0 | heq
    · exact absurd h0 hw
    · exact heq
  rw [key ω₁ h1, key ω₂ h2, hconst]

/-!
  # Modeling · BridgeKernel

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeKernel.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：FinCondIndepMeasure, BridgeProofStep3
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ## §3 ⭐⭐⭐⭐⭐ **桥的第 7 步：`bridgeStatement` 的定义链回装**（**第 157 轮完成**）

**⚠⚠ 这是**桥的最后一步** —— 把 `bridgeStatement`（`CondIndepFun`）
**完全展开**成**可逐点验证的乘积等式**。**

**⭐⭐ 关键发现**（**这正是此前八次尝试都失败的原因**）：
`CondIndepFun m' f g μ` 的定义体内**用的是 `μ.trim hm'`** ——
**而非 `μ`**！
**⟹ 故桥的**最终测度不是 `weightedCount p`，而是 `(weightedCount p).trim hm'`**。**
**⚠ 而我此前一直把它当成 `weightedCount p` ⟹ **测度不匹配**。**

**⭐⭐ 完整链路**：
```
bridgeStatement p
  = Kernel.IndepFun projX projY (condExpKernel μ m') (μ.trim hm')     ← 本定理的 h1
  = Kernel.Indep (comap projX) (comap projY) (condExpKernel μ m') (μ.trim hm')
  = Kernel.IndepSets {comap projX-可测} {comap projY-可测} κ (μ.trim hm')
  = ∀ t₁ t₂, comap projX-可测 t₁ → comap projY-可测 t₂ →
      ∀ᵐ a ∂(μ.trim hm'), (κ a)(t₁∩t₂) = (κ a)t₁ * (κ a)t₂
``` -/

/-- ⭐⭐⭐⭐⭐ **`bridgeStatement` ↔ 逐点乘积等式**（**桥的第 7 步完成**）。

**⚠ 注意**：`∀ᵐ` 是**对 `(weightedCount p).trim hm'`**（**`CondIndepFun` 的内部形式**）。 -/
theorem bridgeStatement_unfold_def [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
    [Countable α] [Countable β] [Countable γ]
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ) :
    letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
      Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
    Fate.FinCondIndepMeasure.bridgeStatement p ↔
      ∀ (t₁ t₂ : Set ((α × β) × γ)),
        MeasurableSet[MeasurableSpace.comap (Fate.FinCondIndepMeasure.projX : (α × β) × γ → α) inferInstance] t₁ →
        MeasurableSet[MeasurableSpace.comap (Fate.FinCondIndepMeasure.projY : (α × β) × γ → β) inferInstance] t₂ →
        ∀ᵐ a ∂(Fate.FinMeasureBridge.weightedCount p).trim
          (MeasurableSpace.comap_le_iff_le_map.mpr Fate.FinCondIndepMeasure.measurable_projZ),
          (condExpKernel (Ω := (α × β) × γ) (Fate.FinMeasureBridge.weightedCount p)
            (MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance) a)
            (t₁ ∩ t₂)
          = (condExpKernel (Ω := (α × β) × γ) (Fate.FinMeasureBridge.weightedCount p)
            (MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance) a) t₁
            * (condExpKernel (Ω := (α × β) × γ) (Fate.FinMeasureBridge.weightedCount p)
            (MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance) a) t₂ := by
  letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
    Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
  have h1 : Fate.FinCondIndepMeasure.bridgeStatement p =
      Kernel.IndepFun Fate.FinCondIndepMeasure.projX Fate.FinCondIndepMeasure.projY
        (condExpKernel (Ω := (α × β) × γ) (Fate.FinMeasureBridge.weightedCount p)
          (MeasurableSpace.comap Fate.FinCondIndepMeasure.projZ inferInstance))
        ((Fate.FinMeasureBridge.weightedCount p).trim
          (MeasurableSpace.comap_le_iff_le_map.mpr Fate.FinCondIndepMeasure.measurable_projZ)) := by
    unfold Fate.FinCondIndepMeasure.bridgeStatement; rfl
  rw [h1]
  unfold Kernel.IndepFun Kernel.Indep Kernel.IndepSets
  simp only [Set.mem_setOf_eq]

/-! ## §4 ⭐⭐⭐ 指示函数积分（**桥的最后一步的第一块**）（**第 160 轮**）

**⚠ 用途**：子问题 B（用条件期望的唯一性证「核值 = 纤维归一化」）需要
`∫ over s of 1_t = μ.real(s ∩ t)`。**本节给出它。** -/

/-- ⭐⭐ **指示函数在可测集上的积分 = 交集的实值测度**。 -/
theorem setIntegral_indicator_one [MeasurableSpace ((α × β) × γ)]
    (μ : Measure ((α × β) × γ)) (s t : Set ((α × β) × γ)) (ht : MeasurableSet t) :
    ∫ w in s, t.indicator (fun _ => (1:ℝ)) w ∂μ = μ.real (s ∩ t) := by
  rw [MeasureTheory.setIntegral_indicator ht]
  rw [MeasureTheory.setIntegral_const]
  simp [smul_eq_mul]

/-! ## §5 ⭐⭐⭐⭐ **绕开 `condExp` 的新路线**（**第 163 轮**）

**⚠⚠ 第 162 轮查明**：`setIntegral_condExp` 要求 `T` 是**纤维饱和**的（`comap projZ`-可测），
**而桥的 `t₁`（`comap projX`-可测）**不是**** ⟹ **那条路**不通**。

**⭐⭐ 新路线**：**不用 `condExp` 的积分性质**，而是：
1. `t₁` 是 `comap projX`-可测 ⟹ **`t₁` 只依赖 `x`**（本节的 `comap_projX_mem_iff`）
2. 同理 `t₂` 只依赖 `y`
3. ⟹ 「`t₁∩t₂` 在纤维 `z` 上的求和」= `∑ x∈S1, ∑ y∈S2, p((x,y),z)`
4. ⟹ 由 `CondIndepFin`（`p·margZ = margXZ·margYZ`）**纯代数**得乘积等式

**⭐⭐ 即**：**完全绕开测度论，只需**纯代数求和重组****。 -/

/-- ⭐⭐⭐ **`comap projX`-可测集只依赖 `x`**（**新路线的基石**）。 -/
theorem comap_projX_mem_iff [MeasurableSpace α] [MeasurableSpace ((α × β) × γ)]
    {t₁ : Set ((α × β) × γ)}
    (ht₁ : MeasurableSet[MeasurableSpace.comap (Fate.FinCondIndepMeasure.projX : (α × β) × γ → α) inferInstance] t₁)
    (x : α) (y₁ y₂ : β) (z₁ z₂ : γ) :
    (((x, y₁), z₁) ∈ t₁) ↔ (((x, y₂), z₂) ∈ t₁) := by
  obtain ⟨S, _, hS⟩ := (MeasurableSpace.measurableSet_comap).mp ht₁
  rw [← hS]
  simp [Fate.FinCondIndepMeasure.projX]

/-- ⭐⭐ **`comap projY`-可测集只依赖 `y`**。 -/
theorem comap_projY_mem_iff [MeasurableSpace β] [MeasurableSpace ((α × β) × γ)]
    {t₂ : Set ((α × β) × γ)}
    (ht₂ : MeasurableSet[MeasurableSpace.comap (Fate.FinCondIndepMeasure.projY : (α × β) × γ → β) inferInstance] t₂)
    (y : β) (x₁ x₂ : α) (z₁ z₂ : γ) :
    (((x₁, y), z₁) ∈ t₂) ↔ (((x₂, y), z₂) ∈ t₂) := by
  obtain ⟨S, _, hS⟩ := (MeasurableSpace.measurableSet_comap).mp ht₂
  rw [← hS]
  simp [Fate.FinCondIndepMeasure.projY]

/-- ⭐⭐⭐⭐ **`CondIndepFin` 的**逐点乘积形式**（新路线的代数核心）**。

**⚠ 它把 `CondIndepFin`（`p·margZ = margXZ·margYZ`）写成三个**具体的和**的形式**，
**⟹ 后续的 `∑` 重组可以直接代入。** -/
theorem condIndepFin_pointwise_sum [Fintype α] [Fintype β] [Fintype γ]
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (h : FateV2.Modeling.FiniteCondIndep.CondIndepFin p) (x : α) (y : β) (z : γ) :
    p ((x, y), z) * (∑ x' : α, ∑ y' : β, p ((x', y'), z))
      = (∑ y' : β, p ((x, y'), z)) * (∑ x' : α, p ((x', y), z)) := by
  have := h x y z
  rw [FateV2.Modeling.FiniteCondIndep.margXZ, FateV2.Modeling.FiniteCondIndep.margYZ, FateV2.Modeling.FiniteCondIndep.margZ] at this
  linarith

/-! ## §6 ⭐⭐⭐⭐⭐ **决定性突破：`fiber z` 是纤维饱和的**（**第 163 轮**）

**⚠⚠ 第 162 轮查明**：`setIntegral_condExp` 要求 `T` 是**纤维饱和**的（`comap projZ`-可测），
**而一般的全可测 `T` **不是**** ⟹ **原目标为假**（`RegressStep9Fiber.claim_implies_false`）。

**⭐⭐⭐ 本轮找到**出路****：
**`fiber z` **本身**就是 `comap projZ`-可测的**（**第 135 轮 `measurableSet_fiber`**）
**⟹ 故在 `T = fiber z` 上，`setIntegral_condExp` **完全适用****！

**⭐⭐ 即**：**我不需要「对任意 `T`」的性质，只需要「对 `fiber z`」的性质** ——
**而这**正是桥真正需要的**（因为条件期望在纤维上是常数）。

**⭐ 这解决了困扰 10+ 轮的技术死结。** -/

/-- ⭐⭐⭐⭐⭐ **`setIntegral_condExp` 在 `fiber z` 上成立**（**解决纤维饱和性障碍**）。

**⚠ 与 `setIntegral_condExp` 的一般形式的区别**：
一般形式要求 `hT : MeasurableSet[comap projZ] T`（**纤维饱和**），
**而本定理取 `T = fiber z`** —— **它**自动满足**该要求**（**`measurableSet_fiber`**）。 -/
theorem setIntegral_condExp_fiber [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (t : Set ((α × β) × γ)) (ht : MeasurableSet t) (z : γ) :
    letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
      Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
    ∫ w in (Fate.FinMeasureBridge.fiber z),
        (Fate.FinMeasureBridge.weightedCount p)[t.indicator fun _ => (1:ℝ)
          | MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance] w
        ∂(Fate.FinMeasureBridge.weightedCount p)
      = ∫ w in (Fate.FinMeasureBridge.fiber z), t.indicator (fun _ => (1:ℝ)) w
        ∂(Fate.FinMeasureBridge.weightedCount p) := by
  letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
    Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
  exact setIntegral_condExp
    (m := MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)
    (m₀ := inferInstance)
    (μ := Fate.FinMeasureBridge.weightedCount p)
    (f := t.indicator fun _ => (1:ℝ)) (s := Fate.FinMeasureBridge.fiber z)
    (hm := MeasurableSpace.comap_le_iff_le_map.mpr Fate.FinCondIndepMeasure.measurable_projZ)
    (hf := (integrable_const (μ := Fate.FinMeasureBridge.weightedCount p) (1:ℝ)).indicator ht)
    (hs := Fate.FinMeasureBridge.measurableSet_fiber z)

/-! ## §7 ⭐⭐⭐⭐ **纤维上的常数积分**（**第 165 轮，在具体语境内证明**）

**⚠⚠ 第 164 轮的失败原因**：我把这条引理**抽成通用引理**（`{α β γ : Type*}` 但 `MeasurableSpace ((α×β)×γ)`
不在签名里），导致 `MeasurableSpace (α × β)` **粘住**。

**⭐⭐ 解法**：**把桥的完整实例集**（含 `Fintype/DecidableEq/DiscreteMeasurableSpace/MeasurableSingletonClass`）
**写进签名**，则 `(α×β)×γ` 的 `MeasurableSpace` 由 `inferInstance` 正常推断，**不再粘住**。

**⭐ 关键技巧**：`measurableSet_fiber` 返回的是 **`comap projZ` 实例下**的可测性，
**而可用 `comap projZ ≤ 默认实例` **正向转换****：
```lean
hle _ (measurableSet_fiber z)
``` -/

/-- ⭐⭐⭐⭐ **在纤维上，常数函数的积分** = `μ.real(fiber z) * c`。 -/
theorem setIntegral_fiber_const_direct [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (g : (α × β) × γ → ℝ) (z : γ) (c : ℝ)
    (hconst : ∀ w ∈ Fate.FinMeasureBridge.fiber z, g w = c) :
    letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
      Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
    ∫ w in (Fate.FinMeasureBridge.fiber z), g w ∂(Fate.FinMeasureBridge.weightedCount p)
      = (Fate.FinMeasureBridge.weightedCount p).real (Fate.FinMeasureBridge.fiber z) * c := by
  letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
    Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
  have hle : MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance
      ≤ (inferInstance : MeasurableSpace ((α × β) × γ)) :=
    MeasurableSpace.comap_le_iff_le_map.mpr Fate.FinCondIndepMeasure.measurable_projZ
  have hfib_meas : MeasurableSet (Fate.FinMeasureBridge.fiber z) :=
    hle _ (Fate.FinMeasureBridge.measurableSet_fiber z)
  have h1 : ∫ w in (Fate.FinMeasureBridge.fiber z), g w ∂(Fate.FinMeasureBridge.weightedCount p)
      = ∫ w in (Fate.FinMeasureBridge.fiber z), c ∂(Fate.FinMeasureBridge.weightedCount p) := by
    apply MeasureTheory.setIntegral_congr_fun hfib_meas
    intro w hw
    exact hconst w hw
  rw [h1, integral_const_over_set]

/-! ## §8 ⭐⭐⭐⭐⭐ **桥的最后一块：核值 = 纤维归一化**（**第 165 轮**） -/

/-- ⭐⭐⭐⭐⭐ **核值 × 纤维质量 = 交集质量**（**桥的最后一块**）。

**⭐ 证明结构**（**11 轮打磨**）：
| 步 | 内容 | 出处 |
|---|---|---|
| 1 | `(κ a).real t =ᵐ μ[1_t \| m']` | **第 147 轮 `bridgeKernelStep1`** |
| 2 | `μ[1_t \| m']` 是 `m'`-可测 ⟹ 在纤维上常数 | **第 148 轮** |
| 3 | 纤维上的常数积分 = `μ.real(fiber) * c` | **⭐ 第 165 轮 `setIntegral_fiber_const_direct`** |
| 4 | `∫ over fiber of μ[1_t\|m'] = ∫ over fiber of 1_t` | **⭐ 第 163 轮 `setIntegral_condExp_fiber`** |
| 5 | `∫ over fiber of 1_t = μ.real(t ∩ fiber)` | **第 160 轮 `setIntegral_indicator_one`** |
| 6 | `=ᵐ` + 正质量 ⟹ 逐点 | **第 137 轮 `ae_iff_forall_or_zero`** |

**⚠ 前提 `hω : μ {ω} ≠ 0`** —— **零质量点的 `κ ω` 值**不受约束**（这是真实现象）。** -/
theorem bridgeKernelValue_mul_fiber [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (t : Set ((α × β) × γ)) (ht : MeasurableSet t)
    (ω : (α × β) × γ)
    (hω : (Fate.FinMeasureBridge.weightedCount p) {ω} ≠ 0) :
    letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
      Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
    ((condExpKernel (Ω := (α × β) × γ) (Fate.FinMeasureBridge.weightedCount p)
      (MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) ω).real t
      * (Fate.FinMeasureBridge.weightedCount p).real (Fate.FinMeasureBridge.fiber ω.2)
      = (Fate.FinMeasureBridge.weightedCount p).real (t ∩ Fate.FinMeasureBridge.fiber ω.2) := by
  letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
    Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
  set ce : (α × β) × γ → ℝ := (Fate.FinMeasureBridge.weightedCount p)[t.indicator fun _ => (1:ℝ)
    | MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance] with hce
  have hstep1 : (fun a => ((condExpKernel (Ω := (α × β) × γ) (Fate.FinMeasureBridge.weightedCount p)
      (MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) a).real t)
      =ᵐ[Fate.FinMeasureBridge.weightedCount p] ce := by
    rw [hce]; exact bridgeKernelStep1 p t ht
  have hmeas := condExp_indicator_measurable (Fate.FinMeasureBridge.weightedCount p) t
  have hconst' : ∀ w ∈ Fate.FinMeasureBridge.fiber ω.2, ce w = ce ω := by
    intro w hw
    have hh := comap_projZ_apply_eq_of_fiber hmeas w ω (by simpa [Fate.FinMeasureBridge.fiber] using hw)
    rw [hce]; exact hh
  have h_int_const : ∫ w in (Fate.FinMeasureBridge.fiber ω.2), ce w
      ∂(Fate.FinMeasureBridge.weightedCount p)
      = (Fate.FinMeasureBridge.weightedCount p).real (Fate.FinMeasureBridge.fiber ω.2) * ce ω :=
    setIntegral_fiber_const_direct p ce ω.2 (ce ω) hconst'
  have h_eq_int : ∫ w in (Fate.FinMeasureBridge.fiber ω.2), ce w
      ∂(Fate.FinMeasureBridge.weightedCount p)
      = (Fate.FinMeasureBridge.weightedCount p).real (t ∩ Fate.FinMeasureBridge.fiber ω.2) := by
    rw [hce]
    rw [setIntegral_condExp_fiber p t ht ω.2]
    have h := setIntegral_indicator_one (Fate.FinMeasureBridge.weightedCount p)
      (Fate.FinMeasureBridge.fiber ω.2) t ht
    rw [h, Set.inter_comm]
  have h_point : ((condExpKernel (Ω := (α × β) × γ) (Fate.FinMeasureBridge.weightedCount p)
      (MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) ω).real t = ce ω := by
    have h' : ∀ᵐ a ∂(Fate.FinMeasureBridge.weightedCount p),
        ((condExpKernel (Ω := (α × β) × γ) (Fate.FinMeasureBridge.weightedCount p)
          (MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) a).real t = ce a := hstep1
    have hz := Fate.FinMeasureBridge.ae_iff_forall_or_zero (Fate.FinMeasureBridge.weightedCount p)
      (fun a => ((condExpKernel (Ω := (α × β) × γ) (Fate.FinMeasureBridge.weightedCount p)
        (MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) a).real t = ce a)
    rw [hz] at h'
    rcases h' ω with h0 | heq
    · exact absurd h0 hω
    · exact heq
  calc ((condExpKernel (Ω := (α × β) × γ) (Fate.FinMeasureBridge.weightedCount p)
      (MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) ω).real t
        * (Fate.FinMeasureBridge.weightedCount p).real (Fate.FinMeasureBridge.fiber ω.2)
      = ce ω * (Fate.FinMeasureBridge.weightedCount p).real (Fate.FinMeasureBridge.fiber ω.2) := by rw [h_point]
    _ = (Fate.FinMeasureBridge.weightedCount p).real (Fate.FinMeasureBridge.fiber ω.2) * ce ω := by rw [mul_comm]
    _ = ∫ w in (Fate.FinMeasureBridge.fiber ω.2), ce w ∂(Fate.FinMeasureBridge.weightedCount p) := h_int_const.symm
    _ = (Fate.FinMeasureBridge.weightedCount p).real (t ∩ Fate.FinMeasureBridge.fiber ω.2) := h_eq_int

/-! ## §9 ⭐⭐⭐ **纤维质量的实数版非零判据**（**第 166 轮，代理 Z1 交付，我独立验证**） -/

/-- ⭐⭐⭐ **纤维质量的**实数版**非零**（由 `fiber_ne_zero_iff` + 有限测度）。

**⭐⭐ 关键**：`ENNReal.toReal_ne_zero` 把 `(μ s).toReal ≠ 0` **一次性拆成**
`μ s ≠ 0` 与 `μ s ≠ ⊤` 两个分量 —— **比走 `toReal_eq_zero_iff` 的绕路干净得多。** -/
theorem fiber_real_ne_zero [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (hp : ∀ w, 0 ≤ p w) (z : γ)
    (hz : (∑ x : α, ∑ y : β, p ((x, y), z)) ≠ 0) :
    letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
      Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
    (Fate.FinMeasureBridge.weightedCount p).real (Fate.FinMeasureBridge.fiber z) ≠ 0 := by
  letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
    Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
  rw [Measure.real, ENNReal.toReal_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [Fate.FinMeasureBridge.fiber_ne_zero_iff p hp z]
    exact hz
  · exact measure_ne_top _ _

/-! ## §10 ⭐⭐⭐⭐⭐⭐ **核心组装引理：核值 = 求和比**（**第 166 轮**）

**⚠⚠ 这是桥组装的**决定性一块**** ——
**它把**测度论**的核值化为**纯代数**的求和比**：
$$(\kappa\ \omega).\mathrm{real}\ t
  = \frac{\sum_{(x,y)\in t} p((x,y),\omega_2)}{\sum_{x,y} p((x,y),\omega_2)}$$

**⭐⭐ 有了它，桥的剩余部分就**只是纯代数****（用 `condIndepFin_pointwise_sum`）。** -/

/-- ⭐⭐⭐⭐⭐⭐ **核值 = 求和比**（**条件概率的显式值**）。

**⭐ 证明**：
1. `bridgeKernelValue_mul_fiber`（**§8**）：`c * F = N`
2. `fiber_normalization_general`（**第 157 轮**）：`N / F = 求和比`
3. `fiber_real_ne_zero`（**§9**）：`F ≠ 0`
**⟹ 由 `eq_div_iff` 即得。** -/
theorem kernelValue_eq_sum_ratio [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (t : Set ((α × β) × γ)) (ht : MeasurableSet t)
    (ω : (α × β) × γ) (hp : ∀ w, 0 ≤ p w)
    (hω : (Fate.FinMeasureBridge.weightedCount p) {ω} ≠ 0)
    (hz : (∑ x : α, ∑ y : β, p ((x, y), ω.2)) ≠ 0)
    [DecidablePred (· ∈ t)] [DecidablePred (· ∈ (t ∩ {w | w.2 = ω.2}))] :
    letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
      Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
    ((condExpKernel (Ω := (α × β) × γ) (Fate.FinMeasureBridge.weightedCount p)
      (MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) ω).real t
      = (∑ x : α, ∑ y : β, (if ((x, y), ω.2) ∈ t then p ((x, y), ω.2) else 0))
        / (∑ x : α, ∑ y : β, p ((x, y), ω.2)) := by
  letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
    Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
  have hmul := bridgeKernelValue_mul_fiber p t ht ω hω
  have hfn := Fate.FinMeasureBridge.fiber_normalization_general p t ω.2 hp
  have hF : (Fate.FinMeasureBridge.weightedCount p).real (Fate.FinMeasureBridge.fiber ω.2) ≠ 0 :=
    fiber_real_ne_zero p hp ω.2 hz
  rw [← hfn]
  rw [eq_div_iff hF]
  exact hmul
/-! ## §11 ⭐⭐⭐ **T2：`t₁` 的原像化（`S1` ⇒ 对 `x ∈ S1` 求和）**（**第 167 轮**）

**⚠ 用途**：桥的纯代数路线（§5）第 (1) 步 —— 把 `comap projX`-可测的 `t₁`
**写成 `S1` 的原像**，从而加权和可化为**对 `x ∈ S1` 的求和**
（`S1` 显式出现在 `_step11/p8.lean` / `p10.lean` 的纤维求和里）。

**⭐ 本条是 `MeasurableSpace.measurableSet_comap` 的**直接实例****：
抽象陈述只需要「存在 `α` 上的可测集」，**不需要任何离散性假设**
（故比 `_step11/p14.lean` 的 `MeasurableSet.of_discrete` 版本更一般）。 -/

/-- ⭐⭐⭐ **`comap projX`-可测集是 `projX` 的原像**（**T2**）。

**证明**：`MeasurableSpace.measurableSet_comap` 给出
`MeasurableSet[comap projX] t ↔ ∃ S, MeasurableSet S ∧ t = projX ⁻¹' S`，
**逐字取之即得。** -/
theorem fiber_sum_projX [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (t₁ : Set ((α × β) × γ))
    (ht₁ : MeasurableSet[MeasurableSpace.comap (Fate.FinCondIndepMeasure.projX : (α × β) × γ → α) inferInstance] t₁)
    (z : γ) :
    ∃ (S1 : Set α), MeasurableSet S1 ∧ t₁ = (Fate.FinCondIndepMeasure.projX : (α × β) × γ → α) ⁻¹' S1 := by
  obtain ⟨S1, hS1, hS1eq⟩ := (MeasurableSpace.measurableSet_comap).mp ht₁
  exact ⟨S1, hS1, hS1eq.symm⟩

/-! ## §12 ⭐⭐⭐⭐⭐ **T4：核心代数引理 —— 条件独立 ⟹ 三重求和的乘积等式**（**第 167 轮**）

**⚠ 任务书原稿的除法形式在 `margZ p z = 0` 时是假的**（Lean 的 `/` 在 0 分母处给 0），
**故本节的**主定理取乘法形式**，并**另给守卫下的除法形式**作为推论 —— 后者是任务书的逐字形式。

### 数学内容

由 `CondIndepFin p`（即 `∀ x y z, p((x,y),z) · margZ z = margXZ x z · margYZ y z`），
对 `x ∈ S1`、`y ∈ S2` 求和（`margZ z` 与 `x,y` 无关，可提出）：

$$\Big(\sum_{x\in S_1}\sum_{y\in S_2} p\,((x,y),z)\Big)\cdot \mathrm{margZ}\ p\ z
  = \Big(\sum_{x\in S_1}\mathrm{margXZ}\ p\,x\,z\Big)\Big(\sum_{y\in S_2}\mathrm{margYZ}\ p\,y\,z\Big)$$

右边先拆成 `∑_{x∈S1} ∑_{y∈S2} margXZ·margYZ`（乘法分配），左边先把 `margZ` 提进内层。
**这是「条件独立 ⟹ 求和比」的唯一正确代数桥梁。**

### ⚠ 与任务书原稿的差异（如实登记）

| 项 | 任务书原稿 | 本节 |
|---|---|---|
| 形式 | **除法** | **乘法**（无条件成立） |
| 除法版 | 无守卫 ⟹ **假** | 加 `margZ ≠ 0` 守卫 ⟹ 真 |
| 正性/归一化假设 | 无 | 无（本定理对任意实值 `p` 成立）|
| `Fintype γ` | 需要 | **不需要**（`z` 是点，不对 `γ` 求和）|

**⟹ 任务书的陈述在字面上**不是定理**（`margZ = 0` 时反例平凡），
**其**唯一的正确化**即下面的乘法形式与带守卫的除法形式。 -/

/-- ⭐⭐⭐⭐⭐ **T4 核心代数引理（乘法形式，无守卫）**。

**这是任务书陈述的正确化**：去掉除法、不设正性/归一化假设、
**对任意实值联合律成立**。 -/
theorem condIndepFin_sum_factorize [Fintype α] [Fintype β]
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (h : FateV2.Modeling.FiniteCondIndep.CondIndepFin p)
    (S1 : Set α) (S2 : Set β) (z : γ)
    [DecidablePred (· ∈ S1)] [DecidablePred (· ∈ S2)] :
    (∑ x : α, ∑ y : β, (if x ∈ S1 ∧ y ∈ S2 then p ((x, y), z) else 0))
        * (∑ x : α, ∑ y : β, p ((x, y), z))
      = (∑ x : α, (if x ∈ S1 then (∑ y : β, p ((x, y), z)) else 0))
        * (∑ y : β, (if y ∈ S2 then (∑ x : α, p ((x, y), z)) else 0)) := by
  -- (i) 逐点的乘性等式（展开三个边缘律的定义）。
  have key : ∀ x y, p ((x, y), z) * (∑ x : α, ∑ y : β, p ((x, y), z))
      = (∑ y : β, p ((x, y), z)) * (∑ x : α, p ((x, y), z)) := by
    intro x y
    have hh := h x y z
    rw [FateV2.Modeling.FiniteCondIndep.margXZ, FateV2.Modeling.FiniteCondIndep.margYZ,
      FateV2.Modeling.FiniteCondIndep.margZ] at hh
    exact hh
  calc (∑ x : α, ∑ y : β, (if x ∈ S1 ∧ y ∈ S2 then p ((x, y), z) else 0))
        * (∑ x : α, ∑ y : β, p ((x, y), z))
      = ∑ x : α, ∑ y : β, (if x ∈ S1 ∧ y ∈ S2 then p ((x, y), z) else 0)
          * (∑ x : α, ∑ y : β, p ((x, y), z)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ x : α, ∑ y : β, (if x ∈ S1 ∧ y ∈ S2 then
          (∑ y' : β, p ((x, y'), z)) * (∑ x' : α, p ((x', y), z)) else 0) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        by_cases hc : x ∈ S1 ∧ y ∈ S2
        · rw [if_pos hc, if_pos hc, key]
        · rw [if_neg hc, if_neg hc, zero_mul]
    _ = (∑ x : α, (if x ∈ S1 then (∑ y : β, p ((x, y), z)) else 0))
        * (∑ y : β, (if y ∈ S2 then (∑ x : α, p ((x, y), z)) else 0)) := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        by_cases h1 : x ∈ S1
        · by_cases h2 : y ∈ S2
          · rw [if_pos (⟨h1, h2⟩ : x ∈ S1 ∧ y ∈ S2), if_pos h1, if_pos h2]
          · rw [if_neg (fun hh => h2 hh.2), if_pos h1, if_neg h2, mul_zero]
        · rw [if_neg (fun hh => h1 hh.1), if_neg h1, zero_mul]

/-- ⭐⭐⭐⭐ **T4 核心代数引理（除法形式，带 `margZ ≠ 0` 守卫）** ——
**这是任务书原稿的逐字形式**（守卫是必需的），在守卫下由乘法形式推出。 -/
theorem condIndepFin_sum_factorize_div [Fintype α] [Fintype β]
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (h : FateV2.Modeling.FiniteCondIndep.CondIndepFin p)
    (S1 : Set α) (S2 : Set β) (z : γ)
    [DecidablePred (· ∈ S1)] [DecidablePred (· ∈ S2)]
    (hz : (∑ x : α, ∑ y : β, p ((x, y), z)) ≠ 0) :
    (∑ x : α, ∑ y : β, (if x ∈ S1 ∧ y ∈ S2 then p ((x, y), z) else 0))
      = (∑ x : α, (if x ∈ S1 then (∑ y : β, p ((x, y), z)) else 0))
        * (∑ y : β, (if y ∈ S2 then (∑ x : α, p ((x, y), z)) else 0))
        / (∑ x : α, ∑ y : β, p ((x, y), z)) := by
  rw [eq_div_iff hz]
  exact condIndepFin_sum_factorize p h S1 S2 z

/-! ## §13 ⭐⭐⭐⭐⭐ **核值的 ENNReal 版**（**第 168 轮**）

**⚠⚠ 组装的**最后一个技术障碍****：
`bridgeStatement` 要的是 `(κ a) t`（**ENNReal**），
**而 §10 的 `kernelValue_eq_sum_ratio` 给的是**实数版** `(κ a).real t`。**

**⭐⭐ 解法**：**`Measure.real` 的定义 + `ENNReal.ofReal_toReal`**
（**因为 `κ a` 是有限测度，`(κ a) t ≠ ⊤`**）。** -/

/-- ⭐⭐⭐⭐⭐ **核值的 ENNReal 版**（**桥组装的最后一块**）。 -/
theorem kernelValue_ennreal [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (t : Set ((α × β) × γ)) (ht : MeasurableSet t)
    (ω : (α × β) × γ) (hp : ∀ w, 0 ≤ p w)
    (hω : (Fate.FinMeasureBridge.weightedCount p) {ω} ≠ 0)
    (hz : (∑ x : α, ∑ y : β, p ((x, y), ω.2)) ≠ 0)
    [DecidablePred (· ∈ t)] [DecidablePred (· ∈ (t ∩ {w | w.2 = ω.2}))] :
    letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
      Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
    ((condExpKernel (Ω := (α × β) × γ) (Fate.FinMeasureBridge.weightedCount p)
      (MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) ω) t
      = ENNReal.ofReal ((∑ x : α, ∑ y : β, (if ((x, y), ω.2) ∈ t then p ((x, y), ω.2) else 0))
        / (∑ x : α, ∑ y : β, p ((x, y), ω.2))) := by
  letI : IsFiniteMeasure (Fate.FinMeasureBridge.weightedCount p) :=
    Fate.FinMeasureBridge.weightedCount_isFiniteMeasure p
  have hreal := kernelValue_eq_sum_ratio p t ht ω hp hω hz
  rw [← hreal]
  rw [Measure.real]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

/-! ## §14 ⭐⭐⭐⭐ **`trim` 在单点上的值 = 纤维质量**（**第 170 轮**）

**⚠⚠ 这解开了第 169 轮的**死结****。

**第 169 轮代理 A2 形式化了一个反例**：
`(μ.trim hm) {a} ≠ 0 → μ {a} ≠ 0` **是假的**
（因为 `trim` 是 `OuterMeasure.toMeasure`，`{a}` 的最小 `m'`-可测覆盖是**整条纤维**）。
**代理 A4 指出**：`(μ.trim hm) {a} = μ (fiber a.2)` ——
**⟹ `trim` 一侧的「零测点」判据是**纤维质量**，不是单点质量。**

**⭐⭐ 本节给出这个事实的形式化基础**：
`m' = comap projZ` 的可测集**都是纤维的并**
⟹ **任何含 `a` 的 `m'`-可测集必含 `fiber a.2`**
⟹ `{a}` 的最小 `m'`-可测覆盖 = `fiber a.2`。 -/

/-- ⭐⭐⭐⭐ **`m'`-可测集是纤维饱和的**（**结构引理**）。

**⚠ 即**：若 `s` 是 `comap projZ`-可测且 `a ∈ s`，则**整条 `fiber a.2` 都在 `s` 里**。 -/
theorem comap_projZ_mem_fiber [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {s : Set ((α × β) × γ)}
    (hs : MeasurableSet[MeasurableSpace.comap (Fate.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance] s)
    {a : (α × β) × γ} (ha : a ∈ s) :
    Fate.FinMeasureBridge.fiber a.2 ⊆ s := by
  obtain ⟨S, _, hS⟩ := (MeasurableSpace.measurableSet_comap).mp hs
  rw [← hS] at ha ⊢
  intro w hw
  have hw2 : w.2 = a.2 := by simpa [Fate.FinMeasureBridge.fiber] using hw
  show w.2 ∈ S
  rw [hw2]
  exact ha

end FateV2.Modeling.BridgeKernel
