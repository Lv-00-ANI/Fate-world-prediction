import FateWorld.FateV2.Modeling.BridgeKernel
open MeasureTheory ProbabilityTheory

-- ⭐ 第 173 轮：移除了 set_option linter.unusedSectionVars false（依 C5 的审核建议）
-- ⚠ 该设置会掩盖「未使用的 section 变量」，导致签名漂移无人察觉。

/-!
  # Modeling · BridgeFinal

  ## 迁移登记
  - 来源：`FateWorld/Legacy/BridgeFinal.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BridgeKernel
  - 补充 open 域：无
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §B3  ⭐⭐⭐⭐⭐ **桥的最终定理**（第 170 轮 A4 洞察的直接组装）

  ```
  FateV2.Modeling.FiniteCondIndep.CondIndepFin p  →  FateV2.Modeling.FinCondIndepMeasure.bridgeStatement p
  ```

  ## 本轮（A4）的关键洞察

  `(μ.trim hm) {a} = μ (fiber a.2)`（`trim_singleton_eq_fiber`）。

  **⟹ `bridgeStatement` 的 `∀ᵐ a ∂(μ.trim hm)` 的「零测点」判据是**
  **纤维质量 `μ (fiber a.2)`，而不是单点质量 `μ {a}`。**

  **⟹ 只需在「纤维质量非零」时做逐点计算** ——
  而在那种情形下，可以用「同纤维内取一个 `p ≠ 0` 的点」把核值搬过去。

  ## 组装链（全部**无 `sorry`**）

  | 步 | 内容 | 工具 |
  |---|---|---|
  | 1 | `bridgeStatement` ↔ 对 `μ.trim hm'` 的逐点乘积等式 | `bridgeStatement_unfold_def` |
  | 2 | `∀ᵐ` 对 `trim` 精确展开为 `∀a, trim{a}=0 ∨ P a` | ⭐ 本文件 `ae_iff_forall_or_zero`（对 `trim` 直接用）|
  | 3 | `trim {a} = μ(fiber a.2)` | ⭐ 本文件 `trim_singleton_eq_fiber`（自含证明）|
  | 4 | 纤维质量 ≠ 0 ⟹ 纤维内存在 `p ≠ 0` 的点 | `Finset.exists_ne_zero_of_sum_ne_zero` + `weightedCount_singleton` |
  | 5 | 同一纤维内 `condExpKernel` 相等 | `measurableAtom` + `Kernel.apply_congr_of_mem_measurableAtom` |
  | 6 | `κ(a).real t = μ.real(t ∩ fiber z) / μ.real(fiber z)` | `bridgeKernelValue_mul_fiber`（`BridgeKernel §8`）|
  | 7 | 三个商的分子分母 = 三个二重和 | ⭐ 本文件 `num1_eq` / `num2_eq` / `num3_eq`（自含）|
  | 8 | `CondIndepFin` 纯代数因子化 | `condIndepFin_sum_factorize`（`BridgeKernel §12`）|
  | 9 | `.real` 等式 ⟹ ENNReal 等式（两边有限）| `ENNReal.toReal_eq_toReal_iff'` |

  ⚠ **注意**：任务书提到若缺 `trim_singleton_eq_fiber`（B1）或
  `kernelValue_fiber_ratio`（B2）可把它们当作假设接受。
  **本轮（B3）实际做法是**：**在本文件内自含证明**这两条（§1、§6），
  故最终定理不依赖任何未入库的假设，也**没有 `sorry`**。
  =========================================================================== -/

namespace FateV2.Modeling
namespace FinalB3

variable {α β γ : Type}
  [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
  [MeasurableSingletonClass ((α × β) × γ)]
  [Countable α] [Countable β] [Countable γ]

open FateV2.Modeling.FinMeasureBridge

/-! ## §1 ⭐⭐⭐⭐ `trim` 在单点上的值 = 纤维质量（**自含证明**）

**⚠ 这里不用 `Fate.GapTrimWeightedCount` 的名字**（它在 `BridgeKernel` 之外），
故在本文件内重证一遍 —— 证明与 `GapTrimWeightedCount §99.3` 完全同构，
只额外需要 `[MeasurableSingletonClass γ]`（由 `[DiscreteMeasurableSpace γ]` 提供）。 -/

omit [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] [MeasurableSpace α] [MeasurableSpace β] [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [MeasurableSingletonClass ((α × β) × γ)] [Countable α] [Countable β] in
/-- **`fiber c` 是 `comap projZ`-可测的**（`{c}` 的原像）。 -/
theorem fiber_measurable_comap (c : γ) :
    MeasurableSet[MeasurableSpace.comap
      (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance]
      (fiber c) := by
  rw [fiber]
  exact MeasurableSpace.measurableSet_comap.mpr
    ⟨{c}, measurableSet_singleton c, rfl⟩

omit [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [MeasurableSingletonClass ((α × β) × γ)] [Countable α] [Countable β] in
/-- ⭐⭐⭐⭐ **`(μ.trim hm) {a} = μ (fiber a.2)`**。 -/
theorem trim_singleton_eq_fiber (μ : Measure ((α × β) × γ))
    (a : (α × β) × γ) :
    μ.trim (MeasurableSpace.comap_le_iff_le_map.mpr
        (FinCondIndepMeasure.measurable_projZ (α := α) (β := β) (γ := γ))) {a}
      = μ (fiber a.2) := by
  obtain hm : MeasurableSpace.comap
        (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance
      ≤ (inferInstance : MeasurableSpace ((α × β) × γ)) :=
    MeasurableSpace.comap_le_iff_le_map.mpr
      (FateV2.Modeling.FinCondIndepMeasure.measurable_projZ (α := α) (β := β) (γ := γ))
  refine le_antisymm ?_ ?_
  · calc (μ.trim hm) {a}
        ≤ (μ.trim hm) (fiber a.2) := by
          refine measure_mono ?_
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          subst hw
          rfl
      _ = μ (fiber a.2) := trim_measurableSet_eq hm (fiber_measurable_comap a.2)
  · -- 下界：`(μ.trim hm) {a} = OuterMeasure.trim μ.toOuterMeasure {a}`，再取 `⨅`
    have hkey : (μ.trim hm) {a} = @OuterMeasure.trim ((α × β) × γ)
        (MeasurableSpace.comap
          (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)
        μ.toOuterMeasure {a} := by
      have h1 := toOuterMeasure_trim_eq_trim_toOuterMeasure μ hm
      have h2 : (@Measure.toOuterMeasure _ (MeasurableSpace.comap
            (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)
          (μ.trim hm)) {a} = (μ.trim hm) {a} := rfl
      rw [← h2, h1]
    have hexp : @OuterMeasure.trim ((α × β) × γ)
        (MeasurableSpace.comap
          (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)
        μ.toOuterMeasure {a}
        = ⨅ (t : Set ((α × β) × γ)), ⨅ (_ : {a} ⊆ t),
            ⨅ (_ : MeasurableSet[MeasurableSpace.comap
              (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance] t), μ t :=
      @OuterMeasure.trim_eq_iInf _ (MeasurableSpace.comap
        (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance) μ.toOuterMeasure {a}
    rw [hkey, hexp]
    refine le_iInf fun t => le_iInf fun hsub => le_iInf fun ht => ?_
    -- `t` 是 `comap projZ`-可测且含 `a` ⟹ `fiber a.2 ⊆ t`（由 `comap_projZ_mem_fiber`）
    exact measure_mono (comap_projZ_mem_fiber ht (hsub (Set.mem_singleton_iff.mpr rfl)))

/-! ## §2 ⭐⭐⭐ `∀ᵐ` 对任意有限测度的精确展开（**自含，避免名字依赖**） -/

/-- ⭐⭐⭐ **有限测度上 `∀ᵐ` 的精确展开**（任意可测空间版本）：
`∀ᵐ ω ∂μ, P ω ↔ ∀ ω, μ {ω} = 0 ∨ P ω`。

**⚠ 本文件自含证明**（`ae_iff_of_countable` 的直接整理），
以便对**任意可测空间上的** `μ`（特别是 `μ.trim hm'`）直接使用。 -/
theorem ae_iff_forall_or_zero {Ω : Type} [MeasurableSpace Ω] [Countable Ω]
    (μ : Measure Ω) (P : Ω → Prop) :
    (∀ᵐ ω ∂μ, P ω) ↔ ∀ ω, μ {ω} = 0 ∨ P ω := by
  rw [ae_iff_of_countable]
  constructor
  · intro h ω
    by_cases hP : P ω
    · exact Or.inr hP
    · left
      by_contra hne
      exact hP (h ω hne)
  · intro h ω hne
    rcases h ω with h0 | hP
    · exact absurd h0 hne
    · exact hP

/-! ## §3 ⭐⭐ 纤维内的代数零件 -/

omit [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ] [Countable α] [Countable β] [Countable γ] in
/-- 纤维质量（ENNReal）非零 ⟹ 存在纤维内 `p ≠ 0` 的点。 -/
theorem exists_pos_in_fiber (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (hp : ∀ w, 0 ≤ p w) (z : γ)
    (hF : (weightedCount p) (fiber z) ≠ 0) :
    ∃ x : α, ∃ y : β, ((weightedCount p) {((x, y), z)} ≠ 0) := by
  have hsum : (∑ x : α, ∑ y : β, p ((x, y), z)) ≠ 0 :=
    (fiber_ne_zero_iff p hp z).mp hF
  obtain ⟨x₀, -, hx₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  obtain ⟨y₀, -, hy₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx₀
  refine ⟨x₀, y₀, ?_⟩
  intro h0
  rw [weightedCount_singleton] at h0
  have hle : p ((x₀, y₀), z) ≤ 0 := by
    by_contra hlt
    rw [not_le] at hlt
    exact absurd h0 (ne_of_gt (ENNReal.ofReal_pos.mpr hlt))
  exact hy₀ (le_antisymm hle (hp _))

omit [MeasurableSingletonClass ((α × β) × γ)] in
/-- 同一纤维内的两点给出相同的 `condExpKernel`（`m' = comap projZ`-原子）。 -/
theorem condExpKernel_fiber_eq (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (x x' : α) (y y' : β) (z : γ) :
    letI : IsFiniteMeasure (weightedCount p) := weightedCount_isFiniteMeasure p
    condExpKernel (Ω := (α × β) × γ) (weightedCount p)
      (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ)
        (inferInstance : MeasurableSpace γ)) ((x, y), z)
    = condExpKernel (Ω := (α × β) × γ) (weightedCount p)
      (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ)
        (inferInstance : MeasurableSpace γ)) ((x', y'), z) := by
  letI : IsFiniteMeasure (weightedCount p) := weightedCount_isFiniteMeasure p
  let m' := MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ)
    (inferInstance : MeasurableSpace γ)
  have h : ((x, y), z) ∈ @measurableAtom ((α × β) × γ) m' ((x', y'), z) := by
    simp only [measurableAtom, Set.mem_iInter]
    intro s hs hms
    have hz : (FateV2.Modeling.FinCondIndepMeasure.projZ ((x, y), z))
        = (FateV2.Modeling.FinCondIndepMeasure.projZ ((x', y'), z)) := rfl
    obtain ⟨T, hT, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hms
    show FateV2.Modeling.FinCondIndepMeasure.projZ ((x, y), z) ∈ T
    rw [hz]; exact hs
  exact Kernel.apply_congr_of_mem_measurableAtom _ h

/-- ⭐⭐⭐ **核值 = 完全显式的商**（**B2 的 `kernelValue_fiber_ratio`**，
本文件自含证明，**只需纤维质量非零**）。

$$\kappa_a(t).\mathrm{real} = \frac{\sum_{(x,y)}[((x,y),z)\in t]\,p((x,y),z)}{\sum_{(x,y)}p((x,y),z)}$$

**⭐ 证明**：
纤维内取 `p ≠ 0` 的点 `((x₀,y₀),z)` ⟹ `bridgeKernelValue_mul_fiber` 给出商；
再由 `condExpKernel_fiber_eq` 把 `a` 处的核值搬到 `((x₀,y₀),z)`。 -/
theorem kernelValue_fiber_ratio (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (t : Set ((α × β) × γ)) (ht : MeasurableSet t)
    (hp : ∀ w, 0 ≤ p w) (a : (α × β) × γ)
    (hF : (weightedCount p).real (fiber a.2) ≠ 0)
    [DecidablePred (· ∈ t)] [DecidablePred (· ∈ (t ∩ fiber a.2))] :
    letI : IsFiniteMeasure (weightedCount p) := weightedCount_isFiniteMeasure p
    ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
      (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) a).real t
      = (∑ x : α, ∑ y : β, (if ((x, y), a.2) ∈ t then p ((x, y), a.2) else 0))
        / (∑ x : α, ∑ y : β, p ((x, y), a.2)) := by
  letI : IsFiniteMeasure (weightedCount p) := weightedCount_isFiniteMeasure p
  obtain ⟨⟨xa, ya⟩, za⟩ := a
  -- 纤维质量（ENNReal）非零
  have hFenn : (weightedCount p) (fiber za) ≠ 0 := by
    intro h0
    exact hF (by rw [Measure.real, h0]; simp)
  obtain ⟨x₀, y₀, hsing⟩ := exists_pos_in_fiber p hp za hFenn
  -- 三个 `=ᵐ` 端点（`bridgeKernelValue_mul_fiber`）
  have hmul := bridgeKernelValue_mul_fiber p t ht ((x₀, y₀), za) hsing
  -- `real` 分母非零
  have hFr : (weightedCount p).real (fiber za) ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨hFenn, measure_ne_top _ _⟩
  -- 商形式（在 `((x₀,y₀),za)` 处）
  have hratio : ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
      (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
        ((x₀, y₀), za)).real t
      = (weightedCount p).real (t ∩ fiber za) / (weightedCount p).real (fiber za) := by
    rw [eq_div_iff hFr]
    have := hmul
    simp only [fiber] at this
    linarith
  -- 把核值从 `a` 搬到 `((x₀,y₀),za)`（同纤维 ⟹ 核相等）
  have hsame := congrArg (fun m => m.real t)
    (condExpKernel_fiber_eq p xa x₀ ya y₀ za)
  -- `Measure.real` 形式的归一化
  have hnorm := fiber_normalization_general (p := p) t za hp
  rw [hsame, hratio]
  simpa [fiber] using hnorm

/-! ## §4 ⭐⭐⭐ **三个分子 / 分母的二重和形式**（`Step11Core §3` 的自含副本） -/

omit [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ] [Countable α] [Countable β] [Countable γ] in
/-- ⭐⭐⭐ `μ.real(t₁ ∩ t₂ ∩ fiber z)` 的二重和形式。 -/
theorem num1_eq (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (hp : ∀ w, 0 ≤ p w) (S1 : Set α) (S2 : Set β)
    [DecidablePred (· ∈ S1)] [DecidablePred (· ∈ S2)] (z : γ) :
    (weightedCount p).real
      (({w : (α × β) × γ | w.1.1 ∈ S1} ∩ {w : (α × β) × γ | w.1.2 ∈ S2}) ∩ fiber z)
      = ∑ x : α, ∑ y : β, (if x ∈ S1 ∧ y ∈ S2 then p ((x, y), z) else 0) := by
  simp only [fiber]
  have hDec : DecidablePred (· ∈ (({w : (α × β) × γ | w.1.1 ∈ S1}
      ∩ {w : (α × β) × γ | w.1.2 ∈ S2}) ∩ {w : (α × β) × γ | w.2 = z})) := fun w => by
    by_cases h1 : w.1.1 ∈ S1
    · by_cases h2 : w.1.2 ∈ S2
      · by_cases h3 : w.2 = z
        · exact isTrue ⟨⟨h1, h2⟩, h3⟩
        · exact isFalse (fun hc => h3 hc.2)
      · exact isFalse (fun hc => h2 hc.1.2)
    · exact isFalse (fun hc => h1 hc.1.1)
  haveI := hDec
  have hset : (({w : (α × β) × γ | w.1.1 ∈ S1} ∩ {w : (α × β) × γ | w.1.2 ∈ S2})
      ∩ {w : (α × β) × γ | w.2 = z})
      = ({w : (α × β) × γ | w.1.1 ∈ S1 ∧ w.1.2 ∈ S2} ∩ {w : (α × β) × γ | w.2 = z}) := by
    ext w; simp [Set.mem_inter_iff]
  rw [hset, Measure.real, weightedCount_apply]
  rw [ENNReal.toReal_sum (f := fun x => ∑ y, ∑ z',
      (if (((x, y), z') ∈ ({w : (α × β) × γ | w.1.1 ∈ S1 ∧ w.1.2 ∈ S2}
            ∩ {w' : (α × β) × γ | w'.2 = z}))
       then ENNReal.ofReal (p ((x, y), z')) else 0))
    (fun x _ => by
      rw [ENNReal.sum_ne_top]; intro y _; rw [ENNReal.sum_ne_top]; intro z' _; split <;> simp)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [ENNReal.toReal_sum (f := fun y => ∑ z',
      (if (((x, y), z') ∈ ({w : (α × β) × γ | w.1.1 ∈ S1 ∧ w.1.2 ∈ S2}
            ∩ {w' : (α × β) × γ | w'.2 = z}))
       then ENNReal.ofReal (p ((x, y), z')) else 0))
    (fun y _ => by
      rw [ENNReal.sum_ne_top]; intro z' _; split <;> simp)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.sum_eq_single z]
  · simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_true]
    by_cases hc : x ∈ S1 ∧ y ∈ S2
    · rw [if_pos hc, if_pos hc, ENNReal.toReal_ofReal (hp _)]
    · rw [if_neg hc, if_neg hc, ENNReal.toReal_zero]
  · intro z' _ hz'
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hz', and_false, if_false]
  · intro h; exact absurd (Finset.mem_univ z) h

omit [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ] [Countable α] [Countable β] [Countable γ] in
/-- ⭐⭐⭐ `μ.real(t₁ ∩ fiber z)` 的二重和形式。 -/
theorem num2_eq (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (hp : ∀ w, 0 ≤ p w) (S1 : Set α) [DecidablePred (· ∈ S1)] (z : γ) :
    (weightedCount p).real
      ({w : (α × β) × γ | w.1.1 ∈ S1} ∩ fiber z)
      = ∑ x : α, ∑ y : β, (if x ∈ S1 then p ((x, y), z) else 0) := by
  simp only [fiber]
  have hDec : DecidablePred (· ∈ ({w : (α × β) × γ | w.1.1 ∈ S1}
      ∩ {w : (α × β) × γ | w.2 = z})) := fun w => by
    by_cases h1 : w.1.1 ∈ S1
    · by_cases h3 : w.2 = z
      · exact isTrue ⟨h1, h3⟩
      · exact isFalse (fun hc => h3 hc.2)
    · exact isFalse (fun hc => h1 hc.1)
  haveI := hDec
  rw [Measure.real, weightedCount_apply,
    ENNReal.toReal_sum (f := fun x => ∑ y, ∑ z',
      (if (((x, y), z') ∈ ({w : (α × β) × γ | w.1.1 ∈ S1}
            ∩ {w' : (α × β) × γ | w'.2 = z}))
       then ENNReal.ofReal (p ((x, y), z')) else 0))
    (fun x _ => by
      rw [ENNReal.sum_ne_top]; intro y _; rw [ENNReal.sum_ne_top]; intro z' _; split <;> simp)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [ENNReal.toReal_sum (f := fun y => ∑ z',
      (if (((x, y), z') ∈ ({w : (α × β) × γ | w.1.1 ∈ S1}
            ∩ {w' : (α × β) × γ | w'.2 = z}))
       then ENNReal.ofReal (p ((x, y), z')) else 0))
    (fun y _ => by
      rw [ENNReal.sum_ne_top]; intro z' _; split <;> simp)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.sum_eq_single z]
  · simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_true]
    by_cases hc : x ∈ S1
    · rw [if_pos hc, if_pos hc, ENNReal.toReal_ofReal (hp _)]
    · rw [if_neg hc, if_neg hc, ENNReal.toReal_zero]
  · intro z' _ hz'
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hz', and_false, if_false]
  · intro h; exact absurd (Finset.mem_univ z) h

omit [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ] [Countable α] [Countable β] [Countable γ] in
/-- ⭐⭐⭐ `μ.real(t₂ ∩ fiber z)` 的二重和形式。 -/
theorem num3_eq (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (hp : ∀ w, 0 ≤ p w) (S2 : Set β) [DecidablePred (· ∈ S2)] (z : γ) :
    (weightedCount p).real
      ({w : (α × β) × γ | w.1.2 ∈ S2} ∩ fiber z)
      = ∑ x : α, ∑ y : β, (if y ∈ S2 then p ((x, y), z) else 0) := by
  simp only [fiber]
  have hDec : DecidablePred (· ∈ ({w : (α × β) × γ | w.1.2 ∈ S2}
      ∩ {w : (α × β) × γ | w.2 = z})) := fun w => by
    by_cases h1 : w.1.2 ∈ S2
    · by_cases h3 : w.2 = z
      · exact isTrue ⟨h1, h3⟩
      · exact isFalse (fun hc => h3 hc.2)
    · exact isFalse (fun hc => h1 hc.1)
  haveI := hDec
  rw [Measure.real, weightedCount_apply]
  have hsum : (∑ x : α, ∑ y : β, ∑ z',
      (if ((x, y), z') ∈ ({w : (α × β) × γ | w.1.2 ∈ S2}
            ∩ {w : (α × β) × γ | w.2 = z})
       then ENNReal.ofReal (p ((x, y), z')) else 0))
      = ∑ x : α, ∑ y : β, (if y ∈ S2 then ENNReal.ofReal (p ((x, y), z)) else 0) := by
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [Finset.sum_eq_single z]
    · by_cases hc : y ∈ S2
      · rw [if_pos hc]; simp [hc]
      · rw [if_neg hc]
        rw [if_neg]; intro hh; exact hc hh.1
    · intro z' _ hz'
      have : ((x, y), z') ∉ ({w : (α × β) × γ | w.1.2 ∈ S2}
          ∩ {w : (α × β) × γ | w.2 = z}) := by simp [hz']
      rw [if_neg this]
    · intro h; exact absurd (Finset.mem_univ z) h
  rw [hsum]
  have hpt : ∀ x : α, ∀ y : β, (if y ∈ S2 then ENNReal.ofReal (p ((x, y), z)) else 0).toReal
      = (if y ∈ S2 then p ((x, y), z) else 0) := by
    intro x y
    by_cases hc : y ∈ S2
    · rw [if_pos hc, if_pos hc, ENNReal.toReal_ofReal (hp _)]
    · rw [if_neg hc, if_neg hc, ENNReal.toReal_zero]
  have hmid : ∀ x : α, (∑ y, (if y ∈ S2 then ENNReal.ofReal (p ((x, y), z)) else 0)).toReal
      = ∑ y, (if y ∈ S2 then p ((x, y), z) else 0) := by
    intro x
    rw [ENNReal.toReal_sum (f := fun y => (if y ∈ S2 then ENNReal.ofReal (p ((x, y), z)) else 0))]
    · exact Finset.sum_congr rfl (fun y _ => hpt x y)
    · intro y _; split <;> simp
  rw [ENNReal.toReal_sum
    (f := fun x => ∑ y, (if y ∈ S2 then ENNReal.ofReal (p ((x, y), z)) else 0))
    (fun x _ => by
      rw [ENNReal.sum_ne_top]; intro y _
      by_cases hy : y ∈ S2 <;> simp [hy])]
  exact Finset.sum_congr rfl (fun x _ => hmid x)

omit [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ] [Countable α] [Countable β] [Countable γ] in
/-- 纤维质量（`ℝ`）= `∑x∑y p`。 -/
theorem fiber_real_eq_sum (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (hp : ∀ w, 0 ≤ p w) (z : γ) :
    (weightedCount p).real (fiber z) = ∑ x : α, ∑ y : β, p ((x, y), z) := by
  rw [Measure.real, weightedCount_fiber]
  rw [ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.toReal_sum (fun y _ => ENNReal.ofReal_ne_top)]
    exact Finset.sum_congr rfl fun y _ => ENNReal.toReal_ofReal (hp _)
  · intro x _
    rw [ENNReal.sum_ne_top]
    exact fun y _ => ENNReal.ofReal_ne_top

/-! ## §5 ⭐⭐⭐ **纤维层面的乘积等式**（`Step11Core §4` 的自含副本） -/

omit [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ] [Countable α] [Countable β] [Countable γ] in
/-- ⭐⭐⭐⭐ **纤维上的乘积等式**（`CondIndepFin` 的纯代数结论）。 -/
theorem fiber_mul_eq (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (h : FateV2.Modeling.FiniteCondIndep.CondIndepFin p) (hp : ∀ w, 0 ≤ p w)
    (S1 : Set α) (S2 : Set β) [DecidablePred (· ∈ S1)] [DecidablePred (· ∈ S2)]
    (z : γ) :
    (weightedCount p).real
        (({w : (α × β) × γ | w.1.1 ∈ S1} ∩ {w : (α × β) × γ | w.1.2 ∈ S2}) ∩ fiber z)
      * (weightedCount p).real (fiber z)
    = (weightedCount p).real ({w : (α × β) × γ | w.1.1 ∈ S1} ∩ fiber z)
      * (weightedCount p).real ({w : (α × β) × γ | w.1.2 ∈ S2} ∩ fiber z) := by
  classical
  rw [num1_eq p hp S1 S2 z, num2_eq p hp S1 z, num3_eq p hp S2 z, fiber_real_eq_sum p hp z]
  set M : ℝ := ∑ x : α, ∑ y : β, p ((x, y), z) with hM
  set A : α → ℝ := fun x => ∑ y : β, p ((x, y), z) with hA
  set B : β → ℝ := fun y => ∑ x : α, p ((x, y), z) with hB
  have hLHS : (∑ x : α, ∑ y : β, (if x ∈ S1 ∧ y ∈ S2 then p ((x, y), z) else 0)) * M
      = ∑ x : α, ∑ y : β, (if x ∈ S1 then A x else 0) * (if y ∈ S2 then B y else 0) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have hpnt : p ((x, y), z) * M = A x * B y := by
      simp only [hA, hB, hM]
      exact condIndepFin_pointwise_sum p h x y z
    by_cases hx : x ∈ S1 <;> by_cases hy : y ∈ S2 <;>
      simp only [hx, hy, true_and, false_and, if_true, if_false, and_false] <;>
      linarith [hpnt]
  have hAx : ∀ x : α, (∑ y : β, (if x ∈ S1 then p ((x, y), z) else 0))
      = (if x ∈ S1 then A x else 0) := by
    intro x
    by_cases hc : x ∈ S1
    · rw [if_pos hc]
      simp only [hA]
      exact Finset.sum_congr rfl (fun y _ => by rw [if_pos hc])
    · rw [if_neg hc]
      exact Finset.sum_eq_zero (fun y _ => by rw [if_neg hc])
  have hBy : ∀ y : β, (∑ x : α, (if y ∈ S2 then p ((x, y), z) else 0))
      = (if y ∈ S2 then B y else 0) := by
    intro y
    by_cases hc : y ∈ S2
    · rw [if_pos hc]
      simp only [hB]
      exact Finset.sum_congr rfl (fun x _ => by rw [if_pos hc])
    · rw [if_neg hc]
      exact Finset.sum_eq_zero (fun x _ => by rw [if_neg hc])
  have hRHS : (∑ x : α, ∑ y : β, (if x ∈ S1 then p ((x, y), z) else 0))
      * (∑ x : α, ∑ y : β, (if y ∈ S2 then p ((x, y), z) else 0))
      = ∑ x : α, ∑ y : β, (if x ∈ S1 then A x else 0) * (if y ∈ S2 then B y else 0) := by
    have h1 : (∑ x : α, ∑ y : β, (if x ∈ S1 then p ((x, y), z) else 0))
        = ∑ x : α, (if x ∈ S1 then A x else 0) :=
      Finset.sum_congr rfl (fun x _ => hAx x)
    have h2 : (∑ x : α, ∑ y : β, (if y ∈ S2 then p ((x, y), z) else 0))
        = ∑ y : β, (if y ∈ S2 then B y else 0) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun y _ => hBy y)
    rw [h1, h2, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum]
  rw [hLHS]
  exact hRHS.symm

/-! ## §6 ⭐⭐⭐⭐⭐ **核心：纤维质量非零时的逐点乘积等式** -/

/-- ⭐⭐⭐⭐⭐ **纤维质量非零 ⟹ 三个核值满足乘积等式**（`ENNReal` 层面）。

**⭐ 这是桥的「逐点」内容** —— 而由 `trim {a} = μ(fiber a.2)`，
`∀ᵐ a ∂(μ.trim hm')` 的例外集恰好是 `μ (fiber a.2) = 0` 的那些点。 -/
theorem kernelValue_product_of_fiber_ne
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ) (hp : ∀ w, 0 ≤ p w)
    (hcond : FateV2.Modeling.FiniteCondIndep.CondIndepFin p)
    (S1 : Set α) (S2 : Set β) [DecidablePred (· ∈ S1)] [DecidablePred (· ∈ S2)]
    (a : (α × β) × γ)
    (hF : (weightedCount p) (fiber a.2) ≠ 0) :
    letI : IsFiniteMeasure (weightedCount p) := weightedCount_isFiniteMeasure p
    ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
        (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) a)
        ((FateV2.Modeling.FinCondIndepMeasure.projX : (α × β) × γ → α) ⁻¹' S1
          ∩ (FateV2.Modeling.FinCondIndepMeasure.projY : (α × β) × γ → β) ⁻¹' S2)
      = ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
          (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) a)
          ((FateV2.Modeling.FinCondIndepMeasure.projX : (α × β) × γ → α) ⁻¹' S1)
        * ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
          (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) a)
          ((FateV2.Modeling.FinCondIndepMeasure.projY : (α × β) × γ → β) ⁻¹' S2) := by
  classical
  letI : IsFiniteMeasure (weightedCount p) := weightedCount_isFiniteMeasure p
  obtain ⟨⟨xa, ya⟩, za⟩ := a
  set t1 : Set ((α × β) × γ) := (FateV2.Modeling.FinCondIndepMeasure.projX : (α × β) × γ → α) ⁻¹' S1 with ht1
  set t2 : Set ((α × β) × γ) := (FateV2.Modeling.FinCondIndepMeasure.projY : (α × β) × γ → β) ⁻¹' S2 with ht2
  have ht1' : t1 = {w : (α × β) × γ | w.1.1 ∈ S1} := rfl
  have ht2' : t2 = {w : (α × β) × γ | w.1.2 ∈ S2} := rfl
  -- 可测性
  have hA : MeasurableSet t1 := by rw [ht1']; exact MeasurableSet.of_discrete
  have hB : MeasurableSet t2 := by rw [ht2']; exact MeasurableSet.of_discrete
  have hAB : MeasurableSet (t1 ∩ t2) := hA.inter hB
  -- `real` 纤维质量非零
  have hForeal : (weightedCount p).real (fiber za) ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨hF, measure_ne_top _ _⟩
  -- 分母（求和）非零
  have hz : (∑ x : α, ∑ y : β, p ((x, y), za)) ≠ 0 := by
    rw [← fiber_real_eq_sum p hp za]; exact hForeal
  -- 三个 ℝ 层面的商，全部在 `a` 处（`kernelValue_fiber_ratio` 只需纤维非零）
  have r1 := kernelValue_fiber_ratio p t1 hA hp ((xa, ya), za) hForeal
  have r2 := kernelValue_fiber_ratio p t2 hB hp ((xa, ya), za) hForeal
  have r3 := kernelValue_fiber_ratio p (t1 ∩ t2) hAB hp ((xa, ya), za) hForeal
  -- 分子化为二重和
  have hn1 : (∑ x : α, ∑ y : β, (if ((x, y), za) ∈ t1 ∩ t2 then p ((x, y), za) else 0))
      = ∑ x : α, ∑ y : β, (if x ∈ S1 ∧ y ∈ S2 then p ((x, y), za) else 0) := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    have hmem : (((x, y), za) ∈ t1 ∩ t2) ↔ (x ∈ S1 ∧ y ∈ S2) := by
      rw [ht1', ht2']
      simp [Set.mem_inter_iff]
    by_cases hc : x ∈ S1 ∧ y ∈ S2
    · rw [if_pos (hmem.mpr hc), if_pos hc]
    · rw [if_neg (fun h => hc (hmem.mp h)), if_neg hc]
  have hn2 : (∑ x : α, ∑ y : β, (if ((x, y), za) ∈ t1 then p ((x, y), za) else 0))
      = ∑ x : α, ∑ y : β, (if x ∈ S1 then p ((x, y), za) else 0) := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    have hmem : (((x, y), za) ∈ t1) ↔ (x ∈ S1) := by
      rw [ht1']; simp
    by_cases hc : x ∈ S1
    · rw [if_pos (hmem.mpr hc), if_pos hc]
    · rw [if_neg (fun h => hc (hmem.mp h)), if_neg hc]
  have hn3 : (∑ x : α, ∑ y : β, (if ((x, y), za) ∈ t2 then p ((x, y), za) else 0))
      = ∑ x : α, ∑ y : β, (if y ∈ S2 then p ((x, y), za) else 0) := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    have hmem : (((x, y), za) ∈ t2) ↔ (y ∈ S2) := by
      rw [ht2']; simp
    by_cases hc : y ∈ S2
    · rw [if_pos (hmem.mpr hc), if_pos hc]
    · rw [if_neg (fun h => hc (hmem.mp h)), if_neg hc]
  -- ℝ 层面的乘积等式
  have hreal : ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
        (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
        ((xa, ya), za)).real (t1 ∩ t2)
      = ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
        (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
        ((xa, ya), za)).real t1
        * ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
        (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
        ((xa, ya), za)).real t2 := by
    have hM : (∑ x : α, ∑ y : β, p ((x, y), za)) ≠ 0 := hz
    -- 把 `condIndepFin_sum_factorize` 的「加权和」化为二重和
    have hfac : (∑ x : α, ∑ y : β, (if x ∈ S1 ∧ y ∈ S2 then p ((x, y), za) else 0))
          * (∑ x : α, ∑ y : β, p ((x, y), za))
        = (∑ x : α, ∑ y : β, (if x ∈ S1 then p ((x, y), za) else 0))
          * (∑ x : α, ∑ y : β, (if y ∈ S2 then p ((x, y), za) else 0)) := by
      have h0 := condIndepFin_sum_factorize p hcond S1 S2 za
      have e1 : (∑ x : α, if x ∈ S1 then ∑ y, p ((x, y), za) else 0)
          = ∑ x : α, ∑ y : β, (if x ∈ S1 then p ((x, y), za) else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : x ∈ S1
        · rw [if_pos hx]; exact Finset.sum_congr rfl fun y _ => by rw [if_pos hx]
        · rw [if_neg hx]
          exact (Finset.sum_eq_zero fun y _ => by rw [if_neg hx]).symm
      have e2 : (∑ y : β, if y ∈ S2 then ∑ x, p ((x, y), za) else 0)
          = ∑ x : α, ∑ y : β, (if y ∈ S2 then p ((x, y), za) else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases hy : y ∈ S2
        · rw [if_pos hy]; exact Finset.sum_congr rfl fun x _ => by rw [if_pos hy]
        · rw [if_neg hy]
          exact (Finset.sum_eq_zero fun x _ => by rw [if_neg hy]).symm
      rw [e1, e2] at h0
      exact h0
    have keyeq : (∑ x : α, ∑ y : β, (if x ∈ S1 ∧ y ∈ S2 then p ((x, y), za) else 0))
          / (∑ x : α, ∑ y : β, p ((x, y), za))
        = ((∑ x : α, ∑ y : β, (if x ∈ S1 then p ((x, y), za) else 0))
            / (∑ x : α, ∑ y : β, p ((x, y), za)))
          * ((∑ x : α, ∑ y : β, (if y ∈ S2 then p ((x, y), za) else 0))
            / (∑ x : α, ∑ y : β, p ((x, y), za))) := by
      field_simp
      linarith
    calc ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
          (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
          ((xa, ya), za)).real (t1 ∩ t2)
        = (∑ x : α, ∑ y : β, (if ((x, y), za) ∈ t1 ∩ t2 then p ((x, y), za) else 0))
            / (∑ x : α, ∑ y : β, p ((x, y), za)) := r3
      _ = (∑ x : α, ∑ y : β, (if x ∈ S1 ∧ y ∈ S2 then p ((x, y), za) else 0))
            / (∑ x : α, ∑ y : β, p ((x, y), za)) := by rw [hn1]
      _ = ((∑ x : α, ∑ y : β, (if x ∈ S1 then p ((x, y), za) else 0))
            / (∑ x : α, ∑ y : β, p ((x, y), za)))
          * ((∑ x : α, ∑ y : β, (if y ∈ S2 then p ((x, y), za) else 0))
            / (∑ x : α, ∑ y : β, p ((x, y), za))) := keyeq
      _ = ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
          (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
          ((xa, ya), za)).real t1
          * ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
          (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
          ((xa, ya), za)).real t2 := by rw [r1, r2, hn2, hn3]
  -- 回到 `ENNReal`
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ?_).mp ?_
  · exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  · rw [ENNReal.toReal_mul]
    exact hreal

/-! ## §7 ⭐⭐⭐⭐⭐⭐ **主定理** -/

/-- ⭐⭐⭐⭐⭐⭐ **桥的最终定理**：条件独立（有限联合律的组合形式）**蕴含**
概率语义下的 `CondIndepFun`。 -/
theorem condIndepFin_to_bridge
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (hp : ∀ w, 0 ≤ p w)
    (hcond : FateV2.Modeling.FiniteCondIndep.CondIndepFin p) :
    FateV2.Modeling.FinCondIndepMeasure.bridgeStatement p := by
  classical
  letI : IsFiniteMeasure (weightedCount p) := weightedCount_isFiniteMeasure p
  refine (bridgeStatement_unfold_def (α := α) (β := β) (γ := γ) p).mpr ?_
  intro t₁ t₂ ht₁ ht₂
  -- `t₁`、`t₂` 化为原像
  obtain ⟨S1, hS1, hS1eq⟩ := (MeasurableSpace.measurableSet_comap).mp ht₁
  obtain ⟨S2, hS2, hS2eq⟩ := (MeasurableSpace.measurableSet_comap).mp ht₂
  rw [← hS1eq, ← hS2eq]
  -- `∀ᵐ` 对 `trim` 精确展开（`ae_iff_forall_or_zero` 直接对 `μ.trim hm'` 用）
  -- ⚠ 显式给出 `m'` 与 `mΩ`（否则 `trim` 的类型类参数被推断成 `Prod.instMeasurableSpace`）
  let hm' : MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ)
      (inferInstance : MeasurableSpace γ) ≤ (inferInstance : MeasurableSpace ((α × β) × γ)) :=
    MeasurableSpace.comap_le_iff_le_map.mpr
      (FateV2.Modeling.FinCondIndepMeasure.measurable_projZ (α := α) (β := β) (γ := γ))
  show (∀ᵐ a ∂(@Measure.trim ((α × β) × γ)
      (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ)
        (inferInstance : MeasurableSpace γ))
      (inferInstance : MeasurableSpace ((α × β) × γ)) (weightedCount p) hm'),
      ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
          (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) a)
          ((FateV2.Modeling.FinCondIndepMeasure.projX : (α × β) × γ → α) ⁻¹' S1
            ∩ (FateV2.Modeling.FinCondIndepMeasure.projY : (α × β) × γ → β) ⁻¹' S2)
        = ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
            (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) a)
            ((FateV2.Modeling.FinCondIndepMeasure.projX : (α × β) × γ → α) ⁻¹' S1)
          * ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
            (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) a)
            ((FateV2.Modeling.FinCondIndepMeasure.projY : (α × β) × γ → β) ⁻¹' S2))
  refine (@ae_iff_forall_or_zero ((α × β) × γ)
    (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ)
      (inferInstance : MeasurableSpace γ)) _
    (@Measure.trim ((α × β) × γ)
      (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ)
        (inferInstance : MeasurableSpace γ))
      (inferInstance : MeasurableSpace ((α × β) × γ)) (weightedCount p) hm')
    (fun a => ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
        (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) a)
        ((FateV2.Modeling.FinCondIndepMeasure.projX : (α × β) × γ → α) ⁻¹' S1
          ∩ (FateV2.Modeling.FinCondIndepMeasure.projY : (α × β) × γ → β) ⁻¹' S2)
      = ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
          (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) a)
          ((FateV2.Modeling.FinCondIndepMeasure.projX : (α × β) × γ → α) ⁻¹' S1)
        * ((condExpKernel (Ω := (α × β) × γ) (weightedCount p)
          (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance)) a)
          ((FateV2.Modeling.FinCondIndepMeasure.projY : (α × β) × γ → β) ⁻¹' S2))).mpr ?_
  intro a
  -- `trim {a} = μ (fiber a.2)`：把 `trim` 的零测判据换成纤维质量
  have htrim : (@Measure.trim ((α × β) × γ)
      (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ)
        (inferInstance : MeasurableSpace γ))
      (inferInstance : MeasurableSpace ((α × β) × γ)) (weightedCount p) hm') {a}
      = (weightedCount p) (fiber a.2) :=
    trim_singleton_eq_fiber (α := α) (β := β) (γ := γ) (weightedCount p) a
  by_cases hF : (weightedCount p) (fiber a.2) = 0
  · left
    rw [htrim]
    exact hF
  · right
    exact kernelValue_product_of_fiber_ne p hp hcond S1 S2 a hF

end FinalB3

end FateV2.Modeling
/-! ## §8 **顶层重导出**（与任务书签名逐字一致） -/

section TopLevel

open MeasureTheory ProbabilityTheory

/-- ⭐⭐⭐⭐⭐⭐ **桥的最终定理（顶层形式）**。 -/
theorem condIndepFin_to_bridge_top {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
    [Countable α] [Countable β] [Countable γ]
    [MeasurableSingletonClass ((α × β) × γ)]
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (hp : ∀ w, 0 ≤ p w)
    (hcond : FateV2.Modeling.FiniteCondIndep.CondIndepFin p) :
    FateV2.Modeling.FinCondIndepMeasure.bridgeStatement p :=
  FateV2.Modeling.FinalB3.condIndepFin_to_bridge p hp hcond

end TopLevel

namespace FateV2.Modeling
namespace FinalB3

variable {α β γ : Type}
  [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
  [MeasurableSingletonClass ((α × β) × γ)]
  [Countable α] [Countable β] [Countable γ]

/-- 别名（便于下游按任务书名字引用）。 -/
theorem bridge_final
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ)
    (hp : ∀ w, 0 ≤ p w)
    (hcond : FateV2.Modeling.FiniteCondIndep.CondIndepFin p) :
    FateV2.Modeling.FinCondIndepMeasure.bridgeStatement p :=
  condIndepFin_to_bridge p hp hcond

end FinalB3

end FateV2.Modeling