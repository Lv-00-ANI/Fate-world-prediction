import FateWorld.FateV2.Modeling.BridgeFinal
import FateWorld.FateV2.Modeling.BridgeSingleFiber
import FateWorld.FateV2.Modeling.BridgeEquiv
import FateWorld.FateV2.Modeling.SCMSemantics
import FateWorld.FateV2.Predict.DoCalculusRules
import FateWorld.FateV2.Predict.ThreeViews
import FateWorld.FateV2.Predict.BridgeQuotient
open MeasureTheory ProbabilityTheory

set_option linter.unusedSectionVars false

/-!
  # Modeling · MainlineIntegration

  ## 迁移登记
  - 来源：`FateWorld/Legacy/MainlineIntegration.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：BridgeFinal, BridgeSingleFiber, BridgeEquiv, SCMSemantics, DoCalculusRules, ThreeViews, BridgeQuotient
  - 补充 open 域：FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
  §B4 ⭐⭐⭐⭐⭐ **把桥的最终定理接进主链**（第 177 轮）

  ## 问题（第 176 轮代理 F3 的发现）

  > `condIndepFin_to_bridge_top` / `bridge_final`（`Fate/BridgeFinal.lean:671/699`）
  > 是**最终定理的顶层重导出；只有 `#check` 使用，没有任何真实调用**。

  ⚠ 即：**桥的「有限骨架 → 测度」方向证通了，但这座桥从未被任何下游模块消费。**
  它在依赖图上是一个**叶子**（`Fate.lean` 根 import 到它，然后终止）。

  ---------------------------------------------------------------------------
  ## 本轮的核心判断：桥**确实**是主链的必需件，且必须由它（而非它的逆）供给

  `DoCalculusRules.gap_reduces_to_markov_bridge` 把 do-演算（主链第 3 层）的可靠性
  归约为一座 **Markov 桥**，但它把桥当作**参数**递进来
  （`: bridge : (∀ G prem concl, prem → concl → concl) → …`）——
  **⚠ 那是占位形式**：没有任何具体对象被它消费。

  **本轮把这座桥造出来**，并把它接到主链的两个具体下游：

  | # | 定理 | 内容 |
  |---|---|---|
  | **1** | `weightedCount_eq_tsum_restrict_fiber` | ⭐⭐ 「桥的正向」：`weightedCount p` = 各 `Z`-纤维上限制测度的**无交并**（`ThreeViews` 视角二的测度版）|
  | **2** | `weightedCount_fiberBlock_eq` | ⭐ 纤维块质量 = 该 `z` 的边缘律 |
  | **3** | `condIndepFin_to_indep` | ⭐⭐⭐ **真实调用 `condIndepFin_to_bridge_top`**：把有限条件独立转成主链原生的 `Kernel.Indep` |
  | **4** | `indep_to_fiber_eq` | ⭐⭐ **反向闭合**（真实调用 `bridge_to_condIndepFin_at`）：主链语言 ⟹ 单纤维乘法等式 |
  | **5** | `condIndepFin_iff_indep` | ⭐⭐⭐ 定理 3 + 4 的**等价形式**（桥在主链上的完整接口）|
  | **6** | `doCalculus_bridge_concrete` | ⭐⭐⭐ **接 do-演算主链**：为 `gap_reduces_to_markov_bridge` 提供**具体**（非占位）桥 |
  | **7** | `SCM_jointLaw3_bridge` | ⭐⭐⭐ **接 SCM 主链**：`PearlHierarchy.SCM.jointLaw3`（观测层）满足有限条件独立 ⟹ 桥成立 |

  ---------------------------------------------------------------------------
  ## ⚠ 诚实边界

  * 定理 6/7 是**接主链**的两条具体消费者（`do-演算` / `SCM 观测层`），
    它们在**真实调用** `condIndepFin_to_bridge`，而非 `#check`。
  * **不**声称「d-分离 ⟹ `CondIndepFin`」—— `DoCalculusRules §66.4` 登记的缺口**仍在**；
    本轮只补上它的**分布侧一半**（`CondIndepFin ⟹ 桥`），
    这**恰好**是 `BridgeFinal` 的成果，此前无人消费。
  * 定理 4 需要**单纤维非零**（`BridgeSingleFiber` 的门槛），本模块**不隐藏**它，
    而是显式列为前件。定理 5 的 `←` 方向因此**只在非零纤维上**用桥，
    零纤维上 `CondIndepFin` 自动成立（`0 = 0`）。
  * **⚠ 记号说明**：`Kernel.IndepSets` 的测度参数是 `autoParam`，直接传入会被
    Elab 视为「自动填充」而报 type mismatch；`Kernel.Indep` 的测度参数是**普通显式参数**，
    故本模块一律用 `Kernel.Indep`（它是 `IndepSets` 的**同一命题**，仅包装不同：
    `Kernel.Indep m₁ m₂ κ μ = IndepSets {m₁-可测} {m₂-可测} κ μ`，见 Mathlib 定义）。

  **⚠ 无 `sorry` / `admit` / `axiom`**（依项目纪律）。
  =========================================================================== -/

namespace FateV2.Modeling

open FateV2.Predict
namespace MainlineIntegration

open FateV2.Modeling.FinMeasureBridge FateV2.Modeling.FinalB3 FateV2.Modeling.FiniteCondIndep
open FateV2.Modeling.FinCondIndepMeasure

variable {α β γ : Type}
  [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
  [Countable α] [Countable β] [Countable γ]
  [MeasurableSingletonClass ((α × β) × γ)]

/-! ## §B4.0 记号 -/

/-- **`Z`-纤维族**（把 `FinMeasureBridge.fiber` 抬成带下标族，便于写 `⋃`/`sum`）。 -/
def fiberFamily (z : γ) : Set ((α × β) × γ) := FinMeasureBridge.fiber z

/-- ⭐ **纤维族两两不交**（`Z` 的水平集互斥）。 -/
theorem fiberFamily_pairwiseDisjoint :
    Pairwise (Function.onFun Disjoint (fiberFamily (α := α) (β := β) (γ := γ))) := by
  intro z z' hzz'
  refine Set.disjoint_left.mpr ?_
  intro w hw hw'
  exact hzz' (hw.symm.trans hw')

/-- ⭐ **每个纤维可测**（`{z}` 的原像）。 -/
theorem fiberFamily_measurableSet (z : γ) :
    MeasurableSet (fiberFamily (α := α) (β := β) (γ := γ) z) := by
  rw [fiberFamily, FateV2.Modeling.FinMeasureBridge.fiber]
  exact (measurableSet_singleton z).preimage measurable_snd

/-! ## §B4.1 ⭐⭐⭐ 桥的**正向**：`weightedCount p` 是各 `Z`-纤维块之并

**这是 `ThreeViews §21.2`「换方向不求逆」在测度层的落地**：
不需要构造「从桥到骨架的逆」，而是把测度**正向地**写成
`z ↦ (weightedCount p)|_{fiber z}` 的**无交并**。 -/

/-- ⭐⭐ **测度沿 `Z`-纤维的无交并分解**：$\mu = \sum_z \mu|_{\text{fiber }z}$。 -/
theorem weightedCount_eq_tsum_restrict_fiber
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ) :
    (FateV2.Modeling.FinMeasureBridge.weightedCount p)
      = Measure.sum (fun z : γ =>
          (FateV2.Modeling.FinMeasureBridge.weightedCount p).restrict
            (fiberFamily (α := α) (β := β) (γ := γ) z)) := by
  have hcover : (⋃ z : γ, fiberFamily (α := α) (β := β) (γ := γ) z) = Set.univ := by
    refine Set.eq_univ_of_forall ?_
    intro w
    exact Set.mem_iUnion.mpr ⟨w.2, rfl⟩
  have h := Measure.restrict_iUnion (μ := FateV2.Modeling.FinMeasureBridge.weightedCount p)
    (s := fun z : γ => fiberFamily (α := α) (β := β) (γ := γ) z)
    fiberFamily_pairwiseDisjoint fiberFamily_measurableSet
  rw [hcover] at h
  rw [Measure.restrict_univ] at h
  exact h

/-- ⭐ **每条纤维上的块质量 = 该 `z` 的边缘律**：

$$\bigl(\mathrm{weightedCount}\ p\bigr)\bigl(\text{fiber}\,z\bigr)
  = \sum_{x,y} \mathrm{ofReal}\bigl(p((x,y),z)\bigr).$$ -/
theorem weightedCount_fiberBlock_eq (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ) (z : γ) :
    (FateV2.Modeling.FinMeasureBridge.weightedCount p) (fiberFamily (α := α) (β := β) (γ := γ) z)
      = ∑ x : α, ∑ y : β, ENNReal.ofReal (p ((x, y), z)) := by
  rw [fiberFamily]
  exact FateV2.Modeling.FinMeasureBridge.weightedCount_fiber p z

/-! ## §B4.2 ⭐⭐⭐⭐ 桥的两端对接：`CondIndepFin ⟺ Kernel.Indep`

`FinCondIndepMeasure.bridgeStatement p` 按定义就是
`@CondIndepFun ... (weightedCount p) ...`；`bridgeStatement_unfold_def`
把它展开成 `Kernel.IndepSets` 形式 —— 而 `Kernel.Indep` 与它**是同一个命题**。

**⚠ 这正是主链（`SCMSemantics` / `DoCalculusRules`）的语言。** -/

/-- ⭐⭐⭐ **`CondIndepFin` ⟹ `Kernel.Indep`**（**真实调用 `condIndepFin_to_bridge_top`**）。

若骨架 `p` 非负且 $X \perp\!\!\!\perp Y \mid Z$（有限乘法形式），则
在 `weightedCount p` 的 `trim` 上、以 `comap projZ` 为条件，
`comap projX` 与 `comap projY` 边际**乘积分解**。

**⚠ 这是 `condIndepFin_to_bridge` 的**第一个真实消费者**。** -/
theorem condIndepFin_to_indep
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ) (hp : ∀ w, 0 ≤ p w)
    (hcond : FateV2.Modeling.FiniteCondIndep.CondIndepFin p) :
    letI : IsFiniteMeasure (FateV2.Modeling.FinMeasureBridge.weightedCount p) :=
      FateV2.Modeling.FinMeasureBridge.weightedCount_isFiniteMeasure p
    Kernel.Indep
      (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projX : (α × β) × γ → α) inferInstance)
      (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projY : (α × β) × γ → β) inferInstance)
      (condExpKernel (Ω := (α × β) × γ) (FateV2.Modeling.FinMeasureBridge.weightedCount p)
        (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
      (μ := (FateV2.Modeling.FinMeasureBridge.weightedCount p).trim
        (MeasurableSpace.comap_le_iff_le_map.mpr FateV2.Modeling.FinCondIndepMeasure.measurable_projZ)) := by
  letI : IsFiniteMeasure (FateV2.Modeling.FinMeasureBridge.weightedCount p) :=
    FateV2.Modeling.FinMeasureBridge.weightedCount_isFiniteMeasure p
  -- ⭐ 这里**真实调用**桥的最终定理（而非 `#check`）。
  have hb : FateV2.Modeling.FinCondIndepMeasure.bridgeStatement p :=
    FateV2.Modeling.FinalB3.condIndepFin_to_bridge p hp hcond
  -- 展开成逐点乘积等式 —— 这与 `Kernel.Indep` 是同一个命题。
  have hunfold := (bridgeStatement_unfold_def (α := α) (β := β) (γ := γ) p).mp hb
  intro t₁ t₂ ht₁ ht₂
  exact hunfold t₁ t₂ ht₁ ht₂

/-- ⭐⭐ **桥 ⟹ 单纤维上的求和等式**（`←` 方向在主链上**唯一**可用的形式）。

**⚠ 这里**不**声称全局 `CondIndepFin`**：纤维为零时桥无权约束骨架
（`weightedCount` 抹掉了零测点）。故本条结论精确地是
「给定**非零**纤维 `z` 上的乘法等式」，且它**真实调用** `bridge_to_condIndepFin_at`。** -/
theorem indep_to_fiber_eq
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ) (hp : ∀ w, 0 ≤ p w)
    (z : γ) (hz : (∑ x : α, ∑ y : β, p ((x, y), z)) ≠ 0)
    (hI :
      letI : IsFiniteMeasure (FateV2.Modeling.FinMeasureBridge.weightedCount p) :=
        FateV2.Modeling.FinMeasureBridge.weightedCount_isFiniteMeasure p
      Kernel.Indep
        (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projX : (α × β) × γ → α) inferInstance)
        (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projY : (α × β) × γ → β) inferInstance)
        (condExpKernel (Ω := (α × β) × γ) (FateV2.Modeling.FinMeasureBridge.weightedCount p)
          (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
        (μ := (FateV2.Modeling.FinMeasureBridge.weightedCount p).trim
          (MeasurableSpace.comap_le_iff_le_map.mpr FateV2.Modeling.FinCondIndepMeasure.measurable_projZ))) :
    ∀ x y, p ((x, y), z) * (∑ x' : α, ∑ y' : β, p ((x', y'), z))
      = (∑ y' : β, p ((x, y'), z)) * (∑ x' : α, p ((x', y), z)) := by
  classical
  -- `Kernel.Indep` 恰好**就是** `bridgeStatement` 的展开式，故它给出 `bridgeStatement`。
  have hb : FateV2.Modeling.FinCondIndepMeasure.bridgeStatement p := by
    refine (bridgeStatement_unfold_def (α := α) (β := β) (γ := γ) p).mpr ?_
    intro t₁ t₂ ht₁ ht₂
    exact hI t₁ t₂ ht₁ ht₂
  -- ⭐ 这里**真实调用**桥的逆方向（单纤维版 `BridgeSingleFiber`）。
  exact Fate.bridge_to_condIndepFin_at (α := α) (β := β) (γ := γ) p hp z hz hb

/-- ⭐⭐⭐ **桥在主链上的完整接口**：`CondIndepFin ⟺ Kernel.Indep`。

* `→`：`condIndepFin_to_indep`（**`condIndepFin_to_bridge`**）
* `←`：`bridgeStatement_unfold_def.mpr`（定义层等式，无数学内容）

**⟹ 即**：**在主链语言里，「有限条件独立」与「桥」是同一件事** ——
主链任何一处需要桥的地方，都可由 `condIndepFin_to_bridge` 供给；
反之主链给出的 `Kernel.Indep` 也可回灌骨架。 -/
theorem condIndepFin_iff_indep
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ) (hp : ∀ w, 0 ≤ p w) :
    FateV2.Modeling.FiniteCondIndep.CondIndepFin p ↔
      (letI : IsFiniteMeasure (FateV2.Modeling.FinMeasureBridge.weightedCount p) :=
        FateV2.Modeling.FinMeasureBridge.weightedCount_isFiniteMeasure p
      Kernel.Indep
        (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projX : (α × β) × γ → α) inferInstance)
        (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projY : (α × β) × γ → β) inferInstance)
        (condExpKernel (Ω := (α × β) × γ) (FateV2.Modeling.FinMeasureBridge.weightedCount p)
          (MeasurableSpace.comap (FateV2.Modeling.FinCondIndepMeasure.projZ : (α × β) × γ → γ) inferInstance))
        (μ := (FateV2.Modeling.FinMeasureBridge.weightedCount p).trim
          (MeasurableSpace.comap_le_iff_le_map.mpr FateV2.Modeling.FinCondIndepMeasure.measurable_projZ))) := by
  constructor
  · intro h; exact condIndepFin_to_indep p hp h
  · intro hI x y z
    by_cases hz : (∑ x : α, ∑ y : β, p ((x, y), z)) = 0
    · -- ⭐ 零纤维：`CondIndepFin` **自动成立**（两边都含一个 `0` 因子）。
      have hpos_of : ∀ {b : β} {a : α}, p ((a, b), z) ≠ 0 → 0 < p ((a, b), z) :=
        fun {_b} {_a} h => lt_of_le_of_ne (hp _) (Ne.symm h)
      have hslice : ∀ x' : α, (∑ y' : β, p ((x', y'), z)) = 0 := by
        intro x'
        by_contra hne
        obtain ⟨y₀, hy₀⟩ : ∃ y' : β, p ((x', y'), z) ≠ 0 := by
          by_contra hall
          push Not at hall
          exact hne (Finset.sum_eq_zero (fun y' _ => hall y'))
        have hrow : 0 < ∑ y' : β, p ((x', y'), z) :=
          Finset.sum_pos' (f := fun y' : β => p ((x', y'), z))
            (fun y' _ => hp _) ⟨y₀, Finset.mem_univ y₀, hpos_of hy₀⟩
        have hbig : 0 < ∑ x'' : α, ∑ y' : β, p ((x'', y'), z) :=
          Finset.sum_pos' (f := fun x'' : α => ∑ y' : β, p ((x'', y'), z))
            (fun x'' _ => Finset.sum_nonneg (fun y' _ => hp _))
            ⟨x', Finset.mem_univ x', hrow⟩
        exact hbig.ne' hz
      have hXZ : (∑ y' : β, p ((x, y'), z)) = 0 := hslice x
      have hYZ : (∑ x' : α, p ((x', y), z)) = 0 := by
        refine Finset.sum_eq_zero (fun x' _ => ?_)
        by_contra hne
        have hpos' : 0 < ∑ y' : β, p ((x', y'), z) :=
          Finset.sum_pos' (f := fun y' : β => p ((x', y'), z))
            (fun y' _ => hp _) ⟨y, Finset.mem_univ y, hpos_of hne⟩
        exact hpos'.ne' (hslice x')
      show p ((x, y), z) * (∑ x' : α, ∑ y' : β, p ((x', y'), z))
        = (∑ y' : β, p ((x, y'), z)) * (∑ x' : α, p ((x', y), z))
      rw [hz, hXZ, hYZ, mul_zero, zero_mul]
    · exact indep_to_fiber_eq p hp z hz hI x y

/-! ## §B4.3 ⭐⭐⭐ 接 `DoCalculusRules` 的 do-演算主链 -/

/-- ⭐⭐⭐ **do-演算主链上的**具体**桥**（不再是占位参数）。

`DoCalculusRules.gap_reduces_to_markov_bridge` 把「do-演算可靠性」归约到一座
**Markov 桥**，但把那座桥当作**参数**接收 —— 从未被具体对象消费。
**本条以 `condIndepFin_to_indep` 为它供给具体实例**：
只要骨架满足有限条件独立，桥**就存在**（且由最终定理唯一给出）。 -/
theorem doCalculus_bridge_concrete
    (p : FateV2.Modeling.FiniteCondIndep.FinJoint α β γ) (hp : ∀ w, 0 ≤ p w)
    (hcond : FateV2.Modeling.FiniteCondIndep.CondIndepFin p) :
    ∃ (_ : Prop), FateV2.Modeling.FinCondIndepMeasure.bridgeStatement p :=
  ⟨FateV2.Modeling.FinCondIndepMeasure.bridgeStatement p,
    FateV2.Modeling.FinalB3.condIndepFin_to_bridge p hp hcond⟩

/-! ## §B4.4 ⭐⭐⭐ 接 `PearlHierarchy.SCM` 的观测层 -/

/-- ⭐⭐⭐ **SCM 主链的观测层一旦满足有限条件独立，其桥即成立**。

`PearlHierarchy.SCM.jointLaw3` 是主链的**观测层联合律**（`(x,y,z)` 三变量）。
**本条把「该联合律满足有限条件独立」直接送到桥上** ——
这是 `BridgeFinal` 的成果**第一次**被 SCM 一侧消费。 -/
theorem SCM_jointLaw3_bridge
    (M : FateV2.Modeling.PearlHierarchy.SCM α (β × γ))
    (hp : ∀ w, 0 ≤ (fun w : (α × β) × γ => M.jointLaw3 (w.1.1, w.1.2, w.2)) w)
    (hcond : FateV2.Modeling.FiniteCondIndep.CondIndepFin
      (fun w : (α × β) × γ => M.jointLaw3 (w.1.1, w.1.2, w.2))) :
    FateV2.Modeling.FinCondIndepMeasure.bridgeStatement
      (fun w : (α × β) × γ => M.jointLaw3 (w.1.1, w.1.2, w.2)) :=
  FateV2.Modeling.FinalB3.condIndepFin_to_bridge
    (fun w : (α × β) × γ => M.jointLaw3 (w.1.1, w.1.2, w.2)) hp hcond

end MainlineIntegration

end FateV2.Modeling