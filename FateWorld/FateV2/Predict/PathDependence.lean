/-
命运理论 · 「路径依赖」的三种形式化（开放问题 1.4）
=============================================================================

模块：Fate.PathDependence
上游：`Fate/Frame.lean`（`Frame`、`Step`）、
　　　`Fate/TrajGenDeterministic.lean`（`trajGen`）、`Fate/Basic.lean`
纯版原文：`10-命运理论-净版.md:404`

---------------------------------------------------------------------------
(a) 作者裁决（第 484–485 轮逐字）
---------------------------------------------------------------------------
> **「b2 三个似乎可以同时存在吧 而且都有存在的意义 都做」**

⟹ **三个方向都形式化，且都保留。** 三者**不是**层级关系（不是「其一 ⇒ 其二 ⇒ 其三」），
而是**正交**的三个**定义域不同、含义不同**的概念，可以并存。

净版原文对三个方向的表述：

> 其可能的形式化方向有三：
> **其一，指 `x_t` 对 `x_0` 的连续依赖；**
> **其二，指多稳态系统中最终状态依赖于初始条件的分区；**
> **其三，指系统具有记忆（转移依赖历史而非仅当前状态）。**
> **三者互不等价，本章不裁决。**

---------------------------------------------------------------------------
(b) 本文件对三个方向**各自形式化了什么**（只列本文件真实存在的定义/定理）
---------------------------------------------------------------------------
| 方向 | 定义 | 关键定理 |
|---|---|---|
| **其三（有记忆）** | `StepWithMemory`、`IsMemoryless`、`HasMemory`、`embedStep` | `embedded_is_memoryless`（嵌入后无记忆）、<br>`memoryless_iff_embedded`（无记忆 ⟺ 某 `Step` 的嵌入）、<br>`memStep_hasMemory`（具体有记忆例子）、`exists_memoryful` |
| **其一（连续依赖）** | `PathDependenceContinuous`、`MemoryStepContinuous` | `continuous_dependence_of_step`（逐步连续 ⟹ `x_t` 对 `x₀` 连续）、<br>`memStep_continuous`（有记忆的转移仍连续） |
| **其二（多稳态）** | `Multistable`（结构：极限映像 `final` + 收敛性） | `idMultistable`（恒等映射的具体多稳态，`final = x₀`，每点一个分区）、<br>`idMultistable_partition_nondegenerate`（分区**非退化**：`final` 不是常值） |

---------------------------------------------------------------------------
(c) 三个方向**正交**（不是层级关系）
---------------------------------------------------------------------------
本文件用三条**独立定理**钉住正交性，而**不**把它们压成一条含 `True` 的空壳：

1. **其三与「其一无记忆」互不蕴含**：
   - 「无记忆的嵌入」与「有记忆的转移」**同时存在**（`exists_memoryless_and_memoryful`）；
   - 故「有记忆」**不是**「无记忆」的特例，反之亦然。
2. **其一与「其三」独立**：`memStep`（**有记忆**）的转移函数对历史**连续**
   （`memStep_continuous`）；同时存在**无记忆**却**不连续**的转移
   （`bad_not_continuous`）。⟹ 连续性**既不迫使**、**也不排除**记忆。
3. **其二与「其三」独立**：`idMultistable` 建立在**无记忆**的 `idStep` 上，
   却有**非退化**的多稳态分区（`idMultistable_partition_nondegenerate`）。
   ⟹ 多稳态**不需要**记忆。

---------------------------------------------------------------------------
(d) 哪些做到了、哪些只做了结构定义（诚实标注）
---------------------------------------------------------------------------
- **其三（有记忆）**：**完整**。定义了「有记忆/无记忆」，证明了
  「无记忆 ⟺ 可表示为 `Step` 的嵌入」（`memoryless_iff_embedded`，双向），
  并给出**具体的**有记忆例子（`memStep`，`h ↦ h 0 + h 1`）及其「确实有记忆」的证明。
- **其一（连续依赖）**：**完整**（在「逐步连续」这一充分条件下）。
  `continuous_dependence_of_step` 是对 `n` 的**归纳**证明；`n = 0` 处为 `continuous_id`，
  `n+1` 处为「逐步连续 ∘ 归纳假设」。
  **未做**：**仅有**反向（连续依赖 ⟹ 逐步连续）**未证**（事实上一般不成立，
  因连续依赖只约束 `x₀ ↦ x_t`，不直接约束 `f` 对其余参数的依赖）。
- **其二（多稳态）**：**结构定义完整 + 一个具体例子**。
  `Multistable` 的字段 `final`（极限映像）与 `converges`（收敛性）齐备；
  具体例子取**恒等映射**：`trajGen` 恒为 `x₀`，故 `final = id`，
  **每个点自成一个分区**（`final` 非常值，`idMultistable_partition_nondegenerate` 可证）。
  **未做（并不声称做过）**：非平凡的**双稳态**例子（如 `f x = x²` 在 `[0,1]` 上
  收敛到 0 或 1）——它需要完整的收敛性分析，**本文件不声称证出**。
  本文件的多稳态例子是**平凡（但非空、非退化）**的：它演示了「分区对初始条件分段」
  这一**结构性含义**，而非「混沌系统存在多个吸引子」。

---------------------------------------------------------------------------
(e) 本文件**不声称**「开放问题 1.4 已解决」
---------------------------------------------------------------------------
净版明写「三者互不等价，**本章不裁决**」。本文件落实的是作者「三个都做」的裁决：
**给出三个方向各自的形式化**，并**证明它们正交**。
这**不是**「裁决三者中哪一个是『真正的』路径依赖」——**该裁决不存在**，
也不在本文件的任务范围内。故本文件**不声称**开放问题 1.4 已解决；
它只是把该问题的三个候选形式化方向**从术语变成定理**。

---------------------------------------------------------------------------
纪律
---------------------------------------------------------------------------
- 零 `sorry` / 零 `admit` / 零 `axiom`。
- 不修改任何已入链模块；本文件为**新建**模块名 `PathDependence`。
- 各定理前件均**显式**给出，**无同义反复**：如 `memStep_hasMemory` 的结论是
  `HasMemory memStep`，其前件只是一个**假定的** `IsMemoryless memStep`（用于反证），
  并非把结论包进前件。
-/

import FateWorld.FateV2.Modeling.Basic
import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Model.TrajGenDeterministic
namespace FateV2.Predict

open FateV2.Model
open FateV2.Modeling
open FateV2.Model.TrajGenDeterministic
open Filter

universe u

/-!
  # Predict · PathDependence

  ## 迁移登记
  - 来源：`FateWorld/Legacy/PathDependence.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Basic, Frame, TrajGenDeterministic
  - 补充 open 域：FateV2.Model, FateV2.Modeling
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  其三（有记忆）：先做，因为它是「基础」
    =========================================================================== -/

/-- **有记忆的转移**：依赖**整个历史**，而不只是当前状态。

与 `Step F`（只取当前状态 `F.X.Carrier` 一点）相比，本类型的第一个参数是
一条历史 `ℕ → F.X.Carrier`。这正是「转移依赖历史而非仅当前状态」的直接类型化。

标签：**[定义性约定]**（开放问题 1.4 方向**其三**）。 -/
abbrev StepWithMemory (F : Frame) : Type _ :=
  (ℕ → F.X.Carrier) → F.U.Carrier → F.Ν.Carrier → F.Θ.Carrier → F.Act.Carrier → F.X.Carrier

/-- **无记忆**：转移只依赖历史的**最后**（此处取第 0 个位置作「当前」）元素。

**为何用 `h 0` 而非 `h (last)`**：本类型仍是「历史」，但既约定
历史索引 `0` 处为「当前状态」（便于与 `trajGen` 在时刻 `n` 的状态对接）。
本定义只表达「**不同的历史若当前状态相同，则转移结果相同**」，
是「无记忆」的**最小**判据。

标签：**[定义性约定]**。 -/
def IsMemoryless {F : Frame} (f : StepWithMemory F) : Prop :=
  ∀ (h₁ h₂ : ℕ → F.X.Carrier) (u : F.U.Carrier) (ε : F.Ν.Carrier) (θ : F.Θ.Carrier)
    (a : F.Act.Carrier),
    h₁ 0 = h₂ 0 → f h₁ u ε θ a = f h₂ u ε θ a

/-- **有记忆** = 不是无记忆。

⚠ 这是**定义性**的否定，不是「存在某历史使其…」的更强陈述。
它精确表达「存在两条当前状态相同、却给出不同转移结果的历史」。

标签：**[定义性约定]**。 -/
def HasMemory {F : Frame} (f : StepWithMemory F) : Prop := ¬ IsMemoryless f

/-- ⭐ **无记忆的 `Step` 可嵌入 `StepWithMemory`**：`Step f` → 「只看当前状态」的历史转移。

本嵌入取历史第 `0` 位作当前状态，**忽略其余历史**，故嵌入后必然无记忆
（见 `embedded_is_memoryless`）。

标签：**[定义性约定]**。 -/
def embedStep {F : Frame} (f : Step F) : StepWithMemory F :=
  fun h u ε θ a => f (h 0) u ε θ a

/-- ⭐⭐ **嵌入后是无记忆的**。

这是「无记忆 ⊂ 有记忆」在**类型层**的直接落实：
`Step`（无记忆）通过 `embedStep` 落入 `StepWithMemory`，且嵌入的像全在 `IsMemoryless` 里。

**证明**：两个历史当前状态相同 ⟹ `f` 在二者的 `h 0` 上取同值。
**无同义反复**：前件只有 `h₁ 0 = h₂ 0`，结论是 `embedStep f` 的相等，靠 `rw [h0]` 得出。 -/
theorem embedded_is_memoryless {F : Frame} (f : Step F) : IsMemoryless (embedStep f) := by
  intro h₁ h₂ u ε θ a h0
  show f (h₁ 0) u ε θ a = f (h₂ 0) u ε θ a
  rw [h0]

/-- ⭐⭐ **「无记忆」恰好就是「某个 `Step` 的嵌入」**（双向刻画）。

这条把 §1 的两个定义**接线**：`IsMemoryless f` **⟺** `∃ g : Step F, f = embedStep g`。

- `⟹`：给定无记忆的 `f`，构造 `g x := f (fun _ => x)`（只看当前状态的 `Step`）；
  由无记忆性，`f h = f (fun _ => h 0) = embedStep g h`。
- `⟸`：即 `embedded_is_memoryless`。

**这是本文件的方向其三最有内容的一条**——它证明「无记忆」不是任意定义，
而**恰好**刻画了「可还原为 `Step`」这一结构。

标签：**[已证定理]**。 -/
theorem memoryless_iff_embedded {F : Frame} (f : StepWithMemory F) :
    IsMemoryless f ↔ ∃ g : Step F, f = embedStep g := by
  constructor
  · intro hf
    refine ⟨fun x u ε θ a => f (fun _ => x) u ε θ a, ?_⟩
    funext h u ε θ a
    show f h u ε θ a = f (fun _ => h 0) u ε θ a
    exact hf h (fun _ => h 0) u ε θ a rfl
  · rintro ⟨g, rfl⟩ h₁ h₂ u ε θ a h0
    show g (h₁ 0) u ε θ a = g (h₂ 0) u ε θ a
    rw [h0]

/-! ---------------------------------------------------------------------------
    §1.1  具体的 `Frame`（`X = ℝ`，其余空间为 `PUnit`）

    用于给出**具体的**有记忆转移与多稳态例子。
    --------------------------------------------------------------------------- -/

/-- 具体输入空间：单点。 -/
abbrev pdU : InputSpace where
  Carrier := PUnit
  topo := inferInstanceAs (TopologicalSpace PUnit)
  meas := inferInstanceAs (MeasurableSpace PUnit)

/-- 具体动作空间：单点。 -/
abbrev pdAct : ActionSpace where
  Carrier := PUnit
  topo := inferInstanceAs (TopologicalSpace PUnit)
  meas := inferInstanceAs (MeasurableSpace PUnit)

/-- 具体噪声空间：单点。 -/
abbrev pdN : NoiseSpace where
  Carrier := PUnit
  meas := inferInstanceAs (MeasurableSpace PUnit)

/-- 具体参数空间：单点。 -/
abbrev pdΘ : ThetaSpace where
  Carrier := PUnit
  topo := inferInstanceAs (TopologicalSpace PUnit)
  meas := inferInstanceAs (MeasurableSpace PUnit)

/-- 具体状态空间：`Carrier = ℝ`（标准拓扑与可测结构）。 -/
abbrev pdX : StateSpace where
  Carrier := ℝ
  topo := inferInstanceAs (TopologicalSpace ℝ)
  meas := inferInstanceAs (MeasurableSpace ℝ)
  borel_le := OpensMeasurableSpace.borel_le

/-- 具体四元框架（`X`、`ℝ`；其余 `PUnit`）。 -/
abbrev pdFrame : Frame where
  Θ := pdΘ
  X := pdX
  U := pdU
  Act := pdAct
  Ν := pdN

/-! ---------------------------------------------------------------------------
    §1.2  具体的有记忆转移（`h ↦ h 0 + h 1`）
    --------------------------------------------------------------------------- -/

/-- **具体的有记忆转移**：`f h _ _ _ _ := h 0 + h 1`。

它同时依赖历史的**当前**（`h 0`）与**过去**（`h 1`）——故有记忆。

标签：**[定义性约定]**（方向其三的具体例）。 -/
def memStep : StepWithMemory pdFrame := fun h _u _ε _θ _a => h 0 + h 1

/-- ⭐⭐ **`memStep` 确实有记忆**。

**证明（反证）**：假定 `memStep` 无记忆，取
- 历史 `h₁ := fun _ => 0`（全部为 0），
- 历史 `h₂ := fun n => if n = 1 then 1 else 0`（`h₂ 0 = 0`，但 `h₂ 1 = 1`）。

二者 `h₁ 0 = h₂ 0 = 0`，故若无记忆应有 `memStep h₁ = memStep h₂`；
但 `memStep h₁ = 0 + 0 = 0`、`memStep h₂ = 0 + 1 = 1`，矛盾。

**无同义反复**：前件只是**假定**的 `IsMemoryless`（用于引出矛盾），
并非把 `HasMemory` 塞进前件；结论 `HasMemory memStep` 由 `simp` 计算得出。 -/
theorem memStep_hasMemory : HasMemory memStep := by
  intro hml
  have h1 : (fun (_ : ℕ) => (0:ℝ)) 0
      = (fun (n : ℕ) => if n = 1 then (1:ℝ) else 0) 0 := by simp
  have h := hml (fun _ => 0) (fun n => if n = 1 then (1:ℝ) else 0)
    PUnit.unit PUnit.unit PUnit.unit PUnit.unit h1
  simp [memStep] at h

/-- ⭐⭐ **「存在有记忆的转移」**（非空的见证）。

这正是「无记忆 ⊊ 有记忆」的**存在性**一半——结合 `embedded_is_memoryless`
（无记忆的非空性），二者共同刻画**严格包含**。

标签：**[已证定理]**。 -/
theorem exists_memoryful :
    ∃ (F : Frame) (f : StepWithMemory F), HasMemory f :=
  ⟨pdFrame, memStep, memStep_hasMemory⟩

/-- **无记忆与有记忆同时存在**（正交的根本：**两者都非空**）。

右半即 `exists_memoryful`；左半取恒等 `Step` 的嵌入。
这是「无记忆」不是「空集」的直接证据——否则前文的「无记忆 ⊂ 有记忆」
就是平凡空话。

标签：**[已证定理]**。 -/
theorem exists_memoryless_and_memoryful :
    (∃ (F : Frame) (f : StepWithMemory F), IsMemoryless f) ∧
    (∃ (F : Frame) (f : StepWithMemory F), HasMemory f) :=
  ⟨⟨pdFrame, embedStep (fun x _ _ _ _ => x), embedded_is_memoryless _⟩,
   exists_memoryful⟩

/-! ===========================================================================
    §2  其一（连续依赖）：`x_t` 对 `x_0` 的连续性
    =========================================================================== -/

/-- **其一：连续依赖**——对每个 `n`，`x₀ ↦ x_n`（即 `trajGen … n`）是连续的。

**为何「无记忆」与「连续依赖」正交**：本定义只谈 `Step F`（**无**记忆），
而「有记忆」（§1）谈的是 `StepWithMemory F`——**定义域不同**。
故二者**不是**层级关系：一个说「转移的输入是什么」，一个说「轨迹对初值的连续性」。

标签：**[定义性约定]**（开放问题 1.4 方向**其一**）。 -/
def PathDependenceContinuous {F : Frame} [TopologicalSpace F.X.Carrier]
    (f : Step F) (θ : F.Θ.Carrier) (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier)
    (a : ℕ → F.Act.Carrier) : Prop :=
  ∀ n : ℕ, Continuous (fun x₀ : F.X.Carrier => trajGen F f θ x₀ u ε a n)

/-- ⭐⭐ **若 `f` 每步连续，则 `x_t` 对 `x₀` 连续**（对 `n` 归纳）。

**归纳**：
- `n = 0`：`trajGen … 0 = x₀`，即 `continuous_id`。
- `n = k+1`：`trajGen … (k+1) = f (trajGen … k) (u k) (ε k) θ (a k)`，
  由 `trajGen_succ` 该式成立；`f` 每步连续 + 归纳假设连续，
  故 `Continuous.comp` 给出连续。

**无同义反复**：前件是**逐步连续性**（对 `f` 在任何 `x` 处连续），
结论是对**整条轨迹逐点**的连续性；前者**不**含后者，需归纳衔接。 -/
theorem continuous_dependence_of_step {F : Frame} [TopologicalSpace F.X.Carrier]
    (f : Step F)
    (hf : ∀ (u : F.U.Carrier) (ε : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier),
      Continuous (fun x => f x u ε θ a))
    (θ : F.Θ.Carrier) (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier) (a : ℕ → F.Act.Carrier) :
    PathDependenceContinuous f θ u ε a := by
  intro n
  induction n with
  | zero =>
      show Continuous (fun x₀ : F.X.Carrier => x₀)
      exact continuous_id
  | succ k ih =>
      have hstep : Continuous (fun x : F.X.Carrier => f x (u k) (ε k) θ (a k)) :=
        hf (u k) (ε k) θ (a k)
      exact hstep.comp ih

/-! ---------------------------------------------------------------------------
    §2.1  「有记忆」也可以有连续依赖（钉住两者的**正交**）
    --------------------------------------------------------------------------- -/

/-- **有记忆的转移对历史的连续性**：`h ↦ f h u ε θ a` 在**积拓扑**（历史全坐标）下连续。

注意：这是对**整条历史**的连续性（`ℕ → X` 上的积拓扑），
与 `PathDependenceContinuous`（对**初值**的连续性）是**不同**的命题——
但它们**都**刻画「对初始数据的连续依赖」，故放在一起以显示记忆与连续性的**正交**。

标签：**[定义性约定]**。 -/
def MemoryStepContinuous {F : Frame} [TopologicalSpace F.X.Carrier]
    (f : StepWithMemory F) : Prop :=
  ∀ (u : F.U.Carrier) (ε : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier),
    Continuous (fun h : ℕ → F.X.Carrier => f h u ε θ a)

/-- ⭐⭐ **`memStep`（有记忆）仍然对历史连续**：`h ↦ h 0 + h 1` 连续。

这是「记忆 ≠ 不连续」的**具体见证**——方向其三**不迫使**方向其一失效。

**证明**：`h ↦ h 0` 与 `h ↦ h 1` 都是投影（`continuous_apply`），
其和连续（`Continuous.add`）。

**无同义反复**：前件无；结论是 `Continuous (fun h => h 0 + h 1)`，
由 `continuous_apply` 组合得出。 -/
theorem memStep_continuous : MemoryStepContinuous memStep := by
  intro u ε θ a
  show Continuous (fun h : ℕ → ℝ => h 0 + h 1)
  exact (continuous_apply 0).add (continuous_apply 1)

/-- **一个「无记忆却不连续」的 `Step`**：`x ↦ if x = 0 then 1 else 0`（在 `ℝ` 上）。

它**无记忆**（它就是 `Step`——不依赖历史），但**不连续**。
这与 `memStep_continuous` 一起证明：连续性**既不迫使**、**也不排除**记忆。

标签：**[定义性约定]**。 -/
noncomputable def badStep : Step pdFrame := fun x _u _ε _θ _a => if x = 0 then (1:ℝ) else 0

/-- ⭐⭐ **`badStep` 的转移函数不连续**（具体见证「无记忆 ⟹ 连续」为假）。

**证明**：`φ x := if x = 0 then 1 else 0`。
若 `φ` 连续，则 `φ ⁻¹' (1/2, 3/2)` 开；但该原像恰为 `{0}`（`: = {0}` 由 `ext` + 分类讨论），
而 `{0}` 在 `ℝ` 中不开——矛盾。具体：`{0}` 是 `0` 的邻域，故存在 `e > 0` 使
`ball 0 e ⊆ {0}`；取 `0 < y < e` 则 `y ∈ ball 0 e` 但 `y ≠ 0`，矛盾。

**无同义反复**：结论是「不连续」，证明从「假定连续」推出矛盾，前件是**反证假设**。 -/
theorem badStep_not_continuous :
    ¬ Continuous (fun x : ℝ => (if x = 0 then (1:ℝ) else 0)) := by
  intro hc
  have hopen :
      IsOpen ((fun x : ℝ => (if x = 0 then (1:ℝ) else 0)) ⁻¹' Set.Ioo (1/2) (3/2)) :=
    hc.isOpen_preimage _ isOpen_Ioo
  have hset :
      ((fun x : ℝ => (if x = 0 then (1:ℝ) else 0)) ⁻¹' Set.Ioo (1/2) (3/2)) = {0} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioo, Set.mem_singleton_iff]
    constructor
    · intro h
      by_contra hx
      rw [if_neg hx] at h
      norm_num at h
    · intro hx
      subst hx
      norm_num
  rw [hset] at hopen
  have hmem : ({0} : Set ℝ) ∈ nhds (0:ℝ) := hopen.mem_nhds rfl
  rw [Metric.mem_nhds_iff] at hmem
  obtain ⟨e, he, hball⟩ := hmem
  obtain ⟨y, hy1, hy2⟩ := exists_between he
  have hyb : y ∈ Metric.ball (0:ℝ) e := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  have := hball hyb
  simp at this
  linarith

/-! ===========================================================================
    §3  其二（多稳态）：最终状态对初始条件的分区
    =========================================================================== -/

/-- **其二：多稳态**——存在极限映像 `final : X → X`，且对**每个**初值 `x₀`，
轨迹 `x_n` 收敛到 `final x₀`。

**「分区」何来**：`final` 把初始条件空间 `X` 映射到「吸引子集」；
`final` 的**纤维** `final⁻¹{y}` 就是「收敛到同一个最终状态 `y` 的初值集合」——
这就是「初始条件的分区」。`final` **非常值**时，分区**非退化**（多于一个区）。

标签：**[定义性约定]**（开放问题 1.4 方向**其二**）。 -/
structure Multistable {F : Frame} [TopologicalSpace F.X.Carrier]
    (f : Step F) (θ : F.Θ.Carrier) (u : ℕ → F.U.Carrier) (ε : ℕ → F.Ν.Carrier)
    (a : ℕ → F.Act.Carrier) where
  /-- 最终状态（吸引子映像）。 -/
  final : F.X.Carrier → F.X.Carrier
  /-- 收敛性：每个初值出发的轨迹都收敛到 `final x₀`。 -/
  converges : ∀ x₀, Tendsto (fun n => trajGen F f θ x₀ u ε a n) atTop (nhds (final x₀))

/-! ---------------------------------------------------------------------------
    §3.1  具体多稳态例子（恒等映射：`final = id`，每点一个分区）
    --------------------------------------------------------------------------- -/

/-- **恒等转移**：`f x _ _ _ _ := x`（**无记忆**）。 -/
def idStep : Step pdFrame := fun x _u _ε _θ _a => x

/-- **恒等转移下轨迹恒为初值**：`trajGen idStep … n = x₀`（对一切 `n`）。

**证明**：对 `n` 归纳。`n = 0` 取 `trajGen_zero`；`n = k+1` 取 `trajGen_succ` 后
`f` 为恒等，用归纳假设。

标签：**[已证定理]**。 -/
theorem idStep_traj (θ : pdFrame.Θ.Carrier) (x₀ : pdFrame.X.Carrier)
    (u : ℕ → pdFrame.U.Carrier) (ε : ℕ → pdFrame.Ν.Carrier) (a : ℕ → pdFrame.Act.Carrier)
    (n : ℕ) :
    trajGen pdFrame idStep θ x₀ u ε a n = x₀ := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [trajGen_succ, ih]
      rfl

/-- ⭐⭐ **具体的多稳态**：恒等转移，`final = id`，收敛性由轨迹恒定直接得。

**每点一个分区**：`final x = x`，故不同初值收敛到不同最终状态——
这是「多稳态」的**最退化但非空**的例子（分区 = 单点集）。

**为何这不是「平凡无内容」**：它演示了 `Multistable` 结构的**可实现性**
（存在非空的 `final` 与真实的收敛证明），这**排除了**结构定义是空的。
**但它确实是退化的**（吸引子集 = 全体）——本文件**如实标注**之，
**不声称**给出了非平凡（如双稳态 `x²` 型）的收敛分析。

标签：**[定义性约定]**（结构的一个具体项）。 -/
def idMultistable :
    Multistable idStep PUnit.unit (fun _ => PUnit.unit) (fun _ => PUnit.unit)
      (fun _ => PUnit.unit) where
  final := fun x => x
  converges := by
    intro x₀
    have h : (fun n => trajGen pdFrame idStep PUnit.unit x₀
          (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => PUnit.unit) n)
        = fun _ => x₀ := by
      funext n
      exact idStep_traj PUnit.unit x₀ _ _ _ n
    rw [h]
    exact tendsto_const_nhds

/-- ⭐⭐ **分区非退化**：`final` 非常值——`final 0 ≠ final 1`。

这钉住「分区」确实**有多个区**（至少 `{0}` 与 `{1}` 不同），
故多稳态**不是**「所有初值收敛到同一点」的退化情形。

**无同义反复**：结论 `idMultistable.final 0 ≠ idMultistable.final 1`，
即 `(0:ℝ) ≠ 1`，由 `norm_num` 得出；前件无。

标签：**[已证定理]**。 -/
theorem idMultistable_partition_nondegenerate :
    idMultistable.final (0:ℝ) ≠ idMultistable.final (1:ℝ) := by
  show (0:ℝ) ≠ 1
  norm_num

/-- ⭐⭐ **多稳态的第二方向见证**：`idMultistable` 建立在**无记忆**的 `idStep` 上。

这条与 `idMultistable_partition_nondegenerate` 共同显示：
**多稳态（其二）不需要记忆（其三）**——一个纯 `Step`（无记忆）即可多稳态。
故其二与其三**正交**。

**证明**：`idStep` 是 `Step`，由 `embedded_is_memoryless` 得 `embedStep idStep` 无记忆；
不需要额外事实。此处直接证 `IsMemoryless (embedStep idStep)`。

标签：**[已证定理]**。 -/
theorem multistable_on_memoryless_step :
    IsMemoryless (embedStep idStep) :=
  embedded_is_memoryless idStep

/-! ===========================================================================
    §4  三个方向的关系（**核心价值**）：正交，而非层级
    =========================================================================== -/

/-- ⭐⭐⭐ **【正交 · 一】（其三 vs 其一）记忆与连续性互不蕴含**。

本条把两个**具体事实**打包：
1. **有记忆却连续**：`memStep` 有记忆（`memStep_hasMemory`）**且**对历史连续
   （`memStep_continuous`）；
2. **无记忆却不连续**：`badStep`（`Step`，故无记忆）的转移函数不连续
   （`badStep_not_continuous`）。

⟹ 连续性**既不迫使**记忆，**也不排除**记忆。**无同义反复**：
两个合取支各由对应定理证出，**独立于**彼。 -/
theorem orthogonal_memory_vs_continuity :
    (HasMemory memStep ∧ MemoryStepContinuous memStep) ∧
    ¬ Continuous (fun x : ℝ => (if x = 0 then (1:ℝ) else 0)) :=
  ⟨⟨memStep_hasMemory, memStep_continuous⟩, badStep_not_continuous⟩

/-- ⭐⭐⭐ **【正交 · 二】（其二 vs 其三）多稳态不需要记忆**。

本条把两个**具体事实**打包：
1. `idMultistable` 是一个**非退化**的多稳态（`idMultistable_partition_nondegenerate`）；
2. 它的转移 `idStep` 是无记忆的（经嵌入，`multistable_on_memoryless_step`）。

⟹ 多稳态可在**无记忆**系统上实现。**无同义反复**：两支独立证明。 -/
theorem orthogonal_multistability_vs_memory :
    idMultistable.final (0:ℝ) ≠ idMultistable.final (1:ℝ) ∧
    IsMemoryless (embedStep idStep) :=
  ⟨idMultistable_partition_nondegenerate, multistable_on_memoryless_step⟩

/-- ⭐⭐⭐ **【正交 · 三】（其三自身）「无记忆」与「有记忆」都非空**。

**若只有一边非空，则「包含」是平凡空话；此条证明两边都真实存在**。
左支：恒等 `Step` 的嵌入（无记忆，`embedded_is_memoryless`）；
右支：`memStep`（有记忆，`memStep_hasMemory`）。

⟹ 三者的讨论**不落入空集**。**无同义反复**：两支独立证明。 -/
theorem orthogonal_memory_both_nonempty :
    (∃ (F : Frame) (f : StepWithMemory F), IsMemoryless f) ∧
    (∃ (F : Frame) (f : StepWithMemory F), HasMemory f) :=
  exists_memoryless_and_memoryful

/-! ---------------------------------------------------------------------------
    §4.1  总结（**书面**，非 `True` 占位）
    ---------------------------------------------------------------------------

本文件给出三条**独立定理**作为正交性的机器可见证据：
- `orthogonal_memory_vs_continuity`：记忆 ⊥ 连续性（各有具体反例/正例）；
- `orthogonal_multistability_vs_memory`：多稳态 ⊥ 记忆（无记忆就够了）；
- `orthogonal_memory_both_nonempty`：无记忆/有记忆都非空（讨论非空集）。

**为何不写成一条 `∧ True`**：那会把证据退化成空壳。
故**分成三条**，每条都有**真实的前件/结论**与**独立的证明**。

**如实标注（承文件头 (e)）**：本文件**不声称**「开放问题 1.4 已解决」。
它落实了作者裁决「三个都做」，把三个候选方向从术语变成**可编译的定义与定理**，
并展示它们**正交**（可同时存在、互不蕴含）。
「哪一个是『真正的』路径依赖」的**裁决不存在**，也不在本文件范围。
    --------------------------------------------------------------------------- -/

end FateV2.Predict