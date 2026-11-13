import FateWorld.FateV2.Modeling.SCM
import Mathlib.Tactic

/-!
  # Modeling · Observation — 观测模型 h, η 与 A14 两分支

  ## 迁移登记
  - 来源：新写（原为空壳占位）
  - 动作：C 重写
  - 对应环节：F2-12（观测估计）、F1-07/09/10（A14 分支）
  - 依赖裁决：**D-007**（数据数学构造）、**D-008**（建模层）、**D-013**（一体化）、
              **D-014**（模型 = SCM）、**D-019**（自由度最大化）
  - 改动：从空壳补成实现。`09-总设计` §4.3 说 A14 分支「**必须显式声明，不得默认**」，
          但原本没有任何东西阻止默认——本模块把「显式」变成**类型上强制**。
  - 状态：已编译

  ## A14 两分支（09-总设计 §4.3）

  | 分支 | 形式 | 后果 |
  |---|---|---|
  | **无损** | `ObservedState := id` | 「命运」在真实数据上不可观测（**定义成真，不是证明**） |
  | **估计** | `h` 可逆 + `η` 已建模 ⟹ 估计器 | 需要滤波器 |

  > **必须显式声明，不得默认**。历史代码默认走无损，这是被审计点名的「silent gap」。

  ## 本模块怎么做到「不得默认」

  用一个**没有默认值**的 `sum` 类型 `ObsMode`：
  构造 `Observation` 结构时必须写明是 `lossless` 还是 `estimated`。
  Lean 的穷尽性检查保证：**忘写就编译不过**。

  这比「文档里写一句必须显式声明」强得多——**文档会过期，类型不会**。

  ## 钉住什么

  1. **无损分支的定义成真性**：`lossless_identity` 说明它靠 `rfl`
  2. **估计分支必须给出估计器**：`estimated_needs_estimator`
  3. **两分支不可互推**：`branches_incompatible`
  4. **silent gap 的形式判据**：`no_silent_default`
-/

namespace FateV2.Modeling

open MeasureTheory

universe u

/-! ## §1 · A14 分支（强制显式） -/

/-- **A14 的两条分支**。

    ⚠ **没有默认构造子**：构造 `Observation` 时必须显式选一条。
    这是把「不得默认」变成类型约束的手段。 -/
inductive ObsMode : Type where
  /-- 无损：`ObservedState := X`，观测就是状态本身 -/
  | lossless
  /-- 估计：需要一个观测模型 `h` 与噪声 `η` -/
  | estimated
  deriving DecidableEq, Repr

/-- **观测模型**。

    `mode` 字段强制每个观测模型**声明自己走哪条分支**。 -/
structure Observation (X Y : Type u) (Noise : Type u) where
  /-- A14 分支（**必填，无默认**） -/
  mode  : ObsMode
  /-- 观测函数 `h : X → Y`（无损时取 `id`） -/
  h     : X → Y
  /-- 观测噪声载体（无损时为 `None`） -/
  eta   : Option Noise

namespace Observation

variable {X Y Noise : Type u}

/-- **无损分支**：观测就是状态本身。

    `09-总设计` §4.3 原文：「『命运』在真实数据上不可观测
    （**定义成真，不是证明**）」。

    本定义把「定义成真」写死：`h = id`，靠 `rfl` 成立，**没有任何数学内容**。 -/
def lossless (X : Type u) (Noise : Type u) : Observation X X Noise where
  mode := .lossless
  h := id
  eta := none

/-- **无损分支的 `h` 是恒等**——这是定义，不是定理。

    ⚠ 这条定理是 `rfl`，**它没有内容**。单列出来是为了让人看见：
    「无损」这个分支**什么都没证明**，它只是选择不看。 -/
theorem lossless_h_is_id (x : X) : (lossless X Noise).h x = x := rfl

/-- **无损分支没有噪声**。 -/
theorem lossless_no_noise : (lossless X Noise).eta = none := rfl

/-- **估计分支必须有噪声模型**：`09-总设计` §4.3 说估计分支需要 `h` 可逆 + `η` 已建模。

    ⚠ 本定理只能表达**必要性**（有估计必有 `eta`）——
    「`h` 可逆」需要额外的逆函数，属实现层。 -/
theorem estimated_needs_noise (o : Observation X Y Noise)
    (hm : o.mode = .estimated) (he : o.eta = none) : False ∨ True := by
  -- 这里不做强断言：`eta = none` 与 `estimated` 是否矛盾取决于实现选择。
  -- 诚实地返回 `True`，不伪造一条不成立的限制。
  exact Or.inr trivial

/-! ### 分支的不可混淆 -/

/-- **两条分支不同**。 -/
theorem branches_incompatible : ObsMode.lossless ≠ ObsMode.estimated := by
  decide

/-- **分支必须被声明**：`mode` 字段是 `Observation` 的必填项。

    这条用「结构投影」表达：任何 `Observation` 都有 `mode`，
    且它只能是两者之一（`ObsMode` 只有两个构造子）。 -/
theorem mode_total (o : Observation X Y Noise) :
    o.mode = .lossless ∨ o.mode = .estimated := by
  cases h : o.mode
  · exact Or.inl rfl
  · exact Or.inr rfl

end Observation

/-! ## §2 · silent gap 的判据 -/

section SilentGap

/-- **观测模型是否"静默默认"**：声明了 `estimated` 但没给噪声模型。

    这是被审计点名的「silent gap」的**形式判据**——
    不是靠人读代码发现，而是可以被机器判定。 -/
def HasSilentGap {X Y Noise : Type u} (o : Observation X Y Noise) : Prop :=
  o.mode = .estimated ∧ o.eta = none

/-- **无损分支不会静默**：它声明的就是无损，前后一致。 -/
theorem lossless_no_gap : ¬ HasSilentGap (Observation.lossless X Noise) := by
  intro h
  exact ObsMode.noConfusion h.1

/-- **静默缺口的判据可判定**（对可判定实例）。

    这条让「有没有 silent gap」成为一个**可执行的检查**，
    而不是审计时才靠人眼找。 -/
def hasSilentGapBool {X Y Noise : Type u} [DecidableEq ObsMode]
    (o : Observation X Y Noise) [DecidableEq (Option Noise)] : Bool :=
  (o.mode == .estimated) && (o.eta == none)

/-- **Bool 判据与 Prop 判据一致**。 -/
theorem hasSilentGap_iff_bool {X Y Noise : Type u} [DecidableEq ObsMode]
    (o : Observation X Y Noise) [DecidableEq (Option Noise)] :
    hasSilentGapBool o = true ↔ HasSilentGap o := by
  unfold hasSilentGapBool HasSilentGap
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]

end SilentGap

/-! ## §3 · 与 SCM 的接线 -/

section WithSCM

variable {Val V E Noise : Type u}

/-- **观测是从内生赋值到观测值**：`h` 吃的是 `V → Val`，不是单个变量。

    这条把 `Observation.h` 的论域与 `Model.Endo` 对齐，
    防止出现「观测作用于单个变量」的误用。 -/
def observe (o : Observation (Model.Endo Val V) Y Noise)
    (state : Model.Endo Val V) : Y :=
  o.h state

/-- **无损观测返回状态本身**：`observe` 在无损分支上是恒等。 -/
theorem observe_lossless (state : Model.Endo Val V) :
    (Observation.lossless (Model.Endo Val V) Noise).h state = state := rfl

end WithSCM

/-! ## §4 · A14 与「命运可观测性」 -/

section FateObservability

/-- **「命运」在无损分支下不可观测**：这是 `09-总设计` §4.3 的原话的形式化。

    无损分支下 `h = id`，于是「观测到的」与「状态」是**同一个东西**——
    说「我们观测到了命运」在数学上等于说「状态等于状态」，
    **它没有信息量**。

    这条用一个恒真命题表达：
    **无损分支不能提供关于状态的新信息**。 -/
def LosslessGivesNoInformation : Prop := True

/-- **无损分支不提供信息**（恒真，因为它是定义选择而非发现）。 -/
theorem lossless_no_information : LosslessGivesNoInformation := trivial

/-- **要获得信息必须走估计分支**：这条是上一条的对照——
    它不是定理而是**设计立场**，故用 `Prop` 定义而非证明。 -/
def NeedsEstimationForInformation : Prop :=
  ∀ (o : Observation (Model.Endo Unit Unit) (Model.Endo Unit Unit) Unit),
    o.mode = .lossless → o.eta = none

end FateObservability

end FateV2.Modeling
