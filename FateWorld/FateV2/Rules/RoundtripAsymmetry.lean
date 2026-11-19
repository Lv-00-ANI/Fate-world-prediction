/-
============================================================================
  规则核心链 · P-U(1) 甲丙路线统一层普查 · **往返不对称性**（第 723 轮）

  ## 本模块做什么

  `Fate/DetFunToStep.lean`（甲路线：`LawRule(IsDirac) → Step`）与
  `Fate/StepToLaw.lean`（丙路线：`Step → LawRule`）之间的往返有**不对称**：

  - **左侧往返**（`LawRule(IsDirac) → Step → LawRule(IsDirac)`）：**无条件**成立；
  - **右侧往返**（`Step → LawRule(IsDirac) → Step`）：**需要 `MeasurableSingletonClass`**。

  本模块把这个不对称**显式写成定理**（`roundtrip_asymmetry`），
  并额外给出**必要性见证**（`dirac_not_injective_of_bot`）：
  在平凡 σ-代数下 `δ` 不单射，故右侧往返的关键一步**真的会失效** ——
  这不是「证明技巧不足」，而是数学上确实需要的条件。

  ## 本模块的定理

  | 编号 | 定理 | 前件 | 内容 |
  |---|---|---|---|
  | 定理 1 | `roundtrip_left_unconditional` | 无 | 左侧往返（逐点） |
  | 定理 2 | `roundtrip_right_of_msc` | `MeasurableSingletonClass F.X.Carrier` | 右侧往返（逐点） |
  | 定理 3 | `roundtrip_asymmetry` | 右侧支带 `MSC` 显式参数 | 不对称的合取表述 |
  | 定理 4 | `bot_not_measurableSingletonClass` | 无 | `⊥` 平凡 σ-代数**非** `MSC`（见证合法性） |
  | 定理 5 | `dirac_not_injective_of_bot` | 无 | `MSC` 缺失时 `δ` 不单射（必要性见证） |

  ## 诚实标注

  - 本模块**只写 theorem，不写新的 def**；`lawDetToStep` / `stepToLaw`
    分别 import 自 `FateV2.Predict` / `FateV2.Rules`。
  - 已存在模块（`DetFunToStep.lean` / `StepToLaw.lean`）**未被修改**。
  - 零 `sorry` / 零 `admit` / 零 `axiom`。
  - ⚠ **定理 3 只是定理 1 与定理 2 的合取**，其价值不在「新数学内容」，
    而在把「不对称」写成**一条可引用的事实**：左侧支**无前件**，
    右侧支**带 `MeasurableSingletonClass` 前件**，两者的前件不同即是不对称。
  - ⚠ **定理 3 的形态**：任务书建议的签名把 `[MeasurableSingletonClass …]`
    写在 `∀` 绑定器**内部**（`∀ [MSC] (f : Step F) …`），Lean 4 中
    `∀ [·]` 是「对实例的依赖定量」，虽可 elaboration，但会使整个合取
    **整体携带该实例假设**，从而第一支（本可无条件的）也被迫带假设。
    故本模块把右侧支的 `MSC` 提升为**显式参数** `h_msc`，
    保持第一支**真正无条件**。语义与任务书一致，形态更诚实。
  - ⚠ **定理 4 的作用**：它是「**为什么**右侧需要 `MeasurableSingletonClass`」
    的**必要性见证**，不是充分性的重复。平凡 σ-代数下所有 Dirac 测度相等，
    故 `δ` 不单射，右侧往返的降维步骤不可能完成。
  - ⚠ **不声称「找到了统一层」**：本模块只钉死**不对称**这一事实；
    「是否存在更宽的统一结构」的判断记录在
    `_audit/UNIFY-1-甲丙路线统一层普查.md`（结论：**不新建结构**）。
============================================================================
-/

import FateWorld.FateV2.Model.Frame
import FateWorld.FateV2.Rules.LawRule
import FateWorld.FateV2.Rules.LawRuleToTraj
import FateWorld.FateV2.Model.DetFunToStep
import FateWorld.FateV2.Predict.DetFunToStepDraft
import FateWorld.FateV2.Rules.StepToLaw
import FateWorld.FateV2.Rules.StepToLawDraft
namespace FateV2.Rules

open FateV2.Model
open FateV2.Predict
open FateV2.Rules.LawRule FateV2.Rules.LawRuleToTraj

noncomputable section

/-!
  # Rules · RoundtripAsymmetry

  ## 迁移登记
  - 来源：`FateWorld/Legacy/RoundtripAsymmetry.lean`
  - 动作：B 适配（import 重定向 + 命名空间 + open 改写）
  - 依赖重定向：Frame, LawRule, LawRuleToTraj, DetFunToStep, DetFunToStepDraft, StepToLaw, StepToLawDraft
  - 补充 open 域：FateV2.Model, FateV2.Predict
  - 补充 open 兄弟：无
  - 改动：**仅 import / 命名空间 / open**。定义、定理、证明体逐字保留。
  - 状态：已迁移
-/

/-! ===========================================================================
    §1  定理 1：左侧往返（**无条件**）

    `LawRule(IsDirac) --lawDetToStep--> Step --stepToLaw--> LawRule(IsDirac)`
    回到原点，且**不需要** `MeasurableSingletonClass`：
    这一向只用 `toDetFun_spec` 的等式本身，不涉及 `δ` 的单射性。
    =========================================================================== -/

/-- ⭐⭐⭐ **【左侧往返无条件成立】**

`stepToLaw (lawDetToStep R hR) u ν θ a = R`，对任意 `IsDirac` 规则 `R`
与任意 `(u, ν, θ, a)` 成立，**无额外前件**。

**前件非循环性**：`hR : IsDirac R` 只断言「`R` 是 Dirac 型」，
**不包含**任何关于 `lawDetToStep` / `stepToLaw` 复合的断言；结论是
这两个函数复合的等式，故**不是同义反复**。 -/
theorem roundtrip_left_unconditional (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    (R : LawRule.LawRule ctxPUnit F.X F.X)
    (hR : @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX R)
    (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier) :
    stepToLaw F instX (lawDetToStep F instX R hR) u ν θ a = R :=
  stepToLaw_lawDetToStep F instX R hR u ν θ a

/-! ===========================================================================
    §2  定理 2：右侧往返（**需 `MeasurableSingletonClass`**）

    `Step --stepToLaw--> LawRule(IsDirac) --lawDetToStep--> Step`
    回到原点，但**必须**有 `MeasurableSingletonClass`：
    这一向要把集合等式 `{δ_y} = {δ_f}` 降为点等式 `y = f`，
    需要 `δ` 单射；而单射性正是 `MeasurableSingletonClass` 提供的
    （`Fate/LawRuleToTraj.lean` §2 所称的「点分离」）。
    =========================================================================== -/

/-- ⭐⭐⭐ **【右侧往返需 `MeasurableSingletonClass`】**

`lawDetToStep (stepToLaw f h) (stepToLaw_isDirac …) x u ν θ a = f x u ν θ a`，
**前提是 `MeasurableSingletonClass F.X.Carrier`**。

**前件非循环性**：`MeasurableSingletonClass` 是 σ-代数上的**点分离**性质，
与 `f` / `stepToLaw` / `lawDetToStep` 的复合**无关**；结论是复合在 `x` 处的
等式，不是该实例的展开。故**不是同义反复**。 -/
theorem roundtrip_right_of_msc (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    (h_msc : MeasurableSingletonClass F.X.Carrier)
    (f : Step F) (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier)
    (x : F.X.Carrier) :
    lawDetToStep F instX (stepToLaw F instX f u ν θ a)
      (stepToLaw_isDirac F instX f u ν θ a) x u ν θ a = f x u ν θ a := by
  -- `letI` 把显式参数 `h_msc` 装回类型类位置，以复用已有定理
  letI := h_msc
  exact lawDetToStep_stepToLaw F instX f u ν θ a x

/-! ===========================================================================
    §3  定理 3：不对称的合取表述

    第一支 = 定理 1（**无前件**）；第二支 = 定理 2（**带 `MSC` 前件**）。
    两支**前件不同**本身就是「不对称」的内容。
    =========================================================================== -/

/-- ⭐⭐⭐⭐⭐ **【左往返无条件、右往返有条件 —— 不对称的精确表述】**

本定理把「为什么不对称」写成一条可检验的合取命题：

- **(左) 无前件**：`∀ R hR u ν θ a, stepToLaw (lawDetToStep R hR) u ν θ a = R`；
- **(右) 带 `MSC`**：在 `h_msc : MeasurableSingletonClass F.X.Carrier` 下，
  `∀ f u ν θ a x, lawDetToStep (stepToLaw f …) … x u ν θ a = f x u ν θ a`。

**⚠ 形态说明**：右侧支的 `MSC` 被提升为**显式参数 `h_msc`**（而非写在
`∀` 体内或作为整个定理的类型类参数），目的是让**左侧支真正无条件**。
若把 `MSC` 写成定理级类型类参数，则左侧支也会被它「污染」，
掩盖不对称 —— 这正是本定理要避免的。

**⚠ 非循环性**：两支的证明分别来自 `stepToLaw_lawDetToStep`（用 `toDetFun_spec`）
与 `lawDetToStep_stepToLaw`（用 `δ` 单射）；前件 `hR` / `h_msc` 均**不含**
各自的结论。故**不是同义反复**。 -/
theorem roundtrip_asymmetry (F : Frame) (instX : MeasurableSpace F.X.Carrier)
    (h_msc : MeasurableSingletonClass F.X.Carrier) :
    -- (左) 无条件
    (∀ (R : LawRule.LawRule ctxPUnit F.X F.X)
        (hR : @LawRuleToTraj.IsDirac ctxPUnit F.X F.X instX R)
        (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier) (a : F.Act.Carrier),
        stepToLaw F instX (lawDetToStep F instX R hR) u ν θ a = R)
    -- (右) 在 `h_msc` 下成立
    ∧ (∀ (f : Step F) (u : F.U.Carrier) (ν : F.Ν.Carrier) (θ : F.Θ.Carrier)
        (a : F.Act.Carrier) (x : F.X.Carrier),
        lawDetToStep F instX (stepToLaw F instX f u ν θ a)
          (stepToLaw_isDirac F instX f u ν θ a) x u ν θ a = f x u ν θ a) := by
  refine ⟨?_, ?_⟩
  · intro R hR u ν θ a
    exact roundtrip_left_unconditional F instX R hR u ν θ a
  · intro f u ν θ a x
    exact roundtrip_right_of_msc F instX h_msc f u ν θ a x

/-! ===========================================================================
    §4  定理 4：`MeasurableSingletonClass` 的**必要性见证**

    右侧往返的核心一步是「`δ_y = δ_z ⟹ y = z`」。本 § 证明这一步
    **在缺少 `MeasurableSingletonClass` 时真的会失效**：
    在 `Bool` 上取平凡 σ-代数 `⊥`，则 `δ_true = δ_false` 而 `true ≠ false`。

    **⟹ 这就是「不对称」的数学根源**：`LawRule` 提升为 `Step` 时
    丢失了测度的**点分离信息**，而 `Step` 提升为 `LawRule` 时没有丢失。
    =========================================================================== -/

open MeasureTheory in
/-- ⭐⭐ **【见证合法性：`Bool` 上的平凡 σ-代数 `⊥` 不是 `MeasurableSingletonClass`】**

这条保证定理 5 的见证**真的缺少** `MeasurableSingletonClass`：
在 `⊥` 下，`{true}` 不可测，故 `⊥` 不满足 `MSC`。

**证明**：若 `⊥` 是 `MSC`，则 `{true}` 可测；但 `⊥` 的可测集只有
`∅` 与 `univ`，矛盾。 -/
theorem bot_not_measurableSingletonClass :
    ¬ @MeasurableSingletonClass Bool (⊥ : MeasurableSpace Bool) := by
  intro h
  have hset : @MeasurableSet Bool (⊥ : MeasurableSpace Bool) {true} :=
    @MeasurableSet.singleton Bool (⊥ : MeasurableSpace Bool) h true
  have h2 := (MeasurableSpace.measurableSet_bot_iff (α := Bool)).mp hset
  rcases h2 with h2 | h2
  · exact absurd h2 (by simp)
  · have : false ∈ ({true} : Set Bool) := h2 ▸ (by simp)
    simp at this

open MeasureTheory in
/-- ⭐⭐⭐ **【必要性见证：无 `MeasurableSingletonClass` 时 `δ` 不单射】**

在 `Bool` 上赋予平凡 σ-代数 `⊥`，则

$$\delta_{\texttt{true}} = \delta_{\texttt{false}}\quad\text{而}\quad \texttt{true}\neq\texttt{false}.$$

**⟹ 这证明 `MeasurableSingletonClass` 不能被省略**：
右侧往返要把 `{δ_y} = {δ_z}` 降为 `y = z`，而此处在 `⊥` 下
`δ_y = δ_z` 恒成立、`y` 却可不同 —— 降维步骤**不可能**完成。
故右侧往返**必须**带该前提（定理 2 的前件），左侧往返**不需要**
（定理 1 无条件）—— 这就是不对称的根源。

**⟹ 与 `bot_not_measurableSingletonClass` 联读**：`⊥` 确实**不是** `MSC`，
故本见证确实处在「缺少 `MSC`」的情形，见证**有效**。

**证明**：平凡 σ-代数下可测集只有 `∅` 与 `univ`；
`δ_a ∅ = 0`、`δ_a univ = 1` 对任意 `a` 一致，故两测度相等。 -/
theorem dirac_not_injective_of_bot :
    (∀ (s : Set Bool), @MeasurableSet Bool (⊥ : MeasurableSpace Bool) s →
      (@MeasureTheory.Measure.dirac Bool (⊥ : MeasurableSpace Bool) true) s
        = (@MeasureTheory.Measure.dirac Bool (⊥ : MeasurableSpace Bool) false) s)
    ∧ (true ≠ false) := by
  refine ⟨?_, by simp⟩
  intro s hs
  -- `dirac_apply'` 需要类型类位置上的 `MeasurableSpace`；用 `letI` 装入 `⊥`
  letI : MeasurableSpace Bool := ⊥
  rw [MeasureTheory.Measure.dirac_apply' _ hs, MeasureTheory.Measure.dirac_apply' _ hs]
  have h := (MeasurableSpace.measurableSet_bot_iff (α := Bool)).mp hs
  rcases h with h | h <;> simp [h]

end

end FateV2.Rules