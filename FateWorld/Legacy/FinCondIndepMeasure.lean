import FateWorld.Legacy.FinMeasureBridge
import Mathlib.Probability.Independence.Conditional

/-! ===========================================================================
  §91  ⭐⭐⭐ **桥的第二端**：把嵌入与 `CondIndepFun` 对齐

  **第 87 轮**建成**第一端**（`FinMeasureBridge`）。**本轮**做**第二端**。

  ## ⚠⚠ 修正两处先前的**错误判断**

  | # | 先前判断 | 来源 | 实测结论 |
  |---|---|---|---|
  | 1 | 「有限类型的 `StandardBorelSpace` 需额外构造」| 第 88 轮评估 | **不准确** —— Mathlib 已有 |
  | 2 | 「`CondIndepFun` 因 `autoParam` 无法显式陈述」| 第 89 轮我的判断 | **不准确** —— 只要实例匹配即可 |

  ## ⭐⭐ 真正的障碍（由 `#print` 读出签名后查明）

  **关键事实**：`StandardBorelSpace Ω` 实际是 `@StandardBorelSpace Ω mΩ`
  （携带 `MeasurableSpace`）。
  **故当条件 σ-代数 `m'` 与 `mΩ` 不相等时，
  该实例必须显式给出且匹配 `mΩ`。**

  **且 `weightedCount` 的 `MeasurableSpace` 是乘积实例，
  故 `mΩ` 必须用它（不能用 `letI := ⊤`）。**

  **无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate

namespace FinCondIndepMeasure

open MeasureTheory ProbabilityTheory

universe u

variable {α β γ : Type u}

/-! ### §91.1 三个投影随机变量 -/

/-- **第一投影**：`(x,y,z) ↦ x`。 -/
def projX : (α × β) × γ → α := fun p => p.1.1

/-- **第二投影**：`(x,y,z) ↦ y`。 -/
def projY : (α × β) × γ → β := fun p => p.1.2

/-- **第三投影**：`(x,y,z) ↦ z`。 -/
def projZ : (α × β) × γ → γ := fun p => p.2

/-! ### §91.2 投影的可测性（无需假设） -/

/-- **三个投影都可测**（对任意 `MeasurableSpace` 成立）。

投影的可测性是乘积 σ-代数的结构性质，不需要任何假设。 -/
theorem measurable_projX [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    Measurable (projX : (α × β) × γ → α) :=
  measurable_fst.fst

theorem measurable_projY [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    Measurable (projY : (α × β) × γ → β) :=
  measurable_fst.snd

theorem measurable_projZ [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    Measurable (projZ : (α × β) × γ → γ) :=
  measurable_snd

/-! ### §91.3 有限类型的 `StandardBorelSpace` -/

/-- **有限类型有 `StandardBorelSpace` 实例**（实测确认）。

这修正了第 88 轮评估的预判：它说该实例需额外构造，但 Mathlib 已有。 -/
example (n : ℕ) : StandardBorelSpace (Fin n) := inferInstance

/-- **抽象类型亦有**（须显式 `DiscreteMeasurableSpace` + `Countable`）。

这正是「门槛」的真实内容：不是「需构造」，而是「需显式实例」。 -/
example {δ : Type} [MeasurableSpace δ] [DiscreteMeasurableSpace δ] [Countable δ] :
    StandardBorelSpace δ := inferInstance

/-! ### §91.4 桥的第二端（可陈述形式） -/

/-- **桥的第二端（可陈述的命题形状）**。

在嵌入测度 `weightedCount p` 下，以「由 Z 生成的 σ-代数」为条件，
X 与 Y 条件独立。

本节只**陈述命题形状**，**不声称已完成** ——
它的证明需要条件期望核的显式计算（见 §91.5 的登记）。

它不含空洞占位：是 `CondIndepFun` 的具体实例化（真实的 `Prop`），
而非 `True` 或 `1 = 1`，故「桥可陈述」这件事本身是可检验的。 -/
noncomputable def bridgeStatement
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace γ]
    [Countable α] [Countable β] [Countable γ]
    (p : FiniteCondIndep.FinJoint α β γ) : Prop :=
  @CondIndepFun ((α × β) × γ)
    (MeasurableSpace.comap (projZ : (α × β) × γ → γ) inferInstance)
    (inferInstance : MeasurableSpace ((α × β) × γ))
    inferInstance
    (MeasurableSpace.comap_le_iff_le_map.mpr measurable_projZ)
    α β inferInstance inferInstance
    (projX : (α × β) × γ → α)
    (projY : (α × β) × γ → β)
    (FinMeasureBridge.weightedCount p)
    (FinMeasureBridge.weightedCount_isFiniteMeasure p)

/-! ### §91.5 精确登记 -/

/-! **桥的第二端的状态**（精确登记，不假装完成）。

| 构件 | 状态 |
|---|---|
| `projX` / `projY` / `projZ` | 已建 |
| `measurable_projX/Y/Z` | 已证（无需假设）|
| `StandardBorelSpace` 在有限类型可用 | 实测确认（修正评估预判）|
| `weightedCount_isFiniteMeasure` | 已证（第 91 轮）|
| `bridgeStatement`（命题可陈述） | 已建 |
| `CondIndepFin p → bridgeStatement p`（证明） | ✅ **第 171 轮已证**（见 `Fate/BridgeFinal.lean` 的 `condIndepFin_to_bridge`）|

> ⚠ **第 175 轮更正**：上表原写此行为「**未做**」，**实际已于第 171 轮完成**
> （见 `Fate/BridgeFinal.lean` 的 `condIndepFin_to_bridge`）。逆方向亦于第 174 轮完成
> （`Fate/BridgeReverse.lean` 的 `bridge_to_condIndepFin`），二者合起来即双向等价
> （`Fate/BridgeEquiv.lean` 的 `condIndepFin_iff_bridge`）。（由第 175 轮代理 E1 的评估发现。）

证明的**历史难点**：
`Kernel.IndepFun f g (condExpKernel μ m') (μ.trim hm')`，
涉及条件期望核与测度截断。而 `weightedCount` 是有限加权计数，
二者之间的桥需要显式计算条件期望在有限测度上的取值 ——
这是测度论的具体工作，不是「不可做」。

⚠⚠ **第 110 轮删除**：此处原有
`theorem bridge_second_end_status : (1 : ℕ) = 1 := rfl` ——
**它是一个**空洞占位**（`1 = 1` 不承载任何内容），
**故删除**，上文的说明保留为模块文档。

**⚠ 本删除的依据由服务器端子代理 **G2-vacuous**（第 110 轮）发现** ——
**我第 109 轮的删除脚本**只做成了 4 个文件中的 2 个**（如实登记这一失误）。 -/

end FinCondIndepMeasure

end Fate
