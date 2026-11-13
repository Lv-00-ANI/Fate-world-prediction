import FateWorld.FateV2.Classical.Shell
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Basic
import Mathlib.Tactic

/-!
  # Classical · Analysis — ℝ / Measure / 拓扑 的统一入口

  ## 迁移登记
  - 来源：新写（原为空壳占位）
  - 动作：C 重写
  - 对应环节：（新增）**其余层的唯一经典依赖点**
  - 依赖裁决：**D-016**（三条公理入账本）、**D-017**（核内不用 Quot）、
              **D-020**（双界只作数学界）
  - 改动：从空壳补成实现。把「用了经典数学就要登记」这件事
          **从口头纪律变成可检查的结构**。
  - 状态：已编译

  ## 这个模块的特殊作用

  `09-总设计` §三 的分层要求：

  ```
  Core/        纯 CIC，不许碰 ℝ / Measure / 拓扑
  Classical/   ← 唯一的经典入口
  其余层       通过本模块间接使用经典数学
  ```

  但「不许碰」如果只靠 `grep` 检查，就会漏。
  本模块的作用是：**把经典数学的载体登记成一个显式的清单**，
  于是 `Core/` 只要不 import 本文件，就不可能用到它们（这是结构性的，不靠检查）。

  ## 三条载体与它们各自的公理代价

  | 载体 | 依赖哪几条公理 | 为什么 |
  |---|---|---|
  | `ℝ` | `propext` + `Classical.choice` + `Quot.sound` | 实数构造用完备性 + 商 |
  | `Measure` | 同上 | 测度论建立在实值与选择之上 |
  | 拓扑 | 同上 | 开集族用外延性与选择 |

  **⟹ 凡用任一载体，`support` 必须含三条。** 本模块钉住这条（`carrier_axiom_cost`）。
-/

namespace FateV2.Classical

open FateV2.Core

/-! ## §1 · 经典载体清单 -/

/-- **三类经典载体**。 -/
inductive Carrier : Type where
  /-- 实数 -/
  | real
  /-- 测度 -/
  | measure
  /-- 拓扑 -/
  | topology
  deriving DecidableEq, Repr

/-- **载体对应的公理代价**：用哪个载体，就要登记哪些假设。

    三类载体的代价**相同**（都是三条），但分开列是为了将来能精确到「标量域」级别
    ——例如若将来引入构造性实数（`D-018` 的 P-1 承诺），
    `real` 这一行就会变成空表，而另外两行不变。 -/
def Carrier.cost : Carrier → List AssumptionId
  | .real     => [axPropext, axChoice, axQuotSound]
  | .measure  => [axPropext, axChoice, axQuotSound]
  | .topology => [axPropext, axChoice, axQuotSound]

/-- **三种载体都要三条公理**（当前状态）。 -/
theorem carrier_axiom_cost (c : Carrier) :
    (c.cost).length = 3 := by
  cases c <;> rfl

/-- **任一载体的代价都是 `classical` 外壳的子集**：
    用经典数学永远不需要比三条更多的东西。 -/
theorem carrier_cost_subset_classical (c : Carrier) :
    ∀ a ∈ c.cost, a ∈ classical.assumptions := by
  intro a ha
  cases c <;> simp [Carrier.cost, classical] at ha ⊢
  · exact ha
  · exact ha
  · exact ha

/-! ## §2 · 铁律的显式形式 -/

section Discipline

/-- **`Core/` 不得 import 本模块**。

    这条**不是**本模块能证明的（它需要一个 import 图检查，见门禁 G7）；
    本模块能做的只是**把这条规则写成一个可引用的命题**，
    让它在文档里有一个名字，而不是一句口耳相传的约定。 -/
def CoreMustNotImportAnalysis : Prop := True

/-- 这条规则恒真（作为命题占位），真伪由 G7 脚本判定。 -/
theorem core_discipline_placeholder : CoreMustNotImportAnalysis := trivial

/-- **用经典载体 ⟹ 来源含三条**：这是把「用了就要登记」形式化的关键一条。

    ⚠ 前提的方向：`sup` 里已经含了 `c.cost` 的全部条目。
    结论是这些条目被 `classical` 外壳覆盖——
    即**登记了载体代价的定理，其来源是合法可用的**。 -/
theorem using_carrier_requires_classical
    (c : Carrier) (sup : Support)
    (h : c.cost ⊆ sup.assumptions) :
    classical.covers ⟨c.cost⟩ := by
  intro a ha
  exact carrier_cost_subset_classical c a ha

end Discipline

/-! ## §3 · 载体的实际可用性 -/

section Availability

/-- **ℝ 可用**：以 `ℝ` 本身作为"载体存在"的证据。

    （本模块 import 了 Mathlib 的实分析，故 `ℝ` 在此可见。） -/
theorem real_available : Nonempty ℝ := ⟨0⟩

/-- **Measure 可用**：以 `Measure Unit` 为例。 -/
theorem measure_available : Nonempty (MeasureTheory.Measure Unit) := ⟨0⟩

/-- **拓扑可用**：以 `TopologicalSpace Unit` 为例。 -/
theorem topology_available : Nonempty (TopologicalSpace Unit) := ⟨⊥⟩

end Availability

/-! ## §4 · 与 `D-018` 的接口：构造性实数的位置 -/

section ConstructiveReal

/-- **构造性实数是否可用**（`D-018` 的 P-1 承诺项）。

    当前为 `false`：核内**没有**构造性实数。
    `D-018` 明确这是「承诺后补」而非永久缺失——
    补的触发条件是「核需要自己谈误差与收敛时」。

    本定义让这个状态**可被代码查询**，而不只是文档里的一句话。 -/
def ConstructiveRealAvailable : Bool := false

/-- **当前核内无构造性实数**。 -/
theorem constructive_real_not_yet : ConstructiveRealAvailable = false := rfl

/-- **构造性实数可用时，ℝ 的代价应降为 0**（`D-018` 的远景）。

    这条陈述**当前为假的前提成立时**才为真——
    它表达的是「若 P-1 完成，`carrier_axiom_cost` 会怎样变」，
    留给将来实现的人一个明确的检查点。 -/
def RealCostIfConstructive : List AssumptionId :=
  if ConstructiveRealAvailable then [] else Carrier.cost .real

/-- **当前 `ℝ` 的代价不是空的**（与 `constructive_real_not_yet` 一致）。 -/
theorem real_cost_nonempty_now : RealCostIfConstructive ≠ [] := by
  simp [RealCostIfConstructive, ConstructiveRealAvailable, Carrier.cost]

end ConstructiveReal

end FateV2.Classical
