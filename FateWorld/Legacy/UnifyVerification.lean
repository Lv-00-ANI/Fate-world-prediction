import FateWorld.Legacy.Frame

/-! ===========================================================================
  §96  ⭐⭐⭐ **裁决 P 落地的验证**：链式组合现在**类型正确**

  依作者裁决 P（选**乙**）：统一 `StateSpace` 与 `OutSpace`。

  **本节验证该统一的核心收益**：
  原先（统一前），链式组合在类型上**不可能** —— 因为
  `Rule` 的签名是 `Rule (C) (X : StateSpace) (Y : OutSpace)`，
  故 `Rule C X Y → Rule C Y Z` 需要 `Y` 同时是 `OutSpace` 和 `StateSpace`。

  统一后（`OutSpace := StateSpace`），**该组合变为类型正确**。

  **无硬编码**（依作者裁决 Q-1）。
  =========================================================================== -/

namespace Fate

namespace UnifyVerification

open MeasureTheory

universe u

/-- ⭐⭐⭐ **链式组合现在类型正确**（**这是裁决 P 的核心收益**）。

统一前：`Rule C X Y → Rule C Y Z` **类型错误**。
统一后：**它正确**，因为 `OutSpace = StateSpace`。

⚠ 此处只**登记类型正确性** ——
组合的**语义**在规格开放问题 5.1 中尚未给出，
故本定义**不假装已实现语义**（依第 86 轮评估的建议）。 -/
def chainCompType {C : CtxSpace} {X Y Z : StateSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] [MeasurableSpace Z.Carrier]
    (R1 : Rule C X Y) (R2 : Rule C Y Z) : Rule C X Y × Rule C Y Z :=
  (R1, R2)

/-- ⭐⭐ **统一后 `OutSpace` 与 `StateSpace` 是同一个类型**。 -/
example : OutSpace = StateSpace := rfl

/-- ⭐⭐ **统一后 `OutSpace` 也带 `TopologicalSpace`**
（**这是「增强」的部分**：原先 `OutSpace` 只有 `Carrier`）。 -/
example (Y : OutSpace) : TopologicalSpace Y.Carrier := Y.topo

/-- ⭐⭐ **统一后 `OutSpace` 也带 `MeasurableSpace`**。 -/
example (Y : OutSpace) : MeasurableSpace Y.Carrier := Y.meas

/-- ⭐⭐⭐ **`Frame.Comb` 的签名与统一后相容**（**推广性**）。 -/
example {C : CtxSpace} {X Y : StateSpace}
    [MeasurableSpace X.Carrier] [MeasurableSpace Y.Carrier] :
    Comb C X Y = (Rule C X Y -> Rule C X Y -> Rule C X Y) := rfl

end UnifyVerification

end Fate
